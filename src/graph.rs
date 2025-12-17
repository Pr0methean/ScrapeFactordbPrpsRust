use crate::Factor::Complex;
use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::ComplexFactor;
use crate::algebraic::ComplexFactor::Multiply;
use crate::algebraic::Factor::Numeric;
use crate::algebraic::div_exact;
use crate::algebraic::{
    Factor, NumericFactor, estimate_log10, evaluate_as_numeric, find_factors_of_numeric,
    find_unique_factors,
};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};
use crate::graph::FactorsKnownToFactorDb::{NotQueried, NotUpToDate, UpToDate};
use crate::net::NumberStatus::{FullyFactored, Prime};
use crate::net::{
    FactorDbClient, FactorDbClientReadIdsAndExprs, NumberStatus, NumberStatusExt,
    ProcessedStatusApiResponse,
};
use crate::{FAILED_U_SUBMISSIONS_OUT, NumberLength, NumberSpecifier, SUBMIT_FACTOR_MAX_ATTEMPTS};
use async_backtrace::framed;
use gryf::Graph;
use gryf::adapt::Subgraph;
use gryf::algo::Connected;
use gryf::core::facts::complete_graph_edge_count;
use gryf::core::id::{DefaultId, VertexId};
use gryf::core::marker::{Directed, Direction, Incoming, Outgoing};
use gryf::storage::{AdjMatrix, Stable};
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use rand::rng;
use rand::seq::SliceRandom;
use replace_with::replace_with_or_abort;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::mem::replace;

pub type EntryId = u128;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Divisibility {
    NotFactor,
    Transitive,
    Direct,
}

pub type DivisibilityGraph = Graph<
    Factor,
    Divisibility,
    Directed,
    Stable<AdjMatrix<Factor, Divisibility, Directed, DefaultId>>,
>;

pub struct FactorData {
    pub divisibility_graph: DivisibilityGraph,
    pub deleted_synonyms: BTreeMap<VertexId, VertexId>,
    pub number_facts_map: BTreeMap<VertexId, NumberFacts>,
    pub vertex_id_by_expr: BTreeMap<Factor, VertexId>,
    pub vertex_id_by_entry_id: BTreeMap<EntryId, VertexId>,
}

impl Default for FactorData {
    fn default() -> Self {
        FactorData {
            divisibility_graph: Graph::new_directed_in(AdjMatrix::new()).stabilize(),
            deleted_synonyms: BTreeMap::new(),
            number_facts_map: BTreeMap::new(),
            vertex_id_by_entry_id: BTreeMap::new(),
            vertex_id_by_expr: BTreeMap::new(),
        }
    }
}

pub fn rule_out_divisibility(data: &mut FactorData, nonfactor: VertexId, dest: VertexId) {
    let nonfactor = to_real_vertex_id(nonfactor, &mut data.deleted_synonyms);
    let dest = to_real_vertex_id(dest, &mut data.deleted_synonyms);
    if nonfactor == dest {
        // happens because of recursion
        return;
    }
    if get_edge(
        &data.divisibility_graph,
        nonfactor,
        dest,
        &mut data.deleted_synonyms,
    )
    .is_some()
    {
        return;
    }
    debug!("rule_out_divisibility: nonfactor {nonfactor:?}, dest {dest:?}");
    data.divisibility_graph.add_edge(nonfactor, dest, NotFactor);
    for (neighbor, divisibility) in neighbor_vids(&data.divisibility_graph, dest, Incoming) {
        if neighbor == nonfactor {
            continue;
        }
        if matches!(divisibility, Direct | Transitive) {
            // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
            rule_out_divisibility(data, nonfactor, neighbor);
        }
    }
}

pub fn propagate_divisibility(
    data: &mut FactorData,
    factor: VertexId,
    dest: VertexId,
    transitive: bool,
) {
    let factor = to_real_vertex_id(factor, &mut data.deleted_synonyms);
    let dest = to_real_vertex_id(dest, &mut data.deleted_synonyms);
    if factor == dest {
        // happens because of recursion
        return;
    }
    let edge = get_edge_mut(data, factor, dest);
    match edge {
        Some(Direct) | Some(NotFactor) => return,
        Some(Transitive) => {
            if transitive {
                return;
            } else {
                *edge.unwrap() = Direct;
            }
        }
        None => {
            data.divisibility_graph.add_edge(
                factor,
                dest,
                if transitive { Transitive } else { Direct },
            );
        }
    }
    debug!("propagate_divisibility: factor {factor:?}, dest {dest:?}");
    rule_out_divisibility(data, dest, factor);
    for (neighbor, divisibility) in neighbor_vids(&data.divisibility_graph, dest, Outgoing) {
        if neighbor == factor {
            continue;
        }
        match divisibility {
            NotFactor => {
                // if factor divides dest_factor and dest_factor doesn't divide neighbor,
                // then factor doesn't divide neighbor
                rule_out_divisibility(data, neighbor, factor);
            }
            _ => {
                propagate_divisibility(data, factor, neighbor, true);
            }
        }
    }
}

fn as_specifier(factor_vid: VertexId, data: &mut FactorData) -> NumberSpecifier {
    if let Some(facts) = facts_of(
        &data.number_facts_map,
        factor_vid,
        &mut data.deleted_synonyms,
    ) && let Some(factor_entry_id) = facts.entry_id
    {
        Id(factor_entry_id)
    } else {
        let factor = get_vertex(
            &data.divisibility_graph,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        factor
            .known_id()
            .map(Id)
            .unwrap_or_else(|| Expression(factor.clone()))
    }
}

pub fn get_edge(
    divisibility_graph: &DivisibilityGraph,
    source: VertexId,
    dest: VertexId,
    deleted_synonyms: &mut BTreeMap<VertexId, VertexId>,
) -> Option<Divisibility> {
    Some(*divisibility_graph.edge(divisibility_graph.edge_id_any(
        to_real_vertex_id(source, deleted_synonyms),
        to_real_vertex_id(dest, deleted_synonyms),
    )?)?)
}

pub fn get_edge_mut(
    data: &mut FactorData,
    source: VertexId,
    dest: VertexId,
) -> Option<&mut Divisibility> {
    data.divisibility_graph
        .edge_mut(data.divisibility_graph.edge_id_any(
            to_real_vertex_id(source, &mut data.deleted_synonyms),
            to_real_vertex_id(dest, &mut data.deleted_synonyms),
        )?)
}

pub fn add_factor_node(
    data: &mut FactorData,
    factor: Factor,
    root_vid: Option<VertexId>,
    mut entry_id: Option<EntryId>,
    http: &impl FactorDbClient,
) -> (VertexId, bool) {
    let existing_vertex = data
        .vertex_id_by_expr
        .get(&factor)
        .map(|vertex_id| to_real_vertex_id(*vertex_id, &mut data.deleted_synonyms));
    let matching_vid = entry_id
        .and_then(|entry_id| data.vertex_id_by_entry_id.get(&entry_id))
        .map(|vertex_id| to_real_vertex_id(*vertex_id, &mut data.deleted_synonyms));
    let (merge_dest, added) = existing_vertex
        .or(matching_vid)
        .map(|x| (x, false))
        .unwrap_or_else(|| {
            let factor_vid = data.divisibility_graph.add_vertex(factor.clone());
            data.vertex_id_by_expr.insert(factor.clone(), factor_vid);
            let factor_numeric = evaluate_as_numeric(&factor);
            let (lower_bound_log10, upper_bound_log10) = estimate_log10(&factor);
            let specifier = as_specifier(factor_vid, data);
            let cached = http
                .cached_factors(&specifier)
                .or(factor_numeric.map(|eval| {
                    let factors: Box<[_]> = find_factors_of_numeric(eval).into_keys().collect();
                    ProcessedStatusApiResponse {
                        status: Some(if factors.len() == 1 {
                            Prime
                        } else {
                            FullyFactored
                        }),
                        factors,
                        id: Numeric(eval).known_id(),
                    }
                }));
            // Only full factorizations are cached or obtained via evaluate_as_numeric.
            let mut has_cached = false;
            let (last_known_status, factors_known_to_factordb) = if let Some(cached) = cached {
                entry_id = entry_id.or(cached.id);
                if let Some(entry_id) = entry_id {
                    data.vertex_id_by_entry_id.insert(entry_id, factor_vid);
                }
                has_cached = true;
                let mut cached_subfactors = Vec::with_capacity(cached.factors.len());
                for subfactor in cached.factors {
                    let (subfactor_vid, _) = if subfactor == factor {
                        (factor_vid, false)
                    } else {
                        let entry_id = subfactor.known_id();
                        add_factor_node(data, subfactor, root_vid, entry_id, http)
                    };
                    cached_subfactors.push(subfactor_vid);
                }
                (cached.status, UpToDate(cached_subfactors))
            } else {
                if let Some(entry_id) = entry_id {
                    data.vertex_id_by_entry_id.insert(entry_id, factor_vid);
                }
                (None, NotQueried)
            };
            data.number_facts_map.insert(
                factor_vid,
                NumberFacts {
                    last_known_status,
                    factors_known_to_factordb,
                    numeric_value: factor_numeric,
                    lower_bound_log10,
                    upper_bound_log10,
                    entry_id,
                    checked_for_listed_algebraic: has_cached,
                    checked_in_factor_finder: has_cached,
                    expression_form_checked_in_factor_finder: has_cached,
                    checked_with_root_denominator: has_cached,
                },
            );
            (factor_vid, true)
        });
    if *get_vertex(
        &data.divisibility_graph,
        merge_dest,
        &mut data.deleted_synonyms,
    ) != factor
    {
        merge_equivalent_expressions(data, root_vid, merge_dest, factor, http);
    }
    if let Some(matching_vid) = matching_vid
        && merge_dest != matching_vid
    {
        neighbor_vids(&data.divisibility_graph, matching_vid, Incoming)
            .into_iter()
            .for_each(|(neighbor_vid, divisibility)| {
                propagate_transitive_divisibility(data, neighbor_vid, merge_dest, divisibility)
            });
        neighbor_vids(&data.divisibility_graph, matching_vid, Outgoing)
            .into_iter()
            .for_each(|(neighbor_vid, divisibility)| {
                propagate_transitive_divisibility(data, merge_dest, neighbor_vid, divisibility)
            });
        data.deleted_synonyms.insert(matching_vid, merge_dest);
        let old_factor = data.divisibility_graph.remove_vertex(matching_vid).unwrap();
        let old_facts = data.number_facts_map.remove(&matching_vid).unwrap();
        merge_equivalent_expressions(data, root_vid, merge_dest, old_factor, http);
        replace_with_or_abort(
            facts_of_mut(
                &mut data.number_facts_map,
                merge_dest,
                &mut data.deleted_synonyms,
            ),
            |facts| facts.merged_with(old_facts),
        );
    }
    (merge_dest, added)
}

fn propagate_transitive_divisibility(
    data: &mut FactorData,
    from: VertexId,
    to: VertexId,
    divisibility: Divisibility,
) {
    match divisibility {
        Direct => propagate_divisibility(data, from, to, false),
        Transitive => propagate_divisibility(data, from, to, true),
        NotFactor => rule_out_divisibility(data, from, to),
    }
}

fn neighbor_vids(
    divisibility_graph: &DivisibilityGraph,
    vertex_id: VertexId,
    direction: Direction,
) -> Vec<(VertexId, Divisibility)> {
    divisibility_graph
        .neighbors_directed(vertex_id, direction)
        .map(|neighbor_ref| {
            (
                neighbor_ref.id,
                *divisibility_graph.edge(neighbor_ref.edge).unwrap(),
            )
        })
        .collect::<Vec<_>>()
}

#[inline(always)]
pub fn to_real_vertex_id(
    mut vertex_id: VertexId,
    deleted_synonyms: &mut BTreeMap<VertexId, VertexId>,
) -> VertexId {
    let mut synonyms_to_forward = Vec::new();
    while let Some(synonym) = deleted_synonyms.get(&vertex_id) {
        synonyms_to_forward.push(*synonym);
        vertex_id = to_real_vertex_id(*synonym, deleted_synonyms);
    }
    synonyms_to_forward.pop(); // last one found points to the real vertex ID
    for synonym in synonyms_to_forward {
        deleted_synonyms.insert(vertex_id, synonym);
    }
    vertex_id
}

#[inline(always)]
pub fn get_vertex<'a, 'b: 'a>(
    divisibility_graph: &'b DivisibilityGraph,
    vertex_id: VertexId,
    deleted_synonyms: &'a mut BTreeMap<VertexId, VertexId>,
) -> &'b Factor {
    divisibility_graph
        .vertex(to_real_vertex_id(vertex_id, deleted_synonyms))
        .unwrap()
}

#[inline(always)]
pub fn get_vertices<'a, 'b: 'a, const N: usize>(
    divisibility_graph: &'b DivisibilityGraph,
    vertex_ids: [VertexId; N],
    deleted_synonyms: &'a mut BTreeMap<VertexId, VertexId>,
) -> [&'b Factor; N] {
    vertex_ids
        .into_iter()
        .map(|vertex_id| {
            divisibility_graph
                .vertex(to_real_vertex_id(vertex_id, deleted_synonyms))
                .unwrap()
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub fn is_known_factor(
    data: &mut FactorData,
    factor_vid: VertexId,
    composite_vid: VertexId,
) -> bool {
    factor_vid != composite_vid
        && (matches!(
            get_edge(
                &data.divisibility_graph,
                factor_vid,
                composite_vid,
                &mut data.deleted_synonyms
            ),
            Some(Direct) | Some(Transitive)
        ) || Connected::on(
            &Subgraph::new(&data.divisibility_graph)
                .filter_edge(|edge_id, graph, _| graph.edge(edge_id).copied() != Some(NotFactor)),
        )
        .between(&factor_vid, &composite_vid)
        .strong()
        .run()
        .is())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FactorsKnownToFactorDb {
    NotQueried,
    NotUpToDate(Vec<VertexId>),
    UpToDate(Vec<VertexId>),
}

impl FactorsKnownToFactorDb {
    pub(crate) fn to_vec(&self) -> Vec<VertexId> {
        match self {
            NotQueried => vec![],
            NotUpToDate(factors) | UpToDate(factors) => factors.clone(),
        }
    }
}

impl FactorsKnownToFactorDb {
    fn len(&self) -> usize {
        match self {
            NotQueried => 0,
            NotUpToDate(factors) | UpToDate(factors) => factors.len(),
        }
    }

    fn needs_update(&self) -> bool {
        match self {
            UpToDate(_) => false,
            NotUpToDate(_) => true,
            NotQueried => true,
        }
    }
}

#[derive(Debug)]
pub struct NumberFacts {
    last_known_status: Option<NumberStatus>,
    factors_known_to_factordb: FactorsKnownToFactorDb,
    numeric_value: Option<NumericFactor>,
    lower_bound_log10: NumberLength,
    upper_bound_log10: NumberLength,
    pub(crate) entry_id: Option<EntryId>,
    checked_for_listed_algebraic: bool,
    checked_in_factor_finder: bool,
    expression_form_checked_in_factor_finder: bool,
    checked_with_root_denominator: bool,
}

impl PartialEq<Self> for NumberFacts {
    fn eq(&self, other: &Self) -> bool {
        if let Some(entry_id) = self.entry_id
            && other.entry_id == Some(entry_id)
        {
            true
        } else {
            self.factors_known_to_factordb == other.factors_known_to_factordb
        }
    }
}

impl NumberFacts {
    #[inline(always)]
    pub(crate) fn is_known_fully_factored(&self) -> bool {
        self.last_known_status.is_known_fully_factored()
    }
    #[inline(always)]
    pub(crate) fn is_final(&self) -> bool {
        self.is_known_fully_factored() && !self.needs_update()
    }
    #[inline(always)]
    pub(crate) fn needs_update(&self) -> bool {
        self.factors_known_to_factordb.needs_update()
    }

    /// True if add_factors_to_graph won't do anything (other than pick up factors someone else has
    /// submitted).
    #[inline(always)]
    pub(crate) fn is_fully_processed(&self) -> bool {
        !self.needs_update()
            && self.checked_for_listed_algebraic
            && self.expression_form_checked_in_factor_finder
            && self.checked_in_factor_finder
    }
    fn marked_stale(self) -> Self {
        if self.is_final() {
            return self;
        }
        if let UpToDate(factors) = self.factors_known_to_factordb {
            NumberFacts {
                factors_known_to_factordb: NotUpToDate(factors),
                ..self
            }
        } else {
            self
        }
    }
    pub fn merged_with(self, other: Self) -> Self {
        NumberFacts {
            lower_bound_log10: self.lower_bound_log10.max(other.lower_bound_log10),
            upper_bound_log10: self.upper_bound_log10.min(other.upper_bound_log10),
            numeric_value: self.numeric_value.or(other.numeric_value),
            entry_id: self.entry_id.or(other.entry_id),
            checked_for_listed_algebraic: self.checked_for_listed_algebraic
                || other.checked_for_listed_algebraic,
            last_known_status: self.last_known_status.max(other.last_known_status),
            factors_known_to_factordb: match self
                .factors_known_to_factordb
                .len()
                .cmp(&other.factors_known_to_factordb.len())
            {
                Less => other.factors_known_to_factordb,
                Greater => self.factors_known_to_factordb,
                Equal => match self.factors_known_to_factordb {
                    UpToDate(f) => {
                        if matches!(other.factors_known_to_factordb, UpToDate(_)) {
                            UpToDate(f)
                        } else {
                            NotUpToDate(
                                f.into_iter()
                                    .chain(other.factors_known_to_factordb.to_vec())
                                    .sorted_unstable()
                                    .unique()
                                    .collect(),
                            )
                        }
                    }
                    x => x,
                },
            },
            checked_in_factor_finder: self.checked_in_factor_finder
                && other.checked_in_factor_finder,
            expression_form_checked_in_factor_finder: self.expression_form_checked_in_factor_finder
                && other.expression_form_checked_in_factor_finder,

            // root_denominator only has to be done with one or the other, because it doesn't depend
            // on the expression form among equivalents
            checked_with_root_denominator: self.checked_with_root_denominator
                || other.checked_with_root_denominator,
        }
    }
}

// If we've received too many "Does not divide" responses since the last accepted factor, abort.
// This is meant to ensure we don't waste too much time on a job much better suited to a more
// sophisticated algebra system.
const DND_ABORT_THRESHOLD: usize = 30;

#[inline(always)]
fn dedup_and_shuffle<T: Ord>(deque: &mut VecDeque<T>) {
    let deque_as_set = BTreeSet::from_iter(deque.drain(..));
    deque.extend(deque_as_set);
    deque.make_contiguous().shuffle(&mut rng());
}

#[framed]
pub async fn find_and_submit_factors(
    http: &mut impl FactorDbClientReadIdsAndExprs,
    id: EntryId,
    digits_or_expr: HipStr<'static>,
    skip_looking_up_known: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let mut data = FactorData::default();
    let root_factor = Factor::from(digits_or_expr.as_str());
    let (root_vid, _) = if !skip_looking_up_known && !digits_or_expr.contains("...") {
        add_factor_node(&mut data, root_factor, None, Some(id), http)
    } else {
        let ProcessedStatusApiResponse {
            factors: known_factors,
            status,
            ..
        } = http.known_factors_as_digits(Id(id), false, true).await;
        if status.is_known_fully_factored() {
            warn!("{id}: Already fully factored");
            return true;
        }
        match known_factors.len() {
            0 => add_factor_node(&mut data, root_factor, None, Some(id), http),
            _ => {
                let (root_node, _) = add_factor_node(&mut data, root_factor, None, Some(id), http);
                let root_factors = UpToDate(if known_factors.len() > 1 {
                    known_factors
                        .into_iter()
                        .map(|known_factor| {
                            let entry_id = known_factor.known_id();
                            let (factor_vid, added) = add_factor_node(
                                &mut data,
                                known_factor,
                                Some(root_node),
                                entry_id,
                                http,
                            );
                            if added {
                                propagate_divisibility(&mut data, factor_vid, root_node, false);
                                digits_or_expr_full.push(factor_vid);
                            }
                            factor_vid
                        })
                        .collect()
                } else {
                    vec![root_node]
                });
                let root_facts = facts_of_mut(
                    &mut data.number_facts_map,
                    root_node,
                    &mut data.deleted_synonyms,
                );
                root_facts.factors_known_to_factordb = root_factors;
                root_facts.last_known_status = status;
                (root_node, true)
            }
        }
    };
    debug!(
        "{id}: Root node for {digits_or_expr} is {} with vertex ID {root_vid:?}",
        get_vertex(
            &data.divisibility_graph,
            root_vid,
            &mut data.deleted_synonyms
        )
    );
    if skip_looking_up_known {
        let root_facts = facts_of_mut(
            &mut data.number_facts_map,
            root_vid,
            &mut data.deleted_synonyms,
        );
        root_facts.factors_known_to_factordb = UpToDate(vec![root_vid]);
    }
    digits_or_expr_full.push(root_vid);
    let mut factor_found = false;
    let mut accepted_factors = 0;
    let mut any_unprocessed = false;
    for factor_vid in digits_or_expr_full.into_iter().rev() {
        factor_found |= !add_factors_to_graph(http, &mut data, root_vid, factor_vid)
            .await
            .is_empty();
        any_unprocessed |= !data
            .number_facts_map
            .get(&factor_vid)
            .unwrap()
            .is_fully_processed();
    }
    if !factor_found && !any_unprocessed {
        info!("{id}: No factors to submit");
        return false;
    }
    // Simplest case: try submitting all factors as factors of the root
    let (root_denominator_terms, root_denominator) = if let Complex(c) = get_vertex(
        &data.divisibility_graph,
        root_vid,
        &mut data.deleted_synonyms,
    ) && let ComplexFactor::Divide {
        ref right,
        right_hash,
        ..
    } = **c
    {
        let multiply = Complex(
            Multiply {
                terms_hash: right_hash,
                terms: right.clone(),
            }
            .into(),
        );
        (Some(right.clone()), Some(multiply))
    } else {
        (None, None)
    };
    let mut dnd_since_last_accepted = 0;
    let mut known_factors = vertex_ids_except::<VecDeque<_>>(&mut data, root_vid);
    known_factors.make_contiguous().shuffle(&mut rng());
    let mut factors_to_submit_in_graph = VecDeque::new();
    while let Some(factor_vid) = known_factors.pop_front() {
        let factor = get_vertex(
            &data.divisibility_graph,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        debug!("{id}: Factor {factor} has vertex ID {factor_vid:?}");
        match get_edge(
            &data.divisibility_graph,
            factor_vid,
            root_vid,
            &mut data.deleted_synonyms,
        ) {
            Some(Direct) | Some(NotFactor) => {
                info!("{id}: Skipping {factor} because it's already linked to {digits_or_expr}");
                // This has been submitted directly to the root already, so it's probably already been
                // factored out of all other divisors.
                continue;
            }
            _ => {}
        }
        if factor.is_elided() {
            // Can't submit a factor that we can't express, but
            // running add_factors_to_graph may provide an equivalent expression, else we can save
            // it in case we find out the ID later
            info!("{id}: Temporarily skipping {factor} because digits are missing");
            let factors_of_factor =
                add_factors_to_graph(http, &mut data, root_vid, factor_vid).await;
            if !factors_of_factor.is_empty() {
                factors_to_submit_in_graph.extend(factors_of_factor);
                dedup_and_shuffle(&mut factors_to_submit_in_graph);
            }
            if !factors_to_submit_in_graph.contains(&factor_vid) {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
            continue;
        }
        match http.try_report_factor(Id(id), factor).await {
            AlreadyFullyFactored => return true,
            Accepted => {
                propagate_divisibility(&mut data, factor_vid, root_vid, false);
                replace_with_or_abort(
                    facts_of_mut(
                        &mut data.number_facts_map,
                        root_vid,
                        &mut data.deleted_synonyms,
                    ),
                    NumberFacts::marked_stale,
                );
                dnd_since_last_accepted = 0;
                accepted_factors += 1;
            }
            DoesNotDivide => {
                dnd_since_last_accepted += 1;
                if dnd_since_last_accepted >= DND_ABORT_THRESHOLD {
                    error!(
                        "{id}: Aborting due to too many 'does not divide' responses with no acceptances"
                    );
                    return accepted_factors > 0;
                }
                let subfactors = add_factors_to_graph(http, &mut data, root_vid, factor_vid).await;
                let subfactors_found = !subfactors.is_empty();
                if subfactors_found {
                    factors_to_submit_in_graph.extend(subfactors);
                    dedup_and_shuffle(&mut factors_to_submit_in_graph);
                }
                if !subfactors_found && let Some(ref root_denominator) = root_denominator {
                    facts_of_mut(
                        &mut data.number_facts_map,
                        factor_vid,
                        &mut data.deleted_synonyms,
                    )
                    .checked_with_root_denominator = true;
                    let factor = get_vertex(
                        &data.divisibility_graph,
                        factor_vid,
                        &mut data.deleted_synonyms,
                    );
                    if root_denominator.may_be_proper_divisor_of(factor) {
                        let divided = div_exact(factor, root_denominator).unwrap_or_else(|| {
                            Factor::divide(
                                factor.clone(),
                                root_denominator_terms.clone().unwrap().into_iter(),
                            )
                        });
                        let (divided_vid, added) =
                            add_factor_node(&mut data, divided, Some(root_vid), None, http);
                        if added {
                            factors_to_submit_in_graph.push_back(divided_vid);
                            // Don't apply this recursively, except when divided was already in
                            // the graph for another reason
                            facts_of_mut(
                                &mut data.number_facts_map,
                                divided_vid,
                                &mut data.deleted_synonyms,
                            )
                            .checked_with_root_denominator = true;
                        }
                    }
                }
            }
            OtherError => {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
        }
    }
    if factors_to_submit_in_graph.is_empty() {
        info!("{id}: {accepted_factors} factors accepted in a single pass");
        return accepted_factors > 0;
    }

    // A submission failed retryably, so now it gets more complicated:
    // (1) We may have found a false factor, in which case we should try submitting factors of that
    //     false factor if there are any.
    // (2) The number may have exceeded the site's capacity because it has too many factors already
    //     known, in which case we should submit the remaining factors to the cofactors rather than
    //     directly to the root.
    // (3) If both (1) and (2) apply, then we may end up with a factor that's a factor of multiple
    //     cofactors, so we need to report it to *all* of them to ensure FactorDB knows its full
    //     exponent.
    let mut iters_without_progress = 0;
    let mut iters_to_next_report = 0;
    info!(
        "{id}: {} factors left to submit after first pass",
        factors_to_submit_in_graph.len()
    );
    'graph_iter: while !facts_of(&data.number_facts_map, root_vid, &mut data.deleted_synonyms)
        .expect("{id}: Reached 'graph_iter when root not entered in number_facts_map")
        .is_known_fully_factored()
        && let node_count = data.divisibility_graph.vertex_count()
        && iters_without_progress < node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        && let Some(factor_vid) = factors_to_submit_in_graph.pop_front()
        && let edge_count = data.divisibility_graph.edge_count()
        && let complete_graph_edge_count = complete_graph_edge_count::<Directed>(node_count)
        && edge_count < complete_graph_edge_count
    {
        if iters_to_next_report == 0 {
            iters_to_next_report = node_count.min(100);
            let (direct_divisors, non_factors) = data
                .divisibility_graph
                .edges()
                .map(|e| match *e.attr {
                    Direct => (1, 0),
                    NotFactor => (0, 1),
                    _ => (0, 0),
                })
                .reduce(|(x1, y1), (x2, y2)| (x1 + x2, y1 + y2))
                .unwrap_or((0, 0));
            info!(
                "{id}: Divisibility graph has {node_count} vertices and {edge_count} edges \
            ({:.2}% fully connected). {direct_divisors} confirmed-known divides relations, \
            {non_factors} ruled out. \
        {accepted_factors} factors accepted so far. {} fully factored numbers. {} known entry IDs",
                edge_count as f64 * 100.0 / complete_graph_edge_count as f64,
                data.number_facts_map
                    .values()
                    .filter(|facts| facts.is_known_fully_factored())
                    .count(),
                data.number_facts_map
                    .values()
                    .filter(|facts| facts.entry_id.is_some())
                    .count()
            );
        }
        iters_without_progress += 1;
        iters_to_next_report -= 1;
        // root can't be a factor of any other number we'll encounter
        rule_out_divisibility(&mut data, root_vid, factor_vid);
        // elided numbers and numbers over 65500 digits without an expression form can only
        // be submitted as factors, even if their IDs are known
        // however, this doesn't affect the divisibility graph because the ID may be found
        // later
        let factor = get_vertex(
            &data.divisibility_graph,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        if factor.is_elided() {
            info!("{id}: Temporarily skipping {factor} because digits are missing");
            // Can't submit a factor that we can't express, but
            // running add_factors_to_graph may provide an equivalent expression, else we can save
            // it in case we find out the ID later
            let new_factors_of_factor =
                add_factors_to_graph(http, &mut data, root_vid, factor_vid).await;
            if !new_factors_of_factor.is_empty() {
                factors_to_submit_in_graph.extend(new_factors_of_factor);
                dedup_and_shuffle(&mut factors_to_submit_in_graph);
            }
            if !factors_to_submit_in_graph.contains(&factor_vid) {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
            continue;
        }
        let mut dest_factors = vertex_ids_except::<Vec<_>>(&mut data, factor_vid)
            .into_iter()
            .filter(|dest_vid|
                    // if this edge exists, FactorDB already knows whether factor is a factor of dest
                    get_edge(&data.divisibility_graph, factor_vid, *dest_vid, &mut data.deleted_synonyms).is_none())
            .collect::<Box<[_]>>();
        let mut did_not_divide = false;
        dest_factors.shuffle(&mut rng());
        if dest_factors.is_empty() {
            let factor = get_vertex(
                &data.divisibility_graph,
                factor_vid,
                &mut data.deleted_synonyms,
            );
            info!("{id}: Skipping {factor} because there are no more cofactors it can divide");
            continue;
        };
        let mut put_factor_back_into_queue = false;
        'per_cofactor: for cofactor_vid in dest_factors.into_iter() {
            if is_known_factor(&mut data, factor_vid, cofactor_vid) {
                let [factor, cofactor] = get_vertices(
                    &data.divisibility_graph,
                    [factor_vid, cofactor_vid],
                    &mut data.deleted_synonyms,
                );
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on graph check)"
                );
                // This factor already known.
                // If transitive, submit to a smaller cofactor instead.
                // If direct, nothing left to do.
                propagate_divisibility(&mut data, factor_vid, cofactor_vid, true);
                continue;
            }
            let factor_facts = facts_of(&data.number_facts_map, factor_vid, &mut data.deleted_synonyms)
                .expect("{id}: Reached factors_known_to_factordb check for a number not entered in number_facts_map");
            match factor_facts.factors_known_to_factordb {
                UpToDate(ref already_known_factors) | NotUpToDate(ref already_known_factors) => {
                    if already_known_factors.contains(&cofactor_vid) {
                        let [factor, cofactor] = get_vertices(
                            &data.divisibility_graph,
                            [factor_vid, cofactor_vid],
                            &mut data.deleted_synonyms,
                        );
                        info!(
                            "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on FactorDB check)"
                        );
                        propagate_divisibility(&mut data, cofactor_vid, factor_vid, false);
                        continue;
                    } else if facts_of(
                        &data.number_facts_map,
                        cofactor_vid,
                        &mut data.deleted_synonyms,
                    )
                    .expect("{id}: cofactor not in number_facts_map")
                    .is_known_fully_factored()
                    {
                        let [factor, cofactor] = get_vertices(
                            &data.divisibility_graph,
                            [factor_vid, cofactor_vid],
                            &mut data.deleted_synonyms,
                        );
                        if !matches!(cofactor, Numeric(_)) {
                            info!(
                                "{id}: Skipping submission of {factor} to {cofactor} because destination is already fully factored (based on FactorDB check)"
                            );
                        }
                        rule_out_divisibility(&mut data, cofactor_vid, factor_vid);
                        continue;
                    }
                }
                NotQueried => {}
            }
            let factor = get_vertex(
                &data.divisibility_graph,
                factor_vid,
                &mut data.deleted_synonyms,
            );
            let cofactor = get_vertex(
                &data.divisibility_graph,
                cofactor_vid,
                &mut data.deleted_synonyms,
            );
            if !factor.may_be_proper_divisor_of(cofactor) {
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it fails a divisibility \
                    test"
                );
                rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                if cofactor_vid == root_vid {
                    continue 'graph_iter;
                }
                continue;
            }
            // NumericFactor entries are already fully factored
            if let Numeric(_) = cofactor {
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because the destination is too small"
                );
                propagate_divisibility(&mut data, factor_vid, cofactor_vid, false);
                continue;
            }
            let cofactor_facts = facts_of(
                &data.number_facts_map,
                cofactor_vid,
                &mut data.deleted_synonyms,
            )
            .expect(
                "{id}: Reached cofactor_facts check for a number not entered in number_facts_map",
            );
            let cofactor_upper_bound_log10 = cofactor_facts.upper_bound_log10;
            if let UpToDate(ref known_factor_vids) | NotUpToDate(ref known_factor_vids) =
                cofactor_facts.factors_known_to_factordb
                && !known_factor_vids.is_empty()
            {
                let mut by_status = known_factor_vids
                    .iter()
                    .copied()
                    .filter_map(|known_factor_vid| {
                        if get_edge(&data.divisibility_graph, factor_vid, known_factor_vid, &mut data.deleted_synonyms) != Some(NotFactor) {
                            None
                        } else if factor.may_be_proper_divisor_of(
                            get_vertex(&data.divisibility_graph, known_factor_vid, &mut data.deleted_synonyms),
                        ) && cofactor_upper_bound_log10
                            >= facts_of(&data.number_facts_map, known_factor_vid, &mut data.deleted_synonyms)
                            .expect("{id}: known_factor_statuses included a number not entered in number_facts_map")
                            .lower_bound_log10 {
                            // possible that cofactor == known_factor * x == factor * x * y
                            Some((true, known_factor_vid))
                        } else {
                            Some((false, known_factor_vid))
                        }
                    })
                    .into_group_map();
                let possible_factors = by_status.remove(&true).unwrap_or(vec![]);
                let unknown_non_factors = by_status.remove(&false).unwrap_or(vec![]);
                drop(by_status);
                if possible_factors.is_empty() {
                    info!(
                        "{id}: Skipping submission of {factor} to {cofactor} because it can't divide any of the remaining cofactors (based on FactorDB check)"
                    );
                    // No possible path from factor to cofactor
                    for unknown_non_factor in unknown_non_factors {
                        rule_out_divisibility(&mut data, factor_vid, unknown_non_factor);
                    }
                    rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                    let factors_to_submit_instead =
                        add_factors_to_graph(http, &mut data, root_vid, factor_vid).await;
                    if !factors_to_submit_instead.is_empty() {
                        factors_to_submit_in_graph.extend(factors_to_submit_instead);
                        dedup_and_shuffle(&mut factors_to_submit_in_graph);
                    }
                    continue;
                } else if possible_factors.into_iter().all(|possible_factor_vid| {
                    get_edge(
                        &data.divisibility_graph,
                        factor_vid,
                        possible_factor_vid,
                        &mut data.deleted_synonyms,
                    ) == Some(Direct)
                }) {
                    info!(
                        "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on graph check)"
                    );
                    // Submit to one of the known_factors instead
                    propagate_divisibility(&mut data, factor_vid, cofactor_vid, true);
                    continue;
                }
            }
            let cofactor_remaining_factors_upper_bound_log10 = cofactor_upper_bound_log10
                .saturating_sub(neighbor_vids(&data.divisibility_graph, cofactor_vid, Incoming)
                    .into_iter()
                    .filter(|(_, divisibility)| *divisibility != NotFactor)
                    .map(|(existing_factor, _)| facts_of(&data.number_facts_map, existing_factor, &mut data.deleted_synonyms)
                        .expect("{id}: known_factors_upper_bound called for a number with a factor not entered in number_facts_map")
                        .lower_bound_log10)
                    .sum());
            let factor_facts = facts_of(&data.number_facts_map, factor_vid, &mut data.deleted_synonyms)
                .expect("{id}: Reached factors_known_to_factordb check for a number not entered in number_facts_map");
            if factor_facts.lower_bound_log10 > cofactor_remaining_factors_upper_bound_log10 {
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it's too large to divide any of the remaining cofactors (based on previous submissions)"
                );
                rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                if cofactor_vid == root_vid {
                    continue 'graph_iter;
                }
                continue;
            }
            if is_known_factor(&mut data, cofactor_vid, factor_vid) {
                // factor is transitively divisible by dest_factor
                let [factor, cofactor] = get_vertices(
                    &data.divisibility_graph,
                    [factor_vid, cofactor_vid],
                    &mut data.deleted_synonyms,
                );
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it's a multiple"
                );
                propagate_divisibility(&mut data, cofactor_vid, factor_vid, true);
                continue;
            }
            // elided numbers and numbers over 65500 digits without an expression form can only
            // be used as dests if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            let cofactor = get_vertex(
                &data.divisibility_graph,
                cofactor_vid,
                &mut data.deleted_synonyms,
            );
            if cofactor.is_elided()
                && facts_of(
                    &data.number_facts_map,
                    cofactor_vid,
                    &mut data.deleted_synonyms,
                )
                .expect(
                    "{id}: Tried to check for entry_id for a cofactor not entered in number_facts_map",
                )
                .entry_id
                .is_none()
            {
                let factor = get_vertex(
                    &data.divisibility_graph,
                    factor_vid,
                    &mut data.deleted_synonyms,
                );
                info!(
                    "{id}: Temporarily skipping submission of {factor} to {cofactor} because we can't unambiguously identify the destination"
                );
                // Running add_factors_to_graph may yield an equivalent expression
                let new_factors_of_cofactor = add_factors_to_graph(http, &mut data, root_vid, cofactor_vid).await;
                if !new_factors_of_cofactor.is_empty() {
                    factors_to_submit_in_graph
                        .extend(new_factors_of_cofactor);
                    factors_to_submit_in_graph.make_contiguous().shuffle(&mut rng());
                }
                put_factor_back_into_queue = true;
                break 'per_cofactor;
            }
            let dest_specifier = as_specifier(cofactor_vid, &mut data);
            match http
                .try_report_factor(
                    dest_specifier,
                    get_vertex(
                        &data.divisibility_graph,
                        factor_vid,
                        &mut data.deleted_synonyms,
                    ),
                )
                .await
            {
                AlreadyFullyFactored => {
                    if cofactor_vid == root_vid {
                        warn!("{id}: Already fully factored");
                        return true;
                    }
                    mark_fully_factored(cofactor_vid, &mut data);
                    continue;
                }
                Accepted => {
                    propagate_divisibility(&mut data, factor_vid, cofactor_vid, false);
                    replace_with_or_abort(
                        facts_of_mut(
                            &mut data.number_facts_map,
                            cofactor_vid,
                            &mut data.deleted_synonyms,
                        ),
                        NumberFacts::marked_stale,
                    );
                    accepted_factors += 1;
                    did_not_divide = false;
                    dnd_since_last_accepted = 0;
                    iters_without_progress = 0;
                    // Move newly-accepted factor to the back of the list
                    if cofactor_vid == root_vid {
                        // skip put_factor_back_into_queue check
                        continue 'graph_iter;
                    }
                    put_factor_back_into_queue = true;
                    break 'per_cofactor;
                }
                DoesNotDivide => {
                    if cofactor_vid == root_vid {
                        dnd_since_last_accepted += 1;
                        if dnd_since_last_accepted >= DND_ABORT_THRESHOLD {
                            error!(
                                "{id}: Aborting due to too many 'does not divide' responses with no acceptances"
                            );
                            return accepted_factors > 0;
                        }
                    }
                    did_not_divide = true;
                    rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                    let subfactors =
                        add_factors_to_graph(http, &mut data, root_vid, factor_vid).await;
                    if !subfactors.is_empty() {
                        factors_to_submit_in_graph.extend(subfactors);
                        factors_to_submit_in_graph
                            .make_contiguous()
                            .shuffle(&mut rng());
                    } else if let Some(ref root_denominator) = root_denominator {
                        let facts = facts_of_mut(
                            &mut data.number_facts_map,
                            factor_vid,
                            &mut data.deleted_synonyms,
                        );
                        if !replace(&mut facts.checked_with_root_denominator, true) {
                            let factor = get_vertex(
                                &data.divisibility_graph,
                                factor_vid,
                                &mut data.deleted_synonyms,
                            );
                            let divided =
                                div_exact(factor, root_denominator).unwrap_or_else(|| {
                                    Factor::divide(
                                        factor.clone(),
                                        root_denominator_terms.clone().unwrap(),
                                    )
                                });
                            let (divided_vid, added) =
                                add_factor_node(&mut data, divided, Some(root_vid), None, http);
                            if added {
                                // Don't apply this recursively, except when divided was already in
                                // the graph for another reason
                                facts_of_mut(
                                    &mut data.number_facts_map,
                                    divided_vid,
                                    &mut data.deleted_synonyms,
                                )
                                .checked_with_root_denominator = true;
                                factors_to_submit_in_graph.push_back(divided_vid);
                            }
                        }
                    }
                    if cofactor_vid == root_vid {
                        continue 'graph_iter; // Skip put_factor_back_into_queue check for factors that don't divide the root
                    } else {
                        let cofactor_facts = facts_of(&data.number_facts_map, cofactor_vid, &mut data.deleted_synonyms)
                            .expect("{id}: Tried to fetch cofactor_facts for a cofactor not entered in number_facts_map");
                        if cofactor_facts.needs_update()
                            || !cofactor_facts.checked_for_listed_algebraic
                        {
                            // An error must have occurred while fetching cofactor's factors
                            put_factor_back_into_queue = true;
                        }
                    }
                }
                OtherError => {
                    put_factor_back_into_queue = true;
                    if !add_factors_to_graph(http, &mut data, root_vid, cofactor_vid)
                        .await
                        .is_empty()
                    {
                        iters_without_progress = 0;
                    }
                }
            }
        }
        if did_not_divide {
            dnd_since_last_accepted += 1;
            if dnd_since_last_accepted >= DND_ABORT_THRESHOLD {
                error!(
                                "{id}: Aborting due to too many 'does not divide' responses with no acceptances"
                            );
                return accepted_factors > 0;
            }
        }
        if put_factor_back_into_queue && !factors_to_submit_in_graph.contains(&factor_vid) {
            factors_to_submit_in_graph.push_back(factor_vid);
        }
    }

    for factor_vid in data
        .divisibility_graph
        .vertices_by_id()
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>()
        .into_iter()
    {
        let factor = get_vertex(
            &data.divisibility_graph,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        if factor
            .as_str_non_numeric()
            .is_some_and(|expr| expr.contains("..."))
        {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        let factor = factor.to_owned_string();
        if is_known_factor(&mut data, factor_vid, root_vid) {
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{factor}\n"))
        {
            Ok(_) => warn!("{id}: wrote {} to failed submissions file", factor),
            Err(e) => error!(
                "{id}: failed to write {} to failed submissions file: {e}",
                factor
            ),
        }
    }
    accepted_factors > 0
}

fn vertex_ids_except<T: FromIterator<VertexId>>(data: &mut FactorData, root_vid: VertexId) -> T {
    let ids = data.divisibility_graph.vertices();
    ids.map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<T>()
}

fn mark_fully_factored(vid: VertexId, data: &mut FactorData) {
    let facts = facts_of_mut(&mut data.number_facts_map, vid, &mut data.deleted_synonyms);
    facts.checked_for_listed_algebraic = true;
    facts.checked_in_factor_finder = true;
    facts.expression_form_checked_in_factor_finder = true;
    facts.checked_with_root_denominator = true;
    let no_other_factors = if let UpToDate(factors) = &facts.factors_known_to_factordb {
        if factors.len() == 1 {
            facts.last_known_status = Some(Prime);
        } else {
            facts.last_known_status = Some(FullyFactored);
            for neighbor in facts.factors_known_to_factordb.to_vec() {
                let neighbor_facts = facts_of_mut(
                    &mut data.number_facts_map,
                    neighbor,
                    &mut data.deleted_synonyms,
                );
                neighbor_facts.factors_known_to_factordb = UpToDate(vec![neighbor]);
                neighbor_facts.last_known_status = Some(Prime);
                propagate_divisibility(data, neighbor, vid, false);
            }
        }
        true
    } else {
        facts.last_known_status = Some(FullyFactored);
        false
    };
    for other_vid in vertex_ids_except::<Vec<_>>(data, vid) {
        let edge = get_edge(
            &data.divisibility_graph,
            other_vid,
            vid,
            &mut data.deleted_synonyms,
        );
        if matches!(edge, Some(Direct) | Some(Transitive)) {
            mark_fully_factored(other_vid, data);
        } else if no_other_factors {
            rule_out_divisibility(data, other_vid, vid);
        }
    }
}

#[framed]
async fn add_factors_to_graph(
    http: &mut impl FactorDbClientReadIdsAndExprs,
    data: &mut FactorData,
    root_vid: VertexId,
    factor_vid: VertexId,
) -> Box<[VertexId]> {
    let facts = facts_of(
        &data.number_facts_map,
        factor_vid,
        &mut data.deleted_synonyms,
    )
    .expect("add_factors_to_graph called on a number that's not entered in number_facts_map");
    let mut added = BTreeSet::new();
    let mut id = facts.entry_id;
    let elided = get_vertex(
        &data.divisibility_graph,
        factor_vid,
        &mut data.deleted_synonyms,
    )
    .is_elided();
    // First, check factordb.com/api for already-known factors
    let needs_update = facts.needs_update();
    if needs_update || elided {
        let factor_specifier = as_specifier(factor_vid, data);
        let ProcessedStatusApiResponse {
            status,
            factors: known_factors,
            id: new_id,
        } = http
            .known_factors_as_digits(factor_specifier, true, elided)
            .await;
        let known_factor_count = known_factors.len();
        if known_factor_count == 1 {
            let factor = get_vertex(
                &data.divisibility_graph,
                factor_vid,
                &mut data.deleted_synonyms,
            );
            let known_factor = known_factors.into_iter().next().unwrap();
            if known_factor != *factor {
                merge_equivalent_expressions(data, Some(root_vid), factor_vid, known_factor, http);
            }
        } else {
            let new_known_factors: Vec<_> = known_factors
                .into_iter()
                .map(|known_factor| {
                    let entry_id = known_factor.known_id();
                    let (known_factor_vid, is_new) =
                        add_factor_node(data, known_factor, Some(root_vid), entry_id, http);
                    propagate_divisibility(data, known_factor_vid, factor_vid, false);
                    if is_new {
                        added.insert(known_factor_vid);
                    }
                    known_factor_vid
                })
                .collect();
            let facts = facts_of_mut(
                &mut data.number_facts_map,
                factor_vid,
                &mut data.deleted_synonyms,
            );
            if known_factor_count > 0 {
                facts.factors_known_to_factordb = UpToDate(new_known_factors);
            }
        }
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        facts.entry_id = facts.entry_id.or(new_id);
        id = facts.entry_id;
        if let Some(id) = id {
            data.vertex_id_by_entry_id.insert(id, factor_vid);
        }
        if let Some(status) = status {
            facts.last_known_status = Some(status);
            if status == Prime || status == FullyFactored {
                mark_fully_factored(factor_vid, data);
            }
        }
    }

    // Next, check factordb.com/frame_moreinfo.php for listed algebraic factors
    if let Some(id) = id
        && !facts_of(&data.number_facts_map, factor_vid, &mut data.deleted_synonyms)
        .expect("Tried to check checked_for_listed_algebraic in add_factors_to_graph when not entered in number_facts_map")
        .checked_for_listed_algebraic
    {
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &mut data.deleted_synonyms);
        if let Some(known_id) = factor.known_id()
            && id != known_id
        {
            error!("Tried to look up {factor} using a smaller number's id {id}");
        } else {
            info!("{id}: Checking for listed algebraic factors");
            // Links before the "Is factor of" header are algebraic factors; links after it aren't
            let url = format!("https://factordb.com/frame_moreinfo.php?id={id}");
            let result = http.try_get_and_decode(&url).await;
            if let Some(result) = result
                && let Some((_before, listed_algebraic_and_rest)) = result.split_once("Algebraic factors")
                && let Some((listed_algebraic, _rest)) = listed_algebraic_and_rest.split_once("Is factor of")
            {
                facts_of_mut(&mut data.number_facts_map, factor_vid, &mut data.deleted_synonyms).checked_for_listed_algebraic = true;
                let algebraic_factors = http.read_ids_and_exprs(&listed_algebraic);
                for (subfactor_entry_id, factor_digits_or_expr) in algebraic_factors {
                    let factor = Factor::from(factor_digits_or_expr);
                    let (subfactor_vid, is_new) = add_factor_node(
                        data,
                        factor,
                        Some(factor_vid),
                        Some(subfactor_entry_id),
                        http,
                    );
                    if is_new {
                        added.insert(subfactor_vid);
                    }
                }
            } else {
                error!("{id}: Failed to decode algebraic-factor list");
            }
        }
    }

    // Next, check if factor_finder can find factors
    let facts = facts_of_mut(
        &mut data.number_facts_map,
        factor_vid,
        &mut data.deleted_synonyms,
    );
    if !replace(&mut facts.checked_in_factor_finder, true) {
        added.extend(add_factor_finder_factor_vertices_to_graph(
            data,
            Some(root_vid),
            factor_vid,
            http,
        ));
    }
    let facts = facts_of_mut(
        &mut data.number_facts_map,
        factor_vid,
        &mut data.deleted_synonyms,
    );
    if let Some(entry_id) = facts.entry_id
        && !facts.expression_form_checked_in_factor_finder
        && let Some(expression_form) = http.try_get_expression_form(entry_id).await
    {
        facts.expression_form_checked_in_factor_finder = true;
        let factor = get_vertex(
            &data.divisibility_graph,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        if expression_form != *factor {
            let added_via_equiv = merge_equivalent_expressions(
                data,
                Some(root_vid),
                factor_vid,
                expression_form.clone(),
                http,
            );
            added.extend(added_via_equiv);
        }
    }

    added.into_iter().collect()
}

fn merge_equivalent_expressions(
    data: &mut FactorData,
    root_vid: Option<VertexId>,
    factor_vid: VertexId,
    equivalent: Factor,
    http: &impl FactorDbClient,
) -> Vec<VertexId> {
    let current = get_vertex(
        &data.divisibility_graph,
        factor_vid,
        &mut data.deleted_synonyms,
    );
    if equivalent == *current {
        vec![]
    } else if let Some(existing_vid) = data.vertex_id_by_expr.get(&equivalent).copied()
        && to_real_vertex_id(existing_vid, &mut data.deleted_synonyms)
            == to_real_vertex_id(factor_vid, &mut data.deleted_synonyms)
    {
        vec![]
    } else {
        info!("Merging equivalent expressions {current} and {equivalent}");
        data.vertex_id_by_expr
            .insert(equivalent.clone(), factor_vid);
        let current_len = if current.is_elided() {
            usize::MAX // replace elided numbers with full ones ASAP
        } else {
            current.to_owned_string().len()
        };
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        let mut new_factor_vids = if !replace(&mut facts.checked_in_factor_finder, true) {
            add_factor_finder_factor_vertices_to_graph(data, root_vid, factor_vid, http)
        } else {
            Vec::new()
        };
        new_factor_vids.extend(find_unique_factors(&equivalent).into_iter().filter_map(
            |new_factor| {
                let entry_id = new_factor.known_id();
                let (vid, added) = add_factor_node(data, new_factor, root_vid, entry_id, http);
                if added { Some(vid) } else { None }
            },
        ));
        let (new_lower_bound_log10, new_upper_bound_log10) = estimate_log10(&equivalent);
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &mut data.deleted_synonyms,
        );
        facts.lower_bound_log10 = facts.lower_bound_log10.max(new_lower_bound_log10);
        facts.upper_bound_log10 = facts.upper_bound_log10.min(new_upper_bound_log10);
        if !equivalent.is_elided() && equivalent.to_owned_string().len() < current_len {
            let _ = replace(
                data.divisibility_graph.vertex_mut(factor_vid).unwrap(),
                equivalent,
            );
        }
        new_factor_vids
    }
}

fn add_factor_finder_factor_vertices_to_graph(
    data: &mut FactorData,
    root_vid: Option<VertexId>,
    factor_vid: VertexId,
    http: &impl FactorDbClient,
) -> Vec<VertexId> {
    let factor = get_vertex(
        &data.divisibility_graph,
        factor_vid,
        &mut data.deleted_synonyms,
    );
    find_unique_factors(factor)
        .into_iter()
        .filter_map(|new_factor| {
            let entry_id = new_factor.known_id();
            let (vid, added) = add_factor_node(data, new_factor, root_vid, entry_id, http);
            if added { Some(vid) } else { None }
        })
        .collect()
}

#[inline(always)]
pub fn facts_of<'a>(
    number_facts_map: &'a BTreeMap<VertexId, NumberFacts>,
    vertex_id: VertexId,
    deleted_synonyms: &mut BTreeMap<VertexId, VertexId>,
) -> Option<&'a NumberFacts> {
    number_facts_map.get(&to_real_vertex_id(vertex_id, deleted_synonyms))
}

#[inline(always)]
pub fn facts_of_mut<'a>(
    number_facts_map: &'a mut BTreeMap<VertexId, NumberFacts>,
    vertex_id: VertexId,
    deleted_synonyms: &mut BTreeMap<VertexId, VertexId>,
) -> &'a mut NumberFacts {
    number_facts_map
        .get_mut(&to_real_vertex_id(vertex_id, deleted_synonyms))
        .unwrap()
}

#[cfg(test)]
mod tests {
    use crate::FAILED_U_SUBMISSIONS_OUT;
    use crate::algebraic::Factor;
    use crate::graph::{
        FactorData, add_factor_node, find_and_submit_factors, is_known_factor,
        merge_equivalent_expressions, propagate_divisibility,
    };
    use crate::net::MockFactorDbClient;

    #[test]
    fn test_is_known_factor() {
        use crate::net::MockFactorDbClient;
        let mut http = MockFactorDbClient::new();
        http.expect_known_factors_as_digits().never();
        http.expect_cached_factors().return_const(None);
        http.expect_parse_resource_limits().never();
        http.expect_report_numeric_factor().never();
        http.expect_retrying_get_and_decode().never();
        http.expect_try_get_and_decode().never();
        http.expect_try_get_expression_form().never();
        http.expect_try_get_resource_limits().never();
        http.expect_try_report_factor().never();

        let mut data = FactorData::default();
        let (node1, added) = add_factor_node(&mut data, Factor::from("2^16-1"), None, None, &http);
        assert!(added);
        let (node2, added) =
            add_factor_node(&mut data, Factor::from("2^8-1"), Some(node1), None, &http);
        assert!(added);
        let (node3, added) =
            add_factor_node(&mut data, Factor::from("2^4-1"), Some(node1), None, &http);
        assert!(added);
        let (node4, added) =
            add_factor_node(&mut data, Factor::from("2^4+1"), Some(node1), None, &http);
        assert!(added);
        let (node5, added) =
            add_factor_node(&mut data, Factor::from("2^8+1"), Some(node1), None, &http);
        assert!(added);
        drop(http);
        propagate_divisibility(&mut data, node2, node1, false);
        propagate_divisibility(&mut data, node3, node2, false);
        propagate_divisibility(&mut data, node4, node2, false);
        propagate_divisibility(&mut data, node5, node1, false);
        assert!(!is_known_factor(&mut data, node1, node1));
        assert!(is_known_factor(&mut data, node2, node1));
        assert!(is_known_factor(&mut data, node3, node1));
        assert!(is_known_factor(&mut data, node4, node1));
        assert!(is_known_factor(&mut data, node5, node1));
        assert!(!is_known_factor(&mut data, node1, node2));
        assert!(!is_known_factor(&mut data, node2, node2));
        assert!(is_known_factor(&mut data, node3, node2));
        assert!(is_known_factor(&mut data, node4, node2));
        for divisibility_leaf in [node3, node4, node5] {
            for other_node in [node1, node2, node3, node4, node5] {
                assert!(!is_known_factor(&mut data, other_node, divisibility_leaf));
            }
        }
    }

    #[test]
    fn test_find_and_submit() {
        use crate::RealFactorDbClient;
        use crate::monitor::Monitor;
        use nonzero::nonzero;
        use rand::RngCore;
        use rand::rng;
        use std::env::temp_dir;
        use std::fs::File;
        use tokio::runtime::Runtime;
        use tokio::sync::Mutex;

        simple_log::console("info").unwrap();
        let runtime = Runtime::new().unwrap();
        runtime.block_on(async {
            FAILED_U_SUBMISSIONS_OUT
                .get_or_init(async || {
                    Mutex::new(
                        File::create_new(temp_dir().join(rng().next_u64().to_string())).unwrap(),
                    )
                })
                .await;
            let (_channel, shutdown) = Monitor::new();
            let mut http = RealFactorDbClient::new(nonzero!(10_000u32), 2, shutdown);
            find_and_submit_factors(
                &mut http,
                11_000_000_004_420_33401,
                format!("I({})", 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19).into(),
                false,
            )
            .await
        });
        runtime.shutdown_background();
    }

    #[test]
    fn test_merge_equivalent_expressions_infinite_recursion_2025_12_12() {
        let mut http = MockFactorDbClient::new();
        http.expect_known_factors_as_digits().never();
        http.expect_cached_factors().return_const(None);
        http.expect_parse_resource_limits().never();
        http.expect_report_numeric_factor().never();
        http.expect_retrying_get_and_decode().never();
        http.expect_try_get_and_decode().never();
        http.expect_try_get_expression_form().never();
        http.expect_try_get_resource_limits().never();
        http.expect_try_report_factor().never();

        let mut data = FactorData::default();
        let (root_vid, added) = add_factor_node(
            &mut data,
            Factor::from("(10^65035*18+10^130071-1)/9"),
            None,
            None,
            &http,
        );
        assert!(added);
        merge_equivalent_expressions(
            &mut data,
            Some(root_vid),
            root_vid,
            Factor::from("(10^65035*18+10^130071-1)/3^2"),
            &http,
        );
    }
}
