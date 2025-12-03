use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::{
    Factor, NumericFactor, estimate_log10, evaluate_as_numeric, find_factors_of_numeric,
    find_unique_factors,
};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};
use crate::graph::FactorsKnownToFactorDb::{NotQueried, NotUpToDate, UpToDate};
use crate::net::NumberStatus::{FullyFactored, Prime};
use crate::net::{FactorDbClient, NumberStatus, NumberStatusExt, ProcessedStatusApiResponse};
use crate::{FAILED_U_SUBMISSIONS_OUT, NumberLength, NumberSpecifier, SUBMIT_FACTOR_MAX_ATTEMPTS};
use async_backtrace::framed;
use gryf::Graph;
use gryf::algo::ShortestPaths;
use gryf::core::base::VertexRef;
use gryf::core::facts::complete_graph_edge_count;
use gryf::core::id::{DefaultId, VertexId};
use gryf::core::marker::{Directed, Direction, Incoming, Outgoing};
use gryf::storage::{AdjMatrix, Stable};
use hipstr::HipStr;
use itertools::Itertools;
use log::{debug, error, info, warn};
use replace_with::replace_with_or_abort;
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::mem::replace;
use std::sync::Arc;

pub type EntryId = u128;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Divisibility {
    NotFactor,
    Transitive,
    Direct,
}

pub type DivisibilityGraph = Graph<
    Arc<Factor>,
    Divisibility,
    Directed,
    Stable<AdjMatrix<Arc<Factor>, Divisibility, Directed, DefaultId>>,
>;

pub struct FactorData {
    pub divisibility_graph: DivisibilityGraph,
    pub deleted_synonyms: BTreeMap<VertexId, VertexId>,
    pub number_facts_map: BTreeMap<VertexId, NumberFacts>,
    pub vertex_id_by_expr: BTreeMap<Arc<Factor>, VertexId>,
    pub vertex_id_by_entry_id: BTreeMap<EntryId, VertexId>,
}

pub fn rule_out_divisibility(data: &mut FactorData, nonfactor: VertexId, dest: VertexId) {
    let nonfactor = to_real_vertex_id(nonfactor, &data.deleted_synonyms);
    let dest = to_real_vertex_id(dest, &data.deleted_synonyms);
    if nonfactor == dest {
        // happens because of recursion
        return;
    }
    if get_edge(data, nonfactor, dest).is_some() {
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
    let factor = to_real_vertex_id(factor, &data.deleted_synonyms);
    let dest = to_real_vertex_id(dest, &data.deleted_synonyms);
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

fn as_specifier(
    factor_vid: VertexId,
    data: &FactorData,
    factor: Option<Arc<Factor>>,
) -> NumberSpecifier {
    if let Some(facts) = facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
        && let Some(factor_entry_id) = facts.entry_id
    {
        debug!(
            "as_specifier: got entry ID {factor_entry_id} for factor {factor:?} with vertex ID {factor_vid:?}"
        );
        Id(factor_entry_id)
    } else {
        let factor = factor.unwrap_or_else(|| {
            get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms)
        });
        factor
            .known_id()
            .map(Id)
            .unwrap_or_else(|| Expression(factor.clone()))
    }
}

pub fn get_edge(data: &FactorData, source: VertexId, dest: VertexId) -> Option<Divisibility> {
    Some(
        *data
            .divisibility_graph
            .edge(data.divisibility_graph.edge_id_any(
                to_real_vertex_id(source, &data.deleted_synonyms),
                to_real_vertex_id(dest, &data.deleted_synonyms),
            )?)?,
    )
}

pub fn get_edge_mut(
    data: &mut FactorData,
    source: VertexId,
    dest: VertexId,
) -> Option<&mut Divisibility> {
    data.divisibility_graph
        .edge_mut(data.divisibility_graph.edge_id_any(
            to_real_vertex_id(source, &data.deleted_synonyms),
            to_real_vertex_id(dest, &data.deleted_synonyms),
        )?)
}

pub fn add_factor_node(
    data: &mut FactorData,
    factor: Arc<Factor>,
    root_vid: Option<VertexId>,
    mut entry_id: Option<EntryId>,
    http: &impl FactorDbClient,
) -> (VertexId, bool) {
    let existing_vertex = data
        .vertex_id_by_expr
        .get(&factor)
        .map(|vertex_id| to_real_vertex_id(*vertex_id, &data.deleted_synonyms));
    let matching_vid = entry_id
        .and_then(|entry_id| data.vertex_id_by_entry_id.get(&entry_id))
        .map(|vertex_id| to_real_vertex_id(*vertex_id, &data.deleted_synonyms));
    let (merge_dest, added) = existing_vertex
        .or(matching_vid)
        .map(|x| (x, false))
        .unwrap_or_else(|| {
            let factor_vid = data.divisibility_graph.add_vertex(factor.clone());
            data.vertex_id_by_expr.insert(factor.clone(), factor_vid);
            let factor_numeric = evaluate_as_numeric(&factor);
            let (lower_bound_log10, upper_bound_log10) = estimate_log10(factor.clone());
            let specifier = as_specifier(factor_vid, data, None);
            let cached = http
                .cached_factors(specifier)
                .or(factor_numeric.map(|eval| {
                    let factors = find_factors_of_numeric(eval);
                    ProcessedStatusApiResponse {
                        status: Some(if factors.len() == 1 {
                            Prime
                        } else {
                            FullyFactored
                        }),
                        factors: factors.into_boxed_slice(),
                        id: Numeric(eval).known_id(),
                    }
                }));
            // Only full factorizations are cached or obtained via evaluate_as_numeric.
            let mut has_cached = false;
            let (last_known_status, factors_known_to_factordb) = if let Some(cached) = cached {
                entry_id = entry_id.or(cached.id);
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
                },
            );
            (factor_vid, true)
        });
    if let Some(entry_id) = entry_id {
        data.vertex_id_by_entry_id.insert(entry_id, merge_dest);
    }
    if get_vertex(&data.divisibility_graph, merge_dest, &data.deleted_synonyms) != factor {
        merge_equivalent_expressions(data, root_vid, merge_dest, factor.clone(), http);
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
                &data.deleted_synonyms,
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
    deleted_synonyms: &BTreeMap<VertexId, VertexId>,
) -> VertexId {
    while let Some(synonym) = deleted_synonyms.get(&vertex_id).copied() {
        vertex_id = synonym;
    }
    vertex_id
}

#[inline(always)]
pub fn get_vertex(
    divisibility_graph: &DivisibilityGraph,
    vertex_id: VertexId,
    deleted_synonyms: &BTreeMap<VertexId, VertexId>,
) -> Arc<Factor> {
    divisibility_graph
        .vertex(to_real_vertex_id(vertex_id, deleted_synonyms))
        .unwrap()
        .clone()
}

pub fn is_known_factor(data: &FactorData, factor_vid: VertexId, composite_vid: VertexId) -> bool {
    matches!(
        get_edge(data, factor_vid, composite_vid),
        Some(Direct) | Some(Transitive)
    ) || ShortestPaths::on(&data.divisibility_graph)
        .edge_weight_fn(|edge| if *edge == NotFactor { 1usize } else { 0usize })
        .goal(factor_vid)
        .run(composite_vid)
        .ok()
        .and_then(|paths| paths.dist(factor_vid).copied())
        == Some(0)
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

    pub(crate) fn iter(&self) -> impl Iterator<Item = &VertexId> {
        static EMPTY: Vec<VertexId> = vec![];
        match self {
            NotQueried => EMPTY.iter(),
            NotUpToDate(factors) | UpToDate(factors) => factors.iter(),
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

/// No ordering could be transitive if it treated an overlapping pair of ranges differently than a
/// nonoverlapping pair. For example:
///
/// let a = Factor::Expression("100#"); // lower bound 10, upper bound 44
/// let b = Factor::BigNumber("123456789012345678901234567890123456789012345678901234567890"); // lower bound 59, upper bound 60
/// let c = Factor::Numeric(12345678901234567890); // lower bound 19, upper bound 20
///
/// So a < b and b < c because of the nonoverlapping bounds, but then c < a because expressions sort
/// last in Factor::Ord, and we hace a cycle. By comparing the upper bounds first, we break this
/// cycle in favor of c < a < b, which is the actual numeric-value ordering. This is probably about
/// as close as we can come to a total numeric-value ordering with no bignum math and no isk of
/// cycles.
fn compare(
    number_facts_map: &BTreeMap<VertexId, NumberFacts>,
    left: &VertexRef<VertexId, Arc<Factor>>,
    right: &VertexRef<VertexId, Arc<Factor>>,
    deleted_synonyms: &BTreeMap<VertexId, VertexId>,
) -> Ordering {
    let left_facts = facts_of(number_facts_map, left.id, deleted_synonyms)
        .expect("compare() called for a number not entered in number_facts_map");
    let right_facts = facts_of(number_facts_map, right.id, deleted_synonyms)
        .expect("compare() called for a number not entered in number_facts_map");
    left_facts
        .upper_bound_log10
        .cmp(&right_facts.upper_bound_log10)
        .then_with(|| {
            left_facts
                .lower_bound_log10
                .cmp(&right_facts.lower_bound_log10)
        })
        .then_with(|| left.attr.cmp(right.attr))
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
                            NotUpToDate(f)
                        }
                    }
                    x => x,
                },
            },
            checked_in_factor_finder: self.checked_in_factor_finder
                && other.checked_in_factor_finder,
            expression_form_checked_in_factor_finder: self.expression_form_checked_in_factor_finder
                && other.expression_form_checked_in_factor_finder,
        }
    }
}

#[framed]
pub async fn find_and_submit_factors(
    http: &mut impl FactorDbClient,
    id: EntryId,
    digits_or_expr: HipStr<'static>,
    skip_looking_up_known: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let mut data = FactorData {
        divisibility_graph: Graph::new_directed_in(AdjMatrix::new()).stabilize(),
        deleted_synonyms: BTreeMap::new(),
        number_facts_map: BTreeMap::new(),
        vertex_id_by_entry_id: BTreeMap::new(),
        vertex_id_by_expr: BTreeMap::new(),
    };
    let (root_vid, _) = if !skip_looking_up_known && !digits_or_expr.contains("...") {
        add_factor_node(
            &mut data,
            Factor::from(digits_or_expr.clone()).into(),
            None,
            Some(id),
            http,
        )
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
        let root_factor = Factor::from(digits_or_expr.clone()).into();
        match known_factors.len() {
            0 => add_factor_node(&mut data, root_factor, None, Some(id), http),
            _ => {
                let (root_node, _) = add_factor_node(&mut data, root_factor, None, Some(id), http);
                digits_or_expr_full.push(root_node);
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
                            } else {
                                warn!("{id}: Tried to add a duplicate node");
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
                    &data.deleted_synonyms,
                );
                root_facts.factors_known_to_factordb = root_factors;
                root_facts.last_known_status = status;
                (root_node, true)
            }
        }
    };
    debug!(
        "{id}: Root node for {digits_or_expr} is {} with vertex ID {root_vid:?}",
        get_vertex(&data.divisibility_graph, root_vid, &data.deleted_synonyms)
    );
    if skip_looking_up_known {
        let root_facts = facts_of_mut(&mut data.number_facts_map, root_vid, &data.deleted_synonyms);
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
    // Sort backwards so that we try to submit largest factors first
    let mut any_failed_retryably = false;
    let known_factors = vertex_ids_except::<Box<[_]>>(&data, root_vid);
    for factor_vid in known_factors.into_iter() {
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
        debug!("{id}: Factor {factor} has vertex ID {factor_vid:?}");
        if factor
            .as_str_non_numeric()
            .is_some_and(|expr| expr.contains("..."))
            && facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
                .expect("Tried to check for entry_id for a number not entered in number_facts_map")
                .entry_id
                .is_none()
        {
            // Can't submit a factor that we can't fit into a URL, but can save it in case we find
            // out the ID later
            continue;
        }
        match get_edge(&data, factor_vid, root_vid) {
            Some(Direct) | Some(NotFactor) => {
                // This has been submitted directly to the root already, so it's probably already been
                // factored out of all other divisors.
                continue;
            }
            _ => {}
        }
        match http.try_report_factor(Id(id), &factor).await {
            AlreadyFullyFactored => return true,
            Accepted => {
                replace_with_or_abort(
                    facts_of_mut(&mut data.number_facts_map, root_vid, &data.deleted_synonyms),
                    NumberFacts::marked_stale,
                );
                accepted_factors += 1;
                propagate_divisibility(&mut data, factor_vid, root_vid, false);
            }
            DoesNotDivide => {
                rule_out_divisibility(&mut data, factor_vid, root_vid);
                any_failed_retryably |=
                    !add_factors_to_graph(http, &mut data, root_vid, factor_vid)
                        .await
                        .is_empty();
            }
            OtherError => {
                any_failed_retryably = true;
            }
        }
    }
    if !any_failed_retryably {
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
    let mut node_count = 1; // print graph stats on first loop iteration
    // Sort backwards so that we try to submit largest factors first
    let mut factors_to_submit = vertex_ids_except::<VecDeque<_>>(&data, root_vid);
    'graph_iter: while !facts_of(&data.number_facts_map, root_vid, &data.deleted_synonyms)
        .expect("Reached 'graph_iter when root not entered in number_facts_map")
        .is_known_fully_factored()
        && iters_without_progress < node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        && let Some(factor_vid) = factors_to_submit.pop_front()
    {
        if iters_without_progress.is_multiple_of(node_count) {
            node_count = data.divisibility_graph.vertex_count();
            let edge_count = data.divisibility_graph.edge_count();
            let complete_graph_edge_count = complete_graph_edge_count::<Directed>(node_count);
            if edge_count == complete_graph_edge_count
                || factors_to_submit.is_empty()
                || iters_without_progress >= node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
            {
                info!("{id}: {accepted_factors} factors accepted");
                // Graph is fully connected, meaning none are left to try
                return accepted_factors > 0;
            }
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
                    .iter()
                    .filter(|(_, facts)| facts.is_known_fully_factored())
                    .count(),
                data.number_facts_map
                    .iter()
                    .filter(|(_, facts)| facts.entry_id.is_some())
                    .count()
            );
        }
        iters_without_progress += 1;
        if is_known_factor(&data, factor_vid, root_vid)
            && facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms).expect("Tried to compare log10 bounds for a number not entered in number_facts_map").lower_bound_log10
            > facts_of(&data.number_facts_map, root_vid, &data.deleted_synonyms).expect("Tried to compare log10 bounds for entry_id for a number not entered in number_facts_map").upper_bound_log10
        {
            // Already a known factor of root, and can't be a factor through any remaining path due to size
            continue;
        }
        // root can't be a factor of any other number we'll encounter
        rule_out_divisibility(&mut data, root_vid, factor_vid);
        // elided numbers and numbers over 65500 digits without an expression form can only
        // be submitted as factors, even if their IDs are known
        // however, this doesn't affect the divisibility graph because the ID may be found
        // later
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
        if factor
            .as_str_non_numeric()
            .is_some_and(|expr| expr.contains("..."))
        {
            factors_to_submit.push_back(factor_vid);
            continue;
        }
        let dest_factors = data
            .divisibility_graph
            .vertices()
            // Try to submit to largest cofactors first
            .sorted_by(|v1, v2| compare(&data.number_facts_map, v2, v1, &data.deleted_synonyms))
            .map(|vertex| vertex.id)
            .filter(|dest_vid|
                // if factor == dest, the relation is trivial
                factor_vid != *dest_vid
                    // if this edge exists, FactorDB already knows whether factor is a factor of dest
                    && get_edge(&data, factor_vid, *dest_vid).is_none())
            .collect::<Box<[_]>>();
        if dest_factors.is_empty() {
            continue;
        };
        let mut submission_errors = false;
        for cofactor_vid in dest_factors.into_iter() {
            if is_known_factor(&data, factor_vid, cofactor_vid) {
                // This factor already known.
                // If transitive, submit to a smaller cofactor instead.
                // If direct, nothing left to do.
                propagate_divisibility(&mut data, factor_vid, cofactor_vid, true);
                continue;
            }
            let factor_facts = facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
                .expect("Reached factors_known_to_factordb check for a number not entered in number_facts_map");
            match factor_facts.factors_known_to_factordb {
                UpToDate(ref already_known_factors) | NotUpToDate(ref already_known_factors) => {
                    if already_known_factors.contains(&cofactor_vid) {
                        propagate_divisibility(&mut data, cofactor_vid, factor_vid, false);
                        continue;
                    } else if factor_facts.is_final() {
                        rule_out_divisibility(&mut data, cofactor_vid, factor_vid);
                        continue;
                    }
                }
                NotQueried => {}
            }
            let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
            let cofactor = get_vertex(
                &data.divisibility_graph,
                cofactor_vid,
                &data.deleted_synonyms,
            );
            if !factor.may_be_proper_divisor_of(&cofactor) {
                debug!(
                    "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                    smaller or equal or fails last-digit test"
                );
                rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                continue;
            }
            // NumericFactor entries are already fully factored
            if let Numeric(_) = *cofactor {
                debug!(
                    "{id}: Skipping submission of {factor} to {cofactor} because the number is too small"
                );
                propagate_divisibility(&mut data, factor_vid, cofactor_vid, false);
                continue;
            }
            let cofactor_facts =
                facts_of(&data.number_facts_map, cofactor_vid, &data.deleted_synonyms).expect(
                    "Reached cofactor_facts check for a number not entered in number_facts_map",
                );
            if cofactor_facts.is_known_fully_factored() {
                debug!(
                    "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                already fully factored"
                );
                if !cofactor_facts.needs_update() {
                    rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                }
                continue;
            }
            if let UpToDate(ref known_factor_vids) | NotUpToDate(ref known_factor_vids) =
                cofactor_facts.factors_known_to_factordb
                && !known_factor_vids.is_empty()
            {
                let known_factor_statuses: Vec<_> = known_factor_vids
                    .iter()
                    .map(|known_factor_vid| {
                        (
                            *known_factor_vid,
                            get_edge(&data, factor_vid, *known_factor_vid),
                        )
                    })
                    .collect();
                let (possible_factors, unknown_non_factors): (Vec<_>, Vec<_>) =
                    known_factor_statuses
                        .iter()
                        .filter(|(_, divisibility)| *divisibility != Some(NotFactor))
                        .partition(|(known_factor_vid, _)| {
                            factor.may_be_proper_divisor_of(
                                &get_vertex(&data.divisibility_graph, *known_factor_vid, &data.deleted_synonyms),
                            ) && cofactor_facts.lower_bound_log10
                                <= facts_of(&data.number_facts_map, *known_factor_vid, &data.deleted_synonyms)
                                .expect("known_factor_statuses included a number not entered in number_facts_map")
                                .upper_bound_log10
                        });
                if possible_factors.is_empty() {
                    // No possible path from factor to cofactor
                    for (unknown_non_factor, _) in unknown_non_factors {
                        rule_out_divisibility(&mut data, factor_vid, unknown_non_factor);
                    }
                    rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                    continue;
                } else if possible_factors
                    .into_iter()
                    .all(|(_, divisibility)| divisibility == Some(Direct))
                {
                    // Submit to one of the known_factors instead
                    propagate_divisibility(&mut data, factor_vid, cofactor_vid, true);
                    continue;
                }
            }
            let cofactor_upper_bound = cofactor_facts
                .upper_bound_log10
                .saturating_sub(known_factors_product_log10_upper_bound(&data, cofactor_vid));
            if factor_facts.lower_bound_log10 > cofactor_upper_bound {
                debug!(
                    "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                    smaller based on log10 bounds"
                );
                rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                continue;
            }
            if is_known_factor(&data, cofactor_vid, factor_vid) {
                debug!(
                    "{id}: Skipping submission of {factor} to {cofactor} because {cofactor} is transitively a factor of {factor}"
                );
                // factor is transitively divisible by dest_factor
                propagate_divisibility(&mut data, cofactor_vid, factor_vid, true);
                continue;
            }
            // elided numbers and numbers over 65500 digits without an expression form can only
            // be used as dests if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            if cofactor
                .as_str_non_numeric()
                .is_some_and(|expr| expr.contains("..."))
                && facts_of(&data.number_facts_map, cofactor_vid, &data.deleted_synonyms)
                .expect("Tried to check for entry_id for a cofactor not entered in number_facts_map")
                .entry_id.is_none()
            {
                debug!(
                    "{id}: Can't submit to {cofactor} right now because we don't know its full specifier"
                );
                continue;
            }
            let dest_specifier = as_specifier(cofactor_vid, &data, Some(cofactor));
            match http
                .try_report_factor(
                    dest_specifier,
                    &get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms),
                )
                .await
            {
                AlreadyFullyFactored => {
                    if cofactor_vid == root_vid {
                        warn!("{id}: Already fully factored");
                        return true;
                    }
                    if !facts_of(&data.number_facts_map, cofactor_vid, &data.deleted_synonyms)
                        .expect("Tried to check whether to mark_fully_factored for a number not entered in number_facts_map").is_known_fully_factored() {
                        mark_fully_factored(
                            cofactor_vid,
                            &mut data
                        );
                    }
                    continue;
                }
                Accepted => {
                    replace_with_or_abort(
                        facts_of_mut(
                            &mut data.number_facts_map,
                            cofactor_vid,
                            &data.deleted_synonyms,
                        ),
                        NumberFacts::marked_stale,
                    );
                    accepted_factors += 1;
                    iters_without_progress = 0;
                    propagate_divisibility(&mut data, factor_vid, cofactor_vid, false);
                    // Move newly-accepted factor to the back of the list
                    factors_to_submit.push_back(factor_vid);
                    continue 'graph_iter;
                }
                DoesNotDivide => {
                    rule_out_divisibility(&mut data, factor_vid, cofactor_vid);
                    factors_to_submit.extend_front(
                        add_factors_to_graph(http, &mut data, root_vid, factor_vid)
                            .await
                            .into_iter()
                            .sorted_by(|v1, v2| {
                                compare(
                                    &data.number_facts_map,
                                    &VertexRef {
                                        id: *v2,
                                        attr: &get_vertex(
                                            &data.divisibility_graph,
                                            *v2,
                                            &data.deleted_synonyms,
                                        ),
                                    },
                                    &VertexRef {
                                        id: *v1,
                                        attr: &get_vertex(
                                            &data.divisibility_graph,
                                            *v1,
                                            &data.deleted_synonyms,
                                        ),
                                    },
                                    &data.deleted_synonyms,
                                )
                            }),
                    );
                    let cofactor_facts = facts_of(&data.number_facts_map, cofactor_vid, &data.deleted_synonyms)
                        .expect("Tried to fetch cofactor_facts for a cofactor not entered in number_facts_map");
                    if cofactor_facts.needs_update() || !cofactor_facts.checked_for_listed_algebraic
                    {
                        // An error must have occurred while fetching cofactor's factors
                        submission_errors = true;
                    }
                }
                OtherError => {
                    submission_errors = true;
                    if !add_factors_to_graph(http, &mut data, root_vid, cofactor_vid)
                        .await
                        .is_empty()
                    {
                        iters_without_progress = 0;
                    }
                }
            }
        }
        if submission_errors {
            factors_to_submit.push_back(factor_vid);
        }
    }

    for factor_vid in data
        .divisibility_graph
        .vertices_by_id()
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>()
        .into_iter()
    {
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
        if factor
            .as_str_non_numeric()
            .is_some_and(|expr| expr.contains("..."))
        {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        if is_known_factor(&data, factor_vid, root_vid) {
            debug!("{id}: {factor} was successfully submitted");
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{}\n", factor.to_owned_string()))
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

fn vertex_ids_except<T: FromIterator<VertexId>>(data: &FactorData, root_vid: VertexId) -> T {
    data.divisibility_graph
        .vertices()
        .sorted_by(|v1, v2| compare(&data.number_facts_map, v2, v1, &data.deleted_synonyms))
        .map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<T>()
}

fn known_factors_product_log10_upper_bound(
    data: &FactorData,
    cofactor_vid: VertexId,
) -> NumberLength {
    neighbor_vids(&data.divisibility_graph, cofactor_vid, Incoming)
        .into_iter()
        .map(|(existing_factor, _)| facts_of(&data.number_facts_map, existing_factor, &data.deleted_synonyms)
            .expect("known_factors_upper_bound called for a number with a factor not entered in number_facts_map")
            .lower_bound_log10)
        .sum()
}

fn mark_fully_factored(vid: VertexId, data: &mut FactorData) {
    let facts = facts_of_mut(&mut data.number_facts_map, vid, &data.deleted_synonyms);
    facts.checked_for_listed_algebraic = true;
    facts.checked_in_factor_finder = true;
    facts.expression_form_checked_in_factor_finder = true;
    let no_other_factors = if let UpToDate(factors) = &facts.factors_known_to_factordb {
        if factors.len() == 1 {
            facts.last_known_status = Some(Prime);
        } else {
            facts.last_known_status = Some(FullyFactored);
            for neighbor in facts.factors_known_to_factordb.to_vec() {
                let neighbor_facts =
                    facts_of_mut(&mut data.number_facts_map, neighbor, &data.deleted_synonyms);
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
    for other_vid in data
        .divisibility_graph
        .vertices_by_id()
        .filter(|other_vid| *other_vid != vid)
        .collect::<Box<[_]>>()
        .into_iter()
    {
        let edge = get_edge(data, other_vid, vid);
        if matches!(edge, Some(Direct) | Some(Transitive)) {
            mark_fully_factored(other_vid, data);
        } else if no_other_factors {
            rule_out_divisibility(data, other_vid, vid);
        }
    }
}

#[framed]
async fn add_factors_to_graph(
    http: &mut impl FactorDbClient,
    data: &mut FactorData,
    root_vid: VertexId,
    factor_vid: VertexId,
) -> Box<[VertexId]> {
    let facts = facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
        .expect("add_factors_to_graph called on a number that's not entered in number_facts_map");
    let mut added = BTreeSet::new();
    let mut id = facts.entry_id;

    // First, check factordb.com/api for already-known factors
    if facts.needs_update() {
        let factor_specifier = as_specifier(factor_vid, data, None);
        let ProcessedStatusApiResponse {
            status,
            factors: known_factors,
            id: new_id,
        } = http
            .known_factors_as_digits(factor_specifier, true, false)
            .await;
        let known_factor_count = known_factors.len();
        if known_factor_count == 1 {
            let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
            let known_factor = known_factors.iter().next().unwrap();
            if **known_factor != *factor {
                merge_equivalent_expressions(
                    data,
                    Some(root_vid),
                    factor_vid,
                    known_factor.clone(),
                    http,
                );
            }
        }
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
            &data.deleted_synonyms,
        );
        let old_factors: BTreeSet<_> = facts.factors_known_to_factordb.iter().collect();
        added.extend(
            new_known_factors
                .iter()
                .filter(|factor_vid| !old_factors.contains(factor_vid)),
        );
        if known_factor_count > 0 {
            facts.factors_known_to_factordb = UpToDate(new_known_factors);
        }
        facts.entry_id = facts.entry_id.or(new_id);
        id = facts.entry_id;
        if let Some(status) = status {
            facts.last_known_status = Some(status);
            if status == Prime || status == FullyFactored {
                mark_fully_factored(factor_vid, data);
            }
        }
    }

    // Next, check factordb.com/frame_moreinfo.php for listed algebraic factors
    if let Some(id) = id
        && !facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
        .expect("Tried to check checked_for_listed_algebraic in add_factors_to_graph when not entered in number_facts_map")
        .checked_for_listed_algebraic
    {
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
        if let Some(known_id) = factor.known_id()
            && id != known_id
        {
            error!("Tried to look up {factor} using a smaller number's id {id}");
        } else {
            info!("{id}: Checking for listed algebraic factors");
            // Links before the "Is factor of" header are algebraic factors; links after it aren't
            let url = format!("https://factordb.com/frame_moreinfo.php?id={id}").into();
            let result = http.try_get_and_decode(url).await;
            if let Some(result) = result
                && let Some((_before, listed_algebraic_and_rest)) = result.split_once("Algebraic factors")
                && let Some((listed_algebraic, _rest)) = listed_algebraic_and_rest.split_once("Is factor of")
            {
                facts_of_mut(&mut data.number_facts_map, factor_vid, &data.deleted_synonyms).checked_for_listed_algebraic = true;
                let algebraic_factors = http.read_ids_and_exprs(&listed_algebraic);
                for (subfactor_entry_id, factor_digits_or_expr) in algebraic_factors {
                    let factor = Factor::from(factor_digits_or_expr).into();
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
    let facts = facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
        .expect("Tried to check checked_in_factor_finder in add_factors_to_graph when not entered in number_facts_map");
    if !facts.checked_in_factor_finder {
        added.extend(add_factor_finder_factor_vertices_to_graph(
            data,
            Some(root_vid),
            factor_vid,
            facts.entry_id,
            http,
        ));
    }
    let facts = facts_of_mut(
        &mut data.number_facts_map,
        factor_vid,
        &data.deleted_synonyms,
    );
    facts.checked_in_factor_finder = true;

    if let Some(entry_id) = facts.entry_id
        && !facts.expression_form_checked_in_factor_finder
        && let Some(expression_form) = http.try_get_expression_form(entry_id).await
    {
        let factor = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
        if expression_form != factor {
            let expression_form = expression_form.clone();
            let added_via_equiv = merge_equivalent_expressions(
                data,
                Some(root_vid),
                factor_vid,
                expression_form.clone(),
                http,
            );
            added.extend(added_via_equiv);
            let factors = find_unique_factors(expression_form);
            added.extend(factors.into_iter().flat_map(|factor| {
                let (vertex_id, added) = add_factor_node(data, factor, Some(root_vid), None, http);
                if added { Some(vertex_id) } else { None }
            }));
        }
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &data.deleted_synonyms,
        );
        facts.expression_form_checked_in_factor_finder = true;
    }

    added.into_iter().collect()
}

fn merge_equivalent_expressions(
    data: &mut FactorData,
    root_vid: Option<VertexId>,
    factor_vid: VertexId,
    equivalent: Arc<Factor>,
    http: &impl FactorDbClient,
) -> Vec<VertexId> {
    let current = get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms);
    if equivalent == current {
        facts_of(&data.number_facts_map, factor_vid, &data.deleted_synonyms)
            .expect("merge_equivalent_expressions called for a destination not entered in number_facts_map")
            .factors_known_to_factordb
            .to_vec()
    } else {
        info!("Merging equivalent expressions {current} and {equivalent}");
        let current_expr = current.to_owned_string();
        let current_len = if current_expr.contains("...") {
            usize::MAX // replace elided numbers with full ones ASAP
        } else {
            current_expr.len()
        };
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &data.deleted_synonyms,
        );
        let entry_id = facts.entry_id;
        let mut new_factor_vids = facts.factors_known_to_factordb.to_vec();
        if !replace(&mut facts.checked_in_factor_finder, true) {
            new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
                data, root_vid, factor_vid, entry_id, http,
            ));
        }
        let (new_lower_bound_log10, new_upper_bound_log10) = estimate_log10(equivalent.clone());
        let facts = facts_of_mut(
            &mut data.number_facts_map,
            factor_vid,
            &data.deleted_synonyms,
        );
        facts.lower_bound_log10 = facts.lower_bound_log10.max(new_lower_bound_log10);
        facts.upper_bound_log10 = facts.upper_bound_log10.min(new_upper_bound_log10);
        let equivalent_expr = equivalent.to_owned_string();
        if !equivalent_expr.contains("...") && equivalent_expr.len() < current_len {
            let _ = replace(
                data.divisibility_graph.vertex_mut(factor_vid).unwrap(),
                equivalent,
            );
        }

        // New expression may allow factor_finder to find factors it couldn't before
        let entry_id = facts.entry_id;
        new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
            data, root_vid, factor_vid, entry_id, http,
        ));
        new_factor_vids
    }
}

fn add_factor_finder_factor_vertices_to_graph(
    data: &mut FactorData,
    root_vid: Option<VertexId>,
    factor_vid: VertexId,
    entry_id: Option<EntryId>,
    http: &impl FactorDbClient,
) -> Vec<VertexId> {
    find_unique_factors(
        get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms).clone(),
    )
    .into_iter()
    .map(|new_factor| {
        let entry_id = if new_factor
            == get_vertex(&data.divisibility_graph, factor_vid, &data.deleted_synonyms)
        {
            entry_id
        } else {
            new_factor.known_id()
        };
        add_factor_node(data, new_factor, root_vid, entry_id, http)
    })
    .flat_map(|(vid, added)| if added { Some(vid) } else { None })
    .collect()
}

#[inline(always)]
pub fn facts_of<'a>(
    number_facts_map: &'a BTreeMap<VertexId, NumberFacts>,
    vertex_id: VertexId,
    deleted_synonyms: &BTreeMap<VertexId, VertexId>,
) -> Option<&'a NumberFacts> {
    number_facts_map.get(&to_real_vertex_id(vertex_id, deleted_synonyms))
}

#[inline(always)]
pub fn facts_of_mut<'a>(
    number_facts_map: &'a mut BTreeMap<VertexId, NumberFacts>,
    vertex_id: VertexId,
    deleted_synonyms: &BTreeMap<VertexId, VertexId>,
) -> &'a mut NumberFacts {
    number_facts_map
        .get_mut(&to_real_vertex_id(vertex_id, deleted_synonyms))
        .unwrap()
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
                Mutex::new(File::create_new(temp_dir().join(rng().next_u64().to_string())).unwrap())
            })
            .await;
        let (_channel, shutdown) = Monitor::new();
        let mut http = RealFactorDbClient::new(nonzero!(10_000u32), 2, shutdown);
        find_and_submit_factors(
            &mut http,
            11_000_000_004_420_33401,
            format!("I({})", 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19).into(),
            true,
        )
        .await
    });
    runtime.shutdown_background();
}
