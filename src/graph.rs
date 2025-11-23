use crate::NumberSpecifier::Id;
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::{FullyFactored, Prime};
use crate::algebraic::{
    Factor, FactorFinder, NumberStatus, NumberStatusExt, OwnedFactor, ProcessedStatusApiResponse,
};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};
use crate::graph::FactorsKnownToFactorDb::{NotQueried, NotUpToDate, UpToDate};
use crate::net::FactorDbClient;
use crate::{FAILED_U_SUBMISSIONS_OUT, SUBMIT_FACTOR_MAX_ATTEMPTS};
use gryf::Graph;
use gryf::algo::ShortestPaths;
use gryf::core::base::VertexRef;
use gryf::core::facts::complete_graph_edge_count;
use gryf::core::id::{DefaultId, EdgeId, VertexId};
use gryf::core::marker::{Directed, Direction, Incoming, Outgoing};
use gryf::core::{EdgeSet, GraphRef};
use gryf::storage::{AdjMatrix, Stable};
use itertools::Itertools;
use log::{debug, error, info, warn};
use replace_with::replace_with_or_abort;
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::mem::replace;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Divisibility {
    NotFactor,
    Transitive,
    Direct,
}

pub type DivisibilityGraph = Graph<
    OwnedFactor,
    Divisibility,
    Directed,
    Stable<AdjMatrix<OwnedFactor, Divisibility, Directed, DefaultId>>,
>;

pub fn rule_out_divisibility(
    divisibility_graph: &mut DivisibilityGraph,
    nonfactor: VertexId,
    dest: VertexId,
) {
    if nonfactor == dest {
        // happens because of recursion
        return;
    }
    let updated_edge = upsert_edge(divisibility_graph, nonfactor, dest, |old_div| {
        old_div.unwrap_or(NotFactor)
    });
    if updated_edge != NotFactor {
        return;
    }
    for (neighbor, edge) in neighbor_vids(divisibility_graph, dest, Incoming)
    {
        if neighbor == nonfactor {
            continue;
        }
        match divisibility_graph.edge(&edge) {
            Some(Transitive) | Some(Direct) => {
                // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
                if divisibility_graph
                    .try_add_edge(nonfactor, neighbor, NotFactor)
                    .is_ok()
                {
                    rule_out_divisibility(divisibility_graph, nonfactor, neighbor);
                };
            }
            _ => {}
        }
    }
}

pub fn propagate_divisibility(
    divisibility_graph: &mut DivisibilityGraph,
    factor: VertexId,
    dest: VertexId,
    transitive: bool,
) {
    if factor == dest {
        // happens because of recursion
        return;
    }
    if upsert_edge(
        divisibility_graph,
        factor,
        dest,
        override_transitive_with_direct(if transitive { Transitive } else { Direct }),
    ) == NotFactor
    {
        return;
    }
    rule_out_divisibility(divisibility_graph, dest, factor);
    for (neighbor, edge) in neighbor_vids(divisibility_graph, dest, Outgoing)
    {
        if neighbor == factor {
            continue;
        }
        match divisibility_graph.edge(&edge) {
            Some(Transitive) | Some(Direct) => {
                // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
                if divisibility_graph
                    .try_add_edge(factor, neighbor, Transitive)
                    .is_ok()
                {
                    propagate_divisibility(divisibility_graph, factor, neighbor, true);
                };
                if divisibility_graph
                    .try_add_edge(&neighbor, &factor, NotFactor)
                    .is_ok()
                {
                    rule_out_divisibility(divisibility_graph, neighbor, factor);
                }
            }
            _ => {}
        }
    }
}

pub fn upsert_edge<F: FnOnce(Option<Divisibility>) -> Divisibility>(
    divisibility_graph: &mut DivisibilityGraph,
    from_vid: VertexId,
    to_vid: VertexId,
    new_value_fn: F,
) -> Divisibility {
    if from_vid == to_vid {
        warn!("Attempted to add an edge from {from_vid:?} to itself!");
        return Direct;
    }
    match divisibility_graph.edge_id_any(&from_vid, &to_vid) {
        Some(old_edge_id) => {
            let old_divisibility = *divisibility_graph.edge(&old_edge_id).unwrap();
            let new_divisibility = new_value_fn(Some(old_divisibility));
            if new_divisibility != old_divisibility {
                divisibility_graph.replace_edge(old_edge_id, new_divisibility);
            }
            new_divisibility
        }
        None => {
            let divisibility = new_value_fn(None);
            divisibility_graph.add_edge(from_vid, to_vid, divisibility);
            divisibility
        }
    }
}

fn override_transitive_with_direct(
    divisible: Divisibility,
) -> impl FnOnce(Option<Divisibility>) -> Divisibility {
    move |old_edge| {
        if old_edge == Some(Direct) || divisible == Direct {
            Direct
        } else if old_edge == Some(Transitive) || divisible == Transitive {
            Transitive
        } else {
            NotFactor
        }
    }
}

pub fn get_edge(
    graph: &DivisibilityGraph,
    source: VertexId,
    dest: VertexId,
) -> Option<Divisibility> {
    Some(*graph.edge(graph.edge_id_any(&source, &dest)?)?)
}

pub fn add_factor_node(
    divisibility_graph: &mut DivisibilityGraph,
    factor: Factor<&str, &str>,
    factor_finder: &FactorFinder,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    root_vid: Option<VertexId>,
    entry_id: Option<u128>,
) -> (VertexId, bool) {
    let (existing_vertex, matching_vertices) = divisibility_graph
        .vertices()
        .filter(|v| {
            v.attr.as_ref() == factor
                || (entry_id.is_some() && facts_of(number_facts_map, v.id).entry_id == entry_id)
        })
        .partition::<Vec<_>, _>(|v| v.attr.as_ref() == factor);
    let existing_vertex = existing_vertex.first().map(|v| v.id);
    let matching_vertices: Vec<_> = matching_vertices.into_iter().map(|v| v.id).collect();
    let (merge_dest, added) = existing_vertex
        .or_else(|| matching_vertices.first().copied())
        .map(|x| (x, false))
        .unwrap_or_else(|| {
            let factor_vid = divisibility_graph.add_vertex(OwnedFactor::from(&factor));
            let (lower_bound_log10, upper_bound_log10) = factor_finder.estimate_log10(&factor);
            number_facts_map.insert(
                factor_vid,
                NumberFacts {
                    last_known_status: None,
                    factors_known_to_factordb: NotQueried,
                    lower_bound_log10,
                    upper_bound_log10,
                    entry_id,
                    checked_for_listed_algebraic: false,
                    checked_in_factor_finder: false,
                    expression_form_checked_in_factor_finder: false,
                },
            );
            (factor_vid, true)
        });
    if divisibility_graph.vertex(&merge_dest).unwrap().as_ref() != factor {
        merge_equivalent_expressions(
            factor_finder,
            divisibility_graph,
            root_vid,
            number_facts_map,
            merge_dest,
            OwnedFactor::from(&factor),
        );
    }
    for matching_vid in matching_vertices {
        if matching_vid == merge_dest {
            continue;
        }
        neighbor_vids(divisibility_graph, matching_vid, Incoming)
            .into_iter()
            .for_each(|(vid, edge)| {
                let merged_edge = *divisibility_graph.edge(&edge).unwrap();
                upsert_edge(divisibility_graph, vid, merge_dest, |old| {
                    old.unwrap_or(merged_edge).max(merged_edge)
                });
            });
        neighbor_vids(divisibility_graph, matching_vid, Outgoing)
            .into_iter()
            .for_each(|(vid, edge)| {
                let merged_edge = *divisibility_graph.edge(&edge).unwrap();
                upsert_edge(divisibility_graph, merge_dest, vid, |old| {
                    old.unwrap_or(merged_edge).max(merged_edge)
                });
            });
        let old_factor = divisibility_graph.remove_vertex(matching_vid).unwrap();
        let old_facts = number_facts_map.remove(&matching_vid).unwrap();
        merge_equivalent_expressions(
            factor_finder,
            divisibility_graph,
            root_vid,
            number_facts_map,
            merge_dest,
            old_factor,
        );
        replace_with_or_abort(facts_of_mut(number_facts_map, merge_dest), |facts| {
            facts.merged_with(old_facts)
        });
    }
    (merge_dest, added)
}

fn neighbor_vids(
    divisibility_graph: &DivisibilityGraph,
    vertex_id: VertexId,
    direction: Direction,
) -> Vec<(VertexId, EdgeId)> {
    divisibility_graph
        .neighbors_directed(vertex_id, direction)
        .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
        .collect::<Vec<_>>()
}

pub fn is_known_factor(
    divisibility_graph: &DivisibilityGraph,
    factor_vid: VertexId,
    composite_vid: VertexId,
) -> bool {
    matches!(
        get_edge(divisibility_graph, factor_vid, composite_vid),
        Some(Direct) | Some(Transitive)
    ) || ShortestPaths::on(&divisibility_graph)
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
    lower_bound_log10: u128,
    upper_bound_log10: u128,
    pub(crate) entry_id: Option<u128>,
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
    left: &VertexRef<VertexId, OwnedFactor>,
    right: &VertexRef<VertexId, OwnedFactor>,
) -> Ordering {
    let left_facts = facts_of(number_facts_map, left.id);
    let right_facts = facts_of(number_facts_map, right.id);
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
                || other.checked_in_factor_finder,
            expression_form_checked_in_factor_finder: self.expression_form_checked_in_factor_finder
                || other.expression_form_checked_in_factor_finder,
        }
    }
}

pub async fn find_and_submit_factors(
    http: &mut FactorDbClient,
    id: u128,
    digits_or_expr: &str,
    factor_finder: &FactorFinder,
    skip_looking_up_known: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let mut divisibility_graph: DivisibilityGraph =
        Graph::new_directed_in(AdjMatrix::new()).stabilize();
    let mut number_facts_map = BTreeMap::new();
    let (root_vid, _) = if !skip_looking_up_known && !digits_or_expr.contains("...") {
        add_factor_node(
            &mut divisibility_graph,
            Factor::<&str, &str>::from(digits_or_expr),
            factor_finder,
            &mut number_facts_map,
            None,
            Some(id),
        )
    } else {
        let ProcessedStatusApiResponse {
            factors: known_factors,
            status,
            ..
        } = http
            .known_factors_as_digits::<&str, &str>(Id(id), false, true)
            .await;
        if status.is_known_fully_factored() {
            warn!("{id}: Already fully factored");
            return true;
        }
        match known_factors.len() {
            0 => add_factor_node(
                &mut divisibility_graph,
                Factor::<&str, &str>::from(digits_or_expr),
                factor_finder,
                &mut number_facts_map,
                None,
                Some(id),
            ),
            _ => {
                let (root_node, _) = add_factor_node(
                    &mut divisibility_graph,
                    Factor::from(known_factors.iter().map(|f| f.as_str()).join("*")).as_ref(),
                    factor_finder,
                    &mut number_facts_map,
                    None,
                    Some(id),
                );
                digits_or_expr_full.push(root_node);
                let root_factors = UpToDate(if known_factors.len() > 1 {
                    known_factors
                        .into_iter()
                        .map(|known_factor| {
                            let (factor_vid, added) = add_factor_node(
                                &mut divisibility_graph,
                                known_factor.as_ref(),
                                factor_finder,
                                &mut number_facts_map,
                                Some(root_node),
                                known_factor.known_id(),
                            );
                            if added {
                                propagate_divisibility(
                                    &mut divisibility_graph,
                                    factor_vid,
                                    root_node,
                                    false,
                                );
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
                let root_facts = facts_of_mut(&mut number_facts_map, root_node);
                root_facts.factors_known_to_factordb = root_factors;
                root_facts.last_known_status = status;
                (root_node, true)
            }
        }
    };
    debug!(
        "{id}: Root node for {digits_or_expr} is {} with vertex ID {root_vid:?}",
        divisibility_graph.vertex(root_vid).unwrap()
    );
    if skip_looking_up_known {
        let root_facts = facts_of_mut(&mut number_facts_map, root_vid);
        root_facts.factors_known_to_factordb = UpToDate(vec![root_vid]);
    }
    let mut factor_found = false;
    let mut accepted_factors = 0;
    for factor_vid in digits_or_expr_full.into_iter().rev() {
        factor_found |= !add_factors_to_graph(
            http,
            factor_finder,
            &mut divisibility_graph,
            &mut number_facts_map,
            root_vid,
            factor_vid,
        )
        .await
        .is_empty();
    }
    if !factor_found {
        info!("{id}: No factors to submit");
        return false;
    }
    // Simplest case: try submitting all factors as factors of the root
    // Sort backwards so that we try to submit largest factors first
    let mut any_failed_retryably = false;
    let known_factors = divisibility_graph
        .vertices()
        .sorted_by(|v1, v2| compare(&number_facts_map, v2, v1))
        .map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>();

    for factor_vid in known_factors.into_iter() {
        let factor = divisibility_graph.vertex(factor_vid).unwrap();
        debug!("{id}: Factor {factor} has vertex ID {factor_vid:?}");
        if factor
            .as_str_non_u128()
            .is_some_and(|expr| expr.contains("..."))
            && facts_of(&number_facts_map, factor_vid).entry_id.is_none()
        {
            // Can't submit a factor that we can't fit into a URL, but can save it in case we find
            // out the ID later
            continue;
        }
        match get_edge(&divisibility_graph, factor_vid, root_vid) {
            Some(Direct) | Some(NotFactor) => {
                // This has been submitted directly to the root already, so it's probably already been
                // factored out of all other divisors.
                continue;
            }
            _ => {}
        }
        match http
            .try_report_factor::<&str, &str, _, _>(&Id(id), factor)
            .await
        {
            AlreadyFullyFactored => return true,
            Accepted => {
                replace_with_or_abort(
                    facts_of_mut(&mut number_facts_map, root_vid),
                    NumberFacts::marked_stale,
                );
                accepted_factors += 1;
                propagate_divisibility(&mut divisibility_graph, factor_vid, root_vid, false);
            }
            DoesNotDivide => {
                rule_out_divisibility(&mut divisibility_graph, factor_vid, root_vid);
                if !add_factors_to_graph(
                    http,
                    factor_finder,
                    &mut divisibility_graph,
                    &mut number_facts_map,
                    root_vid,
                    factor_vid,
                )
                .await.is_empty() {
                    any_failed_retryably = true;
                }
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
    // Sort backwards so that we try to submit largest factors first
    let mut factors_to_submit = divisibility_graph
        .vertices()
        .sorted_by(|v1, v2| compare(&number_facts_map, v2, v1))
        .map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<VecDeque<_>>();
    'graph_iter: while !factors_to_submit.is_empty()
            && !facts_of(&number_facts_map, root_vid).is_known_fully_factored() {
        let node_count = divisibility_graph.vertex_count();
        let edge_count = divisibility_graph.edge_count();
        let complete_graph_edge_count = complete_graph_edge_count::<Directed>(node_count);
        if edge_count == complete_graph_edge_count
            || factors_to_submit.is_empty()
            || iters_without_progress >= node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        {
            info!("{id}: {accepted_factors} factors accepted");
            // Graph is fully connected, meaning none are left to try
            return accepted_factors > 0;
        }
        let (direct_divisors, non_factors) = divisibility_graph
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
            number_facts_map
                .iter()
                .filter(|(_, facts)| facts.is_known_fully_factored())
                .count(),
            number_facts_map
                .iter()
                .filter(|(_, facts)| facts.entry_id.is_some())
                .count()
        );
        while let Some(factor_vid) = factors_to_submit.pop_front()
            && iters_without_progress < node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        {
            iters_without_progress += 1;
            if is_known_factor(&divisibility_graph, factor_vid, root_vid)
                && facts_of(&number_facts_map, factor_vid).lower_bound_log10
                    > facts_of(&number_facts_map, root_vid).upper_bound_log10 / 2
            {
                // Already a known factor of root, and can't be a factor through any remaining path due to size
                continue;
            }
            // root can't be a factor of any other number we'll encounter
            rule_out_divisibility(&mut divisibility_graph, root_vid, factor_vid);
            // elided numbers and numbers over 65500 digits without an expression form can only
            // be submitted as factors, even if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            let factor = divisibility_graph.vertex(factor_vid).unwrap();
            if factor
                .as_str_non_u128()
                .is_some_and(|expr| expr.contains("..."))
            {
                factors_to_submit.push_back(factor_vid);
                continue;
            }
            let dest_factors = divisibility_graph
                .vertices()
                // Try to submit to largest cofactors first
                .sorted_by(|v1, v2| compare(&number_facts_map, v2, v1))
                .map(|vertex| vertex.id)
                .filter(|dest_vid|
                    // if factor == dest, the relation is trivial
                    factor_vid != *dest_vid
                        // if this edge exists, FactorDB already knows whether factor is a factor of dest
                        && get_edge(&divisibility_graph, factor_vid, *dest_vid).is_none())
                .collect::<Box<[_]>>();
            if dest_factors.is_empty() {
                continue;
            };
            let mut submission_errors = false;
            for cofactor_vid in dest_factors.into_iter() {
                if is_known_factor(&divisibility_graph, factor_vid, cofactor_vid) {
                    // This factor already known.
                    // If transitive, submit to a smaller cofactor instead.
                    // If direct, nothing left to do.
                    propagate_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid, true);
                    continue;
                }
                let facts = facts_of(&number_facts_map, factor_vid);
                match facts.factors_known_to_factordb {
                    UpToDate(ref already_known_factors)
                    | NotUpToDate(ref already_known_factors) => {
                        if already_known_factors.contains(&factor_vid) {
                            propagate_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                cofactor_vid,
                                false,
                            );
                            continue;
                        } else if facts.is_final() {
                            rule_out_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                cofactor_vid,
                            );
                            continue;
                        }
                    }
                    NotQueried => {}
                }
                let factor = divisibility_graph.vertex(factor_vid).unwrap();
                let cofactor = divisibility_graph.vertex(cofactor_vid).unwrap();
                if !factor.may_be_proper_divisor_of(cofactor) {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                        smaller or equal or fails last-digit test"
                    );
                    rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                    continue;
                }
                // u128s are already fully factored
                if let Numeric(_) = cofactor {
                    debug!(
                        "{id}: Skipping submission of {factor} to {cofactor} because the number is too small"
                    );
                    propagate_divisibility(
                        &mut divisibility_graph,
                        factor_vid,
                        cofactor_vid,
                        false,
                    );
                    continue;
                }
                let cofactor_facts = facts_of(&number_facts_map, cofactor_vid);
                if cofactor_facts.is_known_fully_factored() {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                    already fully factored"
                    );
                    if !cofactor_facts.needs_update() {
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
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
                                get_edge(&divisibility_graph, factor_vid, *known_factor_vid),
                            )
                        })
                        .collect();
                    let (possible_factors, unknown_non_factors): (Vec<_>, Vec<_>) =
                        known_factor_statuses
                            .iter()
                            .filter(|(_, divisibility)| *divisibility != Some(NotFactor))
                            .partition(|(known_factor_vid, _)| {
                                factor.may_be_proper_divisor_of(
                                    divisibility_graph.vertex(known_factor_vid).unwrap(),
                                ) && facts.lower_bound_log10
                                    <= facts_of(&number_facts_map, *known_factor_vid).upper_bound_log10
                            });
                    if possible_factors.is_empty() {
                        // No possible path from factor to cofactor
                        for (unknown_non_factor, _) in unknown_non_factors {
                            rule_out_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                unknown_non_factor,
                            );
                        }
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                        continue;
                    } else if possible_factors
                        .into_iter()
                        .all(|(_, divisibility)| divisibility == Some(Direct))
                    {
                        // Submit to one of the known_factors instead
                        propagate_divisibility(
                            &mut divisibility_graph,
                            factor_vid,
                            cofactor_vid,
                            true,
                        );
                        continue;
                    }
                }
                let cofactor_upper_bound =
                    cofactor_facts
                        .upper_bound_log10
                        .saturating_sub(known_factors_upper_bound(
                            &divisibility_graph,
                            &number_facts_map,
                            cofactor_vid,
                        ));
                if facts.lower_bound_log10 > cofactor_upper_bound {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                        smaller based on log10 bounds"
                    );
                    rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                    continue;
                }
                if is_known_factor(&divisibility_graph, cofactor_vid, factor_vid) {
                    debug!(
                        "{id}: Skipping submission of {factor} to {cofactor} because {cofactor} is transitively a factor of {factor}"
                    );
                    // factor is transitively divisible by dest_factor
                    propagate_divisibility(&mut divisibility_graph, cofactor_vid, factor_vid, true);
                    continue;
                }
                // elided numbers and numbers over 65500 digits without an expression form can only
                // be used as dests if their IDs are known
                // however, this doesn't affect the divisibility graph because the ID may be found
                // later
                if cofactor
                    .as_str_non_u128()
                    .is_some_and(|expr| expr.contains("..."))
                    && facts_of(&number_facts_map, cofactor_vid)
                        .entry_id
                        .is_none()
                {
                    debug!(
                        "{id}: Can't submit to {cofactor} right now because we don't know its full specifier"
                    );
                    continue;
                }
                let dest_specifier = crate::as_specifier(cofactor_vid, cofactor, &number_facts_map);
                match http
                    .try_report_factor(
                        &dest_specifier,
                        divisibility_graph.vertex(factor_vid).unwrap(),
                    )
                    .await
                {
                    AlreadyFullyFactored => {
                        if cofactor_vid == root_vid {
                            warn!("{id}: Already fully factored");
                            return true;
                        }
                        if !facts_of(&number_facts_map, cofactor_vid).is_known_fully_factored() {
                            mark_fully_factored(cofactor_vid, &mut divisibility_graph, &mut number_facts_map);
                        }
                        continue;
                    }
                    Accepted => {
                        replace_with_or_abort(
                            facts_of_mut(&mut number_facts_map, cofactor_vid),
                            NumberFacts::marked_stale,
                        );
                        accepted_factors += 1;
                        iters_without_progress = 0;
                        propagate_divisibility(
                            &mut divisibility_graph,
                            factor_vid,
                            cofactor_vid,
                            false,
                        );
                        // Move newly-accepted factor to the back of the list
                        factors_to_submit.push_back(factor_vid);
                        continue 'graph_iter;
                    }
                    DoesNotDivide => {
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                        factors_to_submit.extend_front(
                            add_factors_to_graph(
                                http,
                                factor_finder,
                                &mut divisibility_graph,
                                &mut number_facts_map,
                                root_vid,
                                factor_vid,
                            )
                            .await
                            .into_iter()
                            .sorted_by(|v1, v2| {
                                compare(
                                    &number_facts_map,
                                    &VertexRef {
                                        id: *v2,
                                        attr: divisibility_graph.vertex(v2).unwrap(),
                                    },
                                    &VertexRef {
                                        id: *v1,
                                        attr: divisibility_graph.vertex(v1).unwrap(),
                                    },
                                )
                            }),
                        );
                    }
                    OtherError => {
                        submission_errors = true;
                        if !add_factors_to_graph(
                            http,
                            factor_finder,
                            &mut divisibility_graph,
                            &mut number_facts_map,
                            root_vid,
                            cofactor_vid,
                        )
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
    }

    for factor_vid in divisibility_graph
        .vertices_by_id()
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>()
        .into_iter()
    {
        let factor = divisibility_graph.vertex(factor_vid).unwrap();
        if factor
            .as_str_non_u128()
            .is_some_and(|expr| expr.contains("..."))
        {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        if is_known_factor(&divisibility_graph, factor_vid, root_vid) {
            debug!("{id}: {factor} was successfully submitted");
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{}\n", factor))
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

fn known_factors_upper_bound(
    divisibility_graph: &DivisibilityGraph,
    number_facts_map: &BTreeMap<VertexId, NumberFacts>,
    cofactor_vid: VertexId,
) -> u128 {
    neighbor_vids(divisibility_graph, cofactor_vid, Incoming)
        .into_iter()
        .map(|(existing_factor, _)| {
            facts_of(number_facts_map, existing_factor).lower_bound_log10
        })
        .sum()
}

fn mark_fully_factored(vid: VertexId, graph: &mut DivisibilityGraph, number_facts_map: &mut BTreeMap<VertexId, NumberFacts>) {
    let facts = facts_of_mut(number_facts_map, vid);
    facts.checked_for_listed_algebraic = true;
    facts.checked_in_factor_finder = true;
    facts.expression_form_checked_in_factor_finder = true;
    let no_other_factors = if let UpToDate(factors) = &facts.factors_known_to_factordb {
        if factors.len() == 1
        {
            facts.last_known_status = Some(Prime);
        } else {
            facts.last_known_status = Some(FullyFactored);
            for neighbor in facts.factors_known_to_factordb.to_vec() {
                let neighbor_facts = facts_of_mut(number_facts_map, neighbor);
                neighbor_facts.factors_known_to_factordb = UpToDate(vec![neighbor]);
                neighbor_facts.last_known_status = Some(Prime);
                upsert_edge(graph, neighbor, vid, |_| Direct);
            }
        }
        true
    } else {
        facts.last_known_status = Some(FullyFactored);
        false
    };
    for other_vid in graph
            .vertices_by_id()
            .filter(|other_vid| *other_vid != vid)
            .collect::<Box<[_]>>()
            .into_iter()
    {
        let edge = graph.edge_id_any(&other_vid, &vid)
            .and_then(|edge_id| graph.edge(&edge_id).copied());
        if matches!(edge, Some(Direct) | Some(Transitive)) {
            mark_fully_factored(other_vid, graph, number_facts_map);
        } else if no_other_factors {
            rule_out_divisibility(graph, other_vid, vid);
        }
    }
}

async fn add_factors_to_graph(
    http: &mut FactorDbClient,
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    root_vid: VertexId,
    factor_vid: VertexId,
) -> Box<[VertexId]> {
    let facts = facts_of(&number_facts_map, factor_vid);
    let mut added = BTreeSet::new();
    let mut id = facts.entry_id;

    // First, check factordb.com/api for already-known factors
    if facts.needs_update() {
        let factor_specifier = crate::as_specifier(
            factor_vid,
            divisibility_graph.vertex(&factor_vid).unwrap(),
            number_facts_map,
        );
        let ProcessedStatusApiResponse {
            status,
            factors: known_factors,
            id: new_id,
        } = http
            .known_factors_as_digits(factor_specifier, true, false)
            .await;
        let known_factor_count = known_factors.len();
        if known_factor_count == 1 {
            let known_factor = known_factors.iter().next().unwrap();
            let existing_factor = divisibility_graph.vertex(&factor_vid).unwrap();
            if *known_factor != *existing_factor {
                merge_equivalent_expressions(
                    factor_finder,
                    divisibility_graph,
                    Some(root_vid),
                    number_facts_map,
                    factor_vid,
                    known_factor.clone(),
                );
            }
        }
        let new_known_factors: Vec<_> = known_factors
            .into_iter()
            .map(|known_factor| {
                let (known_factor_vid, is_new) = add_factor_node(
                    divisibility_graph,
                    known_factor.as_ref(),
                    factor_finder,
                    number_facts_map,
                    Some(root_vid),
                    known_factor.known_id(),
                );
                propagate_divisibility(divisibility_graph, known_factor_vid, factor_vid, false);
                if is_new {
                    added.insert(known_factor_vid);
                }
                known_factor_vid
            })
            .collect();
        let facts = facts_of_mut(number_facts_map, factor_vid);
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
                mark_fully_factored(factor_vid, divisibility_graph, number_facts_map);
            }
        }
    }

    // Next, check factordb.com/frame_moreinfo.php for listed algebraic factors
    if let Some(id) = id {
        if !facts_of(number_facts_map, factor_vid).checked_for_listed_algebraic {
            let root = divisibility_graph.vertex(&factor_vid).unwrap();
            if let Some(known_id) = root.known_id()
                && id != known_id
            {
                error!("Tried to look up {root} using a smaller number's id {id}");
            } else {
                info!("{id}: Checking for listed algebraic factors");
                // Links before the "Is factor of" header are algebraic factors; links after it aren't
                let url =
                    format!("https://factordb.com/frame_moreinfo.php?id={id}").into_boxed_str();
                let result = http.try_get_and_decode(&url).await;
                if let Some(result) = result
                    && let Some(listed_algebraic) = result.split("Is factor of").next()
                {
                    facts_of_mut(number_facts_map, factor_vid).checked_for_listed_algebraic = true;
                    let algebraic_factors = http.read_ids_and_exprs(listed_algebraic);
                    for (subfactor_entry_id, factor_digits_or_expr) in algebraic_factors {
                        let factor: Factor<&str, &str> = factor_digits_or_expr.into();
                        let (subfactor_vid, is_new) = add_factor_node(
                            divisibility_graph,
                            factor,
                            factor_finder,
                            number_facts_map,
                            Some(factor_vid),
                            Some(subfactor_entry_id),
                        );
                        debug!(
                            "{id}: Factor {factor} has entry ID {subfactor_entry_id} and vertex ID {subfactor_vid:?}"
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
    }

    // Next, check if factor_finder can find factors
    let facts = facts_of(number_facts_map, factor_vid);
    if !facts.checked_in_factor_finder {
        added.extend(add_factor_finder_factor_vertices_to_graph(
            factor_finder,
            divisibility_graph,
            Some(root_vid),
            number_facts_map,
            factor_vid,
            facts.entry_id,
        ));
    }
    let facts = facts_of_mut(number_facts_map, factor_vid);
    facts.checked_in_factor_finder = true;

    if let Some(entry_id) = facts.entry_id
        && !facts.expression_form_checked_in_factor_finder
        && let Some(expression_form) = http.try_get_expression_form(entry_id).await
    {
        let expression_form: Factor<&str, &str> = Factor::from(expression_form.as_str());
        added.extend(
            factor_finder
                .find_unique_factors(&expression_form)
                .into_iter()
                .map(|new_factor| {
                    add_factor_node(
                        divisibility_graph,
                        new_factor.as_ref(),
                        factor_finder,
                        number_facts_map,
                        Some(root_vid),
                        new_factor.known_id(),
                    )
                })
                .flat_map(|(vid, added)| if added { Some(vid) } else { None }),
        );
        let facts = facts_of_mut(number_facts_map, factor_vid);
        facts.expression_form_checked_in_factor_finder = true;
    }

    added.into_iter().collect()
}

fn merge_equivalent_expressions(
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: Option<VertexId>,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    factor_vid: VertexId,
    equivalent: OwnedFactor,
) -> Vec<VertexId> {
    let current = divisibility_graph.vertex(&factor_vid).unwrap();
    if equivalent == *current {
        facts_of(number_facts_map, factor_vid)
            .factors_known_to_factordb
            .to_vec()
    } else {
        info!("Merging equivalent expressions {current} and {equivalent}");
        let current_expr = current.as_str();
        let current_len = if current_expr.contains("...") {
            usize::MAX // replace elided numbers with full ones ASAP
        } else {
            current_expr.len()
        };
        let facts = facts_of_mut(number_facts_map, factor_vid);
        let entry_id = facts.entry_id;
        let mut new_factor_vids = facts.factors_known_to_factordb.to_vec();
        if !replace(&mut facts.checked_in_factor_finder, true) {
            new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
                factor_finder,
                divisibility_graph,
                root_vid,
                number_facts_map,
                factor_vid,
                entry_id,
            ));
        }
        let (new_lower_bound_log10, new_upper_bound_log10) =
            factor_finder.estimate_log10(&equivalent);
        let facts = facts_of_mut(number_facts_map, factor_vid);
        facts.lower_bound_log10 = facts.lower_bound_log10.max(new_lower_bound_log10);
        facts.upper_bound_log10 = facts.upper_bound_log10.min(new_upper_bound_log10);
        let equivalent_expr = equivalent.as_str();
        if !equivalent_expr.contains("...") && equivalent_expr.len() < current_len {
            let _ = replace(
                divisibility_graph.vertex_mut(factor_vid).unwrap(),
                equivalent,
            );
        }

        // New expression may allow factor_finder to find factors it couldn't before
        let entry_id = facts.entry_id;
        new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
            factor_finder,
            divisibility_graph,
            root_vid,
            number_facts_map,
            factor_vid,
            entry_id,
        ));
        new_factor_vids
    }
}

fn add_factor_finder_factor_vertices_to_graph(
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: Option<VertexId>,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    factor_vid: VertexId,
    entry_id: Option<u128>,
) -> Vec<VertexId> {
    factor_finder
        .find_unique_factors(divisibility_graph.vertex(&factor_vid).unwrap())
        .into_iter()
        .map(|new_factor| {
            let entry_id = if new_factor == *divisibility_graph.vertex(&factor_vid).unwrap() {
                entry_id
            } else {
                new_factor.known_id()
            };
            add_factor_node(
                divisibility_graph,
                new_factor.as_ref(),
                factor_finder,
                number_facts_map,
                root_vid,
                entry_id,
            )
        })
        .flat_map(|(vid, added)| if added { Some(vid) } else { None })
        .collect()
}

#[inline]
pub fn facts_of(number_facts_map: &BTreeMap<VertexId, NumberFacts>, vertex_id: VertexId) -> &NumberFacts {
    number_facts_map.get(&vertex_id).unwrap()
}

#[inline]
pub fn facts_of_mut(number_facts_map: &mut BTreeMap<VertexId, NumberFacts>, vertex_id: VertexId) -> &mut NumberFacts {
    number_facts_map.get_mut(&vertex_id).unwrap()
}