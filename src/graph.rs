use std::collections::BTreeMap;
use gryf::core::id::{DefaultId, VertexId};
use gryf::Graph;
use arcstr::ArcStr;
use compact_str::CompactString;
use gryf::core::marker::{Directed, Direction, Incoming, Outgoing};
use gryf::storage::{AdjMatrix, Stable};
use gryf::core::{EdgeSet, GraphRef, Neighbors};
use crate::algebraic::{Factor, FactorFinder};
use crate::{FactorsKnownToFactorDb, NumberFacts};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Divisibility {
    Direct,
    Transitive,
    NotFactor,
}

pub type DivisibilityGraph = Graph<
    Factor<ArcStr, CompactString>,
    Divisibility,
    Directed,
    Stable<AdjMatrix<Factor<ArcStr, CompactString>, Divisibility, Directed, DefaultId>>,
>;

pub fn rule_out_divisibility(
    divisibility_graph: &mut DivisibilityGraph,
    nonfactor: &VertexId,
    dest: &VertexId,
) {
    let _ = divisibility_graph.try_add_edge(nonfactor, dest, NotFactor);
    for (neighbor, edge) in divisibility_graph
        .neighbors_directed(dest, Incoming)
        .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
        .collect::<Box<[_]>>()
        .into_iter()
    {
        match divisibility_graph.edge(&edge) {
            Some(Transitive) | Some(Direct) => {
                // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
                if divisibility_graph
                    .try_add_edge(dest, &neighbor, NotFactor)
                    .is_ok()
                {
                    rule_out_divisibility(divisibility_graph, nonfactor, &neighbor);
                };
            }
            _ => {}
        }
    }
}

pub fn propagate_divisibility(
    divisibility_graph: &mut DivisibilityGraph,
    factor: &VertexId,
    dest: &VertexId,
    transitive: bool,
) {
    if transitive {
        let _ = divisibility_graph.try_add_edge(factor, dest, Transitive);
    } else {
        upsert_edge(
            divisibility_graph,
            factor,
            dest,
            override_transitive_with_direct(Direct),
        );
    }
    rule_out_divisibility(divisibility_graph, dest, factor);
    for (neighbor, edge) in divisibility_graph
        .neighbors_directed(dest, Outgoing)
        .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
        .collect::<Box<[_]>>()
        .into_iter()
    {
        match divisibility_graph.edge(&edge) {
            Some(Transitive) | Some(Direct) => {
                // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
                if divisibility_graph
                    .try_add_edge(factor, &neighbor, Transitive)
                    .is_ok()
                {
                    propagate_divisibility(divisibility_graph, factor, &neighbor, true);
                };
                if divisibility_graph
                    .try_add_edge(&neighbor, factor, NotFactor)
                    .is_ok()
                {
                    rule_out_divisibility(divisibility_graph, &neighbor, factor);
                }
            }
            _ => {}
        }
    }
}

pub fn upsert_edge<F: FnOnce(Option<Divisibility>) -> Divisibility>(
    divisibility_graph: &mut DivisibilityGraph,
    from_vid: &VertexId,
    to_vid: &VertexId,
    new_value_fn: F,
) {
    match divisibility_graph.edge_id_any(from_vid, to_vid) {
        Some(old_edge_id) => {
            divisibility_graph.replace_edge(
                old_edge_id,
                new_value_fn(Some(*divisibility_graph.edge(&old_edge_id).unwrap())),
            );
        }
        None => {
            divisibility_graph.add_edge(from_vid, to_vid, new_value_fn(None));
        }
    }
}

pub fn copy_edges_true_overrides_false(
    divisibility_graph: &mut DivisibilityGraph,
    new_vertex: &VertexId,
    out_edges: Box<[(VertexId, Divisibility)]>,
    in_edges: Box<[(VertexId, Divisibility)]>,
) {
    for (neighbor, divisible) in out_edges {
        upsert_edge(
            divisibility_graph,
            new_vertex,
            &neighbor,
            override_transitive_with_direct(divisible),
        );
    }
    for (neighbor, divisible) in in_edges {
        upsert_edge(
            divisibility_graph,
            &neighbor,
            new_vertex,
            override_transitive_with_direct(divisible),
        );
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

pub fn neighbors_with_edge_weights(
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: &VertexId,
    direction: Direction,
) -> Box<[(VertexId, Divisibility)]> {
    divisibility_graph
        .neighbors_directed(root_vid, direction)
        .map(|neighbor_ref| {
            (
                neighbor_ref.id,
                *divisibility_graph.edge(&neighbor_ref.edge).unwrap(),
            )
        })
        .collect()
}

pub fn get_edge(graph: &DivisibilityGraph, source: &VertexId, dest: &VertexId) -> Option<Divisibility> {
    Some(*graph.edge(graph.edge_id_any(source, dest)?)?)
}

pub fn add_factor_node(
    divisibility_graph: &mut DivisibilityGraph,
    factor: Factor<&str, &str>,
    factor_finder: &FactorFinder,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    root_node: Option<VertexId>,
) -> (VertexId, bool) {
    let (factor_vid, added) = match divisibility_graph.find_vertex(&(&factor).into()) {
        Some(id) => (id, false),
        None => {
            let factor_ref = factor.as_ref();
            let factor_vid = divisibility_graph.add_vertex((&factor).into());
            let (lower_bound_log10, upper_bound_log10) = factor_finder.estimate_log10(&factor_ref);
            let detected_factors = factor_finder.find_unique_factors(&factor_ref);
            let detected_factor_vids: Box<[VertexId]> = detected_factors
                .into_iter()
                .map(|factor| {
                    let (factor_vid, _) = add_factor_node(
                        divisibility_graph,
                        factor.as_ref(),
                        factor_finder,
                        number_facts_map,
                        root_node,
                    );
                    factor_vid
                })
                .collect();
            number_facts_map.insert(
                factor_vid,
                NumberFacts {
                    last_known_status: None,
                    factors_known_to_factordb: FactorsKnownToFactorDb::NotQueried,
                    lower_bound_log10,
                    upper_bound_log10,
                    entry_id: None,
                    factors_detected_by_factor_finder: detected_factor_vids,
                },
            );
            (factor_vid, true)
        }
    };
    if let Some(root_node) = root_node {
        let _ = divisibility_graph.try_add_edge(&root_node, &factor_vid, NotFactor);
    }
    (factor_vid, added)
}