use crate::algebraic::{Factor, FactorFinder, OwnedFactor};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};
use crate::{merge_equivalent_expressions, FactorsKnownToFactorDb, NumberFacts};
use gryf::Graph;
use gryf::algo::ShortestPaths;
use gryf::core::id::{DefaultId, VertexId};
use gryf::core::marker::{Directed, Incoming, Outgoing};
use gryf::core::{EdgeSet, GraphRef, Neighbors};
use gryf::storage::{AdjMatrix, Stable};
use log::warn;
use std::collections::BTreeMap;
use replace_with::replace_with_or_abort;

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
    let updated_edge = upsert_edge(divisibility_graph, nonfactor, dest, |old_div| {
        old_div.unwrap_or(NotFactor)
    });
    if updated_edge != NotFactor {
        return;
    }
    for (neighbor, edge) in divisibility_graph
        .neighbors_directed(&dest, Incoming)
        .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
        .collect::<Box<[_]>>()
        .into_iter()
    {
        match divisibility_graph.edge(&edge) {
            Some(Transitive) | Some(Direct) => {
                // if factor doesn't divide dest_factor, then it also doesn't divide dest_factor's factors
                if divisibility_graph
                    .try_add_edge(dest, neighbor, NotFactor)
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
    for (neighbor, edge) in divisibility_graph
        .neighbors_directed(&dest, Outgoing)
        .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
        .collect::<Box<[_]>>()
        .into_iter()
    {
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
    entry_id: Option<u128>
) -> (VertexId, bool) {
    if entry_id.is_some() && let Some(root_vid) = root_vid {
        let matching_vertices = divisibility_graph
            .vertices()
            .filter(|v| v.attr.as_ref() != factor
                && number_facts_map.get(&v.id).unwrap().entry_id == entry_id)
            .map(|v| v.id)
            .collect::<Vec<_>>();
        if let Some(&first_matching_vid) = matching_vertices.get(1) {
            merge_equivalent_expressions(factor_finder, divisibility_graph, root_vid, number_facts_map, first_matching_vid, OwnedFactor::from(&factor));
            for matching_vid in &matching_vertices[1..] {
                divisibility_graph.neighbors_directed(&matching_vid, Incoming)
                    .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .for_each(|(vid, edge)| {
                        let merged_edge = *divisibility_graph.edge(&edge).unwrap();
                        upsert_edge(divisibility_graph, vid, first_matching_vid, |old| old.unwrap_or(merged_edge).max(merged_edge));
                    });
                divisibility_graph.neighbors_directed(&matching_vid, Outgoing)
                    .map(|neighbor_ref| (neighbor_ref.id, neighbor_ref.edge))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .for_each(|(vid, edge)| {
                        let merged_edge = *divisibility_graph.edge(&edge).unwrap();
                        upsert_edge(divisibility_graph, first_matching_vid, vid, |old| old.unwrap_or(merged_edge).max(merged_edge));
                    });
                let old_factor = divisibility_graph.remove_vertex(matching_vid).unwrap();
                let old_facts = number_facts_map.remove(&matching_vid).unwrap();
                merge_equivalent_expressions(factor_finder, divisibility_graph, root_vid, number_facts_map, first_matching_vid, old_factor);
                replace_with_or_abort(number_facts_map.get_mut(&first_matching_vid).unwrap(),|facts| facts.merged_with(old_facts));
            }
            return (first_matching_vid, false);
        }
    }
    let (factor_vid, added) = match divisibility_graph.vertices().find(|v| v.attr.as_ref() == factor) {
        Some(vertex_ref) => (vertex_ref.id, false),
        None => {
            let factor_vid = divisibility_graph.add_vertex(OwnedFactor::from(&factor));
            let (lower_bound_log10, upper_bound_log10) = factor_finder.estimate_log10(&factor);
            number_facts_map.insert(
                factor_vid,
                NumberFacts {
                    last_known_status: None,
                    factors_known_to_factordb: FactorsKnownToFactorDb::NotQueried,
                    lower_bound_log10,
                    upper_bound_log10,
                    entry_id,
                    checked_for_listed_algebraic: false,
                    checked_in_factor_finder: false,
                },
            );
            (factor_vid, true)
        }
    };
    if let Some(root_vid) = root_vid && factor_vid != root_vid
    {
        let _ = divisibility_graph.try_add_edge(&root_vid, &factor_vid, NotFactor);
    }
    (factor_vid, added)
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
