use std::collections::{HashMap, HashSet};

use petgraph::Graph;

use crate::{Expression, FunctionDefinition, FunctionRule, Location, declaration_references};

pub fn to_components(declarations: &Vec<FunctionDefinition>) -> Vec<Vec<&FunctionDefinition>> {
    let mut name_to_index = HashMap::new();
    let mut index_to_name = HashMap::new();

    let mut graph = Graph::<String, ()>::new();

    for d in declarations {
        let node = graph.add_node(d.name.clone());
        name_to_index.insert(&d.name, node.clone());
        index_to_name.insert(node.clone(), &d.name);
    }

    for f in declarations {
        let referred = declaration_references(f, false);

        for (name, _) in referred {
            if name_to_index.contains_key(&name) {
                graph.add_edge(
                    name_to_index.get(&f.name).unwrap().clone(),
                    name_to_index.get(&name).unwrap().clone(),
                    (),
                );
            }
        }
    }

    let sccs = petgraph::algo::kosaraju_scc(&graph);

    let function_name_to_declaration: HashMap<String, &FunctionDefinition> =
        declarations.iter().map(|d| (d.name.clone(), d)).collect();

    sccs.iter()
        .map(|scc| {
            scc.iter()
                .map(|n| {
                    *function_name_to_declaration
                        .get(index_to_name.get(n).unwrap().clone())
                        .unwrap()
                })
                .collect()
        })
        .collect()
}
