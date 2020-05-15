use std::collections::HashMap;
use std::rc::Rc;

use petgraph::Graph;

use crate::{definition_references, FunctionDefinition};

pub fn to_components(
    function_definitions: &Vec<Rc<FunctionDefinition>>,
) -> Vec<Vec<Rc<FunctionDefinition>>> {
    let mut name_to_index = HashMap::new();
    let mut index_to_name = HashMap::new();

    let mut graph = Graph::<Rc<String>, ()>::new();

    for d in function_definitions {
        let node = graph.add_node(Rc::clone(&d.name));
        name_to_index.insert(&d.name, node.clone());
        index_to_name.insert(node.clone(), &d.name);
    }

    for f in function_definitions {
        let referred = definition_references(f, false);

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

    let function_name_to_definition: HashMap<Rc<String>, Rc<FunctionDefinition>> =
        function_definitions
            .iter()
            .map(|d| (d.name.clone(), Rc::clone(d)))
            .collect();

    sccs.iter()
        .map(|scc| {
            scc.iter()
                .map(|n| {
                    Rc::clone(
                        function_name_to_definition
                            .get(index_to_name.get(n).unwrap().clone())
                            .unwrap(),
                    )
                })
                .collect()
        })
        .collect()
}
