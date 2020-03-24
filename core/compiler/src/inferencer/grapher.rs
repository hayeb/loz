use std::collections::{HashMap, HashSet};

use petgraph::Graph;

use crate::{Expression, FunctionDefinition, FunctionRule, Location};

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
        let referred = declaration_referred_functions(f);

        for (name, _) in referred {

            if name_to_index.contains_key(&name) {
                graph.add_edge(name_to_index.get(&f.name).unwrap().clone(), name_to_index.get(&name).unwrap().clone(), ());
            }
        }
    }

    let sccs = petgraph::algo::kosaraju_scc(&graph);

    let function_name_to_declaration: HashMap<String, &FunctionDefinition> = declarations.iter()
        .map(|d| (d.name.clone(), d))
        .collect();

    sccs.iter()
        .map(|scc|
            scc.iter()
                .map(|n| *function_name_to_declaration.get(index_to_name.get(n).unwrap().clone()).unwrap())
                .collect())
        .collect()
}

fn declaration_referred_functions(d: &FunctionDefinition) -> HashSet<(String, Location)> {
    let mut referred = HashSet::new();

    let mut local_variables = HashSet::new();

    for b in &d.function_bodies {
        for me in &b.match_expressions {
            local_variables.extend(me.variables());
        }
        for d in &b.local_function_definitions {
            local_variables.insert(d.name.clone());
        }
        for r in &b.rules {
            referred.extend(match r {
                FunctionRule::ConditionalRule(_, cond, expr) => Expression::dual_referred_functions(cond, expr),
                FunctionRule::ExpressionRule(_, expr) => expr.function_references(),
                FunctionRule::LetRule(_, match_expression, expr) => {
                    local_variables.extend(match_expression.variables());
                    expr.function_references()
                }
            });
        }
    }

    referred.into_iter().filter(|(v, _)| !local_variables.contains(v)).collect()
}