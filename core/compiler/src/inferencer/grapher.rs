use std::collections::{HashSet, HashMap};

use petgraph::Graph;

use crate::parser::{AST, Expression, FunctionDeclaration, FunctionRule};

pub fn to_components(ast: &AST) -> Vec<Vec<&FunctionDeclaration>> {
    let mut name_to_index = HashMap::new();
    let mut index_to_name = HashMap::new();

    let mut graph = Graph::<String, ()>::new();

    for d in &ast.function_declarations {
        let node = graph.add_node(d.name.clone());
        name_to_index.insert(&d.name, node.clone());
        index_to_name.insert(node.clone(), &d.name);
    }

    for f in &ast.function_declarations {
        let referred = declaration_referred_functions(f);
        for r in referred {
            graph.add_edge(name_to_index.get(&f.name).unwrap().clone(), name_to_index.get(&r).unwrap().clone(), ());
        }
    }


    let sccs = petgraph::algo::kosaraju_scc(&graph);

    let function_name_to_declaration : HashMap<String, &FunctionDeclaration> = ast.function_declarations.iter()
        .map(|d| (d.name.clone(), d))
        .collect();

    sccs.iter()
        .map(|scc|
                scc.iter()
                    .map(|n| *function_name_to_declaration.get(index_to_name.get(n).unwrap().clone()).unwrap())
                    .collect())
        .collect()
}

fn declaration_referred_functions(d: &FunctionDeclaration) -> HashSet<String> {
    let mut referred = HashSet::new();

    for b in &d.function_bodies {
        for r in &b.rules {
           referred.extend(match r {
                FunctionRule::ConditionalRule(_, cond, expr) => dual_referred_functions(cond, expr),
                FunctionRule::ExpressionRule(_, expr) => expression_referred_functions(expr),
                FunctionRule::LetRule(_, _, expr) => expression_referred_functions( expr),
            });
        }
    }

    referred
}

fn expressions_referred_functions(es: &Vec<Expression>) -> HashSet<String> {
    es.iter().flat_map(|e| expression_referred_functions(e)).collect()
}

fn dual_referred_functions(l: &Expression, r: &Expression) -> HashSet<String> {
    let mut lrf = expression_referred_functions(l);
    lrf.extend(expression_referred_functions(r));
    lrf
}

fn expression_referred_functions(e: &Expression) -> HashSet<String> {
    match e {
        Expression::BoolLiteral(_, _) => HashSet::new(),
        Expression::StringLiteral(_, _) => HashSet::new(),
        Expression::CharacterLiteral(_, _) => HashSet::new(),
        Expression::IntegerLiteral(_, _) => HashSet::new(),
        Expression::FloatLiteral(_, _) => HashSet::new(),
        Expression::TupleLiteral(_, expressions) => expressions_referred_functions(expressions),
        Expression::EmptyListLiteral(_) => HashSet::new(),
        Expression::ShorthandListLiteral(_, expressions) => expressions_referred_functions(expressions),
        Expression::LonghandListLiteral(_, e1, e2) => dual_referred_functions(e1, e2),
        Expression::ADTTypeConstructor(_, _, expressions) => expressions_referred_functions(expressions),
        Expression::Record(_, _, expressions) => expressions_referred_functions(&expressions.into_iter().map(|(_, e)| e.clone()).collect()),
        Expression::Case(_, e, rules) => {
            let mut fs = expression_referred_functions(e);
            rules.iter().map(|r| expression_referred_functions(&r.result_rule)).for_each(|s| fs.extend(s));
            fs
        }
        Expression::Call(_, f, expressions) => {
            let mut fs = HashSet::new();
            fs.insert(f.clone());
            fs.extend(expressions_referred_functions(&expressions));
            fs
        }
        Expression::Variable(_, _) => HashSet::new(),
        Expression::Negation(_, e) => expression_referred_functions(e),
        Expression::Minus(_, e) => expression_referred_functions(e),
        Expression::Times(_, l, r) => dual_referred_functions(l, r),
        Expression::Divide(_, l, r) => dual_referred_functions(l, r),
        Expression::Modulo(_, l, r) => dual_referred_functions(l, r),
        Expression::Add(_, l, r) => dual_referred_functions(l, r),
        Expression::Subtract(_, l, r) => dual_referred_functions(l, r),
        Expression::ShiftLeft(_, l, r) => dual_referred_functions(l, r),
        Expression::ShiftRight(_, l, r) => dual_referred_functions(l, r),
        Expression::Greater(_, l, r) => dual_referred_functions(l, r),
        Expression::Greq(_, l, r) => dual_referred_functions(l, r),
        Expression::Leq(_, l, r) => dual_referred_functions(l, r),
        Expression::Lesser(_, l, r) => dual_referred_functions(l, r),
        Expression::Eq(_, l, r) => dual_referred_functions(l, r),
        Expression::Neq(_, l, r) => dual_referred_functions(l, r),
        Expression::And(_, l, r) => dual_referred_functions(l, r),
        Expression::Or(_, l, r) => dual_referred_functions(l, r),
    }
}