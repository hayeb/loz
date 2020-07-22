#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate pest_derive;

extern crate petgraph;

use std::collections::HashSet;

use crate::ast::{
    Expression, FunctionBody, FunctionDefinition, FunctionRule, Location, MatchExpression, Type,
};
use crate::Expression::*;
use std::borrow::Borrow;
use std::rc::Rc;

pub mod ast;
pub mod generator;
pub mod inferencer;
pub mod interpreter;
pub mod module_system;
pub mod parser;
pub mod printer;
pub mod rewriter;

impl Type {
    pub fn collect_free_type_variables(&self) -> HashSet<Rc<String>> {
        match self {
            Type::Bool => HashSet::new(),
            Type::Char => HashSet::new(),
            Type::String => HashSet::new(),
            Type::Int => HashSet::new(),
            Type::Float => HashSet::new(),
            Type::UserType(_, argument_types) => {
                let mut variables = HashSet::new();
                for t in argument_types {
                    for v in t.collect_free_type_variables() {
                        variables.insert(v);
                    }
                }
                variables
            }
            Type::Tuple(element_types) => {
                let mut variables = HashSet::new();
                for t in element_types {
                    for v in t.collect_free_type_variables() {
                        variables.insert(v);
                    }
                }
                variables
            }
            Type::List(t) => t.collect_free_type_variables(),
            Type::Variable(tv) => vec![Rc::clone(tv)].into_iter().collect(),
            Type::Function(from, to) => {
                let mut variables = HashSet::new();
                for t in from {
                    for v in t.collect_free_type_variables() {
                        variables.insert(v);
                    }
                }
                for v in to.collect_free_type_variables() {
                    variables.insert(v);
                }

                variables
            }
        }
    }

    pub fn referenced_custom_types(&self) -> HashSet<Rc<String>> {
        match self {
            Type::Bool => HashSet::new(),
            Type::Char => HashSet::new(),
            Type::String => HashSet::new(),
            Type::Int => HashSet::new(),
            Type::Float => HashSet::new(),
            Type::UserType(name, arguments) => {
                let mut types: HashSet<Rc<String>> = HashSet::new();
                types.insert(Rc::clone(name));
                for a in arguments {
                    types.extend(a.referenced_custom_types());
                }
                types
            }
            Type::Tuple(elements) => elements
                .iter()
                .flat_map(|e| e.referenced_custom_types().into_iter())
                .collect(),
            Type::List(list_type) => list_type.referenced_custom_types(),
            Type::Variable(_) => HashSet::new(),
            Type::Function(from_types, to_type) => {
                let mut types: HashSet<Rc<String>> = from_types
                    .iter()
                    .flat_map(|t| t.referenced_custom_types().into_iter())
                    .collect();
                types.extend(to_type.referenced_custom_types());
                types
            }
        }
    }
}

impl Expression {
    pub fn locate(&self) -> Rc<Location> {
        match self {
            BoolLiteral(loc, _) => Rc::clone(loc),
            StringLiteral(loc, _) => Rc::clone(loc),
            CharacterLiteral(loc, _) => Rc::clone(loc),
            IntegerLiteral(loc, _) => Rc::clone(loc),
            FloatLiteral(loc, _) => Rc::clone(loc),
            TupleLiteral(loc, _) => Rc::clone(loc),
            EmptyListLiteral(loc) => Rc::clone(loc),
            ShorthandListLiteral(loc, _) => Rc::clone(loc),
            LonghandListLiteral(loc, _, _) => Rc::clone(loc),
            ADTTypeConstructor(loc, _, _) => Rc::clone(loc),
            Record(loc, _, _) => Rc::clone(loc),
            Case(loc, _, _) => Rc::clone(loc),
            Call(loc, _, _) => Rc::clone(loc),
            Variable(loc, _) => Rc::clone(loc),
            Negation(loc, _) => Rc::clone(loc),
            Minus(loc, _) => Rc::clone(loc),
            Times(loc, _, _) => Rc::clone(loc),
            Divide(loc, _, _) => Rc::clone(loc),
            Modulo(loc, _, _) => Rc::clone(loc),
            Add(loc, _, _) => Rc::clone(loc),
            Subtract(loc, _, _) => Rc::clone(loc),
            ShiftLeft(loc, _, _) => Rc::clone(loc),
            ShiftRight(loc, _, _) => Rc::clone(loc),
            Greater(loc, _, _) => Rc::clone(loc),
            Greq(loc, _, _) => Rc::clone(loc),
            Leq(loc, _, _) => Rc::clone(loc),
            Lesser(loc, _, _) => Rc::clone(loc),
            Eq(loc, _, _) => Rc::clone(loc),
            Neq(loc, _, _) => Rc::clone(loc),
            And(loc, _, _) => Rc::clone(loc),
            Or(loc, _, _) => Rc::clone(loc),
            RecordFieldAccess(loc, _, _, _) => Rc::clone(loc),
            Lambda(loc, _, _) => Rc::clone(loc),
        }
    }

    fn list_references(
        es: &Vec<Rc<Expression>>,
        include_variables: bool,
    ) -> HashSet<(Rc<String>, Rc<Location>)> {
        es.iter()
            .flat_map(|e| e.references(include_variables))
            .collect()
    }

    pub fn dual_references(
        l: &Rc<Expression>,
        r: &Rc<Expression>,
        include_variables: bool,
    ) -> HashSet<(Rc<String>, Rc<Location>)> {
        let mut lrf = l.references(include_variables);
        lrf.extend(r.references(include_variables));
        lrf
    }

    pub fn references(&self, include_variables: bool) -> HashSet<(Rc<String>, Rc<Location>)> {
        match self {
            Expression::BoolLiteral(_, _) => HashSet::new(),
            Expression::StringLiteral(_, _) => HashSet::new(),
            Expression::CharacterLiteral(_, _) => HashSet::new(),
            Expression::IntegerLiteral(_, _) => HashSet::new(),
            Expression::FloatLiteral(_, _) => HashSet::new(),
            Expression::TupleLiteral(_, expressions) => {
                Expression::list_references(expressions, include_variables)
            }
            Expression::EmptyListLiteral(_) => HashSet::new(),
            Expression::ShorthandListLiteral(_, expressions) => {
                Expression::list_references(expressions, include_variables)
            }
            Expression::LonghandListLiteral(_, e1, e2) => {
                Expression::dual_references(e1, e2, include_variables)
            }
            Expression::ADTTypeConstructor(_, _, expressions) => {
                Expression::list_references(expressions, include_variables)
            }
            Expression::Record(_, _, expressions) => Expression::list_references(
                &expressions.into_iter().map(|(_, e)| e.clone()).collect(),
                include_variables,
            ),
            Expression::Case(_, e, rules) => {
                let mut fs = e.references(include_variables);

                for r in rules {
                    for fref in &r.result_rule.references(include_variables) {
                        fs.insert(fref.clone());
                    }
                }

                fs
            }
            Expression::Call(loc, f, expressions) => {
                let mut fs = HashSet::new();
                fs.insert((f.clone(), loc.clone()));
                fs.extend(Expression::list_references(&expressions, include_variables));
                fs
            }
            Expression::Variable(loc, name) if include_variables => {
                vec![(name.clone(), loc.clone())].into_iter().collect()
            }
            Expression::Variable(_, _) => HashSet::new(),
            Expression::Negation(_, e) => e.references(include_variables),
            Expression::Minus(_, e) => e.references(include_variables),
            Expression::Times(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Divide(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Modulo(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Add(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Subtract(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::ShiftLeft(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::ShiftRight(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Greater(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Greq(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Leq(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Lesser(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Eq(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Neq(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::And(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::Or(_, l, r) => Expression::dual_references(l, r, include_variables),
            Expression::RecordFieldAccess(_, _, l, r) => {
                Expression::dual_references(l, r, include_variables)
            }
            Expression::Lambda(_, me, e) => {
                let fs = e.references(include_variables);
                let introduced_variables: HashSet<Rc<String>> = me
                    .iter()
                    .flat_map(|me| me.variables().into_iter())
                    .collect();

                fs.into_iter()
                    .filter(|(n, _)| !introduced_variables.contains(n))
                    .collect()
            }
        }
    }
}

impl MatchExpression {
    pub fn locate(&self) -> Rc<Location> {
        match self {
            MatchExpression::IntLiteral(loc, _) => Rc::clone(loc),
            MatchExpression::CharLiteral(loc, _) => Rc::clone(loc),
            MatchExpression::StringLiteral(loc, _) => Rc::clone(loc),
            MatchExpression::BoolLiteral(loc, _) => Rc::clone(loc),
            MatchExpression::Identifier(loc, _) => Rc::clone(loc),
            MatchExpression::Tuple(loc, _) => Rc::clone(loc),
            MatchExpression::ShorthandList(loc, _) => Rc::clone(loc),
            MatchExpression::LonghandList(loc, _, _) => Rc::clone(loc),
            MatchExpression::Wildcard(loc) => Rc::clone(loc),
            MatchExpression::ADT(loc, _, _) => Rc::clone(loc),
            MatchExpression::Record(loc, _, _) => Rc::clone(loc),
        }
    }

    pub fn variables(&self) -> HashSet<Rc<String>> {
        match self {
            MatchExpression::IntLiteral(_, _) => HashSet::new(),
            MatchExpression::CharLiteral(_, _) => HashSet::new(),
            MatchExpression::StringLiteral(_, _) => HashSet::new(),
            MatchExpression::BoolLiteral(_, _) => HashSet::new(),
            MatchExpression::Identifier(_, id) => vec![Rc::clone(id)].into_iter().collect(),
            MatchExpression::Tuple(_, elements) => elements
                .into_iter()
                .flat_map(|e| e.variables().into_iter())
                .collect(),
            MatchExpression::ShorthandList(_, elements) => elements
                .into_iter()
                .flat_map(|e| e.variables().into_iter())
                .collect(),
            MatchExpression::LonghandList(_, h, t) => {
                let mut vars = HashSet::new();
                vars.extend(h.variables());
                vars.extend(t.variables());
                vars
            }
            MatchExpression::Wildcard(_) => HashSet::new(),
            MatchExpression::ADT(_, _, elements) => elements
                .into_iter()
                .flat_map(|e| e.variables().into_iter())
                .collect(),
            MatchExpression::Record(_, _, fields) => fields.into_iter().cloned().collect(),
        }
    }
}

pub fn definition_references(
    d: &Rc<FunctionDefinition>,
    include_variables: bool,
) -> HashSet<(Rc<String>, Rc<Location>)> {
    let mut referred = HashSet::new();

    for b in &d.function_bodies {
        referred.extend(body_references(b, include_variables));
    }

    referred
}

pub fn body_references(
    b: &FunctionBody,
    include_variables: bool,
) -> HashSet<(Rc<String>, Rc<Location>)> {
    let mut local_references = HashSet::new();
    for me in &b.match_expressions {
        local_references.extend(me.variables());
    }
    for d in &b.local_function_definitions {
        local_references.insert(d.name.clone());
    }

    let mut locally_referred = HashSet::new();
    for r in &b.rules {
        locally_referred.extend(match r.borrow() {
            FunctionRule::ConditionalRule(_, cond, expr) => {
                Expression::dual_references(cond, expr, include_variables)
            }
            FunctionRule::ExpressionRule(_, expr) => expr.references(include_variables),
            FunctionRule::LetRule(_, match_expression, expr) => {
                let lambda_variables = match_expression.variables();

                expr.references(include_variables)
                    .into_iter()
                    .filter(|(v, _)| !lambda_variables.contains(v))
                    .collect()
            }
        });
    }
    locally_referred
        .into_iter()
        .filter(|(v, _)| !local_references.contains(v))
        .collect()
}
