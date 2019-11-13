extern crate pest;

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;

use Expression::StringLiteral;

use crate::parser::Expression::{CharacterLiteral, Number, Call, Variable};

#[derive(Debug)]
pub enum FunctionRule {
    ConditionalRule(Expression, Expression),
    ExpressionRule(Expression),
}

#[derive(Debug)]
pub struct FunctionBody {
    parameters: Vec<String>,
    rules: Vec<FunctionRule>
}

#[derive(Debug)]
pub enum Type {
    NoType,
    Bool,
    Char,
    String,
    Int,
}

#[derive(Debug)]
pub struct FunctionType {
    from: Vec<Type>,
    to: Type,
}

#[derive(Debug)]
pub struct FunctionDeclaration {
    name: String,
    function_type: FunctionType,
    function_bodies: Vec<FunctionBody>,
}

#[derive(Debug)]
pub enum Expression {
    StringLiteral(String),
    CharacterLiteral(char),
    Number(usize),
    Call(String, Vec<String>),
    Variable(String)
}

#[derive(Debug)]
pub struct AST {
    function_declarations: Vec<FunctionDeclaration>,
    main: Expression,
}

#[derive(Parser)]
#[grammar = "loz.pest"]
pub struct LOZParser;

pub fn parse(input: &str) -> Result<AST, Error<Rule>> {
    let ast = LOZParser::parse(Rule::ast, input)?.next().unwrap();
    Ok(to_ast(ast))
}

fn to_ast(pair: Pair<Rule>) -> AST {
    match pair.as_rule() {
        Rule::ast => {
            let mut rules = pair.into_inner().peekable();
            let mut function_declarations = Vec::new();

            while let Some(rule) = rules.next() {
                if rules.peek().is_some() {
                    // Not the last one, function declaration.
                    function_declarations.push(to_function_declaration(rule));
                } else {
                    // Not the last one, function declaration.
                    return AST { function_declarations, main: to_expression(rule.into_inner().next().unwrap()) };
                }
            }
            unreachable!()
        }
        _ => unreachable!()
    }
}

fn to_function_declaration(pair: Pair<Rule>) -> FunctionDeclaration {
    let mut inner_rules = pair.into_inner();
    let name = inner_rules.next().unwrap().as_str();
    let function_type = to_function_type(inner_rules.next().unwrap());
    FunctionDeclaration {
        name: name.to_string(),
        function_type,
        function_bodies: inner_rules.map(|b| to_function_body(b)).collect()
    }
}

fn to_expression(pair: Pair<Rule>) -> Expression {
    let sub = pair.into_inner().next().unwrap();
    match sub.as_rule() {
        Rule::string_literal => StringLiteral(sub.into_inner().next().unwrap().as_str().to_string()),
        Rule::char_literal => CharacterLiteral(sub.as_str().to_string().chars().nth(1).unwrap()),
        Rule::number => Number(sub.as_str().parse::<usize>().unwrap()),
        Rule::call => {
            let mut subs = sub.into_inner();
            let function = subs.next().unwrap().as_str();
            let arguments = subs.map(|a| a.as_str().to_string()).collect();
            Call(function.to_string(), arguments)
        },
        Rule::identifier => Variable(sub.as_str().to_string()),
        _ => unreachable!()
    }
}

fn to_function_type(pair: Pair<Rule>) -> FunctionType {

    let mut types = pair.into_inner().peekable();
    let mut from_types = Vec::new();

    while let Some(t) = types.next() {
        if types.peek().is_some() {
            // Not the last, from type
            from_types.push(to_type(t));
        } else {
            // The last, to type
            return FunctionType { from: from_types, to: to_type(t) };
        }
    }
    unreachable!()
}

fn to_function_body(pair: Pair<Rule>) -> FunctionBody {
    let mut rules = pair.into_inner();
    let parameters = to_parameter_names(rules.next().unwrap());
    let function_rules = rules.map(to_function_rule).collect();
    FunctionBody {parameters, rules: function_rules}
}

fn to_function_rule(pair: Pair<Rule>) -> FunctionRule {
    match pair.as_rule() {
        Rule::function_conditional_rule => {
            let mut rules = pair.into_inner().next().unwrap().into_inner();
            let left = to_expression(rules.next().unwrap());
            let right = to_expression(rules.next().unwrap());
            FunctionRule::ConditionalRule(left, right)
        },
        Rule::function_expression_rule =>  {
            let mut rules = pair.into_inner();
            FunctionRule::ExpressionRule(to_expression(rules.next().unwrap()))
        }
        _ => unreachable!()
    }
}

fn to_parameter_names(pair: Pair<Rule>) -> Vec<String> {
    pair.into_inner().map(|param| param.as_str().to_string()).collect()
}

fn to_type(pair: Pair<Rule>) -> Type {
    match pair.as_rule() {
        Rule::loz_type => {
            match pair.as_span().as_str() {
                "Bool" => Type::Bool,
                "String" => Type::String,
                "Int" => Type::Int,
                "Char" => Type::Char,
                _ => Type::NoType
            }
        }
        _ => unreachable!()
    }
}