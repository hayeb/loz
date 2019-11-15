extern crate pest;

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
use pest::prec_climber::*;

use Expression::StringLiteral;

use crate::parser::Expression::*;

use self::pest::iterators::Pairs;

#[derive(Debug)]
pub enum FunctionRule {
    ConditionalRule(Expression, Expression),
    ExpressionRule(Expression),
}

#[derive(Debug)]
pub struct FunctionBody {
    parameters: Vec<String>,
    rules: Vec<FunctionRule>,
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
    BoolLiteral(bool),
    StringLiteral(String),
    CharacterLiteral(char),
    Number(usize),
    Call(String, Vec<Expression>),
    Variable(String),
    Negation(Box<Expression>),
    Minus(Box<Expression>),

    Times(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
    Modulo(Box<Expression>, Box<Expression>),

    Add(Box<Expression>, Box<Expression>),
    Substract(Box<Expression>, Box<Expression>),

    ShiftLeft(Box<Expression>, Box<Expression>),
    ShiftRight(Box<Expression>, Box<Expression>),

    Greater(Box<Expression>, Box<Expression>),
    Greq(Box<Expression>, Box<Expression>),
    Leq(Box<Expression>, Box<Expression>),
    Lesser(Box<Expression>, Box<Expression>),

    Eq(Box<Expression>, Box<Expression>),
    Neq(Box<Expression>, Box<Expression>),

    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>)
}

#[derive(Debug)]
pub struct AST {
    function_declarations: Vec<FunctionDeclaration>,
    main: Expression,
}

#[derive(Parser)]
#[grammar = "loz.pest"]
pub struct LOZParser;

lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
        use Assoc::*;

        PrecClimber::new(vec![
            Operator::new(Rule::and, Left) | Operator::new(Rule::or, Left),
            Operator::new(Rule::eq, Left) | Operator::new(Rule::neq, Left),
            Operator::new(Rule::lesser, Left) | Operator::new(Rule::leq, Left) | Operator::new(Rule::greater, Left) | Operator::new(Rule::greq, Left),
            Operator::new(Rule::shift_left, Left) | Operator::new(Rule::shift_right, Left),
            Operator::new(Rule::add, Left) | Operator::new(Rule::substract, Left),
            Operator::new(Rule::times, Left) | Operator::new(Rule::divide, Left) | Operator::new(Rule::modulo, Left)
        ])
    };
}


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
        function_bodies: inner_rules.map(|b| to_function_body(b)).collect(),
    }
}

fn to_expression(expression: Pair<Rule>) -> Expression {
    PREC_CLIMBER.climb(
        expression.into_inner(),
        |pair: Pair<Rule>| {
            match pair.as_rule() {
                Rule::term => to_term(pair),
                _ => unreachable!(),
            }
        },
        |lhs: Expression, op: Pair<Rule>, rhs: Expression| match op.as_rule() {
            Rule::times => Times(Box::new(lhs), Box::new(rhs)),
            Rule::divide => Divide(Box::new(lhs), Box::new(rhs)),
            Rule::modulo => Modulo(Box::new(lhs), Box::new(rhs)),

            Rule::add => Add(Box::new(lhs), Box::new(rhs)),
            Rule::substract => Substract(Box::new(lhs), Box::new(rhs)),

            Rule::shift_left => ShiftLeft(Box::new(lhs), Box::new(rhs)),
            Rule::shift_right => ShiftRight(Box::new(lhs), Box::new(rhs)),

            Rule::lesser => Lesser(Box::new(lhs), Box::new(rhs)),
            Rule::leq => Leq(Box::new(lhs), Box::new(rhs)),
            Rule::greater => Greater(Box::new(lhs), Box::new(rhs)),
            Rule::greq => Greq(Box::new(lhs), Box::new(rhs)),

            Rule::eq => Eq(Box::new(lhs), Box::new(rhs)),
            Rule::neq => Neq(Box::new(lhs), Box::new(rhs)),

            Rule::and => And(Box::new(lhs), Box::new(rhs)),
            Rule::or => Or(Box::new(lhs), Box::new(rhs)),
            r => panic!("Prec climber unhandled rule: {:#?}", r)
        },
    )
}

fn to_term(pair: Pair<Rule>) -> Expression {
    println!("to_term {:#?}", pair);
    let sub = pair.into_inner().next().unwrap();
    match sub.as_rule() {
        Rule::bool_literal => BoolLiteral(sub.as_str().parse::<bool>().unwrap()),
        Rule::string_literal => StringLiteral(sub.into_inner().next().unwrap().as_str().to_string()),
        Rule::char_literal => CharacterLiteral(sub.as_str().to_string().chars().nth(1).unwrap()),
        Rule::number => Number(sub.as_str().parse::<usize>().unwrap()),
        Rule::call => {
            let mut subs = sub.into_inner();
            let function = subs.next().unwrap().as_str();
            println!("args: {:#?}", subs);
            let arguments = subs.map(to_term).collect();
            Call(function.to_string(), arguments)
        }
        Rule::identifier => Variable(sub.as_str().to_string()),
        Rule::subexpr => to_expression(sub.into_inner().next().unwrap()),
        Rule::negation => Negation(Box::new(to_expression(sub.into_inner().next().unwrap()))),
        Rule::minus => Minus(Box::new(to_expression(sub.into_inner().next().unwrap()))),
        r => panic!("Reached term {:#?}", r),
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
    FunctionBody { parameters, rules: function_rules }
}

fn to_function_rule(pair: Pair<Rule>) -> FunctionRule {
    match pair.as_rule() {
        Rule::function_conditional_rule => {
            let mut rules = pair.into_inner().next().unwrap().into_inner();
            let left = to_expression(rules.next().unwrap());
            let right = to_expression(rules.next().unwrap());
            FunctionRule::ConditionalRule(left, right)
        }
        Rule::function_expression_rule => {
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