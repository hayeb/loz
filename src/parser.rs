extern crate pest;

use std::collections::HashMap;

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
use pest::prec_climber::*;

use Expression::StringLiteral;

use crate::parser::Expression::*;

#[derive(Debug, Clone)]
pub struct Location {
    pub file: String,
    pub function: String,
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone)]
pub enum FunctionRule {
    ConditionalRule(Location, Expression, Expression),
    ExpressionRule(Location, Expression),
}

#[derive(Debug, Clone)]
pub struct FunctionBody {
    pub location: Location,
    pub parameters: Vec<String>,
    pub rules: Vec<FunctionRule>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    NoType,
    Bool,
    Char,
    String,
    Int,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub location: Location,
    pub from: Vec<Type>,
    pub to: Type,
}

#[derive(Debug, Clone)]
pub struct FunctionDeclaration {
    pub location: Location,
    pub name: String,
    pub function_type: FunctionType,
    pub function_bodies: Vec<FunctionBody>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    BoolLiteral(Location, bool),
    StringLiteral(Location, String),
    CharacterLiteral(Location, char),
    Number(Location, isize),
    Call(Location, String, Vec<Expression>),
    Variable(Location, String),
    Negation(Location, Box<Expression>),
    Minus(Location, Box<Expression>),

    Times(Location, Box<Expression>, Box<Expression>),
    Divide(Location, Box<Expression>, Box<Expression>),
    Modulo(Location, Box<Expression>, Box<Expression>),

    Add(Location, Box<Expression>, Box<Expression>),
    Subtract(Location, Box<Expression>, Box<Expression>),

    ShiftLeft(Location, Box<Expression>, Box<Expression>),
    ShiftRight(Location, Box<Expression>, Box<Expression>),

    Greater(Location, Box<Expression>, Box<Expression>),
    Greq(Location, Box<Expression>, Box<Expression>),
    Leq(Location, Box<Expression>, Box<Expression>),
    Lesser(Location, Box<Expression>, Box<Expression>),

    Eq(Location, Box<Expression>, Box<Expression>),
    Neq(Location, Box<Expression>, Box<Expression>),

    And(Location, Box<Expression>, Box<Expression>),
    Or(Location, Box<Expression>, Box<Expression>),
}

#[derive(Debug, Clone)]
pub struct AST {
    pub function_declarations: HashMap<String, FunctionDeclaration>,
    pub main: Expression,
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


pub fn parse(file_name: &String, input: &str) -> Result<AST, Error<Rule>> {
    let ast = LOZParser::parse(Rule::ast, input)?.next().unwrap();
    //println!("raw ast: {:#?}", ast);
    let line_starts = build_line_start_cache(input);
    //println!("line starts {:?}", line_starts);
    Ok(to_ast(ast, file_name, &line_starts))
}

fn build_line_start_cache(input: &str) -> Vec<usize> {
    let mut line_starts: Vec<usize> = Vec::new();
    let mut start_current_line = 0;
    let mut previous_character = '\0';
    for (i, c) in input.char_indices() {
        if previous_character == '\n' {
            start_current_line = i;
        }
        if c == '\n' {
            line_starts.push(start_current_line);
        }
        previous_character = c;
    }

    line_starts
}

fn line_col_number(line_starts: &Vec<usize>, pos: usize) -> (usize, usize) {
    let mut previous_index = 1;
    let mut previous_start = 0;
    for (i, line_start) in line_starts.iter().enumerate() {
        if *line_start >= pos {
            return (previous_index + 1, pos - previous_start + 1);
        }
        previous_index = i;
        previous_start = *line_start;
    }

    (previous_index + 1, pos - previous_start + 1)
}

fn to_ast(pair: Pair<Rule>, file_name: &String, line_starts: &Vec<usize>) -> AST {
    match pair.as_rule() {
        Rule::ast => {
            let mut rules = pair.into_inner().peekable();
            let mut decls = HashMap::new();

            while let Some(rule) = rules.next() {
                if rules.peek().is_some() {
                    // Not the last one, function declaration.
                    let fd = to_function_declaration(file_name, rule, line_starts);
                    decls.insert(fd.clone().name, fd.clone());
                } else {
                    // Not the last one, function declaration.
                    return AST { function_declarations: decls, main: to_expression(rule.into_inner().next().unwrap(), file_name, &"StartRule".to_string(), line_starts) };
                }
            }
            unreachable!()
        }
        _ => unreachable!()
    }
}

fn to_function_declaration(file_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> FunctionDeclaration {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let mut inner_rules = pair.into_inner();
    let name = inner_rules.next().unwrap().as_str();
    let function_type = to_function_type(file_name, &name.to_string(), inner_rules.next().unwrap(), line_starts);
    FunctionDeclaration {
        location: Location { file: file_name.clone(), function: name.to_string(), line, col },
        name: name.to_string(),
        function_type,
        function_bodies: inner_rules.map(|b| to_function_body(file_name, &name.to_string(), b, line_starts)).collect(),
    }
}

fn to_expression(expression: Pair<Rule>, file_name: &String, function_name: &String, line_starts: &Vec<usize>) -> Expression {
    PREC_CLIMBER.climb(
        expression.into_inner(),
        |pair: Pair<Rule>| {
            match pair.as_rule() {
                Rule::term => to_term(pair, file_name, function_name, line_starts),
                _ => unreachable!(),
            }
        },
        |lhs: Expression, op: Pair<Rule>, rhs: Expression| {
            let (line, col) = line_col_number(line_starts, op.as_span().start());
            let loc_info = Location { file: file_name.clone(), function: function_name.clone(), line, col };
            match op.as_rule() {
                Rule::times => Times(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::divide => Divide(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::modulo => Modulo(loc_info, Box::new(lhs), Box::new(rhs)),

                Rule::add => Add(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::substract => Subtract(loc_info, Box::new(lhs), Box::new(rhs)),

                Rule::shift_left => ShiftLeft(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::shift_right => ShiftRight(loc_info, Box::new(lhs), Box::new(rhs)),

                Rule::lesser => Lesser(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::leq => Leq(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::greater => Greater(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::greq => Greq(loc_info, Box::new(lhs), Box::new(rhs)),

                Rule::eq => Eq(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::neq => Neq(loc_info, Box::new(lhs), Box::new(rhs)),

                Rule::and => And(loc_info, Box::new(lhs), Box::new(rhs)),
                Rule::or => Or(loc_info, Box::new(lhs), Box::new(rhs)),
                r => panic!("Prec climber unhandled rule: {:#?}", r)
            }
        },
    )
}

fn to_term(pair: Pair<Rule>, file_name: &String, function_name: &String, line_starts: &Vec<usize>) -> Expression {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let loc_info = Location { file: file_name.clone(), function: function_name.clone(), line, col };
    let sub = pair.into_inner().next().unwrap();
    match sub.as_rule() {
        Rule::bool_literal => BoolLiteral(loc_info, sub.as_str().parse::<bool>().unwrap()),
        Rule::string_literal => StringLiteral(loc_info, sub.into_inner().next().unwrap().as_str().to_string()),
        Rule::char_literal => CharacterLiteral(loc_info, sub.as_str().to_string().chars().nth(1).unwrap()),
        Rule::number => Number(loc_info, sub.as_str().parse::<isize>().unwrap()),
        Rule::call => {
            let mut subs = sub.into_inner();
            let function = subs.next().unwrap().as_str();
            let arguments = subs.map(|a| to_term(a, file_name, function_name, line_starts)).collect();
            Call(loc_info, function.to_string(), arguments)
        }
        Rule::identifier => Variable(loc_info, sub.as_str().to_string()),
        Rule::subexpr => to_expression(sub.into_inner().next().unwrap(), file_name, function_name, line_starts),
        Rule::negation => Negation(loc_info, Box::new(to_expression(sub.into_inner().next().unwrap(), file_name, function_name, line_starts))),
        Rule::minus => Minus(loc_info, Box::new(to_expression(sub.into_inner().next().unwrap(), file_name, function_name, line_starts))),
        r => panic!("Reached term {:#?}", r),
    }
}

fn to_function_type(file_name: &String, function_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> FunctionType {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let mut types = pair.into_inner().peekable();
    let mut from_types = Vec::new();

    // f :: From From From -> To
    while let Some(t) = types.next() {
        if types.peek().is_some() {
            // Not the last, from type
            from_types.push(to_type(t));
        } else {
            // The last, to type
            return FunctionType { location: Location { file: file_name.clone(), function: function_name.clone(), line, col }, from: from_types, to: to_type(t) };
        }
    }
    unreachable!()
}

fn to_function_body(file_name: &String, function_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> FunctionBody {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let mut rules = pair.into_inner();
    let parameters = to_parameter_names(rules.next().unwrap());
    let function_rules = rules.map(|b| to_function_rule(b, file_name, function_name, line_starts)).collect();
    FunctionBody { location: Location { file: file_name.clone(), function: function_name.clone(), line, col }, parameters, rules: function_rules }
}

fn to_function_rule(pair: Pair<Rule>, file_name: &String, function_name: &String, line_starts: &Vec<usize>) -> FunctionRule {
    match pair.as_rule() {
        Rule::function_conditional_rule => {
            let pair = pair.into_inner().next().unwrap();
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            let mut rules = pair.into_inner();
            let left = to_expression(rules.next().unwrap(), file_name, function_name, line_starts);
            let right = to_expression(rules.next().unwrap(), file_name, function_name, line_starts);
            FunctionRule::ConditionalRule(Location { file: file_name.clone(), function: function_name.clone(), line, col }, left, right)
        }
        Rule::function_expression_rule => {
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            FunctionRule::ExpressionRule(Location { file: file_name.clone(), function: function_name.clone(), line, col }, to_expression(pair.into_inner().next().unwrap(), file_name, function_name, line_starts))
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