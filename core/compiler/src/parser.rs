extern crate pest;

use std::collections::HashMap;

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
use pest::prec_climber::*;

use crate::{ADTConstructor, ADTDefinition, AST, CaseRule, CustomType, Expression, FunctionBody, FunctionDefinition, FunctionRule, Location, MatchExpression, RecordDefinition, Type, TypeScheme};
use crate::Expression::*;
use crate::parser::ParseError::PestError;
use self::pest::iterators::Pairs;
use std::fmt::{Display, Formatter};

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
            Operator::new(Rule::times, Left) | Operator::new(Rule::divide, Left) | Operator::new(Rule::modulo, Left),
            Operator::new(Rule::record_field_access, Left)
        ])
    };
}

#[derive(Clone, Debug)]
pub enum ParseError {
    PestError(Error<Rule>),

    FunctionTypeWithoutBody(String, Location),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            PestError(pe) => write!(f, "{}", pe),
            ParseError::FunctionTypeWithoutBody(name, _loc) => write!(f, "Found type for function {}, but no bodies were found", name),
        }
    }
}


pub fn parse(file_name: &String, input: &str) -> Result<AST, ParseError> {
    let ast = LOZParser::parse(Rule::ast, input).map_err(|e| PestError(e))?.next().unwrap();
    //println!("Raw AST: {:#?}", ast);
    let line_starts = build_line_start_cache(input);
    to_ast(ast, file_name, &line_starts)
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

    if previous_character != '\n' {
        line_starts.push(start_current_line);
    }

    line_starts
}

fn line_col_number(line_starts: &Vec<usize>, pos: usize) -> (usize, usize) {
    let mut previous_index = 0;
    let mut previous_start = 0;
    for (i, line_start) in line_starts.iter().enumerate() {
        if *line_start > pos {
            return (previous_index + 1, pos - previous_start + 1);
        }
        previous_index = i;
        previous_start = *line_start;
    }

    (previous_index + 1, pos - previous_start + 1)
}

fn contract_function_declarations(mut function_bodies: HashMap<String, Vec<FunctionBody>>, function_types: HashMap<String, (Location, TypeScheme)>) -> Result<Vec<FunctionDefinition>, ParseError> {
    let mut function_declarations = Vec::new();
    for (function_name, (location, function_scheme)) in function_types {
        match function_bodies.remove(&function_name) {
            None => return Err(ParseError::FunctionTypeWithoutBody(function_name.clone(), location)),
            Some(bodies) => {
                function_declarations.push(FunctionDefinition {
                    location,
                    name: function_name.clone(),
                    function_type: Some(function_scheme),
                    function_bodies: bodies,
                })
            }
        }
    }

    // Add the remaining functions that do not have a defined type.
    for (function_name, bodies) in function_bodies {
        function_declarations.push(FunctionDefinition {
            location: bodies.get(0).unwrap().location.clone(),
            name: function_name.clone(),
            function_type: None,
            function_bodies: bodies
        });
    }

    Ok(function_declarations)
}

fn to_ast(pair: Pair<Rule>, file_name: &String, line_starts: &Vec<usize>) -> Result<AST, ParseError> {
    match pair.as_rule() {
        Rule::ast => {
            let (type_declarations, function_declarations) = to_declaration_block_elements(pair.into_inner(), file_name, line_starts)?;
            return Ok(AST {
                function_declarations,
                type_declarations
            })
        }
        _ => unreachable!()
    }
}

fn to_declaration_block_elements(pairs: Pairs<Rule>, file_name: &String, line_starts: &Vec<usize>) -> Result<(Vec<CustomType>, Vec<FunctionDefinition>), ParseError> {
    let mut function_types = HashMap::new();
    let mut function_bodies = HashMap::new();

    let mut type_declarations = Vec::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::type_definition => {
                let def = to_type_definition(pair, file_name, line_starts);
                type_declarations.push(def);
            }
            Rule::function_body => {
                let fb = to_function_body(file_name, pair, line_starts)?;
                match function_bodies.get_mut(&fb.name) {
                    None => {
                        function_bodies.insert(fb.name.clone(), vec![fb]);
                    }
                    Some(bodies) => bodies.push(fb),
                };
            }
            Rule::function_type_definition => {
                let (line, col) = line_col_number(line_starts, pair.as_span().start());
                let mut elements = pair.into_inner();
                let function_name = elements.next().unwrap().as_str().to_string();
                let function_type = to_type(elements.next().unwrap());
                function_types.insert(function_name.clone(), (Location {
                    file: file_name.clone(),
                    function: function_name.clone(),
                    line,
                    col
                }, TypeScheme {bound_variables: function_type.clone().collect_free_type_variables(), enclosed_type: function_type}));
            }
            _ => continue,
        }
    }
    Ok((type_declarations, contract_function_declarations(function_bodies, function_types)?))
}

fn to_type_definition(pair: Pair<Rule>, file_name: &String, line_starts: &Vec<usize>) -> CustomType {
    let type_definition = pair.into_inner().next().unwrap();
    match type_definition.as_rule() {
        Rule::adt_definition => {
            let mut elements = type_definition.clone().into_inner();
            let name = elements.next().unwrap().as_str().to_string();
            let type_variables = elements.next().unwrap().into_inner()
                .map(|tv| tv.as_str().to_string())
                .collect();

            let constructors = elements.next().unwrap().into_inner()
                .map(|alternative_rule| {
                    let mut alternative_elements = alternative_rule.into_inner();
                    let alternative_name = alternative_elements.next().unwrap().as_str().to_string();
                    let alternative_elements = alternative_elements.map(to_type).collect();
                    (alternative_name.clone(), ADTConstructor { name: alternative_name.clone(), elements: alternative_elements })
                })
                .collect();

            let (line, col) = line_col_number(line_starts, type_definition.clone().as_span().start());
            CustomType::ADT(Location { file: file_name.clone(), function: name.clone(), line, col }, ADTDefinition { name: name.clone(), constructors, type_variables })
        }
        Rule::record_definition => {
            let mut elements = type_definition.clone().into_inner();
            let name = elements.next().unwrap().as_str().to_string();
            let type_variables = elements.next().unwrap().into_inner()
                .map(|tv| tv.as_str().to_string())
                .collect();
            let fields = elements.next().unwrap().into_inner().map(|field_rule| {
                let mut field_elements = field_rule.into_inner();
                let field_name = field_elements.next().unwrap().as_str().to_string();
                let field_type = to_type(field_elements.next().unwrap());
                (field_name, field_type)
            }).collect();

            let (line, col) = line_col_number(line_starts, type_definition.clone().as_span().start());
            CustomType::Record(Location { file: file_name.clone(), function: name.clone(), line, col }, RecordDefinition { name: name.clone(), fields, type_variables })
        }
        r => unreachable!("Unhandled type rule: {:?}", r)
    }
}

fn to_function_body(file_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> Result<FunctionBody, ParseError> {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());

    let mut parents = pair.into_inner();
    let mut function_header_elements = parents.next().unwrap().into_inner();
    let function_name = function_header_elements.next().unwrap().as_str().to_string();

    let mut match_expressions = Vec::new();
    for r in function_header_elements {
        match_expressions.push(to_match_expression(r.into_inner().next().unwrap(), file_name, &function_name, line_starts));
    }

    let mut rules = Vec::new();
    let mut local_function_definitions = Vec::new();
    let mut local_type_definitions = Vec::new();
    for r in parents {
        match r.as_rule() {
            // Guaranteed to only occur once.
            Rule::local_definitions => {
                let (type_definitions, function_definitions) = to_declaration_block_elements(r.into_inner(), file_name, line_starts)?;
                local_function_definitions = function_definitions;
                local_type_definitions = type_definitions;

            }
            _ => rules.push(to_function_rule(r, file_name, &function_name, line_starts)),
        }
    }

    let location = Location {
        file: file_name.clone(),
        function: function_name.clone(),
        line,
        col,
    };
    Ok(FunctionBody {
        name: function_name.clone(),
        location: location.clone(),
        match_expressions,
        rules,
        local_function_definitions,
        local_type_definitions
    })
}

fn to_expression(expression: Pair<Rule>, file_name: &String, function_name: &String, line_starts: &Vec<usize>) -> Expression {
    PREC_CLIMBER.climb(
        expression.into_inner(),
        |pair: Pair<Rule>| {
            match pair.as_rule() {
                Rule::term => to_term(pair, file_name, function_name, line_starts),
                _ => unreachable!("prec_climber reached: {:?}", pair),
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
                Rule::record_field_access => RecordFieldAccess(loc_info, Box::new(lhs), Box::new(rhs)),
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
        Rule::number => IntegerLiteral(loc_info, sub.as_str().parse::<isize>().unwrap()),
        Rule::float => FloatLiteral(loc_info, sub.as_str().parse::<f64>().unwrap()),
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
        Rule::tuple_literal => TupleLiteral(loc_info, sub.into_inner().map(|te| to_expression(te, file_name, function_name, line_starts)).collect()),
        Rule::list_empty => EmptyListLiteral(loc_info),
        Rule::list_singleton => ShorthandListLiteral(loc_info, vec![to_expression(sub.into_inner().nth(0).unwrap(), file_name, function_name, line_starts)]),
        Rule::list_shorthand => ShorthandListLiteral(loc_info, sub.into_inner().map(|te| to_expression(te, file_name, function_name, line_starts)).collect()),
        Rule::list_longhand => {
            let mut children = sub.into_inner();
            let head = children.next().unwrap();
            let tail = children.next().unwrap();
            LonghandListLiteral(loc_info, Box::new(to_expression(head, file_name, function_name, line_starts)), Box::new(to_expression(tail, file_name, function_name, line_starts)))
        }
        Rule::case_expression => {
            let mut children = sub.into_inner();
            let expression = to_term(children.next().unwrap(), file_name, function_name, line_starts);
            let rules = children.map(|match_rule| {
                let (line, col) = line_col_number(line_starts, match_rule.as_span().start());
                let location = Location { file: file_name.clone(), function: function_name.clone(), line, col };
                let mut scs = match_rule.into_inner();
                let case_rule = to_match_expression(scs.next().unwrap().into_inner().next().unwrap(), file_name, function_name, line_starts);
                let result_rule = to_expression(scs.next().unwrap(), file_name, function_name, line_starts);
                CaseRule { loc_info: location, case_rule, result_rule }
            }).collect();
            Case(loc_info, Box::new(expression), rules)
        }
        Rule::adt_term => {
            let mut elements = sub.into_inner();
            let alternative = elements.next().unwrap().as_str().to_string();
            let arguments = elements.map(|e| to_expression(e, file_name, function_name, line_starts)).collect();
            ADTTypeConstructor(loc_info, alternative, arguments)
        }

        Rule::record_term => {
            let mut record_term_elements = sub.into_inner();
            let record_name = record_term_elements.next().unwrap().as_str().to_string();
            let field_expressions = record_term_elements
                .map(|e| {
                    let mut field_expression_elements = e.into_inner();
                    let identifier = field_expression_elements.next().unwrap().as_str().to_string();
                    let expression = to_expression(field_expression_elements.next().unwrap(), file_name, function_name, line_starts);
                    (identifier, expression)
                })
                .collect();


            Record(loc_info, record_name, field_expressions)
        }
        Rule::lambda => {
            let mut elements = sub.into_inner();
            let argument_match_expressions: Vec<MatchExpression> = elements.next().unwrap().into_inner().map(|me| to_match_expression(me.into_inner().next().unwrap(), file_name, function_name, line_starts)).collect();
            let body = to_expression(elements.next().unwrap(), file_name, function_name, line_starts);
            Lambda(loc_info, argument_match_expressions, Box::new(body))
        }

        r => panic!("Reached term {:#?}", r),
    }
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
        Rule::function_let_rule => {
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            let mut inner_rules = pair.into_inner();
            let identifier = to_match_expression(inner_rules.next().unwrap().into_inner().next().unwrap(), file_name, function_name, line_starts);
            let expression = to_expression(inner_rules.next().unwrap(), file_name, function_name, line_starts);
            FunctionRule::LetRule(Location { file: file_name.clone(), function: function_name.clone(), line, col }, identifier, expression)
        }
        r => unreachable!("to_function_rule reached: {:#?}", r)
    }
}

fn to_match_expression(match_expression: Pair<Rule>, file_name: &String, function_name: &String, line_starts: &Vec<usize>) -> MatchExpression {
    let (line, col) = line_col_number(line_starts, match_expression.as_span().start());
    let loc_info = Location { file: file_name.clone(), function: function_name.clone(), line, col };
    match match_expression.as_rule() {
        Rule::identifier => {
            MatchExpression::Identifier(loc_info, match_expression.as_str().to_string())
        }
        Rule::match_wildcard => MatchExpression::Wildcard(loc_info),
        Rule::tuple_match => MatchExpression::Tuple(loc_info, match_expression.into_inner().map(|e| to_match_expression(e, file_name, function_name, line_starts)).collect()),
        Rule::sub_match => to_match_expression(match_expression.into_inner().next().unwrap(), file_name, function_name, line_starts),
        Rule::list_match_empty => MatchExpression::ShorthandList(loc_info, vec![]),
        Rule::list_match_singleton => MatchExpression::ShorthandList(loc_info, vec![to_match_expression(match_expression.into_inner().next().unwrap(), file_name, function_name, line_starts)]),
        Rule::list_match_shorthand => MatchExpression::ShorthandList(loc_info, match_expression.into_inner().map(|e| to_match_expression(e, file_name, function_name, line_starts)).collect()),
        Rule::list_match_longhand => {
            let mut inner = match_expression.into_inner();
            let head = to_match_expression(inner.next().unwrap(), file_name, function_name, line_starts);
            let tail = to_match_expression(inner.next().unwrap(), file_name, function_name, line_starts);
            MatchExpression::LonghandList(loc_info, Box::new(head), Box::new(tail))
        }
        Rule::number => MatchExpression::IntLiteral(loc_info, match_expression.as_str().parse::<isize>().unwrap()),
        Rule::char_literal => MatchExpression::CharLiteral(loc_info, match_expression.as_str().to_string().chars().nth(1).unwrap()),
        Rule::string_literal => MatchExpression::StringLiteral(loc_info, match_expression.into_inner().next().unwrap().as_str().to_string()),
        Rule::bool_literal => MatchExpression::BoolLiteral(loc_info, match_expression.as_str().parse::<bool>().unwrap()),
        Rule::adt_match => {
            let mut elements = match_expression.into_inner();
            let alternative_name = elements.next().unwrap().as_str().to_string();

            MatchExpression::ADT(loc_info, alternative_name, elements.map(|m| to_match_expression(m, file_name, function_name, line_starts)).collect())
        }

        Rule::record_match => {
            let mut children = match_expression.into_inner();
            let name = children.next().unwrap().as_str().to_string();
            MatchExpression::Record(loc_info, name, children.map(|e| e.as_str().to_string()).collect())
        }

        r => unreachable!("Reached to_match_expression with: {:?}", r)
    }
}

fn to_type(pair: Pair<Rule>) -> Type {
    match pair.as_rule() {
        Rule::bool_type => Type::Bool,
        Rule::string_type => Type::String,
        Rule::int_type => Type::Int,
        Rule::char_type => Type::Char,
        Rule::float_type => Type::Float,
        Rule::tuple_type => {
            Type::Tuple(pair.into_inner().map(|r| to_type(r)).collect())
        }
        Rule::list_type => {
            Type::List(Box::new(to_type(pair.into_inner().next().unwrap())))
        }
        Rule::custom_type_single => {
            let name = pair.into_inner().next().unwrap().as_str().to_string();
            Type::UserType(name, vec![])
        }
        Rule::custom_type => {
            let mut elements = pair.into_inner();
            let name = elements.next().unwrap().as_str().to_string();

            let mut type_arguments = Vec::new();
            while let Some(e) = elements.next() {
                type_arguments.push(to_type(e))
            }
            Type::UserType(name, type_arguments)
        }
        Rule::type_variable => {
            Type::Variable(pair.as_str().to_string())
        }
        Rule::function_type => {
            let types: Vec<Type> = pair.into_inner()
                .map(|t| to_type(t))
                .collect();

            let (result_type, arguments) = types.split_last().unwrap();
            Type::Function(arguments.into_iter().cloned().collect(), Box::new(result_type.clone()))
        }
        t => unreachable!("Unhandled type: {:?}: {:#?}", t, pair)
    }
}