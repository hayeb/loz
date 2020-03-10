extern crate pest;

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
use pest::prec_climber::*;

use Expression::StringLiteral;

use crate::parser::Expression::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub file: String,
    pub function: String,
    pub line: usize,
    pub col: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}::{}[{}:{}]", self.file, self.function, self.line, self.col)
    }
}

#[derive(Debug, Clone)]
pub enum FunctionRule {
    ConditionalRule(Location, Expression, Expression),
    ExpressionRule(Location, Expression),
    LetRule(Location, MatchExpression, Expression),
}

#[derive(Debug, Clone)]
pub struct FunctionBody {
    pub location: Location,
    pub match_expressions: Vec<MatchExpression>,
    pub rules: Vec<FunctionRule>,
}

pub type TypeVar = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Char,
    String,
    Int,
    Float,
    UserType(String, Vec<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Variable(TypeVar),

    // a a b b -> b
    Function(Vec<Type>, Box<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Char => write!(f, "Char"),
            Type::String => write!(f, "String"),
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::UserType(t, type_arguments) if type_arguments.len() == 0 => write!(f, "{}", t),
            Type::UserType(t, type_arguments) => write!(f, "{} {}", t, type_arguments.into_iter().map(|e| e.to_string()).collect::<Vec<String>>().join(" ")),
            Type::Variable(name) => write!(f, "{}", name),
            Type::Tuple(elements) => {
                write!(f, "({})", elements.into_iter().map(|e| e.to_string()).collect::<Vec<String>>().join(", "))
            }
            Type::List(e) => {
                write!(f, "[{}]", e)
            }
            Type::Function(from, to) => {
                write!(f, "{} -> {}", from.iter().map(|t| t.to_string()).collect::<Vec<String>>().join(" "), to.to_string())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub bound_variables: HashSet<String>,
    pub enclosed_type: Type,
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.bound_variables.len() > 0 {
            write!(f, "∀{}: {}", self.bound_variables.iter().cloned().collect::<Vec<String>>().join(" "), self.enclosed_type)
        } else {
            write!(f, "{}", self.enclosed_type)
        }
    }
}

impl Type {
    /*
    f :: a a a Int -> a

    map :: (a -> b) [a] -> [b]

    foldr :: [a] a (a a -> a) -> a


    */
    pub fn collect_free_type_variables(&self) -> HashSet<String> {
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
            Type::Variable(tv) => vec![tv.clone()].into_iter().collect(),
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum CustomType {
    ADT(Location, ADTDefinition),
    Record(Location, RecordDefinition),
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDefinition {
    pub name: String,
    pub type_variables: Vec<String>,
    pub fields: HashMap<String, Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTDefinition {
    pub name: String,
    pub type_variables: Vec<String>,
    pub constructors: HashMap<String, ADTConstructor>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTConstructor {
    pub name: String,
    pub elements: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct FunctionDeclaration {
    pub location: Location,
    pub name: String,
    pub function_type: Option<TypeScheme>,
    pub function_bodies: Vec<FunctionBody>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    BoolLiteral(Location, bool),
    StringLiteral(Location, String),
    CharacterLiteral(Location, char),
    IntegerLiteral(Location, isize),
    FloatLiteral(Location, f64),

    TupleLiteral(Location, Vec<Expression>),

    EmptyListLiteral(Location),
    ShorthandListLiteral(Location, Vec<Expression>),
    LonghandListLiteral(Location, Box<Expression>, Box<Expression>),

    ADTTypeConstructor(Location, String, Vec<Expression>),
    Record(Location, String, Vec<(String, Expression)>),

    Case(Location, Box<Expression>, Vec<CaseRule>),

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

    RecordFieldAccess(Location, Box<Expression>, Box<Expression>),

    Lambda(Location, Vec<MatchExpression>, Box<Expression>),
}

impl Expression {
    pub fn locate(&self) -> Location {
        match self {
            BoolLiteral(loc, _) => loc.clone(),
            StringLiteral(loc, _) => loc.clone(),
            CharacterLiteral(loc, _) => loc.clone(),
            IntegerLiteral(loc, _) => loc.clone(),
            FloatLiteral(loc, _) => loc.clone(),
            TupleLiteral(loc, _) => loc.clone(),
            EmptyListLiteral(loc) => loc.clone(),
            ShorthandListLiteral(loc, _) => loc.clone(),
            LonghandListLiteral(loc, _, _) => loc.clone(),
            ADTTypeConstructor(loc, _, _) => loc.clone(),
            Record(loc, _, _) => loc.clone(),
            Case(loc, _, _) => loc.clone(),
            Call(loc, _, _) => loc.clone(),
            Variable(loc, _) => loc.clone(),
            Negation(loc, _) => loc.clone(),
            Minus(loc, _) => loc.clone(),
            Times(loc, _, _) => loc.clone(),
            Divide(loc, _, _) => loc.clone(),
            Modulo(loc, _, _) => loc.clone(),
            Add(loc, _, _) => loc.clone(),
            Subtract(loc, _, _) => loc.clone(),
            ShiftLeft(loc, _, _) => loc.clone(),
            ShiftRight(loc, _, _) => loc.clone(),
            Greater(loc, _, _) => loc.clone(),
            Greq(loc, _, _) => loc.clone(),
            Leq(loc, _, _) => loc.clone(),
            Lesser(loc, _, _) => loc.clone(),
            Eq(loc, _, _) => loc.clone(),
            Neq(loc, _, _) => loc.clone(),
            And(loc, _, _) => loc.clone(),
            Or(loc, _, _) => loc.clone(),
            RecordFieldAccess(loc, _, _) => loc.clone(),
            Lambda(loc, _, _) => loc.clone(),
        }
    }

    fn expressions_referred_functions(es: &Vec<Expression>) -> HashSet<(String, Location)> {
        es.iter().flat_map(|e| e.function_references()).collect()
    }

    pub fn dual_referred_functions(l: &Expression, r: &Expression) -> HashSet<(String, Location)> {
        let mut lrf = l.function_references();
        lrf.extend(r.function_references());
        lrf
    }

    pub fn function_references(&self) -> HashSet<(String, Location)> {
        match self {
            Expression::BoolLiteral(_, _) => HashSet::new(),
            Expression::StringLiteral(_, _) => HashSet::new(),
            Expression::CharacterLiteral(_, _) => HashSet::new(),
            Expression::IntegerLiteral(_, _) => HashSet::new(),
            Expression::FloatLiteral(_, _) => HashSet::new(),
            Expression::TupleLiteral(_, expressions) => Expression::expressions_referred_functions(expressions),
            Expression::EmptyListLiteral(_) => HashSet::new(),
            Expression::ShorthandListLiteral(_, expressions) => Expression::expressions_referred_functions(expressions),
            Expression::LonghandListLiteral(_, e1, e2) => Expression::dual_referred_functions(e1, e2),
            Expression::ADTTypeConstructor(_, _, expressions) => Expression::expressions_referred_functions(expressions),
            Expression::Record(_, _, expressions) => Expression::expressions_referred_functions(&expressions.into_iter().map(|(_, e)| e.clone()).collect()),
            Expression::Case(_, e, rules) => {
                let mut fs: HashSet<(String, Location)> = e.function_references();

                for r in rules {
                    for fref in &r.result_rule.function_references() {
                        fs.insert(fref.clone());
                    }
                }

                fs
            }
            Expression::Call(loc, f, expressions) => {
                let mut fs = HashSet::new();
                fs.insert((f.clone(), loc.clone()));
                fs.extend(Expression::expressions_referred_functions(&expressions));
                fs
            }
            Expression::Variable(_, _) => HashSet::new(),
            Expression::Negation(_, e) => e.function_references(),
            Expression::Minus(_, e) => e.function_references(),
            Expression::Times(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Divide(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Modulo(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Add(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Subtract(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::ShiftLeft(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::ShiftRight(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Greater(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Greq(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Leq(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Lesser(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Eq(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Neq(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::And(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Or(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::RecordFieldAccess(_, l, r ) => Expression::dual_referred_functions(l, r),
            Expression::Lambda(_, arguments, e) => {
                let fs = e.function_references();
                // TODO: Remove introduced identifiers by lambda arguments
                fs
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseRule {
    pub loc_info: Location,
    pub case_rule: MatchExpression,
    pub result_rule: Expression,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchExpression {
    IntLiteral(Location, isize),
    CharLiteral(Location, char),
    StringLiteral(Location, String),
    BoolLiteral(Location, bool),
    Identifier(Location, String),
    Tuple(Location, Vec<MatchExpression>),
    ShorthandList(Location, Vec<MatchExpression>),
    LonghandList(Location, Box<MatchExpression>, Box<MatchExpression>),
    Wildcard(Location),
    ADT(Location, String, Vec<MatchExpression>),
    Record(Location, String, Vec<String>),
}

impl MatchExpression {
    pub fn locate(&self) -> Location {
        match self {
            MatchExpression::IntLiteral(loc, _) => loc.clone(),
            MatchExpression::CharLiteral(loc, _) => loc.clone(),
            MatchExpression::StringLiteral(loc, _) => loc.clone(),
            MatchExpression::BoolLiteral(loc, _) => loc.clone(),
            MatchExpression::Identifier(loc, _) => loc.clone(),
            MatchExpression::Tuple(loc, _) => loc.clone(),
            MatchExpression::ShorthandList(loc, _) => loc.clone(),
            MatchExpression::LonghandList(loc, _, _) => loc.clone(),
            MatchExpression::Wildcard(loc) => loc.clone(),
            MatchExpression::ADT(loc, _, _) => loc.clone(),
            MatchExpression::Record(loc, _, _) => loc.clone(),
        }
    }

    pub fn variables(&self) -> HashSet<String> {
        match self {
            MatchExpression::IntLiteral(_, _) => HashSet::new(),
            MatchExpression::CharLiteral(_, _) => HashSet::new(),
            MatchExpression::StringLiteral(_, _) => HashSet::new(),
            MatchExpression::BoolLiteral(_, _) => HashSet::new(),
            MatchExpression::Identifier(_, id) => vec![id.clone()].into_iter().collect(),
            MatchExpression::Tuple(_, elements) => elements.into_iter().flat_map(|e| e.variables().into_iter()).collect(),
            MatchExpression::ShorthandList(_, elements) =>  elements.into_iter().flat_map(|e| e.variables().into_iter()).collect(),
            MatchExpression::LonghandList(_, h, t) => {
                let mut vars = HashSet::new();
                vars.extend(h.variables());
                vars.extend(t.variables());
                vars
            },
            MatchExpression::Wildcard(_) => HashSet::new(),
            MatchExpression::ADT(_, _, elements) =>  elements.into_iter().flat_map(|e| e.variables().into_iter()).collect(),
            MatchExpression::Record(_, _, fields) => fields.into_iter().cloned().collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AST {
    pub function_declarations: Vec<FunctionDeclaration>,
    pub type_declarations: Vec<CustomType>,
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
            Operator::new(Rule::times, Left) | Operator::new(Rule::divide, Left) | Operator::new(Rule::modulo, Left),
            Operator::new(Rule::record_field_access, Left)
        ])
    };
}


pub fn parse(file_name: &String, input: &str) -> Result<AST, Error<Rule>> {
    let ast = LOZParser::parse(Rule::ast, input)?.next().unwrap();
    println!("Raw AST: {:#?}", ast);
    let line_starts = build_line_start_cache(input);
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

fn to_ast(pair: Pair<Rule>, file_name: &String, line_starts: &Vec<usize>) -> AST {
    match pair.as_rule() {
        Rule::ast => {
            let mut rules = pair.into_inner().peekable();
            let mut decls = Vec::new();
            let mut type_declarations = Vec::new();

            while let Some(pair) = rules.next() {
                match pair.as_rule() {
                    Rule::type_definition => {
                        let def = to_type_definition(pair, file_name, line_starts);
                        type_declarations.push(def);
                    }
                    Rule::function_definition => {
                        let fd = to_function_declaration(file_name, pair, line_starts);
                        decls.push(fd);
                    }
                    Rule::main => return AST { function_declarations: decls, type_declarations, main: to_expression(pair.into_inner().next().unwrap(), file_name, &"StartRule".to_string(), line_starts) },
                    Rule::EOI => continue,
                    r => unreachable!("Unhandled top-level rule: {:?}", r),
                }
            }
            unreachable!()
        }
        _ => unreachable!()
    }
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

fn to_function_declaration(file_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> FunctionDeclaration {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let rule = pair.into_inner().next().unwrap();
    match rule.as_rule() {
        Rule::function_definition_no_type => {
            let mut name = "".to_string();
            let mut bodies = vec![];

            for pair in rule.into_inner() {
                match pair.as_rule() {
                    Rule::function_body_no_type_first => {
                        name = pair.clone().into_inner().next().unwrap().into_inner().next().unwrap().as_str().to_string();
                        bodies.push(to_function_body(file_name, &name, pair, line_starts))
                    }
                    Rule::function_body_no_type_following => {
                        bodies.push(to_function_body(file_name, &name, pair, line_starts))
                    }
                    _ => unreachable!()
                }
            }
            FunctionDeclaration {
                location: Location { file: file_name.clone(), function: name.to_string(), line, col },
                name,
                function_type: None,
                function_bodies: bodies,
            }
        }
        Rule::function_definition_with_type => {
            let mut inner_rules = rule.into_inner();
            let name = inner_rules.next().unwrap().as_str();
            let function_type = to_function_type(inner_rules.next().unwrap());
            FunctionDeclaration {
                location: Location { file: file_name.clone(), function: name.to_string(), line, col },
                name: name.to_string(),
                function_type: Some(TypeScheme { bound_variables: function_type.clone().collect_free_type_variables(), enclosed_type: function_type.clone() }),
                function_bodies: inner_rules.map(|b| to_function_body(file_name, &name.to_string(), b, line_starts)).collect(),
            }
        }
        _ => unreachable!()
    }
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
            let argument_match_expressions : Vec<MatchExpression> = elements.next().unwrap().into_inner().map(|me| to_match_expression(me.into_inner().next().unwrap(), file_name, function_name, line_starts)).collect();
            let body = to_expression(elements.next().unwrap(), file_name, function_name, line_starts);
            Lambda(loc_info, argument_match_expressions, Box::new(body))
        }

        r => panic!("Reached term {:#?}", r),
    }
}

fn to_function_type(pair: Pair<Rule>) -> Type {
    let type_elements = pair.into_inner().peekable();

    let types: Vec<Type> = type_elements.map(|e| to_type(e)).collect();
    let (to, from) = types.split_last().unwrap();
    Type::Function(from.to_vec(), Box::new(to.clone()))
}

fn to_function_body(file_name: &String, function_name: &String, pair: Pair<Rule>, line_starts: &Vec<usize>) -> FunctionBody {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());

    match pair.as_rule() {
        Rule::function_body_no_type_first => {
            let mut parents = pair.into_inner();
            let match_parent = parents.next().unwrap();

            let mut match_expressions = Vec::new();
            for me in match_parent.into_inner() {
                if let Rule::identifier = me.as_rule() {
                    // When the function declaration has not type, the first of the match expressions is the name of the function.
                    continue;
                }
                match_expressions.push(to_match_expression(me.into_inner().next().unwrap(), file_name, function_name, line_starts));
            }

            println!("Parents: {:#?}", parents);

            let function_rules = parents.next().unwrap().into_inner().map(|b| to_function_rule(b, file_name, function_name, line_starts)).collect();
            FunctionBody { location: Location { file: file_name.clone(), function: function_name.clone(), line, col }, match_expressions, rules: function_rules }
        }
        Rule::function_body_no_type_following => {
            let mut parents = pair.into_inner();
            let match_parent = parents.next().unwrap();

            let mut match_expressions = Vec::new();
            for me in match_parent.into_inner() {
                if let Rule::identifier = me.as_rule() {
                    // When the function declaration has not type, the first of the match expressions is the name of the function.
                    continue;
                }
                match_expressions.push(to_match_expression(me.into_inner().next().unwrap(), file_name, function_name, line_starts));
            }

            let function_rules = parents.map(|b| to_function_rule(b.into_inner().next().unwrap(), file_name, function_name, line_starts)).collect();
            FunctionBody { location: Location { file: file_name.clone(), function: function_name.clone(), line, col }, match_expressions, rules: function_rules }
        }
        Rule::function_body_with_type => {
            let mut parents = pair.into_inner();
            let match_parent = parents.next().unwrap();

            let mut match_expressions = Vec::new();
            for me in match_parent.into_inner() {
                match_expressions.push(to_match_expression(me.into_inner().next().unwrap(), file_name, function_name, line_starts));
            }
            let function_rules = parents.map(|b| to_function_rule(b, file_name, function_name, line_starts)).collect();
            FunctionBody { location: Location { file: file_name.clone(), function: function_name.clone(), line, col }, match_expressions, rules: function_rules }
        }
        r => unreachable!("to_function_body {:?}", r)
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