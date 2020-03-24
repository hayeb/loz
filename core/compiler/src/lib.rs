#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate pest_derive;
extern crate petgraph;

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use crate::Expression::*;

pub mod inferencer;
pub mod interpreter;
pub mod parser;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub file: String,
    pub function: String,
    pub line: usize,
    pub col: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "{}::{}[{}:{}]",
            self.file, self.function, self.line, self.col
        )
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
    pub name: String,
    pub location: Location,
    pub match_expressions: Vec<MatchExpression>,
    pub rules: Vec<FunctionRule>,
    pub local_function_definitions: Vec<FunctionDefinition>,
    pub local_type_definitions: Vec<CustomType>,
}

pub type TypeVar = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Char,
    String,
    Int,
    Float,

    // :: A b c d = A a | B b | C c
    UserType(String, Vec<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Variable(TypeVar),

    // a a b b -> b
    Function(Vec<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub bound_variables: HashSet<String>,
    pub enclosed_type: Type,
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
pub struct FunctionDefinition {
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

#[derive(Debug, Clone)]
pub struct AST {
    pub function_declarations: Vec<FunctionDefinition>,
    pub type_declarations: Vec<CustomType>,
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
            Type::UserType(t, type_arguments) => write!(
                f,
                "{} {}",
                t,
                type_arguments
                    .into_iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Type::Variable(name) => write!(f, "{}", name),
            Type::Tuple(elements) => write!(
                f,
                "({})",
                elements
                    .into_iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Type::List(e) => write!(f, "[{}]", e),
            Type::Function(from, to) => write!(
                f,
                "{} -> {}",
                from.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(" "),
                to.to_string()
            ),
        }
    }
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.bound_variables.len() > 0 {
            write!(
                f,
                "∀{}: {}",
                self.bound_variables
                    .iter()
                    .cloned()
                    .collect::<Vec<String>>()
                    .join(" "),
                self.enclosed_type
            )
        } else {
            write!(f, "{}", self.enclosed_type)
        }
    }
}

impl Type {
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

    pub fn referenced_custom_types(&self) -> HashSet<String> {
        match self {
            Type::Bool => HashSet::new(),
            Type::Char => HashSet::new(),
            Type::String => HashSet::new(),
            Type::Int => HashSet::new(),
            Type::Float => HashSet::new(),
            Type::UserType(name, arguments) => {
                let mut types: HashSet<String> = HashSet::new();
                types.insert(name.clone());
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
                let mut types: HashSet<String> = from_types
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
            Expression::TupleLiteral(_, expressions) => {
                Expression::expressions_referred_functions(expressions)
            }
            Expression::EmptyListLiteral(_) => HashSet::new(),
            Expression::ShorthandListLiteral(_, expressions) => {
                Expression::expressions_referred_functions(expressions)
            }
            Expression::LonghandListLiteral(_, e1, e2) => {
                Expression::dual_referred_functions(e1, e2)
            }
            Expression::ADTTypeConstructor(_, _, expressions) => {
                Expression::expressions_referred_functions(expressions)
            }
            Expression::Record(_, _, expressions) => Expression::expressions_referred_functions(
                &expressions.into_iter().map(|(_, e)| e.clone()).collect(),
            ),
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
            Expression::RecordFieldAccess(_, l, r) => Expression::dual_referred_functions(l, r),
            Expression::Lambda(_, _, e) => {
                let fs = e.function_references();
                // TODO: Remove introduced identifiers by lambda arguments
                fs
            }
        }
    }
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
