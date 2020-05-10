#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate pest_derive;

extern crate petgraph;

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use crate::Expression::*;
use std::rc::Rc;

pub mod inferencer;
pub mod interpreter;
pub mod parser;
pub mod module_system;

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

pub type ExportMember = String;

#[derive(Debug, Clone)]
pub enum Import {
    // Module name, imported members
    // from A import b, d
    ImportMembers(Location, String, HashSet<String>),

    // Import A
    // Import A as B
    ImportModule(Location, String, Option<String>),
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
    pub local_function_definitions: Vec<Rc<FunctionDefinition>>,
    pub local_adt_definitions: Vec<Rc<ADTDefinition>>,
    pub local_record_definitions: Vec<Rc<RecordDefinition>>
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
    UserType(String, Vec<Rc<Type>>),
    Tuple(Vec<Rc<Type>>),
    List(Rc<Type>),
    Variable(TypeVar),

    // a a b b -> b
    Function(Vec<Rc<Type>>, Rc<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub bound_variables: HashSet<String>,
    pub enclosed_type: Rc<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDefinition {
    pub name: String,
    pub location: Location,
    pub type_variables: Vec<String>,
    pub fields: HashMap<String, Rc<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTDefinition {
    pub name: String,
    pub location: Location,
    pub type_variables: Vec<String>,
    pub constructors: HashMap<String, ADTConstructor>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTConstructor {
    pub name: String,
    pub elements: Vec<Rc<Type>>,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    pub location: Location,
    pub name: String,
    pub function_type: Option<Rc<TypeScheme>>,
    pub function_bodies: Vec<Rc<FunctionBody>>,
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
pub struct Module {
    pub name: String,
    pub file_name: String,
    pub exported_members: HashSet<ExportMember>,
    pub imports: Vec<Import>,
    pub function_declarations: Vec<Rc<FunctionDefinition>>,
    pub adt_definitions: Vec<Rc<ADTDefinition>>,
    pub record_definitions: Vec<Rc<RecordDefinition>>,
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
                "({} -> {})",
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

    fn list_references(
        es: &Vec<Expression>,
        include_variables: bool,
    ) -> HashSet<(String, Location)> {
        es.iter()
            .flat_map(|e| e.references(include_variables))
            .collect()
    }

    pub fn dual_references(
        l: &Expression,
        r: &Expression,
        include_variables: bool,
    ) -> HashSet<(String, Location)> {
        let mut lrf = l.references(include_variables);
        lrf.extend(r.references(include_variables));
        lrf
    }

    pub fn references(&self, include_variables: bool) -> HashSet<(String, Location)> {
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
                let mut fs: HashSet<(String, Location)> = e.references(include_variables);

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
            Expression::RecordFieldAccess(_, l, r) => {
                Expression::dual_references(l, r, include_variables)
            }
            Expression::Lambda(_, _, e) => {
                let fs = e.references(include_variables);
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

pub fn declaration_references(
    d: &Rc<FunctionDefinition>,
    include_variables: bool,
) -> HashSet<(String, Location)> {
    let mut referred = HashSet::new();

    for b in &d.function_bodies {
        referred.extend(body_references(b, include_variables));
    }

    referred
}

pub fn body_references(b: &FunctionBody, include_variables: bool) -> HashSet<(String, Location)> {
    let mut local_references = HashSet::new();
    for me in &b.match_expressions {
        local_references.extend(me.variables());
    }
    for d in &b.local_function_definitions {
        local_references.insert(d.name.clone());
    }

    let mut locally_referred = HashSet::new();
    for r in &b.rules {
        locally_referred.extend(match r {
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
