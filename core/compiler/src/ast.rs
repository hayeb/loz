use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub module: Rc<String>,
    pub function: Rc<String>,
    pub line: usize,
    pub col: usize,
}

pub type ExportMember = String;

#[derive(Debug, Clone)]
pub enum Import {
    // Module name, imported members
    // from A import b, d
    ImportMembers(Rc<Location>, Rc<String>, HashSet<Rc<String>>),

    // Import A
    // Import A as B
    ImportModule(Rc<Location>, Rc<String>, Option<Rc<String>>),
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
    // :: A b c d = {a :: a, b :: b, c :: c, d :: d}
    UserType(Rc<String>, Vec<Rc<Type>>),
    Tuple(Vec<Rc<Type>>),
    List(Rc<Type>),
    Variable(Rc<TypeVar>),

    // a a b b -> b
    Function(Vec<Rc<Type>>, Rc<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub bound_variables: HashSet<Rc<String>>,
    pub enclosed_type: Rc<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDefinition {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub type_variables: Vec<Rc<String>>,
    pub fields: HashMap<Rc<String>, Rc<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTDefinition {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub type_variables: Vec<Rc<String>>,
    pub constructors: HashMap<Rc<String>, Rc<ADTConstructor>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ADTConstructor {
    pub name: Rc<String>,
    pub elements: Vec<Rc<Type>>,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    pub location: Rc<Location>,
    pub name: Rc<String>,
    pub function_type: Option<Rc<TypeScheme>>,
    pub function_bodies: Vec<Rc<FunctionBody>>,
}

#[derive(Debug, Clone)]
pub struct FunctionBody {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub match_expressions: Vec<Rc<MatchExpression>>,
    pub rules: Vec<Rc<FunctionRule>>,
    pub local_function_definitions: Vec<Rc<FunctionDefinition>>,
    pub local_adt_definitions: Vec<Rc<ADTDefinition>>,
    pub local_record_definitions: Vec<Rc<RecordDefinition>>,
}

#[derive(Debug, Clone)]
pub enum FunctionRule {
    // blabla
    ConditionalRule(Rc<Location>, Rc<Expression>, Rc<Expression>),
    ExpressionRule(Rc<Location>, Rc<Expression>),
    LetRule(Rc<Location>, Rc<MatchExpression>, Rc<Expression>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    BoolLiteral(Rc<Location>, bool),
    StringLiteral(Rc<Location>, Rc<String>),
    CharacterLiteral(Rc<Location>, char),
    IntegerLiteral(Rc<Location>, isize),
    FloatLiteral(Rc<Location>, f64),

    TupleLiteral(Rc<Location>, Vec<Rc<Expression>>),

    EmptyListLiteral(Rc<Location>),
    ShorthandListLiteral(Rc<Location>, Vec<Rc<Expression>>),
    LonghandListLiteral(Rc<Location>, Rc<Expression>, Rc<Expression>),

    ADTTypeConstructor(Rc<Location>, Rc<String>, Vec<Rc<Expression>>),
    Record(Rc<Location>, Rc<String>, Vec<(Rc<String>, Rc<Expression>)>),

    Case(Rc<Location>, Rc<Expression>, Vec<Rc<CaseRule>>),

    Call(Rc<Location>, Rc<String>, Vec<Rc<Expression>>),
    Variable(Rc<Location>, Rc<String>),

    Negation(Rc<Location>, Rc<Expression>),
    Minus(Rc<Location>, Rc<Expression>),

    Times(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Divide(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Modulo(Rc<Location>, Rc<Expression>, Rc<Expression>),

    Add(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Subtract(Rc<Location>, Rc<Expression>, Rc<Expression>),

    ShiftLeft(Rc<Location>, Rc<Expression>, Rc<Expression>),
    ShiftRight(Rc<Location>, Rc<Expression>, Rc<Expression>),

    Greater(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Greq(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Leq(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Lesser(Rc<Location>, Rc<Expression>, Rc<Expression>),

    Eq(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Neq(Rc<Location>, Rc<Expression>, Rc<Expression>),

    And(Rc<Location>, Rc<Expression>, Rc<Expression>),
    Or(Rc<Location>, Rc<Expression>, Rc<Expression>),

    RecordFieldAccess(Rc<Location>, Rc<Expression>, Rc<Expression>),

    Lambda(Rc<Location>, Vec<Rc<MatchExpression>>, Rc<Expression>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseRule {
    pub loc_info: Rc<Location>,
    pub case_rule: Rc<MatchExpression>,
    pub result_rule: Rc<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchExpression {
    IntLiteral(Rc<Location>, isize),
    CharLiteral(Rc<Location>, char),
    StringLiteral(Rc<Location>, Rc<String>),
    BoolLiteral(Rc<Location>, bool),
    Identifier(Rc<Location>, Rc<String>),
    Tuple(Rc<Location>, Vec<Rc<MatchExpression>>),
    ShorthandList(Rc<Location>, Vec<Rc<MatchExpression>>),
    LonghandList(Rc<Location>, Rc<MatchExpression>, Rc<MatchExpression>),
    Wildcard(Rc<Location>),
    ADT(Rc<Location>, Rc<String>, Vec<Rc<MatchExpression>>),
    Record(Rc<Location>, Rc<String>, Vec<Rc<String>>),
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: Rc<String>,
    pub file_name: Rc<String>,
    pub exported_members: HashSet<ExportMember>,
    pub imports: Vec<Rc<Import>>,
    pub function_definitions: Vec<Rc<FunctionDefinition>>,
    pub adt_definitions: Vec<Rc<ADTDefinition>>,
    pub record_definitions: Vec<Rc<RecordDefinition>>,
}
