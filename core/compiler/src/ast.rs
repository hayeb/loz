use std::collections::HashMap;
use std::rc::Rc;

use crate::{ADTDefinition, Import, Location, RecordDefinition, Type, TypeScheme};

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
    pub type_information: HashMap<Rc<String>, Rc<TypeScheme>>,
    pub match_expressions: Vec<Rc<MatchExpression>>,
    pub rules: Vec<Rc<FunctionRule>>,
    pub local_function_definitions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    pub local_adt_definitions: HashMap<Rc<String>, Rc<ADTDefinition>>,
    pub local_record_definitions: HashMap<Rc<String>, Rc<RecordDefinition>>,
}

#[derive(Debug, Clone)]
pub enum FunctionRule {
    ConditionalRule(Rc<Location>, Rc<Expression>, Rc<Expression>),
    ExpressionRule(Rc<Location>, Rc<Expression>),
    LetRule(
        Rc<Location>,
        HashMap<Rc<String>, Rc<TypeScheme>>,
        Rc<MatchExpression>,
        Rc<Expression>,
    ),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    BoolLiteral(Rc<Location>, bool),
    StringLiteral(Rc<Location>, Rc<String>),
    CharacterLiteral(Rc<Location>, char),
    IntegerLiteral(Rc<Location>, i64),
    FloatLiteral(Rc<Location>, f64),

    TupleLiteral(Rc<Location>, Vec<Rc<Expression>>),

    EmptyListLiteral(Rc<Location>, Option<Rc<Type>>),
    ShorthandListLiteral(Rc<Location>, Option<Rc<Type>>, Vec<Rc<Expression>>),
    LonghandListLiteral(
        Rc<Location>,
        Option<Rc<Type>>,
        Rc<Expression>,
        Rc<Expression>,
    ),

    ADTTypeConstructor(
        Rc<Location>,
        Option<Rc<Type>>,
        Rc<String>,
        Vec<Rc<Expression>>,
    ),
    Record(
        Rc<Location>,
        Option<Rc<Type>>,
        Rc<String>,
        Vec<(Rc<String>, Rc<Expression>)>,
    ),

    Case(
        Rc<Location>,
        Rc<Expression>,
        Vec<Rc<CaseRule>>,
        Option<Rc<Type>>,
    ),

    Call(
        Rc<Location>,
        Option<Rc<Type>>,
        Rc<String>,
        Vec<Rc<Expression>>,
    ),
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

    RecordFieldAccess(
        Rc<Location>,
        Option<Rc<Type>>,
        Rc<String>,
        Rc<Expression>,
        Rc<Expression>,
    ),

    Lambda(
        Rc<Location>,
        HashMap<Rc<String>, Rc<TypeScheme>>,
        Vec<Rc<MatchExpression>>,
        Rc<Expression>,
    ),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseRule {
    pub loc_info: Rc<Location>,
    pub type_information: HashMap<Rc<String>, Rc<TypeScheme>>,
    pub case_rule: Rc<MatchExpression>,
    pub result_rule: Rc<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MatchExpression {
    IntLiteral(Rc<Location>, i64),
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
    pub imports: Vec<Rc<Import>>,
    pub function_name_to_definition: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    pub adt_name_to_definition: HashMap<Rc<String>, Rc<ADTDefinition>>,
    pub record_name_to_definition: HashMap<Rc<String>, Rc<RecordDefinition>>,
}
