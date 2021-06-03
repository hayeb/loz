use crate::{Import, Location};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub struct IRRecordDefinition {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub fields: Vec<(Rc<String>, Rc<IRType>)>,
}
#[derive(Clone)]
pub struct IRADTDefinition {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub constructors: Vec<Rc<IRADTConstructor>>,
}
#[derive(Clone)]
pub struct IRADTConstructor {
    pub name: Rc<String>,
    pub elements: Vec<Rc<IRType>>,
}
#[derive(Clone)]
pub struct IRFunctionDefinition {
    pub location: Rc<Location>,
    pub name: Rc<String>,
    pub function_type: Rc<IRType>,
    pub function_bodies: Vec<Rc<IRFunctionBody>>,
}
#[derive(Clone)]
pub struct IRFunctionBody {
    pub name: Rc<String>,
    pub location: Rc<Location>,
    pub match_expressions: Vec<Rc<IRMatchExpression>>,
    pub rules: Vec<Rc<IRFunctionRule>>,
}
#[derive(Clone)]
pub enum IRFunctionRule {
    ConditionalRule(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    ExpressionRule(Rc<Location>, Rc<IRExpression>),
    LetRule(Rc<Location>, Rc<IRMatchExpression>, Rc<IRExpression>),
}
#[derive(Clone)]
pub enum IRExpression {
    BoolLiteral(Rc<Location>, bool),
    StringLiteral(Rc<Location>, Rc<String>),
    CharacterLiteral(Rc<Location>, char),
    IntegerLiteral(Rc<Location>, i64),
    FloatLiteral(Rc<Location>, f64),

    TupleLiteral(Rc<Location>, Vec<Rc<IRExpression>>),

    EmptyListLiteral(Rc<Location>, Rc<IRType>),
    ShorthandListLiteral(Rc<Location>, Rc<IRType>, Vec<Rc<IRExpression>>),
    LonghandListLiteral(Rc<Location>, Rc<IRType>, Rc<IRExpression>, Rc<IRExpression>),

    ADTTypeConstructor(Rc<Location>, Rc<IRType>, Rc<String>, Vec<Rc<IRExpression>>),
    Record(
        Rc<Location>,
        Rc<IRType>,
        Rc<String>,
        Vec<(Rc<String>, Rc<IRExpression>)>,
    ),

    Case(
        Rc<Location>,
        Rc<IRExpression>,
        Vec<Rc<IRCaseRule>>,
        Rc<IRType>,
    ),

    Call(Rc<Location>, Rc<IRType>, Rc<String>, Vec<Rc<IRExpression>>),
    Variable(Rc<Location>, Rc<String>),

    Negation(Rc<Location>, Rc<IRExpression>),
    Minus(Rc<Location>, Rc<IRExpression>),

    Times(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Divide(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Modulo(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    Add(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Subtract(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    ShiftLeft(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    ShiftRight(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    Greater(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Greq(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Leq(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Lesser(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    Eq(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Neq(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    And(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),
    Or(Rc<Location>, Rc<IRExpression>, Rc<IRExpression>),

    RecordFieldAccess(
        Rc<Location>,
        Rc<IRType>,
        Rc<String>,
        Rc<IRExpression>,
        Rc<IRExpression>,
    ),
}
#[derive(Clone)]
pub struct IRCaseRule {
    pub loc_info: Rc<Location>,
    pub case_rule: Rc<IRMatchExpression>,
    pub result_rule: Rc<IRExpression>,
}
#[derive(Clone)]
pub enum IRMatchExpression {
    IntLiteral(Rc<Location>, i64),
    CharLiteral(Rc<Location>, char),
    StringLiteral(Rc<Location>, Rc<String>),
    BoolLiteral(Rc<Location>, bool),
    Identifier(Rc<Location>, Rc<String>),
    Tuple(Rc<Location>, Vec<Rc<IRMatchExpression>>),
    ShorthandList(Rc<Location>, Vec<Rc<IRMatchExpression>>),
    LonghandList(Rc<Location>, Rc<IRMatchExpression>, Rc<IRMatchExpression>),
    Wildcard(Rc<Location>),
    ADT(Rc<Location>, Rc<String>, Vec<Rc<IRMatchExpression>>),
    Record(Rc<Location>, Rc<String>, Vec<Rc<String>>),
}
#[derive(Clone)]
pub struct IRModule {
    pub name: Rc<String>,
    pub file_name: Rc<String>,
    pub imports: Vec<Rc<Import>>,
    pub function_name_to_definition: HashMap<Rc<String>, Rc<IRFunctionDefinition>>,
    pub adt_name_to_definition: HashMap<Rc<String>, Rc<IRADTDefinition>>,
    pub record_name_to_definition: HashMap<Rc<String>, Rc<IRRecordDefinition>>,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IRType {
    Bool,
    Char,
    String,
    Int,
    Float,

    // :: A b c d = A a | B b | C c
    // :: A b c d = {a :: a, b :: b, c :: c, d :: d}
    UserType(Rc<String>),
    Tuple(Vec<Rc<IRType>>),
    List(Rc<IRType>),

    // a a b b -> b
    Function(Vec<Rc<IRType>>, Rc<IRType>),
}
