use crate::parser::AST;

#[derive(Debug)]
pub enum TypeError {
    NoError,
}

#[derive(Debug)]
pub struct TypeResult {

}

pub fn _type(ast: AST) -> Result<TypeResult, Vec<TypeError>> {
    Ok(TypeResult{})
}