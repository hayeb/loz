use std::borrow::Borrow;
use std::rc::Rc;

use crate::{Type, TypeScheme, TypeVar};

pub fn substitute(substitutions: &Vec<(TypeVar, Rc<Type>)>, target: &Rc<TypeScheme>) -> TypeScheme {
    let bound_variables = &target.bound_variables;
    let subs: Vec<(TypeVar, Rc<Type>)> = substitutions
        .clone()
        .into_iter()
        .filter(|(v, _)| !bound_variables.contains(v))
        .collect();
    TypeScheme {
        bound_variables: bound_variables.clone(),
        enclosed_type: substitute_type(&subs, &target.enclosed_type),
    }
}

fn apply_substitution(v: &TypeVar, t: &Type, target: &Rc<Type>) -> Rc<Type> {
    Rc::new(match target.borrow() {
        Type::Bool => Type::Bool,
        Type::Char => Type::Char,
        Type::String => Type::String,
        Type::Int => Type::Int,
        Type::Float => Type::Float,

        Type::UserType(name, argument_types) => Type::UserType(
            name.clone(),
            argument_types
                .into_iter()
                .map(|target| apply_substitution(v, t, target))
                .collect(),
        ),

        Type::Tuple(element_types) => Type::Tuple(
            element_types
                .into_iter()
                .map(|target| apply_substitution(v, t, target))
                .collect(),
        ),
        Type::List(element_type) => Type::List(apply_substitution(
            v,
            t,
            element_type,
        )),
        Type::Variable(name) if name == v => t.clone(),
        Type::Variable(ref name) => Type::Variable(name.clone()),

        Type::Function(from_types, to_type) => Type::Function(
            from_types
                .into_iter()
                .map(|ft| apply_substitution(v, t, ft))
                .collect(),
            apply_substitution(v, t, to_type),
        ),
    })
}

pub fn substitute_type(substitutions: &Vec<(TypeVar, Rc<Type>)>, target: &Rc<Type>) -> Rc<Type> {
    let mut result_type = Rc::clone(target);
    for (v, t) in substitutions {
        result_type = apply_substitution(&v, &t, &result_type);
    }
    result_type
}

pub fn substitute_list(substitutions: &Vec<(TypeVar, Rc<Type>)>, targets: &Vec<Rc<Type>>) -> Vec<Rc<Type>> {
    targets
        .into_iter()
        .map(|target| substitute_type(substitutions, target))
        .collect()
}
