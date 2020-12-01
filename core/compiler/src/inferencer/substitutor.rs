use std::borrow::Borrow;
use std::rc::Rc;

use crate::{Type, TypeScheme, TypeVar};

pub type Substitutions = Vec<(Rc<TypeVar>, Rc<Type>)>;

pub fn substitute(substitutions: &Substitutions, target: &Rc<TypeScheme>) -> TypeScheme {
    let bound_variables = &target.bound_variables;
    let subs = substitutions
        .into_iter()
        .filter(|(v, _)| !bound_variables.contains(v))
        .map(|(n, v)| (Rc::clone(n), Rc::clone(v)))
        .collect();
    TypeScheme {
        bound_variables: bound_variables.iter().map(Rc::clone).collect(),
        enclosed_type: substitute_type(&subs, &target.enclosed_type),
    }
}

pub fn substitute_type(substitutions: &Substitutions, target: &Rc<Type>) -> Rc<Type> {
    let mut result_type = Rc::clone(target);
    for (v, t) in substitutions {
        result_type = apply_substitution(&v, &t, &result_type);
    }
    result_type
}

pub fn substitute_list(substitutions: &Substitutions, targets: &Vec<Rc<Type>>) -> Vec<Rc<Type>> {
    targets
        .into_iter()
        .map(|target| substitute_type(substitutions, target))
        .collect()
}

fn apply_substitution(v: &Rc<TypeVar>, t: &Rc<Type>, target: &Rc<Type>) -> Rc<Type> {
    match target.borrow() {
        Type::Bool => Rc::new(Type::Bool),
        Type::Char => Rc::new(Type::Char),
        Type::String => Rc::new(Type::String),
        Type::Int => Rc::new(Type::Int),
        Type::Float => Rc::new(Type::Float),

        Type::UserType(name, argument_types) => Rc::new(Type::UserType(
            Rc::clone(name),
            argument_types
                .into_iter()
                .map(|target| apply_substitution(v, t, target))
                .collect(),
        )),

        Type::Tuple(element_types) => Rc::new(Type::Tuple(
            element_types
                .into_iter()
                .map(|target| apply_substitution(v, t, target))
                .collect(),
        )),
        Type::List(element_type) => Rc::new(Type::List(apply_substitution(v, t, element_type))),
        Type::Variable(name) if name == v => Rc::clone(t),
        Type::Variable(ref name) => Rc::new(Type::Variable(Rc::clone(name))),

        Type::Function(from_types, to_type) => Rc::new(Type::Function(
            from_types
                .into_iter()
                .map(|ft| apply_substitution(v, t, ft))
                .collect(),
            apply_substitution(v, t, to_type),
        )),
    }
}
