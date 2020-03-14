use crate::{Type, TypeScheme, TypeVar};

pub fn substitute(substitutions: &Vec<(TypeVar, Type)>, target: &TypeScheme) -> TypeScheme {
    let bound_variables = &target.bound_variables;
    let subs: Vec<(TypeVar, Type)> = substitutions.clone().into_iter()
        .filter(|(v, _)| !bound_variables.contains(v))
        .collect();
    TypeScheme { bound_variables: bound_variables.clone(), enclosed_type: substitute_type(&subs, &target.enclosed_type) }
}

fn apply_substitution(v: &TypeVar, t: &Type, target: &Type) -> Type {
    match target {
        Type::Bool => Type::Bool,
        Type::Char => Type::Char,
        Type::String => Type::String,
        Type::Int => Type::Int,
        Type::Float => Type::Float,

        Type::UserType(name, argument_types)
        => Type::UserType(name.clone(), argument_types.into_iter().map(|t| apply_substitution(v, t, target)).collect()),

        Type::Tuple(element_types) => Type::Tuple(element_types.into_iter().map(|target| apply_substitution(v, t, target)).collect()),
        Type::List(element_type) => Type::List(Box::new(apply_substitution(v, t, element_type.clone().as_ref()))),
        Type::Variable(name) if name == v => t.clone(),
        Type::Variable(ref name) => Type::Variable(name.clone()),

        Type::Function(from_types, to_type)
        => Type::Function(from_types.into_iter()
                              .map(|ft| apply_substitution(v, t, ft))
                              .collect(),
                          Box::new(apply_substitution(v, t, to_type)))
    }
}

pub fn substitute_type(substitutions: &Vec<(TypeVar, Type)>, target: &Type) -> Type {
    let mut result_type = target.clone();
    for (v, t) in substitutions {
        result_type = apply_substitution(&v, &t, &result_type);
    }
    result_type
}

pub fn substitute_list(substitutions: &Vec<(TypeVar, Type)>, targets: &Vec<Type>) -> Vec<Type> {
    targets.into_iter()
        .map(|target| substitute_type(substitutions, target))
        .collect()
}