use std::borrow::Borrow;
use std::rc::Rc;

use crate::ast::{Type, TypeVar};
use crate::inferencer::substitutor::substitute_type;
use crate::inferencer::InferenceErrorType;

pub fn unify(
    a: &Rc<Type>,
    b: &Rc<Type>,
) -> Result<Vec<(Rc<TypeVar>, Rc<Type>)>, InferenceErrorType> {
    match (a.borrow(), b.borrow()) {
        // Basic types always succeed with no unifications
        (Type::Bool, Type::Bool) => Ok(Vec::new()),
        (Type::Char, Type::Char) => Ok(Vec::new()),
        (Type::String, Type::String) => Ok(Vec::new()),
        (Type::Int, Type::Int) => Ok(Vec::new()),
        (Type::Float, Type::Float) => Ok(Vec::new()),

        (Type::UserType(a_name, a_argument_types), Type::UserType(b_name, b_argument_types)) => {
            if a_name != b_name {
                Err(InferenceErrorType::UnificationError(
                    Rc::clone(a),
                    Rc::clone(b),
                ))
            } else {
                unify_types(a_argument_types, b_argument_types)
            }
        }

        (Type::Tuple(a_element_types), Type::Tuple(b_element_types)) => {
            unify_types(a_element_types, b_element_types)
        }

        (Type::List(a_type), Type::List(b_type)) => match unify(a_type, b_type) {
            Ok(subs) => Ok(subs),
            Err(InferenceErrorType::UnificationError(l, r)) => {
                Err(InferenceErrorType::UnificationError(
                    Rc::new(Type::List(l)),
                    Rc::new(Type::List(r)),
                ))
            }
            Err(e) => Err(e),
        },

        (Type::Function(a_from_types, a_to_type), Type::Function(b_from_types, b_to_type)) => {
            unify_functions(a_from_types, a_to_type, b_from_types, b_to_type)
        }

        (Type::Variable(a_var), Type::Variable(b_var)) if a_var == b_var => Ok(Vec::new()),

        (Type::Variable(a_var), b_type)
            if !b_type.collect_free_type_variables().contains(a_var) =>
        {
            let mut subs = Vec::new();
            subs.push((Rc::clone(a_var), Rc::clone(b)));
            Ok(subs)
        }
        (a_type, Type::Variable(b_var))
            if !a_type.collect_free_type_variables().contains(b_var) =>
        {
            let mut subs = Vec::new();
            subs.push((Rc::clone(b_var), Rc::clone(a)));
            Ok(subs)
        }

        (_, _) => Err(InferenceErrorType::UnificationError(
            Rc::clone(a),
            Rc::clone(b),
        )),
    }
}

pub fn unify_one_of(
    types: &Vec<Rc<Type>>,
    r: &Rc<Type>,
) -> Result<Vec<(Rc<TypeVar>, Rc<Type>)>, InferenceErrorType> {
    for l in types {
        match unify(&l, &r) {
            Ok(unifiers) => return Ok(unifiers),
            Err(_) => continue,
        }
    }
    Err(InferenceErrorType::UnificationErrorMultiple(
        types.iter().map(|t| Rc::clone(t)).collect(),
        Rc::clone(r),
    ))
}

fn unify_types(
    a_types: &Vec<Rc<Type>>,
    b_types: &Vec<Rc<Type>>,
) -> Result<Vec<(Rc<TypeVar>, Rc<Type>)>, InferenceErrorType> {
    if a_types.len() != b_types.len() {
        return Err(InferenceErrorType::WrongNumberOfTypes(
            a_types.len(),
            b_types.len(),
        ));
    }
    let mut unifiers = Vec::new();
    for (a_argument_type, b_argument_type) in a_types.iter().zip(b_types.iter()) {
        let u = unify(
            &substitute_type(&unifiers, a_argument_type),
            &substitute_type(&unifiers, b_argument_type),
        )?;
        unifiers.extend(u);
    }
    Ok(unifiers)
}

fn unify_functions(
    a_arguments: &Vec<Rc<Type>>,
    a_result: &Rc<Type>,
    b_arguments: &Vec<Rc<Type>>,
    b_result: &Rc<Type>,
) -> Result<Vec<(Rc<TypeVar>, Rc<Type>)>, InferenceErrorType> {
    if a_arguments.len() != b_arguments.len() {
        return Err(InferenceErrorType::UnificationError(
            Rc::new(Type::Function(
                a_arguments.iter().map(Rc::clone).collect(),
                Rc::clone(a_result),
            )),
            Rc::new(Type::Function(
                b_arguments.iter().map(Rc::clone).collect(),
                Rc::clone(b_result),
            )),
        ));
    }

    let mut subs = Vec::new();
    let mut a_result_type = Rc::clone(a_result);
    let mut b_result_type = Rc::clone(b_result);
    for (a_argument_type, b_argument_type) in a_arguments.iter().zip(b_arguments.iter()) {
        let new_subs = unify(
            &substitute_type(&subs, a_argument_type),
            &substitute_type(&subs, b_argument_type),
        )
        .map_err(|_| {
            InferenceErrorType::UnificationError(
                Rc::new(Type::Function(
                    a_arguments.iter().map(Rc::clone).collect(),
                    Rc::clone(a_result),
                )),
                Rc::new(Type::Function(
                    b_arguments.iter().map(Rc::clone).collect(),
                    Rc::clone(b_result),
                )),
            )
        })?;
        a_result_type = substitute_type(&new_subs, &a_result_type);
        b_result_type = substitute_type(&new_subs, &b_result_type);

        subs.extend(new_subs);
    }

    let result_unifiers = unify(
        &substitute_type(&subs, &a_result_type),
        &substitute_type(&subs, &b_result_type),
    )
    .map_err(|_| {
        InferenceErrorType::UnificationError(
            Rc::new(Type::Function(
                a_arguments.iter().map(Rc::clone).collect(),
                Rc::clone(a_result),
            )),
            Rc::new(Type::Function(
                b_arguments.iter().map(Rc::clone).collect(),
                Rc::clone(b_result),
            )),
        )
    })?;
    subs.extend(result_unifiers);
    Ok(subs.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_basic_types() {
        assert!(unify(&Rc::new(Type::Bool), &Rc::new(Type::Bool)).is_ok());
        assert!(unify(&Rc::new(Type::Int), &Rc::new(Type::Int)).is_ok());
        assert!(unify(&Rc::new(Type::Float), &Rc::new(Type::Float)).is_ok());
        assert!(unify(&Rc::new(Type::String), &Rc::new(Type::String)).is_ok());
        assert!(unify(&Rc::new(Type::Char), &Rc::new(Type::Char)).is_ok());
    }

    #[test]
    fn test_variable() {
        let unify_result = unify(
            &Rc::new(Type::Variable(Rc::new("a".to_string()))),
            &Rc::new(Type::Bool),
        );
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        )
    }

    #[test]
    fn test_unify_tuple() {
        assert!(unify(
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Bool), Rc::new(Type::Int)])),
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Bool), Rc::new(Type::Int)])),
        )
        .is_ok());
        assert!(unify(
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Bool), Rc::new(Type::Int)])),
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Int), Rc::new(Type::Int)])),
        )
        .is_err());

        let unify_result = unify(
            &Rc::new(Type::Tuple(vec![
                Rc::new(Type::Variable(Rc::new("a".to_string()))),
                Rc::new(Type::Int),
            ])),
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Bool), Rc::new(Type::Int)])),
        );
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        );

        let unify_result = unify(
            &Rc::new(Type::Tuple(vec![Rc::new(Type::Bool), Rc::new(Type::Int)])),
            &Rc::new(Type::Tuple(vec![
                Rc::new(Type::Variable(Rc::new("a".to_string()))),
                Rc::new(Type::Int),
            ])),
        );
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        )
    }

    #[test]
    fn test_unify_list() {
        assert!(unify(
            &Rc::new(Type::List(Rc::new(Type::Bool))),
            &Rc::new(Type::List(Rc::new(Type::Bool))),
        )
        .is_ok());
        assert!(unify(
            &Rc::new(Type::List(Rc::new(Type::Int))),
            &Rc::new(Type::List(Rc::new(Type::Bool))),
        )
        .is_err());

        let unify_result = unify(
            &Rc::new(Type::List(Rc::new(Type::Variable(Rc::new(
                "a".to_string(),
            ))))),
            &Rc::new(Type::List(Rc::new(Type::Bool))),
        );
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        );

        let unify_result = unify(
            &Rc::new(Type::List(Rc::new(Type::Bool))),
            &Rc::new(Type::List(Rc::new(Type::Variable(Rc::new(
                "a".to_string(),
            ))))),
        );
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        )
    }

    #[test]
    fn test_unify_custom_type() {
        let adt_a = Rc::new(Type::UserType(
            Rc::new("A".to_string()),
            vec![Rc::new(Type::Bool), Rc::new(Type::Int)],
        ));
        let adt_b = Rc::new(Type::UserType(
            Rc::new("B".to_string()),
            vec![Rc::new(Type::String)],
        ));
        let adt_c = Rc::new(Type::UserType(
            Rc::new("A".to_string()),
            vec![
                Rc::new(Type::Variable(Rc::new("a".to_string()))),
                Rc::new(Type::Variable(Rc::new("b".to_string()))),
            ],
        ));

        assert!(unify(&adt_a, &Rc::new(Type::Variable(Rc::new("a".to_string())))).is_ok());
        assert!(unify(&adt_a, &adt_b).is_err());

        let unify_result = unify(&adt_a, &adt_c);
        assert!(unify_result.is_ok());
        let unify_result = unify_result.unwrap();
        assert_eq!(
            unify_result.get(0),
            Some(&("a".to_string(), Rc::new(Type::Bool)))
        );
        assert_eq!(
            unify_result.get(1),
            Some(&("b".to_string(), Rc::new(Type::Int)))
        );
    }

    #[test]
    fn test_free_variables() {
        let f_a = Rc::new(Type::Function(
            vec![Rc::new(Type::Variable(Rc::new("a".to_string())))],
            Rc::new(Type::Variable(Rc::new("b".to_string()))),
        ));
        let b = Rc::new(Type::Variable(Rc::new("a".to_string())));

        let unify_result = unify(&f_a, &b);
        assert!(unify_result.is_err());
        let e = unify_result.unwrap_err();
        assert_eq!(e, InferenceErrorType::UnificationError(f_a, b))
    }
}
