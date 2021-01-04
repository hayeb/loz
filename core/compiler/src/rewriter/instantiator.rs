use crate::inferencer::substitutor::{substitute, substitute_type, Substitutions};
use crate::inferencer::unifier::unify;
use crate::{hash_type, ADT_SEPARATOR, MONOMORPHIC_PREFIX};

use super::*;

/// Instantiates calls to functions with a polymorphic type.
/// For example:
/// ```haskell
/// map :: [a] (a -> b) -> [b]
/// f = map [1, 2, 3] (\a. a + 1)
/// ```
///
/// Here, the call to map instantiates the type of map to [Int] (Int -> Int) -> [Int]
/// We add a new definition for map in which all a and b type variables have (in this instance) been replaced with Int.
///
/// Note that this must be done recursively. Should map call another function, this call should also be instantiated.
///
/// A side effect of this is that only functions that are actually used are included in the final runtime module.
///
///
/// TODO:
/// 1. Instantiate function calls
/// 2. Instantiate record and ADT expressions.
pub fn instantiate(
    main_function: &Rc<String>,
    functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    records: HashMap<Rc<String>, Rc<RecordDefinition>>,
) -> Instantiated {
    InstantiatorState::new(functions, adts, records).instantiate(main_function)
}

pub struct Instantiated {
    pub functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    pub adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    pub records: HashMap<Rc<String>, Rc<RecordDefinition>>,
}

impl Instantiated {
    fn new() -> Self {
        Instantiated {
            functions: HashMap::new(),
            records: HashMap::new(),
            adts: HashMap::new(),
        }
    }
    fn merge(&mut self, other: Instantiated) {
        self.functions.extend(
            other
                .functions
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
        );
        self.adts
            .extend(other.adts.iter().map(|(n, d)| (Rc::clone(n), Rc::clone(d))));
        self.records.extend(
            other
                .records
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d))),
        );
    }
}

struct InstantiatorState {
    function_definitions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    adt_definitions: HashMap<Rc<String>, Rc<ADTDefinition>>,
    record_definitions: HashMap<Rc<String>, Rc<RecordDefinition>>,
}

impl InstantiatorState {
    fn new(
        function_definitions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
        adt_definitions: HashMap<Rc<String>, Rc<ADTDefinition>>,
        record_definitions: HashMap<Rc<String>, Rc<RecordDefinition>>,
    ) -> Self {
        InstantiatorState {
            function_definitions,
            adt_definitions,
            record_definitions,
        }
    }

    fn instantiate(&self, main_function: &Rc<String>) -> Instantiated {
        let mut function_queue: Vec<Rc<FunctionDefinition>> = vec![Rc::clone(
            self.function_definitions.get(main_function).unwrap(),
        )];

        // We need to deal with (polymorphic) types one at a time because they can be recursive..
        // It is not sufficient do do all records first, AND THEN all adts.
        let mut type_queue: Vec<(Option<Rc<RecordDefinition>>, Option<Rc<ADTDefinition>>)> =
            Vec::new();

        let mut instantiated_functions: HashMap<Rc<String>, Rc<FunctionDefinition>> =
            HashMap::new();
        let mut instantiated_records: HashMap<Rc<String>, Rc<RecordDefinition>> = HashMap::new();
        let mut instantiated_adts: HashMap<Rc<String>, Rc<ADTDefinition>> = HashMap::new();

        while let Some(d) = function_queue.pop() {
            if instantiated_functions.contains_key(&d.name) {
                // Skip function definitions for which we have already generated an instantiated definition.
                continue;
            }

            let (d, new_instantiated) = self.resolve_function_definition(&d);
            for (_, d) in new_instantiated.functions.iter() {
                function_queue.insert(0, Rc::clone(d))
            }
            for (_, d) in new_instantiated.records.iter() {
                type_queue.insert(0, (Some(Rc::clone(d)), None));
            }
            for (_, d) in new_instantiated.adts.iter() {
                type_queue.insert(0, (None, Some(Rc::clone(d))));
            }
            instantiated_functions.insert(Rc::clone(&d.name), d);
        }

        while let Some((l, r)) = type_queue.pop() {
            if let Some(record_definition) = l {
                if instantiated_records.contains_key(&record_definition.name) {
                    continue;
                }
                let (record_definition, new_instantiated) =
                    self.resolve_record_definition(&record_definition);

                for (_, d) in new_instantiated.records.iter() {
                    type_queue.insert(0, (Some(Rc::clone(d)), None));
                }
                for (_, d) in new_instantiated.adts.iter() {
                    type_queue.insert(0, (None, Some(Rc::clone(d))));
                }

                instantiated_records.insert(Rc::clone(&record_definition.name), record_definition);
            }
            if let Some(adt_definition) = r {
                if instantiated_adts.contains_key(&adt_definition.name) {
                    continue;
                }
                let (adt_definition, new_instantiated) =
                    self.resolve_adt_definition(&adt_definition);

                for (_, d) in new_instantiated.records.iter() {
                    type_queue.insert(0, (Some(Rc::clone(d)), None));
                }
                for (_, d) in new_instantiated.adts.iter() {
                    type_queue.insert(0, (None, Some(Rc::clone(d))));
                }
                instantiated_adts.insert(Rc::clone(&adt_definition.name), adt_definition);
            }
        }

        Instantiated {
            functions: instantiated_functions,
            adts: instantiated_adts,
            records: instantiated_records,
        }
    }

    fn resolve_adt_definition(
        &self,
        adt_definition: &Rc<ADTDefinition>,
    ) -> (Rc<ADTDefinition>, Instantiated) {
        let mut instantiated = Instantiated::new();

        // Type variables should be replace with concrete types earlier
        let mut constructors = Vec::new();
        for constructor in adt_definition.constructors.iter() {
            let mut elements = Vec::new();
            for element in constructor.elements.iter() {
                let (instantiated_element, new_instantiated) = self.resolve_type(element);
                elements.push(instantiated_element);
                instantiated.merge(new_instantiated);
            }
            constructors.push(Rc::new(ADTConstructor {
                name: Rc::clone(&constructor.name),
                elements,
            }));
        }

        (
            Rc::new(ADTDefinition {
                name: Rc::clone(&adt_definition.name.clone()),
                location: Rc::clone(&adt_definition.location.clone()),
                type_variables: vec![],
                constructors,
            }),
            instantiated,
        )
    }

    fn resolve_record_definition(
        &self,
        record_definition: &Rc<RecordDefinition>,
    ) -> (Rc<RecordDefinition>, Instantiated) {
        let mut instantiated = Instantiated::new();
        // Type variables should be replace with concrete types earlier
        let mut fields = Vec::new();

        for (n, field_type) in record_definition.fields.iter() {
            let (instantiated_field_type, new_instantiated) = self.resolve_type(field_type);
            fields.push((Rc::clone(n), instantiated_field_type));
            instantiated.merge(new_instantiated);
        }

        (
            Rc::new(RecordDefinition {
                name: Rc::clone(&record_definition.name),
                location: Rc::clone(&record_definition.location),
                type_variables: vec![],
                fields,
            }),
            instantiated,
        )
    }

    fn resolve_type(&self, loz_type: &Rc<Type>) -> (Rc<Type>, Instantiated) {
        match loz_type.borrow() {
            Type::Bool => (Rc::new(Type::Bool), Instantiated::new()),
            Type::Char => (Rc::new(Type::Char), Instantiated::new()),
            Type::String => (Rc::new(Type::String), Instantiated::new()),
            Type::Int => (Rc::new(Type::Int), Instantiated::new()),
            Type::Float => (Rc::new(Type::Float), Instantiated::new()),
            Type::UserType(name, _) => {
                if let Some(record_definition) = self.record_definitions.get(name) {
                    let record_type = Rc::new(Type::UserType(
                        Rc::clone(&name),
                        record_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    ));
                    let subs = unify(loz_type, &record_type).unwrap();

                    let instantiated_type = substitute_type(&subs, &record_type);
                    let type_hash = hash_type(&instantiated_type);
                    let instantiated_record_name =
                        Rc::new(format!("{}{}{}", &name, MONOMORPHIC_PREFIX, type_hash));

                    let mut instantiated = Instantiated::new();
                    instantiated.records.insert(
                        Rc::clone(&instantiated_record_name),
                        Rc::new(RecordDefinition {
                            name: Rc::clone(&instantiated_record_name),
                            location: Rc::clone(&record_definition.location),
                            type_variables: Vec::new(),
                            fields: record_definition
                                .fields
                                .iter()
                                .map(|(v, t)| (Rc::clone(v), substitute_type(&subs, t)))
                                .collect(),
                        }),
                    );
                    (
                        Rc::new(Type::UserType(
                            Rc::clone(&instantiated_record_name),
                            record_definition
                                .type_variables
                                .iter()
                                .map(|v| {
                                    substitute_type(&subs, &Rc::new(Type::Variable(Rc::clone(v))))
                                })
                                .collect(),
                        )),
                        instantiated,
                    )
                } else if let Some(adt_definition) = self.adt_definitions.get(name) {
                    let adt_type = Rc::new(Type::UserType(
                        Rc::clone(&name),
                        adt_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    ));
                    let subs = unify(loz_type, &adt_type).unwrap();

                    let instantiated_type = substitute_type(&subs, &adt_type);
                    let type_hash = hash_type(&instantiated_type);

                    let instantiated_adt_name =
                        Rc::new(format!("{}{}{}", &name, MONOMORPHIC_PREFIX, type_hash));

                    let mut instantiated = Instantiated::new();
                    instantiated.adts.insert(
                        Rc::clone(&instantiated_adt_name),
                        Rc::new(ADTDefinition {
                            name: Rc::clone(&instantiated_adt_name),
                            location: Rc::clone(&adt_definition.location),
                            type_variables: Vec::new(),
                            constructors: adt_definition
                                .constructors
                                .iter()
                                .map(|cd| {
                                    Rc::new(ADTConstructor {
                                        name: Rc::clone(&cd.name),
                                        elements: cd
                                            .elements
                                            .iter()
                                            .map(|e| substitute_type(&subs, e))
                                            .collect(),
                                    })
                                })
                                .collect(),
                        }),
                    );
                    (
                        Rc::new(Type::UserType(
                            Rc::clone(&instantiated_adt_name),
                            adt_definition
                                .type_variables
                                .iter()
                                .map(|v| {
                                    substitute_type(&subs, &Rc::new(Type::Variable(Rc::clone(v))))
                                })
                                .collect(),
                        )),
                        instantiated,
                    )
                } else {
                    unreachable!()
                }
            }
            Type::Tuple(elements) => {
                let mut initiated = Instantiated::new();

                let mut initiated_elements = Vec::new();
                for e in elements {
                    let (initiated_element, new_initiated) = self.resolve_type(e);
                    initiated_elements.push(initiated_element);
                    initiated.merge(new_initiated);
                }
                (Rc::new(Type::Tuple(initiated_elements)), initiated)
            }
            Type::List(e) => {
                let (initiated_e, initiated) = self.resolve_type(e);
                (Rc::new(Type::List(initiated_e)), initiated)
            }

            // TODO: Interesting..
            Type::Variable(_) => (Rc::clone(&loz_type), Instantiated::new()),

            Type::Function(arguments, result) => {
                let mut initiated = Instantiated::new();

                let mut initiated_arguments = Vec::new();
                for arg in arguments {
                    let (initiated_arg, new_initiated) = self.resolve_type(arg);
                    initiated_arguments.push(initiated_arg);
                    initiated.merge(new_initiated);
                }
                let (initiated_result, new_initiated) = self.resolve_type(result);
                initiated.merge(new_initiated);
                (
                    Rc::new(Type::Function(initiated_arguments, initiated_result)),
                    initiated,
                )
            }
        }
    }

    fn resolve_function_definition(
        &self,
        function_definition: &Rc<FunctionDefinition>,
    ) -> (Rc<FunctionDefinition>, Instantiated) {
        let mut instantiated = Instantiated::new();

        let mut instantiated_bodies = Vec::new();
        for b in function_definition.function_bodies.iter() {
            let (function_body, new_instantiated) = self.resolve_function_body(b);
            instantiated.merge(new_instantiated);
            instantiated_bodies.push(function_body);
        }

        let (instantiated_type, new_instantiated) = self.resolve_type(
            &function_definition
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
        );
        instantiated.merge(new_instantiated);
        (
            Rc::new(FunctionDefinition {
                location: Rc::clone(&function_definition.location),
                name: Rc::clone(&function_definition.name),
                function_type: Some(Rc::new(TypeScheme {
                    bound_variables: HashSet::new(),
                    enclosed_type: instantiated_type,
                })),
                function_bodies: instantiated_bodies,
            }),
            instantiated,
        )
    }

    fn resolve_function_body(
        &self,
        function_body: &Rc<FunctionBody>,
    ) -> (Rc<FunctionBody>, Instantiated) {
        let mut instantiated = Instantiated::new();

        let mut instantiated_rules = Vec::new();
        let mut type_information = function_body.type_information.clone();
        for function_rule in function_body.rules.iter() {
            match function_rule.borrow() {
                FunctionRule::ConditionalRule(loc, condition, expression) => {
                    let (instantiated_condition, new_instantiated) =
                        self.resolve_expression(condition, &type_information);
                    instantiated.merge(new_instantiated);
                    let (instantiated_expression, new_instantiated) =
                        self.resolve_expression(expression, &type_information);
                    instantiated.merge(new_instantiated);

                    instantiated_rules.push(Rc::new(FunctionRule::ConditionalRule(
                        Rc::clone(loc),
                        instantiated_condition,
                        instantiated_expression,
                    )))
                }
                FunctionRule::ExpressionRule(loc, expression) => {
                    let (instantiated_expression, new_instantiated) =
                        self.resolve_expression(expression, &type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_rules.push(Rc::new(FunctionRule::ExpressionRule(
                        Rc::clone(loc),
                        instantiated_expression,
                    )))
                }
                FunctionRule::LetRule(loc, let_type_information, match_expression, expression) => {
                    type_information.extend(
                        let_type_information
                            .iter()
                            .map(|(v, t)| (Rc::clone(v), Rc::clone(t))),
                    );
                    let (instantiated_expression, new_instantiated) =
                        self.resolve_expression(expression, &type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_rules.push(Rc::new(FunctionRule::LetRule(
                        Rc::clone(loc),
                        let_type_information.clone(),
                        Rc::clone(match_expression),
                        instantiated_expression,
                    )));
                }
            }
        }
        (
            Rc::new(FunctionBody {
                name: Rc::clone(&function_body.name),
                location: Rc::clone(&function_body.location),
                type_information: function_body.type_information.clone(),
                match_expressions: function_body.match_expressions.clone(),
                rules: instantiated_rules,
                // There are no local definitions at this point.
                local_function_definitions: HashMap::new(),
                local_adt_definitions: HashMap::new(),
                local_record_definitions: HashMap::new(),
            }),
            instantiated,
        )
    }

    fn resolve_expression(
        &self,
        expression: &Rc<Expression>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> (Rc<Expression>, Instantiated) {
        match expression.borrow() {
            Expression::BoolLiteral(loc, b) => (
                Rc::new(Expression::BoolLiteral(Rc::clone(loc), *b)),
                Instantiated::new(),
            ),
            Expression::StringLiteral(loc, s) => (
                Rc::new(Expression::StringLiteral(Rc::clone(loc), Rc::clone(s))),
                Instantiated::new(),
            ),
            Expression::CharacterLiteral(loc, c) => (
                Rc::new(Expression::CharacterLiteral(Rc::clone(loc), *c)),
                Instantiated::new(),
            ),
            Expression::IntegerLiteral(loc, i) => (
                Rc::new(Expression::IntegerLiteral(Rc::clone(loc), *i)),
                Instantiated::new(),
            ),
            Expression::FloatLiteral(loc, f) => (
                Rc::new(Expression::FloatLiteral(Rc::clone(loc), *f)),
                Instantiated::new(),
            ),

            Expression::TupleLiteral(loc, elements) => {
                let mut instantiated_elements = Vec::new();
                let mut instantiated = Instantiated::new();
                for element in elements {
                    let (instantiated_element, new_instantiated) =
                        self.resolve_expression(element, type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_elements.push(instantiated_element);
                }
                (
                    Rc::new(Expression::TupleLiteral(
                        Rc::clone(loc),
                        instantiated_elements,
                    )),
                    instantiated,
                )
            }
            Expression::EmptyListLiteral(loc, list_type) => (
                Rc::new(Expression::EmptyListLiteral(
                    Rc::clone(loc),
                    list_type.clone(),
                )),
                Instantiated::new(),
            ),
            Expression::ShorthandListLiteral(loc, list_type, elements) => {
                let mut instantiated_elements = Vec::new();
                let mut instantiated = Instantiated::new();
                for element in elements {
                    let (instantiated_element, new_instantiated) =
                        self.resolve_expression(element, type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_elements.push(instantiated_element);
                }
                (
                    Rc::new(Expression::ShorthandListLiteral(
                        Rc::clone(loc),
                        list_type.clone(),
                        instantiated_elements,
                    )),
                    instantiated,
                )
            }
            Expression::LonghandListLiteral(loc, list_type, h, t) => {
                let mut instantiated = Instantiated::new();
                let (instantiated_h, new_instantiated) =
                    self.resolve_expression(h, type_information);
                instantiated.merge(new_instantiated);
                let (instantiated_t, new_instantiated) =
                    self.resolve_expression(t, type_information);
                instantiated.merge(new_instantiated);
                (
                    Rc::new(Expression::LonghandListLiteral(
                        Rc::clone(loc),
                        list_type.clone(),
                        instantiated_h,
                        instantiated_t,
                    )),
                    instantiated,
                )
            }
            Expression::ADTTypeConstructor(loc, adt_type, constructor_name, arguments) => {
                let mut instantiated_arguments = Vec::new();
                let mut instantiated = Instantiated::new();
                for argument in arguments {
                    let (instantiated_argument, new_instantiated) =
                        self.resolve_expression(argument, type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_arguments.push(instantiated_argument);
                }

                let (instantiated_adt_type, new_instantiated) =
                    self.resolve_type(adt_type.as_ref().unwrap());
                instantiated.merge(new_instantiated);
                (
                    Rc::new(Expression::ADTTypeConstructor(
                        Rc::clone(loc),
                        Some(instantiated_adt_type),
                        Rc::clone(constructor_name),
                        instantiated_arguments,
                    )),
                    instantiated,
                )
            }
            Expression::Record(loc, record_type, record_name, field_expressions) => {
                let record_definition = self.record_definitions.get(record_name).unwrap();
                let type_hash = hash_type(record_type.as_ref().unwrap());
                let new_record_name = Rc::new(format!(
                    "{}{}{}",
                    record_name, MONOMORPHIC_PREFIX, type_hash
                ));

                let subs = unify(
                    record_type.as_ref().unwrap(),
                    &Rc::new(Type::UserType(
                        Rc::clone(record_name),
                        record_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    )),
                )
                .unwrap();

                let mut instantiated_field_expressions = Vec::new();
                let mut instantiated = Instantiated::new();
                instantiated.records.insert(
                    Rc::clone(&new_record_name),
                    substitute_record_definition(&new_record_name, &subs, record_definition),
                );
                for (field_name, field_expression) in field_expressions {
                    let (instantiated_field_expression, new_instantiated) =
                        self.resolve_expression(field_expression, type_information);
                    instantiated.merge(new_instantiated);
                    instantiated_field_expressions
                        .push((Rc::clone(field_name), instantiated_field_expression));
                }

                let (instantiated_record_type, new_instantiated) =
                    self.resolve_type(record_type.as_ref().unwrap());
                instantiated.merge(new_instantiated);
                (
                    Rc::new(Expression::Record(
                        Rc::clone(loc),
                        Some(instantiated_record_type),
                        Rc::clone(&new_record_name),
                        instantiated_field_expressions,
                    )),
                    instantiated,
                )
            }
            Expression::Case(loc, expression, rules, result_type) => {
                let mut instantiated = Instantiated::new();
                let (instantiated_expression, new_instantiated) =
                    self.resolve_expression(expression, type_information);
                instantiated.merge(new_instantiated);

                let mut instantiated_rules = Vec::new();

                for rule in rules {
                    let mut combined_type_information = HashMap::new();
                    combined_type_information.extend(type_information.clone());
                    combined_type_information.extend(rule.type_information.clone());

                    let (instantiated_result_rule, new_instantiated) =
                        self.resolve_expression(&rule.result_rule, &combined_type_information);
                    instantiated.merge(new_instantiated);

                    instantiated_rules.push(Rc::new(CaseRule {
                        loc_info: Rc::clone(&rule.loc_info),
                        type_information: rule.type_information.clone(),
                        case_rule: rule.case_rule.clone(),
                        result_rule: instantiated_result_rule,
                    }))
                }

                (
                    Rc::new(Expression::Case(
                        Rc::clone(loc),
                        instantiated_expression,
                        instantiated_rules,
                        result_type.clone(),
                    )),
                    instantiated,
                )
            }
            Expression::Call(loc, function_type, function_name, arguments) => {
                let (new_call, arguments, instantiated) = self.resolve_function_call(
                    function_name,
                    function_type.as_ref().unwrap(),
                    arguments,
                    type_information,
                );
                (
                    Rc::new(Expression::Call(
                        Rc::clone(loc),
                        function_type.clone(),
                        new_call,
                        arguments,
                    )),
                    instantiated,
                )
            }
            Expression::Variable(loc, name) => (
                Rc::new(Expression::Variable(Rc::clone(loc), Rc::clone(name))),
                Instantiated::new(),
            ),
            Expression::Negation(loc, expression) => {
                let (instantiated_expression, new_instantiated) =
                    self.resolve_expression(expression, type_information);
                (
                    Rc::new(Expression::Negation(
                        Rc::clone(loc),
                        instantiated_expression,
                    )),
                    new_instantiated,
                )
            }
            Expression::Minus(loc, expression) => {
                let (instantiated_expression, new_instantiated) =
                    self.resolve_expression(expression, type_information);
                (
                    Rc::new(Expression::Minus(Rc::clone(loc), instantiated_expression)),
                    new_instantiated,
                )
            }
            Expression::Times(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Times(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Divide(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Divide(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Modulo(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Modulo(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Add(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::Add(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::Subtract(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Subtract(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::ShiftLeft(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::ShiftLeft(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::ShiftRight(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::ShiftRight(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Greater(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Greater(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Greq(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Greq(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Leq(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::Leq(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::Lesser(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (
                    Rc::new(Expression::Lesser(Rc::clone(loc), l, r)),
                    instantiated,
                )
            }
            Expression::Eq(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::Eq(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::Neq(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::Neq(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::And(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::And(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::Or(loc, l, r) => {
                let (l, r, instantiated) = self.resolve_duo(l, r, type_information);
                (Rc::new(Expression::Or(Rc::clone(loc), l, r)), instantiated)
            }
            Expression::RecordFieldAccess(
                loc,
                record_type,
                record_name,
                record_expression,
                field_expression,
            ) => {
                let (instantiated_expression, new_instantiated) =
                    self.resolve_expression(record_expression, type_information);
                let new_record_name = format!(
                    "{}{}{}",
                    record_name,
                    MONOMORPHIC_PREFIX,
                    hash_type(record_type.as_ref().unwrap())
                );
                (
                    Rc::new(Expression::RecordFieldAccess(
                        Rc::clone(loc),
                        record_type.clone(),
                        Rc::new(new_record_name),
                        instantiated_expression,
                        Rc::clone(field_expression),
                    )),
                    new_instantiated,
                )
            }
            Expression::Lambda(loc, lambda_type_information, match_expressions, expression) => {
                let mut combined_type_information = HashMap::new();
                combined_type_information.extend(type_information.clone());
                combined_type_information.extend(lambda_type_information.clone());
                let (instantiated_expression, new_instantiated) =
                    self.resolve_expression(expression, &combined_type_information);
                (
                    Rc::new(Expression::Lambda(
                        Rc::clone(loc),
                        lambda_type_information.clone(),
                        match_expressions.clone(),
                        instantiated_expression,
                    )),
                    new_instantiated,
                )
            }
        }
    }

    fn resolve_function_call(
        &self,
        name: &Rc<String>,
        function_type: &Rc<Type>,
        arguments: &Vec<Rc<Expression>>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> (Rc<String>, Vec<Rc<Expression>>, Instantiated) {
        let function_definition = self.function_definitions.get(name).unwrap();
        let type_hash = hash_type(function_type);
        let call_name = Rc::new(format!("{}{}{}", name, MONOMORPHIC_PREFIX, type_hash));

        let subs = unify(
            &function_definition
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
            function_type,
        )
        .unwrap();

        let mut resolved_arguments = Vec::new();
        let mut instantiated = Instantiated::new();
        instantiated.functions.insert(
            Rc::clone(&call_name),
            substitute_function_definition(
                &self.adt_definitions,
                &self.record_definitions,
                &call_name,
                &subs,
                function_definition,
            ),
        );
        for argument in arguments {
            let (resolved_argument, new_instantiated) =
                self.resolve_expression(argument, type_information);
            instantiated.merge(new_instantiated);
            resolved_arguments.push(resolved_argument);
        }

        (Rc::clone(&call_name), resolved_arguments, instantiated)
    }

    fn resolve_duo(
        &self,
        l: &Rc<Expression>,
        r: &Rc<Expression>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> (Rc<Expression>, Rc<Expression>, Instantiated) {
        let mut instantiated = Instantiated::new();
        let (instantiated_l, new_instantiated) = self.resolve_expression(l, type_information);
        instantiated.merge(new_instantiated);
        let (instantiated_r, new_instantiated) = self.resolve_expression(r, type_information);
        instantiated.merge(new_instantiated);
        (instantiated_l, instantiated_r, instantiated)
    }
}

fn substitute_function_definition(
    adts: &HashMap<Rc<String>, Rc<ADTDefinition>>,
    records: &HashMap<Rc<String>, Rc<RecordDefinition>>,
    new_name: &Rc<String>,
    substitutions: &Substitutions,
    target: &Rc<FunctionDefinition>,
) -> Rc<FunctionDefinition> {
    let function_type = substitute_type(
        substitutions,
        &target.function_type.as_ref().unwrap().enclosed_type,
    );
    let argument_types = match function_type.borrow() {
        Type::Function(args, _) => args.clone(),
        _ => vec![function_type.clone()],
    };
    Rc::new(FunctionDefinition {
        location: target.location.clone(),
        name: Rc::clone(new_name),
        function_type: Some(Rc::new(TypeScheme {
            bound_variables: HashSet::new(),
            enclosed_type: function_type,
        })),
        function_bodies: target
            .function_bodies
            .iter()
            .map(|b| substitute_function_body(adts, records, &argument_types, substitutions, b))
            .collect(),
    })
}

fn substitute_record_definition(
    new_name: &Rc<String>,
    substitutions: &Substitutions,
    target: &Rc<RecordDefinition>,
) -> Rc<RecordDefinition> {
    Rc::new(RecordDefinition {
        location: Rc::clone(&target.location),
        name: Rc::clone(new_name),
        type_variables: Vec::new(),
        fields: target
            .fields
            .iter()
            .map(|(n, t)| (Rc::clone(n), substitute_type(substitutions, t)))
            .collect(),
    })
}

fn substitute_function_body(
    adts: &HashMap<Rc<String>, Rc<ADTDefinition>>,
    records: &HashMap<Rc<String>, Rc<RecordDefinition>>,
    argument_types: &Vec<Rc<Type>>,
    substitutions: &Substitutions,
    target: &Rc<FunctionBody>,
) -> Rc<FunctionBody> {
    let type_information = target
        .type_information
        .iter()
        .map(|(n, t)| (n.clone(), Rc::new(substitute(substitutions, t))))
        .collect();

    let match_expressions = target
        .match_expressions
        .iter()
        .zip(argument_types.iter())
        .map(|(me, mt)| substitute_type_references(&type_information, adts, records, me, mt))
        .collect();

    Rc::new(FunctionBody {
        name: target.name.clone(),
        location: target.location.clone(),
        type_information,
        match_expressions,
        rules: target
            .rules
            .iter()
            .map(|r| substitute_function_rule(substitutions, r))
            .collect(),

        // These are no longer present at this stage.
        local_function_definitions: HashMap::new(),
        local_adt_definitions: HashMap::new(),
        local_record_definitions: HashMap::new(),
    })
}

fn substitute_function_rule(
    substitutions: &Substitutions,
    target: &Rc<FunctionRule>,
) -> Rc<FunctionRule> {
    Rc::new(match target.borrow() {
        FunctionRule::ConditionalRule(loc, condition, expression) => FunctionRule::ConditionalRule(
            loc.clone(),
            substitute_expression(substitutions, condition),
            substitute_expression(substitutions, expression),
        ),
        FunctionRule::ExpressionRule(loc, expression) => FunctionRule::ExpressionRule(
            loc.clone(),
            substitute_expression(substitutions, expression),
        ),
        FunctionRule::LetRule(loc, type_information, match_expression, expression) => {
            FunctionRule::LetRule(
                loc.clone(),
                type_information
                    .iter()
                    .map(|(v, t)| (Rc::clone(v), Rc::new(substitute(substitutions, t))))
                    .collect(),
                match_expression.clone(),
                substitute_expression(substitutions, expression),
            )
        }
    })
}

fn substitute_type_references(
    type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    adts: &HashMap<Rc<String>, Rc<ADTDefinition>>,
    records: &HashMap<Rc<String>, Rc<RecordDefinition>>,
    match_expression: &Rc<MatchExpression>,
    match_type: &Rc<Type>,
) -> Rc<MatchExpression> {
    match (match_expression.borrow(), match_type.borrow()) {
        (MatchExpression::IntLiteral(_, _), _) => Rc::clone(match_expression),
        (MatchExpression::CharLiteral(_, _), _) => Rc::clone(match_expression),
        (MatchExpression::StringLiteral(_, _), _) => Rc::clone(match_expression),
        (MatchExpression::BoolLiteral(_, _), _) => Rc::clone(match_expression),
        (MatchExpression::Identifier(_, _), _) => Rc::clone(match_expression),
        (MatchExpression::Wildcard(_), _) => Rc::clone(match_expression),

        (MatchExpression::Tuple(l, elements), Type::Tuple(element_types)) => {
            Rc::new(MatchExpression::Tuple(
                Rc::clone(l),
                elements
                    .iter()
                    .zip(element_types.iter())
                    .map(|(e, t)| substitute_type_references(type_information, adts, records, e, t))
                    .collect(),
            ))
        }

        (MatchExpression::ShorthandList(l, elements), Type::List(list_type)) => {
            Rc::new(MatchExpression::ShorthandList(
                Rc::clone(l),
                elements
                    .iter()
                    .map(|e| {
                        substitute_type_references(type_information, adts, records, e, list_type)
                    })
                    .collect(),
            ))
        }
        (MatchExpression::LonghandList(l, h, t), Type::List(list_type)) => {
            Rc::new(MatchExpression::LonghandList(
                Rc::clone(l),
                substitute_type_references(type_information, adts, records, h, list_type),
                substitute_type_references(&type_information, adts, records, t, match_type),
            ))
        }

        (MatchExpression::ADT(l, constructor_name, arguments), Type::UserType(name, _)) => {
            let type_hash = hash_type(match_type);

            let adt_definition = adts.get(name).unwrap();

            let adt_constructor = adt_definition
                .constructors
                .iter()
                .filter(|c| &c.name == constructor_name)
                .next()
                .unwrap();

            let subs = unify(
                match_type,
                &Rc::new(Type::UserType(
                    Rc::clone(name),
                    adt_definition
                        .type_variables
                        .iter()
                        .map(|tv| Rc::new(Type::Variable(tv.clone())))
                        .collect(),
                )),
            )
            .unwrap();

            let adt_constructor_argument_types: Vec<Rc<Type>> = adt_constructor
                .elements
                .iter()
                .map(|t| substitute_type(&subs, t))
                .collect();
            Rc::new(MatchExpression::ADT(
                Rc::clone(l),
                Rc::new(format!(
                    "{}{}{}{}{}",
                    name, ADT_SEPARATOR, &constructor_name, MONOMORPHIC_PREFIX, type_hash
                )),
                arguments
                    .iter()
                    .zip(adt_constructor_argument_types.iter())
                    .map(|(me, mt)| {
                        substitute_type_references(type_information, adts, records, me, mt)
                    })
                    .collect(),
            ))
        }

        (MatchExpression::Record(l, _, fields), Type::UserType(name, _)) => {
            let type_hash = hash_type(match_type);
            Rc::new(MatchExpression::Record(
                Rc::clone(l),
                Rc::new(format!("{}{}{}", &name, MONOMORPHIC_PREFIX, type_hash)),
                fields.clone(),
            ))
        }

        (l, r) => unreachable!(
            "Illegal match expression * type combination at location {} with type {}",
            l.locate(),
            r
        ),
    }
}

fn substitute_expression(substitutions: &Substitutions, target: &Rc<Expression>) -> Rc<Expression> {
    Rc::new(match target.borrow() {
        Expression::BoolLiteral(loc, b) => Expression::BoolLiteral(Rc::clone(loc), *b),
        Expression::StringLiteral(loc, s) => {
            Expression::StringLiteral(Rc::clone(loc), Rc::clone(s))
        }
        Expression::CharacterLiteral(loc, c) => Expression::CharacterLiteral(Rc::clone(loc), *c),
        Expression::IntegerLiteral(loc, i) => Expression::IntegerLiteral(Rc::clone(loc), *i),
        Expression::FloatLiteral(loc, f) => Expression::FloatLiteral(Rc::clone(loc), *f),

        Expression::TupleLiteral(loc, elements) => Expression::TupleLiteral(
            Rc::clone(loc),
            elements
                .iter()
                .map(|e| substitute_expression(substitutions, e))
                .collect(),
        ),
        Expression::EmptyListLiteral(loc, list_type) => Expression::EmptyListLiteral(
            Rc::clone(loc),
            list_type
                .as_ref()
                .map(|t| substitute_type(&substitutions, t)),
        ),
        Expression::ShorthandListLiteral(loc, list_type, elements) => {
            Expression::ShorthandListLiteral(
                Rc::clone(loc),
                list_type
                    .as_ref()
                    .map(|t| substitute_type(&substitutions, t)),
                elements
                    .iter()
                    .map(|e| substitute_expression(substitutions, e))
                    .collect(),
            )
        }
        Expression::LonghandListLiteral(loc, list_type, h, t) => Expression::LonghandListLiteral(
            Rc::clone(loc),
            list_type
                .as_ref()
                .map(|t| substitute_type(&substitutions, t)),
            substitute_expression(substitutions, h),
            substitute_expression(substitutions, t),
        ),

        Expression::ADTTypeConstructor(loc, adt_type, name, arguments) => {
            Expression::ADTTypeConstructor(
                Rc::clone(loc),
                adt_type
                    .as_ref()
                    .map(|t| substitute_type(&substitutions, t)),
                Rc::clone(name),
                arguments
                    .iter()
                    .map(|a| substitute_expression(substitutions, a))
                    .collect(),
            )
        }

        Expression::Record(loc, record_type, record_name, fields) => Expression::Record(
            Rc::clone(loc),
            record_type
                .as_ref()
                .map(|t| substitute_type(&substitutions, t)),
            Rc::clone(record_name),
            fields
                .iter()
                .map(|(n, e)| (Rc::clone(n), substitute_expression(substitutions, e)))
                .collect(),
        ),

        Expression::Case(loc, expression, rules, result_type) => Expression::Case(
            Rc::clone(loc),
            substitute_expression(substitutions, expression),
            rules
                .iter()
                .map(|r| {
                    Rc::new(CaseRule {
                        loc_info: r.loc_info.clone(),
                        type_information: r
                            .type_information
                            .iter()
                            .map(|(v, t)| (Rc::clone(v), Rc::new(substitute(substitutions, t))))
                            .collect(),
                        case_rule: r.case_rule.clone(),
                        result_rule: substitute_expression(substitutions, &r.result_rule),
                    })
                })
                .collect(),
            result_type
                .as_ref()
                .map(|rt| substitute_type(substitutions, rt)),
        ),
        Expression::Call(loc, function_type, name, arguments) => Expression::Call(
            loc.clone(),
            function_type
                .as_ref()
                .map(|t| substitute_type(substitutions, t)),
            name.clone(),
            arguments
                .iter()
                .map(|a| substitute_expression(substitutions, a))
                .collect(),
        ),
        Expression::Variable(loc, name) => Expression::Variable(Rc::clone(loc), Rc::clone(name)),

        Expression::Negation(loc, e) => {
            Expression::Negation(Rc::clone(loc), substitute_expression(substitutions, e))
        }
        Expression::Minus(loc, e) => {
            Expression::Minus(Rc::clone(loc), substitute_expression(substitutions, e))
        }

        Expression::Times(loc, l, r) => Expression::Times(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Divide(loc, l, r) => Expression::Divide(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Modulo(loc, l, r) => Expression::Modulo(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Add(loc, l, r) => Expression::Add(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Subtract(loc, l, r) => Expression::Subtract(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::ShiftLeft(loc, l, r) => Expression::ShiftLeft(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::ShiftRight(loc, l, r) => Expression::ShiftRight(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Greater(loc, l, r) => Expression::Greater(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Greq(loc, l, r) => Expression::Greq(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Leq(loc, l, r) => Expression::Leq(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Lesser(loc, l, r) => Expression::Lesser(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Eq(loc, l, r) => Expression::Eq(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Neq(loc, l, r) => Expression::Neq(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::And(loc, l, r) => Expression::And(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),
        Expression::Or(loc, l, r) => Expression::Or(
            Rc::clone(loc),
            substitute_expression(substitutions, l),
            substitute_expression(substitutions, r),
        ),

        Expression::RecordFieldAccess(loc, record_type, record, expression, field) => {
            Expression::RecordFieldAccess(
                Rc::clone(loc),
                record_type
                    .as_ref()
                    .map(|t| substitute_type(substitutions, t)),
                Rc::clone(record),
                substitute_expression(substitutions, expression),
                Rc::clone(field),
            )
        }
        Expression::Lambda(loc, type_information, match_expression, expression) => {
            Expression::Lambda(
                Rc::clone(loc),
                type_information
                    .iter()
                    .map(|(v, t)| (Rc::clone(v), Rc::new(substitute(substitutions, t))))
                    .collect(),
                match_expression.clone(),
                substitute_expression(substitutions, expression),
            )
        }
    })
}
