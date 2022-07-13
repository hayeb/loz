use itertools::Either;

use crate::ast::ADTConstructor;
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
) -> InstantiatorState {
    let mut state = InstantiatorState::new(functions, adts, records, main_function);
    state.instantiate();
    state
}

pub struct InstantiatorState {
    input_function_definitions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    input_adt_definitions: HashMap<Rc<String>, Rc<ADTDefinition>>,
    input_record_definitions: HashMap<Rc<String>, Rc<RecordDefinition>>,

    function_queue: Vec<Rc<FunctionDefinition>>,
    type_queue: Vec<Either<Rc<RecordDefinition>, Rc<ADTDefinition>>>,

    pub functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    pub adts: HashMap<Rc<String>, Rc<ADTDefinition>>,
    pub records: HashMap<Rc<String>, Rc<RecordDefinition>>,
}

impl InstantiatorState {
    fn new(
        function_definitions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
        adt_definitions: HashMap<Rc<String>, Rc<ADTDefinition>>,
        record_definitions: HashMap<Rc<String>, Rc<RecordDefinition>>,
        main_function: &Rc<String>,
    ) -> Self {
        let main_function = (&function_definitions).get(main_function).cloned();

        InstantiatorState {
            input_function_definitions: function_definitions,
            input_adt_definitions: adt_definitions,
            input_record_definitions: record_definitions,
            function_queue: vec![main_function.unwrap()],
            type_queue: Vec::new(),

            functions: HashMap::new(),
            adts: HashMap::new(),
            records: HashMap::new(),
        }
    }

    fn add_function(&mut self, function: Rc<FunctionDefinition>) {
        println!("Adding function definition {:#?}", function);
        self.function_queue.push(Rc::clone(&function));
        self.functions
            .insert(Rc::clone(&function.name), Rc::clone(&function));
    }

    fn add_record(&mut self, record: Rc<RecordDefinition>) {
        println!("Adding record definition {:#?}", record);
        self.type_queue.push(Either::Left(Rc::clone(&record)));
        self.records
            .insert(Rc::clone(&record.name), Rc::clone(&record));
    }

    fn add_adt(&mut self, adt: Rc<ADTDefinition>) {
        println!("Adding adt definition {:#?}", adt);
        self.type_queue.push(Either::Right(Rc::clone(&adt)));
        self.adts.insert(Rc::clone(&adt.name), Rc::clone(&adt));
    }

    fn instantiate(&mut self) {
        while let Some(function_definition) = self.function_queue.pop() {
            let function_definition = self.resolve_function_definition(&function_definition);
            println!("Resolved function definition: {:#?}", function_definition);
            self.functions
                .insert(Rc::clone(&function_definition.name), function_definition);
        }

        while let Some(t) = self.type_queue.pop() {
            match t.borrow() {
                Either::Left(r) => {
                    let record_definition = self.resolve_record_definition(&r);
                    println!("Resolved record definition: {:#?}", record_definition);
                    self.records
                        .insert(Rc::clone(&record_definition.name), record_definition);
                }
                Either::Right(a) => {
                    let adt_definition = self.resolve_adt_definition(&a);
                    println!("Resolved adt definition: {:#?}", adt_definition);
                    self.adts
                        .insert(Rc::clone(&adt_definition.name), adt_definition);
                }
            }
        }
    }

    fn resolve_adt_definition(&mut self, adt_definition: &Rc<ADTDefinition>) -> Rc<ADTDefinition> {
        // Type variables should be replace with concrete types earlier
        let mut constructors = Vec::new();
        for constructor in adt_definition.constructors.iter() {
            let mut elements = Vec::new();
            for element in constructor.elements.iter() {
                let instantiated_element = self.resolve_type(element);
                elements.push(instantiated_element);
            }
            constructors.push(Rc::new(ADTConstructor {
                name: Rc::clone(&constructor.name),
                elements,
            }));
        }

        Rc::new(ADTDefinition {
            name: Rc::clone(&adt_definition.name.clone()),
            location: Rc::clone(&adt_definition.location.clone()),
            type_variables: vec![],
            constructors,
        })
    }

    fn resolve_record_definition(
        &mut self,
        record_definition: &Rc<RecordDefinition>,
    ) -> Rc<RecordDefinition> {
        // Type variables should be replace with concrete types earlier
        let mut fields = Vec::new();

        for (n, field_type) in record_definition.fields.iter() {
            let instantiated_field_type = self.resolve_type(field_type);
            fields.push((Rc::clone(n), instantiated_field_type));
        }

        Rc::new(RecordDefinition {
            name: Rc::clone(&record_definition.name),
            location: Rc::clone(&record_definition.location),
            type_variables: vec![],
            fields,
        })
    }

    fn resolve_type(&mut self, loz_type: &Rc<Type>) -> Rc<Type> {
        match loz_type.borrow() {
            Type::Bool => Rc::new(Type::Bool),
            Type::Char => Rc::new(Type::Char),
            Type::String => Rc::new(Type::String),
            Type::Int => Rc::new(Type::Int),
            Type::Float => Rc::new(Type::Float),
            Type::UserType(name, args) => {
                println!("Resolving type {:#?}", loz_type);

                if let Some(record_definition) = self.input_record_definitions.get(name).cloned() {
                    let type_hash = hash_type(&loz_type);
                    let instantiated_record_name =
                        Rc::new(format!("{}{}{}", &name, MONOMORPHIC_PREFIX, type_hash));

                    if self.records.contains_key(&instantiated_record_name) {
                        // We have encountered this definition before so we do not resolve a new definition
                        return Rc::clone(loz_type);
                    }

                    let record_type = Rc::new(Type::UserType(
                        Rc::clone(&name),
                        record_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    ));
                    let subs = unify(loz_type, &record_type).unwrap();
                    let resolved_record_definiton = Rc::new(RecordDefinition {
                        name: Rc::clone(&instantiated_record_name),
                        location: Rc::clone(&record_definition.location),
                        type_variables: Vec::new(),
                        fields: record_definition
                            .fields
                            .iter()
                            .map(|(v, t)| (Rc::clone(v), substitute_type(&subs, t)))
                            .collect(),
                    });

                    self.add_record(resolved_record_definiton);

                    Rc::new(Type::UserType(
                        Rc::clone(&instantiated_record_name),
                        record_definition
                            .type_variables
                            .iter()
                            .map(|v| substitute_type(&subs, &Rc::new(Type::Variable(Rc::clone(v)))))
                            .collect(),
                    ))
                } else if let Some(adt_definition) = self.input_adt_definitions.get(name).cloned() {
                    println!("resolve_type adt_definition {:#?}", &adt_definition.name);
                    let type_hash = hash_type(&loz_type);
                    let instantiated_adt_name =
                        Rc::new(format!("{}{}{}", &name, MONOMORPHIC_PREFIX, type_hash));

                    if self.adts.contains_key(&instantiated_adt_name) {
                        println!(
                            "resolve_type adt_definition {:#?} already exists",
                            &instantiated_adt_name
                        );
                        return Rc::new(Type::UserType(
                            instantiated_adt_name,
                            args.iter().cloned().collect(),
                        ));
                    }

                    let adt_type = Rc::new(Type::UserType(
                        Rc::clone(&name),
                        adt_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    ));
                    let subs = unify(loz_type, &adt_type).unwrap();

                    let resolved_adt_definition = Rc::new(ADTDefinition {
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
                    });
                    println!("Resolved adt definition: {:#?}", resolved_adt_definition);
                    self.add_adt(resolved_adt_definition);
                    Rc::new(Type::UserType(
                        Rc::clone(&instantiated_adt_name),
                        adt_definition
                            .type_variables
                            .iter()
                            .map(|v| substitute_type(&subs, &Rc::new(Type::Variable(Rc::clone(v)))))
                            .collect(),
                    ))
                } else {
                    panic!("User type")
                }
            }
            Type::Tuple(elements) => Rc::new(Type::Tuple(
                elements.iter().map(|e| self.resolve_type(e)).collect(),
            )),
            Type::List(e) => Rc::new(Type::List(self.resolve_type(e))),

            // TODO: Interesting..
            Type::Variable(_) => Rc::clone(&loz_type),

            Type::Function(arguments, result) => Rc::new(Type::Function(
                arguments.iter().map(|a| self.resolve_type(a)).collect(),
                self.resolve_type(result),
            )),
        }
    }

    fn resolve_function_definition(
        &mut self,
        function_definition: &Rc<FunctionDefinition>,
    ) -> Rc<FunctionDefinition> {
        let mut instantiated_bodies = Vec::new();
        for b in function_definition.function_bodies.iter() {
            instantiated_bodies.push(self.resolve_function_body(b));
        }

        let instantiated_type = self.resolve_type(
            &function_definition
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
        );
        println!(
            "resolve_function_definition instantiated_type {:#?}",
            instantiated_type
        );
        Rc::new(FunctionDefinition {
            location: Rc::clone(&function_definition.location),
            name: Rc::clone(&function_definition.name),
            function_type: Some(Rc::new(TypeScheme {
                bound_variables: HashSet::new(),
                enclosed_type: instantiated_type,
            })),
            function_bodies: instantiated_bodies,
        })
    }

    fn resolve_function_body(&mut self, function_body: &Rc<FunctionBody>) -> Rc<FunctionBody> {
        let mut instantiated_rules = Vec::new();
        let mut type_information = function_body.type_information.clone();
        for function_rule in function_body.rules.iter() {
            match function_rule.borrow() {
                FunctionRule::ConditionalRule(loc, condition, expression) => {
                    let instantiated_condition =
                        self.resolve_expression(condition, &type_information);
                    let instantiated_expression =
                        self.resolve_expression(expression, &type_information);

                    instantiated_rules.push(Rc::new(FunctionRule::ConditionalRule(
                        Rc::clone(loc),
                        instantiated_condition,
                        instantiated_expression,
                    )))
                }
                FunctionRule::ExpressionRule(loc, expression) => {
                    let instantiated_expression =
                        self.resolve_expression(expression, &type_information);
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
                    let instantiated_expression =
                        self.resolve_expression(expression, &type_information);
                    instantiated_rules.push(Rc::new(FunctionRule::LetRule(
                        Rc::clone(loc),
                        let_type_information.clone(),
                        Rc::clone(match_expression),
                        instantiated_expression,
                    )));
                }
            }
        }
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
        })
    }

    fn resolve_expression(
        &mut self,
        expression: &Rc<Expression>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> Rc<Expression> {
        match expression.borrow() {
            Expression::BoolLiteral(loc, b) => Rc::new(Expression::BoolLiteral(Rc::clone(loc), *b)),
            Expression::StringLiteral(loc, s) => {
                Rc::new(Expression::StringLiteral(Rc::clone(loc), Rc::clone(s)))
            }
            Expression::CharacterLiteral(loc, c) => {
                Rc::new(Expression::CharacterLiteral(Rc::clone(loc), *c))
            }
            Expression::IntegerLiteral(loc, i) => {
                Rc::new(Expression::IntegerLiteral(Rc::clone(loc), *i))
            }
            Expression::FloatLiteral(loc, f) => {
                Rc::new(Expression::FloatLiteral(Rc::clone(loc), *f))
            }

            Expression::TupleLiteral(loc, elements) => Rc::new(Expression::TupleLiteral(
                Rc::clone(loc),
                elements
                    .iter()
                    .map(|e| self.resolve_expression(e, type_information))
                    .collect(),
            )),
            Expression::EmptyListLiteral(loc, list_type) => Rc::new(Expression::EmptyListLiteral(
                Rc::clone(loc),
                list_type.clone(),
            )),
            Expression::ShorthandListLiteral(loc, list_type, elements) => {
                Rc::new(Expression::ShorthandListLiteral(
                    Rc::clone(loc),
                    list_type.clone(),
                    elements
                        .iter()
                        .map(|e| self.resolve_expression(e, type_information))
                        .collect(),
                ))
            }

            Expression::LonghandListLiteral(loc, list_type, h, t) => {
                Rc::new(Expression::LonghandListLiteral(
                    Rc::clone(loc),
                    list_type.clone(),
                    self.resolve_expression(h, type_information),
                    self.resolve_expression(t, type_information),
                ))
            }

            Expression::ADTTypeConstructor(loc, adt_type, constructor_name, arguments) => {
                let adt_type = adt_type.as_ref().expect("ADTTypeConstructor without type");

                let resolved_arguments = arguments
                    .iter()
                    .map(|fe| self.resolve_expression(fe, type_information))
                    .collect();

                let adt_definition_name = match adt_type.borrow() {
                    Type::UserType(name, _) => {
                        name.split(ADT_SEPARATOR).next().unwrap().to_string()
                    }
                    other => panic!("ADTTypeConstructor without UserType, found {:?}", other),
                };

                let adt_definition =
                    self.input_adt_definitions
                        .get(&adt_definition_name)
                        .expect(&format!(
                            "Could not find ADTDefinition with name {}",
                            &adt_definition_name
                        ));

                let type_hash = hash_type(&adt_type);
                let instantiated_adt_name = Rc::new(format!(
                    "{}{}{}",
                    adt_definition_name, MONOMORPHIC_PREFIX, type_hash
                ));

                if self.adts.contains_key(&instantiated_adt_name) {
                    return Rc::new(Expression::ADTTypeConstructor(
                        Rc::clone(loc),
                        Some(self.resolve_type(&adt_type)),
                        Rc::clone(constructor_name),
                        resolved_arguments,
                    ));
                }

                let subs = unify(
                    &adt_type,
                    &Rc::new(Type::UserType(
                        Rc::new(adt_definition_name),
                        adt_definition
                            .type_variables
                            .iter()
                            .map(|tv| Rc::new(Type::Variable(Rc::clone(tv))))
                            .collect(),
                    )),
                )
                .unwrap();

                let substituted_adt_definition =
                    substitute_adt_definition(&instantiated_adt_name, &adt_definition, &subs);
                self.add_adt(substituted_adt_definition);

                Rc::new(Expression::ADTTypeConstructor(
                    Rc::clone(loc),
                    Some(self.resolve_type(&adt_type)),
                    Rc::clone(constructor_name),
                    resolved_arguments,
                ))
            }

            Expression::Record(loc, record_type, record_name, field_expressions) => {
                let resolved_field_expressions = field_expressions
                    .iter()
                    .map(|(fname, fe)| {
                        (
                            Rc::clone(fname),
                            self.resolve_expression(fe, type_information),
                        )
                    })
                    .collect();

                let record_definition = self.input_record_definitions.get(record_name).unwrap();
                let type_hash = hash_type(record_type.as_ref().unwrap());
                let new_record_name = Rc::new(format!(
                    "{}{}{}",
                    record_name, MONOMORPHIC_PREFIX, type_hash
                ));

                if self.records.contains_key(&new_record_name) {
                    return Rc::new(Expression::Record(
                        Rc::clone(loc),
                        Some(self.resolve_type(record_type.as_ref().unwrap())),
                        Rc::clone(&new_record_name),
                        resolved_field_expressions,
                    ));
                }

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

                let substituted_record_definition =
                    substitute_record_definition(&new_record_name, &subs, record_definition);
                self.add_record(substituted_record_definition);

                let instantiated_record_type = self.resolve_type(record_type.as_ref().unwrap());

                Rc::new(Expression::Record(
                    Rc::clone(loc),
                    Some(instantiated_record_type),
                    Rc::clone(&new_record_name),
                    resolved_field_expressions,
                ))
            }
            Expression::Case(loc, expression, rules, result_type) => {
                let instantiated_expression = self.resolve_expression(expression, type_information);

                let mut instantiated_rules = Vec::new();
                for rule in rules {
                    let mut combined_type_information = HashMap::new();
                    combined_type_information.extend(type_information.clone());
                    combined_type_information.extend(rule.type_information.clone());

                    let instantiated_result_rule =
                        self.resolve_expression(&rule.result_rule, &combined_type_information);

                    instantiated_rules.push(Rc::new(CaseRule {
                        loc_info: Rc::clone(&rule.loc_info),
                        type_information: rule.type_information.clone(),
                        case_rule: rule.case_rule.clone(),
                        result_rule: instantiated_result_rule,
                    }))
                }

                Rc::new(Expression::Case(
                    Rc::clone(loc),
                    instantiated_expression,
                    instantiated_rules,
                    result_type.clone(),
                ))
            }
            Expression::Call(loc, function_type, function_name, arguments) => {
                let (new_call, arguments) = self.resolve_function_call(
                    function_name,
                    function_type.as_ref().unwrap(),
                    arguments,
                    type_information,
                );
                Rc::new(Expression::Call(
                    Rc::clone(loc),
                    function_type.clone(),
                    new_call,
                    arguments,
                ))
            }
            Expression::Variable(loc, name) => {
                Rc::new(Expression::Variable(Rc::clone(loc), Rc::clone(name)))
            }
            Expression::Negation(loc, expression) => Rc::new(Expression::Negation(
                Rc::clone(loc),
                self.resolve_expression(expression, type_information),
            )),
            Expression::Minus(loc, expression) => Rc::new(Expression::Minus(
                Rc::clone(loc),
                self.resolve_expression(expression, type_information),
            )),
            Expression::Times(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Times(Rc::clone(loc), l, r))
            }
            Expression::Divide(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Divide(Rc::clone(loc), l, r))
            }
            Expression::Modulo(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Modulo(Rc::clone(loc), l, r))
            }
            Expression::Add(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Add(Rc::clone(loc), l, r))
            }
            Expression::Subtract(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Subtract(Rc::clone(loc), l, r))
            }
            Expression::ShiftLeft(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::ShiftLeft(Rc::clone(loc), l, r))
            }
            Expression::ShiftRight(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::ShiftRight(Rc::clone(loc), l, r))
            }
            Expression::Greater(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Greater(Rc::clone(loc), l, r))
            }
            Expression::Greq(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Greq(Rc::clone(loc), l, r))
            }
            Expression::Leq(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Leq(Rc::clone(loc), l, r))
            }
            Expression::Lesser(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Lesser(Rc::clone(loc), l, r))
            }
            Expression::Eq(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Eq(Rc::clone(loc), l, r))
            }
            Expression::Neq(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Neq(Rc::clone(loc), l, r))
            }
            Expression::And(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::And(Rc::clone(loc), l, r))
            }
            Expression::Or(loc, l, r) => {
                let (l, r) = self.resolve_duo(l, r, type_information);
                Rc::new(Expression::Or(Rc::clone(loc), l, r))
            }
            Expression::RecordFieldAccess(
                loc,
                record_type,
                record_name,
                record_expression,
                field_expression,
            ) => {
                let instantiated_expression =
                    self.resolve_expression(record_expression, type_information);
                let new_record_name = format!(
                    "{}{}{}",
                    record_name,
                    MONOMORPHIC_PREFIX,
                    hash_type(record_type.as_ref().unwrap())
                );
                Rc::new(Expression::RecordFieldAccess(
                    Rc::clone(loc),
                    record_type.clone(),
                    Rc::new(new_record_name),
                    instantiated_expression,
                    Rc::clone(field_expression),
                ))
            }
            Expression::Lambda(_, _, _, _, _) => unreachable!(),
        }
    }

    fn resolve_function_call(
        &mut self,
        name: &Rc<String>,
        function_type: &Rc<Type>,
        arguments: &Vec<Rc<Expression>>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> (Rc<String>, Vec<Rc<Expression>>) {
        let function_definition = self.input_function_definitions.get(name).cloned().unwrap();
        let type_hash = hash_type(function_type);
        let call_name = Rc::new(format!("{}{}{}", name, MONOMORPHIC_PREFIX, type_hash));

        if self.functions.contains_key(&call_name) {
            // We already generated this function with this specific type.
            let resolved_arguments = arguments
                .iter()
                .map(|a| self.resolve_expression(a, type_information))
                .collect();
            return (call_name, resolved_arguments);
        }

        let subs = unify(
            &function_definition
                .function_type
                .as_ref()
                .unwrap()
                .enclosed_type,
            function_type,
        )
        .unwrap();

        self.add_function(substitute_function_definition(
            &self.input_adt_definitions,
            &self.input_record_definitions,
            &call_name,
            &subs,
            &function_definition,
        ));

        (
            Rc::clone(&call_name),
            arguments
                .iter()
                .map(|a| self.resolve_expression(a, type_information))
                .collect(),
        )
    }

    fn resolve_duo(
        &mut self,
        l: &Rc<Expression>,
        r: &Rc<Expression>,
        type_information: &HashMap<Rc<String>, Rc<TypeScheme>>,
    ) -> (Rc<Expression>, Rc<Expression>) {
        let instantiated_l = self.resolve_expression(l, type_information);
        let instantiated_r = self.resolve_expression(r, type_information);
        (instantiated_l, instantiated_r)
    }
}

fn substitute_adt_definition(
    instantiated_name: &Rc<String>,
    adt_definition: &Rc<ADTDefinition>,
    subs: &Substitutions,
) -> Rc<ADTDefinition> {
    Rc::new(ADTDefinition {
        name: Rc::clone(instantiated_name),
        location: Rc::clone(&adt_definition.location),
        type_variables: Vec::new(),
        constructors: adt_definition
            .constructors
            .iter()
            .map(|c| {
                Rc::new(ADTConstructor {
                    name: Rc::clone(&c.name),
                    elements: c
                        .elements
                        .iter()
                        .map(|e| substitute_type(subs, e))
                        .collect(),
                })
            })
            .collect(),
    })
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
                    name, MONOMORPHIC_PREFIX, type_hash, ADT_SEPARATOR, &constructor_name
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
        Expression::Lambda(_loc, _, _type_information, _match_expression, _expression) => {
            unreachable!()
        }
    })
}
