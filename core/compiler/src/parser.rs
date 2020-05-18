extern crate pest;

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::rc::Rc;

use pest::error::Error;
use pest::iterators::Pair;
use pest::prec_climber::*;
use pest::Parser;

use crate::ast::{
    ADTConstructor, ADTDefinition, CaseRule, ExportMember, Expression, FunctionBody,
    FunctionDefinition, FunctionRule, Import, Location, MatchExpression, Module, RecordDefinition,
    Type, TypeScheme,
};
use crate::parser::ParseError::PestError;
use crate::Expression::*;

use self::pest::iterators::Pairs;

#[derive(Parser)]
#[grammar = "loz.pest"]
pub struct LOZParser;

lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
        use Assoc::*;

        PrecClimber::new(vec![
            Operator::new(Rule::and, Left) | Operator::new(Rule::or, Left),
            Operator::new(Rule::eq, Left) | Operator::new(Rule::neq, Left),
            Operator::new(Rule::lesser, Left)
                | Operator::new(Rule::leq, Left)
                | Operator::new(Rule::greater, Left)
                | Operator::new(Rule::greq, Left),
            Operator::new(Rule::shift_left, Left) | Operator::new(Rule::shift_right, Left),
            Operator::new(Rule::add, Left) | Operator::new(Rule::substract, Left),
            Operator::new(Rule::times, Left)
                | Operator::new(Rule::divide, Left)
                | Operator::new(Rule::modulo, Left),
            Operator::new(Rule::record_field_access, Left),
        ])
    };
}

#[derive(Clone, Debug)]
pub enum ParseError {
    PestError(Error<Rule>),

    FunctionTypeWithoutBody(Rc<String>, Rc<Location>),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            PestError(pe) => write!(f, "{}", pe),
            ParseError::FunctionTypeWithoutBody(name, _loc) => write!(
                f,
                "Found type for function {}, but no bodies were found",
                name
            ),
        }
    }
}

pub fn parse(
    file_name: String,
    module_name: Rc<String>,
    input: String,
) -> Result<Module, ParseError> {
    let ast = LOZParser::parse(Rule::ast, &input)
        .map_err(|e| PestError(e))?
        .next()
        .unwrap();
    //println!("Raw AST: {:#?}", ast);
    let line_starts = build_line_start_cache(&input);
    to_module(ast, &module_name, &Rc::new(file_name), &line_starts)
}

fn build_line_start_cache(input: &str) -> Vec<usize> {
    let mut line_starts: Vec<usize> = Vec::new();
    let mut start_current_line = 0;
    let mut previous_character = '\0';
    for (i, c) in input.char_indices() {
        if previous_character == '\n' {
            start_current_line = i;
        }
        if c == '\n' {
            line_starts.push(start_current_line);
        }
        previous_character = c;
    }

    if previous_character != '\n' {
        line_starts.push(start_current_line);
    }

    line_starts
}

fn line_col_number(line_starts: &Vec<usize>, pos: usize) -> (usize, usize) {
    let mut previous_index = 0;
    let mut previous_start = 0;
    for (i, line_start) in line_starts.iter().enumerate() {
        if *line_start > pos {
            return (previous_index + 1, pos - previous_start + 1);
        }
        previous_index = i;
        previous_start = *line_start;
    }

    (previous_index + 1, pos - previous_start + 1)
}

fn contract_function_declarations(
    mut function_bodies: HashMap<Rc<String>, Vec<Rc<FunctionBody>>>,
    function_types: HashMap<Rc<String>, (Rc<Location>, Rc<TypeScheme>)>,
) -> Result<Vec<Rc<FunctionDefinition>>, ParseError> {
    let mut function_declarations = Vec::new();
    for (function_name, (location, function_scheme)) in function_types {
        match function_bodies.remove(&function_name) {
            None => {
                return Err(ParseError::FunctionTypeWithoutBody(
                    Rc::clone(&function_name),
                    location,
                ));
            }
            Some(bodies) => function_declarations.push(Rc::new(FunctionDefinition {
                location,
                name: Rc::clone(&function_name),
                function_type: Some(function_scheme),
                function_bodies: bodies,
            })),
        }
    }

    // Add the remaining functions that do not have a defined type.
    for (function_name, bodies) in function_bodies {
        function_declarations.push(Rc::new(FunctionDefinition {
            location: Rc::clone(&bodies.get(0).unwrap().location),
            name: function_name,
            function_type: None,
            function_bodies: bodies,
        }));
    }

    Ok(function_declarations)
}

fn to_module(
    pair: Pair<Rule>,
    module_name: &Rc<String>,
    file_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> Result<Module, ParseError> {
    match pair.as_rule() {
        Rule::ast => {
            let (adt_definitions, record_definitions, function_declarations, exports, imports) =
                to_declaration_block_elements(pair.into_inner(), module_name, line_starts)?;
            return Ok(Module {
                name: Rc::clone(module_name),
                file_name: Rc::clone(file_name),
                exported_members: exports,
                imports,
                function_definitions: function_declarations,
                adt_definitions,
                record_definitions,
            });
        }
        _ => unreachable!(),
    }
}

fn to_declaration_block_elements(
    pairs: Pairs<Rule>,
    module_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> Result<
    (
        Vec<Rc<ADTDefinition>>,
        Vec<Rc<RecordDefinition>>,
        Vec<Rc<FunctionDefinition>>,
        HashSet<ExportMember>,
        Vec<Rc<Import>>,
    ),
    ParseError,
> {
    let mut function_types = HashMap::new();
    let mut function_bodies: HashMap<Rc<String>, Vec<Rc<FunctionBody>>> = HashMap::new();

    let mut adt_definitions = Vec::new();
    let mut record_definitions = Vec::new();

    let mut module_exports = HashSet::<String>::new();
    let mut module_imports = Vec::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::type_definition => {
                let child = pair.into_inner().next().unwrap();
                match child.as_rule() {
                    Rule::adt_definition => {
                        adt_definitions.push(Rc::new(to_adt_type(child, module_name, line_starts)))
                    }
                    Rule::record_definition => record_definitions.push(Rc::new(to_record_type(
                        child,
                        module_name,
                        line_starts,
                    ))),
                    r => unreachable!("{:?}", r),
                }
            }
            Rule::function_body => {
                let fb = Rc::new(to_function_body(module_name, pair, line_starts)?);
                match function_bodies.get_mut(&fb.name) {
                    None => {
                        function_bodies.insert(Rc::clone(&fb.name), vec![fb]);
                    }
                    Some(bodies) => bodies.push(fb),
                };
            }
            Rule::function_type_definition => {
                let (line, col) = line_col_number(line_starts, pair.as_span().start());
                let mut elements = pair.into_inner();
                let function_name = Rc::new(elements.next().unwrap().as_str().to_string());
                let function_type = to_type(elements.next().unwrap());
                function_types.insert(
                    Rc::clone(&function_name),
                    (
                        Rc::new(Location {
                            module: Rc::clone(module_name),
                            function: Rc::clone(&function_name),
                            line,
                            col,
                        }),
                        Rc::new(TypeScheme {
                            bound_variables: function_type.collect_free_type_variables(),
                            enclosed_type: Rc::new(function_type),
                        }),
                    ),
                );
            }
            Rule::module_export => {
                module_exports.insert(pair.into_inner().next().unwrap().as_str().to_string());
            }
            Rule::module_import => {
                let (line, col) = line_col_number(line_starts, pair.as_span().start());
                let module_import = pair.into_inner().next().unwrap();
                match module_import.as_rule() {
                    Rule::module_import_full => {
                        let mut members = module_import.into_inner();
                        let defined_module_name =
                            Rc::new(members.next().unwrap().as_str().to_string());
                        module_imports.push(Rc::new(Import::ImportModule(
                            Rc::new(Location {
                                module: Rc::clone(module_name),
                                function: Rc::new("".to_owned()),
                                line,
                                col,
                            }),
                            defined_module_name,
                            members.next().map(|r| Rc::new(r.as_str().to_string())),
                        )))
                    }
                    Rule::module_import_members => {
                        let mut members = module_import.into_inner();
                        let defined_module_name =
                            Rc::new(members.next().unwrap().as_str().to_string());
                        let imported_members = members
                            .into_iter()
                            .map(|m| Rc::new(m.as_str().to_string()))
                            .collect();
                        module_imports.push(Rc::new(Import::ImportMembers(
                            Rc::new(Location {
                                module: Rc::clone(module_name),
                                function: Rc::new("".to_owned()),
                                line,
                                col,
                            }),
                            defined_module_name,
                            imported_members,
                        )))
                    }
                    _ => unreachable!("Module import: {:?}", module_import),
                }
            }
            _ => continue,
        }
    }
    Ok((
        adt_definitions,
        record_definitions,
        contract_function_declarations(function_bodies, function_types)?,
        module_exports,
        module_imports,
    ))
}

fn to_adt_type(
    adt_definition: Pair<Rule>,
    module_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> ADTDefinition {
    let (line, col) = line_col_number(line_starts, adt_definition.as_span().start());
    let mut elements = adt_definition.into_inner();
    let name = Rc::new(elements.next().unwrap().as_str().to_string());
    let type_variables = elements
        .next()
        .unwrap()
        .into_inner()
        .map(|tv| Rc::new(tv.as_str().to_string()))
        .collect();

    let constructors = elements
        .next()
        .unwrap()
        .into_inner()
        .map(|alternative_rule| {
            let mut alternative_elements = alternative_rule.into_inner();
            let alternative_name =
                Rc::new(alternative_elements.next().unwrap().as_str().to_string());
            let alternative_elements = alternative_elements.map(to_type).map(Rc::new).collect();
            (
                Rc::clone(&alternative_name),
                Rc::new(ADTConstructor {
                    name: Rc::clone(&alternative_name),
                    elements: alternative_elements,
                }),
            )
        })
        .collect();

    ADTDefinition {
        name: Rc::clone(&name),
        location: Rc::new(Location {
            module: Rc::clone(module_name),
            function: Rc::clone(&name),
            line,
            col,
        }),
        constructors,
        type_variables,
    }
}

fn to_record_type(
    record_definition: Pair<Rule>,
    module_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> RecordDefinition {
    let (line, col) = line_col_number(line_starts, record_definition.as_span().start());
    let mut elements = record_definition.into_inner();
    let name = Rc::new(elements.next().unwrap().as_str().to_string());
    let type_variables = elements
        .next()
        .unwrap()
        .into_inner()
        .map(|tv| Rc::new(tv.as_str().to_string()))
        .collect();
    let fields = elements
        .next()
        .unwrap()
        .into_inner()
        .map(|field_rule| {
            let mut field_elements = field_rule.into_inner();
            let field_name = field_elements.next().unwrap().as_str().to_string();
            let field_type = to_type(field_elements.next().unwrap());
            (Rc::new(field_name), Rc::new(field_type))
        })
        .collect();

    RecordDefinition {
        name: Rc::clone(&name),
        location: Rc::new(Location {
            module: Rc::clone(module_name),
            function: Rc::clone(&name),
            line,
            col,
        }),
        fields,
        type_variables,
    }
}

fn to_function_body(
    module_name: &Rc<String>,
    pair: Pair<Rule>,
    line_starts: &Vec<usize>,
) -> Result<FunctionBody, ParseError> {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());

    let mut parents = pair.into_inner();
    let mut function_header_elements = parents.next().unwrap().into_inner();
    let function_name = Rc::new(
        function_header_elements
            .next()
            .unwrap()
            .as_str()
            .to_string(),
    );

    let mut match_expressions = Vec::new();
    for r in function_header_elements {
        match_expressions.push(Rc::new(to_match_expression(
            r.into_inner().next().unwrap(),
            module_name,
            &function_name,
            line_starts,
        )));
    }

    let mut rules = Vec::new();
    let mut local_function_definitions = Vec::new();
    let mut local_adt_definitions = Vec::new();
    let mut local_record_definitions = Vec::new();
    for r in parents {
        match r.as_rule() {
            // Guaranteed to only occur once.
            Rule::local_definitions => {
                let (adt_definitions, record_definitions, function_definitions, _, _) =
                    to_declaration_block_elements(r.into_inner(), module_name, line_starts)?;
                local_function_definitions = function_definitions;
                local_adt_definitions = adt_definitions;
                local_record_definitions = record_definitions;
            }
            _ => rules.push(Rc::new(to_function_rule(
                r,
                module_name,
                &function_name,
                line_starts,
            ))),
        }
    }

    let location = Rc::new(Location {
        module: Rc::clone(module_name),
        function: Rc::clone(&function_name),
        line,
        col,
    });
    Ok(FunctionBody {
        name: Rc::clone(&function_name),
        location: Rc::clone(&location),
        match_expressions,
        rules,
        local_function_definitions,
        local_adt_definitions,
        local_record_definitions,
    })
}

fn to_expression(
    expression: Pair<Rule>,
    module_name: &Rc<String>,
    function_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> Expression {
    PREC_CLIMBER.climb(
        expression.into_inner(),
        |pair: Pair<Rule>| match pair.as_rule() {
            Rule::term => to_term(pair, module_name, function_name, line_starts),
            _ => unreachable!("prec_climber reached: {:?}", pair),
        },
        |lhs: Expression, op: Pair<Rule>, rhs: Expression| {
            let (line, col) = line_col_number(line_starts, op.as_span().start());
            let loc_info = Rc::new(Location {
                module: Rc::clone(module_name),
                function: Rc::clone(function_name),
                line,
                col,
            });
            match op.as_rule() {
                Rule::times => Times(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::divide => Divide(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::modulo => Modulo(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::add => Add(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::substract => Subtract(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::shift_left => ShiftLeft(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::shift_right => ShiftRight(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::lesser => Lesser(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::leq => Leq(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::greater => Greater(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::greq => Greq(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::eq => Eq(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::neq => Neq(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::and => And(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::or => Or(loc_info, Rc::new(lhs), Rc::new(rhs)),
                Rule::record_field_access => {
                    RecordFieldAccess(loc_info, Rc::new(lhs), Rc::new(rhs))
                }
                r => panic!("Prec climber unhandled rule: {:#?}", r),
            }
        },
    )
}

fn to_term(
    pair: Pair<Rule>,
    module_name: &Rc<String>,
    function_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> Expression {
    let (line, col) = line_col_number(line_starts, pair.as_span().start());
    let loc_info = Rc::new(Location {
        module: Rc::clone(module_name),
        function: Rc::clone(function_name),
        line,
        col,
    });
    let sub = pair.into_inner().next().unwrap();
    match sub.as_rule() {
        Rule::bool_literal => BoolLiteral(loc_info, sub.as_str().parse::<bool>().unwrap()),
        Rule::string_literal => StringLiteral(
            loc_info,
            Rc::new(sub.into_inner().next().unwrap().as_str().to_string()),
        ),
        Rule::char_literal => {
            CharacterLiteral(loc_info, sub.as_str().to_string().chars().nth(1).unwrap())
        }
        Rule::number => IntegerLiteral(loc_info, sub.as_str().parse::<isize>().unwrap()),
        Rule::float => FloatLiteral(loc_info, sub.as_str().parse::<f64>().unwrap()),
        Rule::call => {
            let mut subs = sub.into_inner();
            let function = subs.next().unwrap().as_str();
            let arguments = subs
                .map(|a| Rc::new(to_term(a, module_name, function_name, line_starts)))
                .collect();
            Call(loc_info, Rc::new(function.to_string()), arguments)
        }
        Rule::qualifiable_identifier => Variable(loc_info, Rc::new(sub.as_str().to_string())),
        Rule::subexpr => to_expression(
            sub.into_inner().next().unwrap(),
            module_name,
            function_name,
            line_starts,
        ),
        Rule::negation => Negation(
            loc_info,
            Rc::new(to_expression(
                sub.into_inner().next().unwrap(),
                module_name,
                function_name,
                line_starts,
            )),
        ),
        Rule::minus => Minus(
            loc_info,
            Rc::new(to_expression(
                sub.into_inner().next().unwrap(),
                module_name,
                function_name,
                line_starts,
            )),
        ),
        Rule::tuple_literal => TupleLiteral(
            loc_info,
            sub.into_inner()
                .map(|te| Rc::new(to_expression(te, module_name, function_name, line_starts)))
                .collect(),
        ),
        Rule::list_empty => EmptyListLiteral(loc_info),
        Rule::list_singleton => ShorthandListLiteral(
            loc_info,
            vec![Rc::new(to_expression(
                sub.into_inner().nth(0).unwrap(),
                module_name,
                function_name,
                line_starts,
            ))],
        ),
        Rule::list_shorthand => ShorthandListLiteral(
            loc_info,
            sub.into_inner()
                .map(|te| Rc::new(to_expression(te, module_name, function_name, line_starts)))
                .collect(),
        ),
        Rule::list_longhand => {
            let mut children = sub.into_inner();
            let head = children.next().unwrap();
            let tail = children.next().unwrap();
            LonghandListLiteral(
                loc_info,
                Rc::new(to_expression(head, module_name, function_name, line_starts)),
                Rc::new(to_expression(tail, module_name, function_name, line_starts)),
            )
        }
        Rule::case_expression => {
            let mut children = sub.into_inner();
            let expression = to_term(
                children.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            let rules = children
                .map(|match_rule| {
                    let (line, col) = line_col_number(line_starts, match_rule.as_span().start());
                    let location = Rc::new(Location {
                        module: Rc::clone(module_name),
                        function: Rc::clone(function_name),
                        line,
                        col,
                    });
                    let mut scs = match_rule.into_inner();
                    let case_rule = to_match_expression(
                        scs.next().unwrap().into_inner().next().unwrap(),
                        module_name,
                        function_name,
                        line_starts,
                    );
                    let result_rule =
                        to_expression(scs.next().unwrap(), module_name, function_name, line_starts);
                    Rc::new(CaseRule {
                        loc_info: location,
                        case_rule: Rc::new(case_rule),
                        result_rule: Rc::new(result_rule),
                    })
                })
                .collect();
            Case(loc_info, Rc::new(expression), rules)
        }
        Rule::adt_term => {
            let mut elements = sub.into_inner();
            let alternative = elements.next().unwrap().as_str().to_string();
            let arguments = elements
                .map(|e| Rc::new(to_expression(e, module_name, function_name, line_starts)))
                .collect();
            ADTTypeConstructor(loc_info, Rc::new(alternative), arguments)
        }

        Rule::record_term => {
            let mut record_term_elements = sub.into_inner();
            let record_name = record_term_elements.next().unwrap().as_str().to_string();
            let field_expressions = record_term_elements
                .map(|e| {
                    let mut field_expression_elements = e.into_inner();
                    let identifier = field_expression_elements
                        .next()
                        .unwrap()
                        .as_str()
                        .to_string();
                    let expression = to_expression(
                        field_expression_elements.next().unwrap(),
                        module_name,
                        function_name,
                        line_starts,
                    );
                    (Rc::new(identifier), Rc::new(expression))
                })
                .collect();

            Record(loc_info, Rc::new(record_name), field_expressions)
        }
        Rule::lambda => {
            let mut elements = sub.into_inner();
            let argument_match_expressions: Vec<Rc<MatchExpression>> = elements
                .next()
                .unwrap()
                .into_inner()
                .map(|me| {
                    Rc::new(to_match_expression(
                        me.into_inner().next().unwrap(),
                        module_name,
                        function_name,
                        line_starts,
                    ))
                })
                .collect();
            let body = to_expression(
                elements.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            Lambda(loc_info, argument_match_expressions, Rc::new(body))
        }

        r => panic!("Reached term {:#?}", r),
    }
}

fn to_function_rule(
    pair: Pair<Rule>,
    module_name: &Rc<String>,
    function_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> FunctionRule {
    match pair.as_rule() {
        Rule::function_conditional_rule => {
            let pair = pair.into_inner().next().unwrap();
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            let mut rules = pair.into_inner();
            let left = to_expression(
                rules.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            let right = to_expression(
                rules.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            FunctionRule::ConditionalRule(
                Rc::new(Location {
                    module: Rc::clone(module_name),
                    function: Rc::clone(function_name),
                    line,
                    col,
                }),
                Rc::new(left),
                Rc::new(right),
            )
        }
        Rule::function_expression_rule => {
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            FunctionRule::ExpressionRule(
                Rc::new(Location {
                    module: Rc::clone(module_name),
                    function: Rc::clone(function_name),
                    line,
                    col,
                }),
                Rc::new(to_expression(
                    pair.into_inner().next().unwrap(),
                    module_name,
                    function_name,
                    line_starts,
                )),
            )
        }
        Rule::function_let_rule => {
            let (line, col) = line_col_number(line_starts, pair.as_span().start());
            let mut inner_rules = pair.into_inner();
            let identifier = to_match_expression(
                inner_rules.next().unwrap().into_inner().next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            let expression = to_expression(
                inner_rules.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            FunctionRule::LetRule(
                Rc::new(Location {
                    module: Rc::clone(module_name),
                    function: Rc::clone(function_name),
                    line,
                    col,
                }),
                Rc::new(identifier),
                Rc::new(expression),
            )
        }
        r => unreachable!("to_function_rule reached: {:#?}", r),
    }
}

fn to_match_expression(
    match_expression: Pair<Rule>,
    module_name: &Rc<String>,
    function_name: &Rc<String>,
    line_starts: &Vec<usize>,
) -> MatchExpression {
    let (line, col) = line_col_number(line_starts, match_expression.as_span().start());
    let loc_info = Rc::new(Location {
        module: Rc::clone(module_name),
        function: Rc::clone(function_name),
        line,
        col,
    });
    match match_expression.as_rule() {
        Rule::identifier => {
            MatchExpression::Identifier(loc_info, Rc::new(match_expression.as_str().to_string()))
        }
        Rule::match_wildcard => MatchExpression::Wildcard(loc_info),
        Rule::tuple_match => MatchExpression::Tuple(
            Rc::clone(&loc_info),
            match_expression
                .into_inner()
                .map(|e| {
                    Rc::new(to_match_expression(
                        e,
                        module_name,
                        function_name,
                        line_starts,
                    ))
                })
                .collect(),
        ),
        Rule::sub_match => to_match_expression(
            match_expression.into_inner().next().unwrap(),
            module_name,
            function_name,
            line_starts,
        ),
        Rule::list_match_empty => MatchExpression::ShorthandList(loc_info, vec![]),
        Rule::list_match_singleton => MatchExpression::ShorthandList(
            Rc::clone(&loc_info),
            vec![Rc::new(to_match_expression(
                match_expression.into_inner().next().unwrap(),
                module_name,
                function_name,
                line_starts,
            ))],
        ),
        Rule::list_match_shorthand => MatchExpression::ShorthandList(
            Rc::clone(&loc_info),
            match_expression
                .into_inner()
                .map(|e| {
                    Rc::new(to_match_expression(
                        e,
                        module_name,
                        function_name,
                        line_starts,
                    ))
                })
                .collect(),
        ),
        Rule::list_match_longhand => {
            let mut inner = match_expression.into_inner();
            let head = to_match_expression(
                inner.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            let tail = to_match_expression(
                inner.next().unwrap(),
                module_name,
                function_name,
                line_starts,
            );
            MatchExpression::LonghandList(loc_info, Rc::new(head), Rc::new(tail))
        }
        Rule::number => MatchExpression::IntLiteral(
            Rc::clone(&loc_info),
            match_expression.as_str().parse::<isize>().unwrap(),
        ),
        Rule::char_literal => MatchExpression::CharLiteral(
            Rc::clone(&loc_info),
            match_expression
                .as_str()
                .to_string()
                .chars()
                .nth(1)
                .unwrap(),
        ),
        Rule::string_literal => MatchExpression::StringLiteral(
            Rc::clone(&loc_info),
            Rc::new(
                match_expression
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_str()
                    .to_string(),
            ),
        ),
        Rule::bool_literal => MatchExpression::BoolLiteral(
            Rc::clone(&loc_info),
            match_expression.as_str().parse::<bool>().unwrap(),
        ),
        Rule::adt_match => {
            let mut elements = match_expression.into_inner();
            let alternative_name = elements.next().unwrap().as_str().to_string();

            MatchExpression::ADT(
                Rc::clone(&loc_info),
                Rc::new(alternative_name),
                elements
                    .map(|m| {
                        Rc::new(to_match_expression(
                            m,
                            module_name,
                            function_name,
                            line_starts,
                        ))
                    })
                    .collect(),
            )
        }

        Rule::record_match => {
            let mut children = match_expression.into_inner();
            let name = children.next().unwrap().as_str().to_string();
            MatchExpression::Record(
                Rc::clone(&loc_info),
                Rc::new(name),
                children.map(|e| Rc::new(e.as_str().to_string())).collect(),
            )
        }

        r => unreachable!("Reached to_match_expression with: {:?}", r),
    }
}

fn to_type(pair: Pair<Rule>) -> Type {
    match pair.as_rule() {
        Rule::bool_type => Type::Bool,
        Rule::string_type => Type::String,
        Rule::int_type => Type::Int,
        Rule::char_type => Type::Char,
        Rule::float_type => Type::Float,
        Rule::tuple_type => Type::Tuple(pair.into_inner().map(|r| Rc::new(to_type(r))).collect()),
        Rule::list_type => Type::List(Rc::new(to_type(pair.into_inner().next().unwrap()))),
        Rule::custom_type_single => {
            let name = pair.into_inner().next().unwrap().as_str().to_string();
            Type::UserType(Rc::new(name), vec![])
        }
        Rule::custom_type => {
            let mut elements = pair.into_inner();
            let name = elements.next().unwrap().as_str().to_string();

            let mut type_arguments = Vec::new();
            while let Some(e) = elements.next() {
                type_arguments.push(Rc::new(to_type(e)))
            }
            Type::UserType(Rc::new(name), type_arguments)
        }
        Rule::type_variable => Type::Variable(Rc::new(pair.as_str().to_string())),
        Rule::function_type => {
            let types: Vec<Rc<Type>> = pair.into_inner().map(|t| Rc::new(to_type(t))).collect();

            let (result_type, arguments) = types.split_last().unwrap();
            Type::Function(
                arguments.into_iter().cloned().collect(),
                Rc::clone(result_type),
            )
        }
        t => unreachable!("Unhandled type: {:?}: {:#?}", t, pair),
    }
}
