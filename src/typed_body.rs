//! Typed, source-located body arena. Dense IDs survive copying and lowering;
//! checked type/span capture still bridges through the borrowed legacy AST.
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emission_order_is_reconstructed_from_stable_nodes() {
        let source = "(#fn main () #u64
          (#let-mut total #u64 0u64)
          (#for (#let-mut i #u64 0u64) (#u64.< i 3u64)
            (#set i (#u64.+.wrap i 1u64))
            (#set total (#u64.+.wrap total i)))
          (#return (#if true total 0u64)))";
        let first = crate::parse_program(source).unwrap();
        let second = crate::parse_program(source).unwrap();
        let checked_first = crate::CheckedProgram::validate(&first).unwrap();
        let checked_second = crate::CheckedProgram::validate(&second).unwrap();
        let body_first = &checked_first.declarations().bodies["main"];
        let body_second = &checked_second.declarations().bodies["main"];
        assert_eq!(body_first.emission_nodes, body_first.emission_node_order());
        assert_eq!(body_first.emission_nodes, body_second.emission_nodes);
        let function = first
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        body_first.emission_types(function).unwrap();
    }

    #[test]
    fn emission_metadata_retains_resolved_field_declaration_ids() {
        let source = "(#struct Pair ((left #u64) (right #u64)))
          (#fn read ((pair Pair)) #u64 (#return (#get pair left)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["read"];
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "read" => Some(function),
                _ => None,
            })
            .unwrap();
        let field = declarations
            .field_id(&Type::Named("Pair".into()), "left")
            .unwrap();
        let declaration = DeclarationId::Field(field);
        let node = body
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::Declaration(id) if id == declaration))
            .unwrap();
        let expression_id = node.expression_id.unwrap();

        let emission = body.emission_types(function).unwrap();
        assert_eq!(emission.aggregate_names[&field.owner], "Pair");
        assert_eq!(
            emission.by_id[&expression_id].declaration,
            Some(declaration)
        );
        let span = emission.by_id[&expression_id].span.unwrap();
        assert_eq!(&source[span.start..span.end], "left");
    }

    #[test]
    fn emission_metadata_retains_resolved_global_declaration_ids() {
        let source = "(#const Answer #u64 42u64)
          (#fn main () #u64 (#return Answer))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let global = declarations.global_id("Answer").unwrap();
        let declaration = DeclarationId::Global(global);
        let node = body
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::Declaration(id) if id == declaration))
            .unwrap();
        let expression_id = node.expression_id.unwrap();

        let emission = body.emission_types(function).unwrap();
        assert_eq!(emission.global_names[&global], "Answer");
        assert_eq!(
            emission.by_id[&expression_id].declaration,
            Some(declaration)
        );
    }

    #[test]
    fn emission_metadata_retains_enum_variant_owner_and_identity() {
        let source = "(#enum Maybe ((Some #u64) None))
          (#fn main () Maybe (#return None))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let variant = declarations
            .variant_id(&Type::Named("Maybe".into()), "None")
            .unwrap();
        let declaration = DeclarationId::Variant(variant);
        let node = body
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::Declaration(id) if id == declaration))
            .unwrap();
        let expression_id = node.expression_id.unwrap();

        let emission = body.emission_types(function).unwrap();
        assert_eq!(emission.aggregate_names[&variant.owner], "Maybe");
        assert_eq!(
            emission.by_id[&expression_id].declaration,
            Some(declaration)
        );
    }

    #[test]
    fn match_arms_use_the_checked_scrutinee_node_type() {
        let source = "(#enum Choice ((Value #u64) Empty))
          (#fn main () #u64
            (#let choice Choice (Value 42u64))
            (#return (#match choice
              (#case (Value payload) payload)
              (#case Empty 0u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let scrutinee = body
            .nodes
            .iter()
            .find_map(|node| match node.kind {
                NodeKind::Match { value, .. } => Some(value),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            body.nodes[scrutinee.0].ty,
            Some(Type::Named("Choice".into()))
        );
        assert!(crate::generate_assembly(&program).is_ok());
    }

    #[test]
    fn numeric_opcodes_round_trip_without_free_form_operation_names() {
        for spelling in [
            "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<", "<=", ">", ">=", "==", "!=",
            "!", "&&", "||",
        ] {
            let name = format!("u64.{spelling}");
            let operation = NumericOperation::parse(&name).unwrap();
            assert_eq!(operation.operand_type, Type::U64);
            assert_eq!(operation.operation.as_str(), spelling);
            assert_eq!(operation.spelling(), name);
        }
        for (name, ty, overflow) in [
            ("i8.+.wrap", Type::I8, Overflow::Wrap),
            ("u128.*.saturate", Type::U128, Overflow::Saturate),
            ("f32./", Type::F32, Overflow::NotApplicable),
        ] {
            let operation = NumericOperation::parse(name).unwrap();
            assert_eq!(operation.operand_type, ty);
            assert_eq!(operation.overflow, overflow);
            assert_eq!(operation.spelling(), name);
        }
        assert!(NumericOperation::parse("u64.unknown").is_none());
    }

    #[test]
    fn borrowed_places_retain_binding_identity_and_checked_type() {
        let source = "(#fn main () #u64
          (#let u64-value #u64 42u64)
          (#let view (#ref #u64) (#borrow u64-value))
          (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let owner = body
            .nodes
            .iter()
            .find(|node| {
                matches!(&node.kind,
            NodeKind::Symbol { name, binding: Some(_) } if name == "u64-value")
            })
            .unwrap();
        assert_eq!(owner.ty, Some(Type::U64));
        let NodeKind::Symbol {
            binding: Some(id), ..
        } = owner.kind
        else {
            unreachable!()
        };
        assert_eq!(body.bindings[id.0].name, "u64-value");
        assert_eq!(body.bindings.len(), 2, "syntax must not create bindings");
    }

    #[test]
    fn typed_bindings_retain_the_source_identifier_span() {
        let source = "(#struct Resource ((value #u64)))
          (#linear Resource)
          (#fn main () #u64
            (#let resource Resource (#struct-literal Resource ((value 1u64))))
            (#forget resource)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let binding = checked.declarations().bodies["main"]
            .bindings
            .iter()
            .find(|binding| binding.name == "resource")
            .unwrap();
        let span = binding
            .span
            .expect("typed local keeps its declaration span");
        assert_eq!(&source[span.start..span.end], "resource");
    }

    #[test]
    fn typed_parameters_retain_the_source_identifier_span() {
        let source = "(#struct Resource ((value #u64)))
          (#linear Resource)
          (#fn consume ((token Resource)) ()
            (#forget token)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let binding = &checked.declarations().bodies["consume"].bindings[0];
        let span = binding
            .span
            .expect("typed parameter keeps its declaration span");
        assert_eq!(&source[span.start..span.end], "token");
    }

    #[test]
    fn nested_block_bindings_retain_their_source_identifier_spans() {
        let source = "(#fn main () #u64
          (#block (#let nested #u64 21u64) nested)
          (#if true
            (#block (#let branch #u64 22u64) branch)
            0u64)
          (#while false
            (#block (#let repeated #u64 23u64) repeated))
          (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let bindings = &checked.declarations().bodies["main"].bindings;
        for name in ["nested", "branch", "repeated"] {
            let binding = bindings
                .iter()
                .find(|binding| binding.name == name)
                .unwrap_or_else(|| panic!("missing typed binding {name}"));
            let span = binding
                .span
                .unwrap_or_else(|| panic!("missing source span for {name}"));
            assert_eq!(&source[span.start..span.end], name);
        }
    }

    #[test]
    fn nested_initializer_and_distinct_binding_spans_follow_lowering_order() {
        let source = "(#fn main () #u64
          (#let item #u64 1u64)
          (#block (#let nested-item #u64 2u64) nested-item)
          (#let outer #u64 (#block (#let inner #u64 3u64) inner))
          (#return (#u64.+.wrap item outer)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let bindings = &checked.declarations().bodies["main"].bindings;
        for name in ["item", "nested-item", "inner", "outer"] {
            let binding = bindings
                .iter()
                .find(|binding| binding.name == name)
                .unwrap();
            let span = binding.span.expect("nested initializer source span");
            assert_eq!(&source[span.start..span.end], name);
        }
    }

    #[test]
    fn colliding_calls_keep_declaration_identity_and_reject_builtin_head_drift() {
        let source = "(#fn u64.+.wrap ((left #u64) (right #u64)) #u64 (#return left))
          (#fn main () #u64 (#return (#u64.+.wrap
            (#call u64.+.wrap (: right 99u64 : left 42u64)) 0u64)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let target = declarations.function_id("u64.+.wrap").unwrap();
        let call = body
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                NodeKind::Form {
                    head,
                    children,
                    callee: Some(id),
                    numeric,
                    ..
                } => {
                    assert_eq!(*id, target);
                    assert_eq!(head, "call");
                    assert!(numeric.is_none());
                    assert!(matches!(body.nodes[children[0].0].kind,
                    NodeKind::Declaration(DeclarationId::Function(id)) if id == target));
                    Some(children)
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(call.len(), 3);
        assert!(body.nodes.iter().any(|node| matches!(
            &node.kind,
            NodeKind::Form {
                callee: None,
                numeric: Some(_),
                ..
            }
        )));
        let mut function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => {
                    Some(function.clone())
                }
                _ => None,
            })
            .unwrap();
        body.emission_types(&function).unwrap();
        let Statement::Return(Some(Expr::List(outer))) = &mut function.body[0] else {
            panic!()
        };
        let Expr::List(inner) = &mut outer[1] else {
            panic!()
        };
        inner[0] = Expr::Symbol("u64.+.wrap".into());
        assert!(body
            .emission_types(&function)
            .err()
            .unwrap()
            .contains("shape"));
    }

    #[test]
    fn nodes_keep_contextual_types_numeric_modes_and_reordered_call_spans() {
        let source =
            "(#fn add ((left #u32) (right #u32)) #u32 (#return (#u32.+.saturate left right)))
          (#fn main () #u32 (#let x #u32 40) (#return (#call add (: right 2 : left x))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let literal = body
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::Literal(Expr::Integer(40))))
            .unwrap();
        assert_eq!(literal.ty, Some(Type::U32));
        let call = body
            .nodes
            .iter()
            .find(|node| {
                matches!(
                    &node.kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                )
            })
            .unwrap();
        let NodeKind::Form {
            children,
            argument_source_order,
            ..
        } = &call.kind
        else {
            unreachable!()
        };
        assert_eq!(argument_source_order.as_deref(), Some(&[1, 0][..]));
        let left = body.nodes[children[1].0].span.unwrap();
        let right = body.nodes[children[2].0].span.unwrap();
        assert_eq!(&source[left.start..left.end], "x");
        assert_eq!(&source[right.start..right.end], "2");
        assert!(right.start < left.start);
        let add = &checked.declarations().bodies["add"];
        assert!(add.nodes.iter().any(|node| matches!(
            &node.kind,
            NodeKind::Form {
                numeric: Some(NumericOperation {
                    overflow: Overflow::Saturate,
                    operand_type: Type::U32,
                    ..
                }),
                ..
            }
        )));
        let independent = crate::parse_program(source).unwrap();
        let other = crate::CheckedProgram::validate(&independent).unwrap();
        assert_eq!(checked.dump_typed_ir(), other.dump_typed_ir());
    }

    #[test]
    fn generated_function_body_nodes_retain_generated_source_spans() {
        let source = "(#gn make (name) `((#fn ,name () #u64 (#return 5u64))))
          (@make generated)
          (#fn main () #u64 (#return (#call generated (:))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["generated"];
        let literal = body
            .nodes
            .iter()
            .find(|node| matches!(node.kind, NodeKind::Literal(Expr::Integer(5))))
            .unwrap_or_else(|| panic!("{}", checked.dump_typed_ir()));
        let span = literal.span.unwrap();
        assert_ne!(span.source_id, 0);
        let generated_source = &program.source_files[span.source_id as usize].source;
        assert_eq!(&generated_source[span.start..span.end], "5");
    }

    #[test]
    fn lowered_instructions_retain_stable_statement_ids_and_spans() {
        let source = "(#fn main () #u64 (#let value #u64 1u64) (#return value))";
        let program = crate::parse_program(source).unwrap();
        let crate::Item::Function(function) = &program.items[0] else {
            unreachable!()
        };
        let ids = crate::typed_ir::statement_ids(&program);
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        assert!(checked
            .dump_typed_ir()
            .contains("statement Some(StatementId("));
        for (instruction, statement) in body.instructions.iter().zip(&function.body) {
            let id = ids[&(std::ptr::from_ref(statement) as usize)];
            assert_eq!(instruction.statement_id, Some(id));
            let span = instruction.span.expect("retained statement span");
            assert!(source[span.start..span.end].starts_with("(#"));
        }
    }

    #[test]
    fn call_argument_order_is_separate_from_parameter_order() {
        let source = "(#fn combine ((first #u64) (second #u64) (third #u64)) #u64 (#return first))
          (#fn main () #u64
            (#return (#call combine (: third 3u64 : first 1u64 : second 2u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let (children, source_order) = body
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                NodeKind::Form {
                    children,
                    callee: Some(_),
                    argument_source_order,
                    ..
                } => Some((children, argument_source_order)),
                _ => None,
            })
            .unwrap();
        assert_eq!(source_order.as_deref(), Some(&[2, 0, 1][..]));
        let values = children
            .iter()
            .skip(1)
            .map(|id| {
                let span = body.nodes[id.0].span.unwrap();
                &source[span.start..span.end]
            })
            .collect::<Vec<_>>();
        assert_eq!(values, ["1u64", "2u64", "3u64"]);
    }

    #[test]
    fn call_without_arguments_has_empty_written_order() {
        let program = crate::parse_program(
            "(#fn value () #u64 (#return 42u64))
             (#fn main () #u64 (#return (#call value (:))))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let order = body.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::Form {
                callee: Some(_),
                argument_source_order,
                ..
            } => argument_source_order.as_deref(),
            _ => None,
        });
        assert_eq!(order, Some(&[][..]));
    }

    #[test]
    fn emission_overlay_distinguishes_checked_syntax_from_synthesized_nodes() {
        fn find_symbol<'a>(expression: &'a Expr, name: &str) -> Option<&'a Expr> {
            match expression {
                Expr::Symbol(found) if found == name => Some(expression),
                Expr::List(items) => items.iter().find_map(|item| find_symbol(item, name)),
                Expr::Block(statements) | Expr::Loop(statements) => {
                    statements.iter().find_map(|statement| match statement {
                        Statement::Expr(value)
                        | Statement::Return(Some(value))
                        | Statement::Let { value, .. } => find_symbol(value, name),
                        _ => None,
                    })
                }
                Expr::Labeled { expression, .. }
                | Expr::Quote(expression)
                | Expr::QuasiQuote(expression)
                | Expr::Unquote(expression)
                | Expr::UnquoteSplicing(expression) => find_symbol(expression, name),
                _ => None,
            }
        }

        let source = "(#fn increment ((value #u32)) #u32 (#return (#u32.+.wrap value 1u32)))\n\
          (#fn main () #u32\n\
            (#let value #u32 40)\n\
            (#return (#call increment (: value (#u32.+.wrap value 2)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let overlay = checked.declarations().bodies["main"]
            .emission_types(function)
            .unwrap();
        let checked_symbol = function
            .body
            .iter()
            .find_map(|statement| match statement {
                Statement::Return(Some(expression)) => find_symbol(expression, "value"),
                _ => None,
            })
            .unwrap();
        assert!(overlay.has_checked_identity(checked_symbol));
        assert!(!overlay.has_checked_identity(&Expr::Symbol("value".into())));
        assert_eq!(overlay.address_to_id.len(), overlay.by_id.len());
        assert!(overlay
            .address_to_id
            .values()
            .all(|id| overlay.by_id.contains_key(id)));
        assert!(
            overlay.by_id.len()
                > overlay
                    .by_id
                    .values()
                    .filter(|node| node.ty.is_some())
                    .count()
        );
        assert!(overlay.by_id.values().any(|node| {
            node.numeric.as_ref().is_some_and(|operation| {
                operation.operand_type == Type::U32
                    && operation.operation == NumericOpcode::Add
                    && operation.overflow == Overflow::Wrap
            })
        }));
        assert!(overlay.by_id.values().any(|node| node.binding.is_some()));
        let increment = checked.declarations().function_id("increment");
        assert!(increment.is_some());
        assert!(overlay.by_id.values().any(|node| node.callee == increment));
    }

    #[test]
    fn emission_overlay_keeps_nonoverlapping_local_binding_ids_distinct() {
        let source = "(#fn main () #u64
          (#let outer-value #u64 1u64)
          (#block (#let inner-value #u64 2u64) inner-value)
          (#return outer-value))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let body = &checked.declarations().bodies["main"];
        let overlay = body.emission_types(function).unwrap();
        let bindings = overlay
            .by_id
            .values()
            .filter_map(|node| node.binding)
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(bindings.len(), 2);
        assert_eq!(overlay.binding_names, ["outer-value", "inner-value"]);
    }

    #[test]
    fn emission_statement_targets_distinguish_an_initializer_pattern_from_its_destination() {
        let program = crate::parse_program(
            "(#enum Maybe ((Some #u64) None))
          (#fn main () #u64
            (#let answer #u64 (#match (Some 41u64)
              (#case (Some answer) answer) (#case None 0u64)))
            (#return (#u64.+.wrap answer 1u64)))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let overlay = checked.declarations().bodies["main"]
            .emission_types(function)
            .unwrap();
        let Statement::Let { name, value, .. } = &function.body[0] else {
            panic!("missing declaration")
        };
        let destination = overlay.statement_target(value).unwrap();
        let ids = overlay
            .by_id
            .values()
            .filter_map(|node| node.binding)
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(ids.len(), 2);
        assert!(ids.contains(&destination));
        assert_eq!(overlay.binding_names.len(), 2);
        assert_eq!(&overlay.binding_names[destination.0], name);
        let Expr::List(items) = value else {
            panic!("missing match")
        };
        let Expr::List(arm) = &items[2] else {
            panic!("missing arm")
        };
        let Expr::List(pattern) = &arm[0] else {
            panic!("missing pattern")
        };
        let pattern_binding = overlay.get(&pattern[1]).unwrap().binding.unwrap();
        let Expr::Symbol(pattern_name) = &pattern[1] else {
            panic!("missing pattern binding")
        };
        assert_eq!(&overlay.binding_names[pattern_binding.0], pattern_name);
        assert_ne!(destination, pattern_binding);
        assert_eq!(overlay.statement_target(&pattern[1]), None);
    }

    #[test]
    fn checked_node_metadata_survives_unsafe_wrapper_lowering() {
        let source = "(#fn main () #u64\n\
          (#return (#unsafe (#u64.+.wrap 40u64 2u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let original = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => Some(function),
                _ => None,
            })
            .unwrap();
        let body = &checked.declarations().bodies["main"];
        let stable_nodes = body.emission_nodes.clone();
        let checked_operator = stable_nodes
            .iter()
            .map(|id| &body.nodes[id.0])
            .find(|node| {
                matches!(
                    &node.kind,
                    NodeKind::Form {
                        numeric: Some(operation),
                        ..
                    } if operation.operation == NumericOpcode::Add
                )
            })
            .unwrap();
        let checked_span = checked_operator.span;
        let checked_type = checked_operator.ty.clone();

        let mut lowered = original.clone();
        lowered.body = body.statements(&body.instructions, false);
        assert_eq!(stable_nodes, body.emission_nodes);
        assert_eq!(body.statements(&body.instructions, false), original.body);
        let overlay = body.emission_types(&lowered).unwrap();
        assert!(overlay.by_id.values().any(|metadata| {
            metadata.ty == checked_type
                && metadata.numeric.as_ref().is_some_and(|operation| {
                    operation.operation == NumericOpcode::Add
                        && operation.operand_type == Type::U64
                        && operation.overflow == Overflow::Wrap
                })
        }));
        assert!(checked_span.is_some());
        assert!(format!("{:?}", lowered.body).contains("unsafe"));
    }

    #[test]
    fn emission_bridge_rejects_reordered_literals_with_the_same_node_count() {
        let source = "(#fn main () #u64
          (#return (#unsafe (#u64.+.wrap 40u64 2u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut lowered = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => {
                    Some(function.clone())
                }
                _ => None,
            })
            .unwrap();
        lowered.body = body.statements(&body.instructions, false);
        body.emission_types(&lowered).unwrap();
        let Statement::Return(Some(Expr::List(wrapper))) = &mut lowered.body[0] else {
            unreachable!()
        };
        let Expr::List(operands) = &mut wrapper[1] else {
            unreachable!()
        };
        operands.swap(1, 2);
        let error = body.emission_types(&lowered).err().unwrap();
        assert!(
            error.contains("checked expression shape changed"),
            "{error}"
        );
    }

    #[test]
    fn emission_bridge_rejects_symbol_identity_drift() {
        let source = "(#fn main () #u64
          (#let first #u64 1u64)
          (#let second #u64 2u64)
          (#return first))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut lowered = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => {
                    Some(function.clone())
                }
                _ => None,
            })
            .unwrap();
        lowered.body = body.statements(&body.instructions, true);
        body.emission_types(&lowered).unwrap();
        let Statement::Return(Some(Expr::Symbol(name))) = &mut lowered.body[2] else {
            unreachable!()
        };
        *name = "second".into();
        let error = body.emission_types(&lowered).err().unwrap();
        assert!(
            error.contains("checked expression shape changed"),
            "{error}"
        );
    }

    #[test]
    fn emission_bridge_rejects_form_head_drift() {
        let source = "(#fn main () #u64
          (#return (#u64.+.wrap 40u64 2u64)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut lowered = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "main" => {
                    Some(function.clone())
                }
                _ => None,
            })
            .unwrap();
        lowered.body = body.statements(&body.instructions, true);
        body.emission_types(&lowered).unwrap();
        let Statement::Return(Some(Expr::List(items))) = &mut lowered.body[0] else {
            unreachable!()
        };
        items[0] = Expr::Symbol("u64.-.wrap".into());
        let error = body.emission_types(&lowered).err().unwrap();
        assert!(
            error.contains("checked expression shape changed"),
            "{error}"
        );
    }

    #[test]
    fn lowering_preserves_mutation_projections_and_nested_control_flow() {
        let sources = [
            "(#fn main () #u64 (#let-mut value #u64 0u64) (#while (#u64.< value 2u64) (#set value (#u64.+.wrap value 1u64))) (#return value))",
            "(#struct Pair ((a #u64) (b #u64))) (#fn main () #u64 (#let-mut value Pair (#struct-literal Pair ((a 1u64) (b 2u64)))) (#set-field value b 42u64) (#return (#get value b)))",
        ];
        for source in sources {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let original = program
                .items
                .iter()
                .find_map(|item| match item {
                    crate::Item::Function(f) if f.name == "main" => Some(f),
                    _ => None,
                })
                .unwrap();
            let body = &checked.declarations().bodies["main"];
            assert_eq!(body.statements(&body.instructions, false), original.body);
        }
    }

    #[test]
    fn expression_branches_and_match_scopes_are_explicit_in_the_body_ir() {
        let source = "(#enum Maybe ((Some #u64) None))\n\
          (#fn choose ((flag #bool) (input Maybe)) #u64\n\
            (#return (#if flag\n\
              (#match input (#case (Some payload) payload) (#case None 0u64))\n\
              1u64)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let function = program
            .items
            .iter()
            .find_map(|item| match item {
                crate::Item::Function(function) if function.name == "choose" => Some(function),
                _ => None,
            })
            .unwrap();
        let body = &checked.declarations().bodies["choose"];
        assert_eq!(body.statements(&body.instructions, false), function.body);
        assert!(body
            .nodes
            .iter()
            .any(|node| matches!(node.kind, NodeKind::If { .. })));
        assert!(body
            .nodes
            .iter()
            .any(|node| matches!(node.kind, NodeKind::Match { .. })));
        let arm = body
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                NodeKind::MatchArm { pattern, values } if !values.is_empty() => {
                    Some((*pattern, values[0]))
                }
                _ => None,
            })
            .unwrap();
        let pattern_binding = body.nodes.iter().find_map(|node| match &node.kind {
            NodeKind::Symbol {
                name,
                binding: Some(binding),
            } if name == "payload" => Some(*binding),
            _ => None,
        });
        let pattern_binding = pattern_binding.expect("match pattern binding identity");
        assert!(body.nodes[arm.0 .0].ty.is_none());
        assert!(body.nodes[arm.1 .0].ty.is_some());
        assert!(body.nodes.iter().any(|node| matches!(
            &node.kind,
            NodeKind::Symbol {
                name,
                binding: Some(binding),
            } if name == "payload" && *binding == pattern_binding
        )));
    }
}

use crate::typed_ir::{
    resolve_type, DeclarationId, Declarations, ExpressionId, FieldId, FunctionId, GlobalId,
    VariantId,
};
use crate::{Expr, Function, Span, Statement, Type};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct NodeId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct BindingId(pub usize);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Overflow {
    NotApplicable,
    Wrap,
    Saturate,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NumericOpcode {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    Not,
    LogicalAnd,
    LogicalOr,
}

impl NumericOpcode {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "+" => Self::Add,
            "-" => Self::Subtract,
            "*" => Self::Multiply,
            "/" => Self::Divide,
            "%" => Self::Remainder,
            "&" => Self::BitAnd,
            "|" => Self::BitOr,
            "^" => Self::BitXor,
            "<<" => Self::ShiftLeft,
            ">>" => Self::ShiftRight,
            "<" => Self::Less,
            "<=" => Self::LessEqual,
            ">" => Self::Greater,
            ">=" => Self::GreaterEqual,
            "==" => Self::Equal,
            "!=" => Self::NotEqual,
            "!" => Self::Not,
            "&&" => Self::LogicalAnd,
            "||" => Self::LogicalOr,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Subtract => "-",
            Self::Multiply => "*",
            Self::Divide => "/",
            Self::Remainder => "%",
            Self::BitAnd => "&",
            Self::BitOr => "|",
            Self::BitXor => "^",
            Self::ShiftLeft => "<<",
            Self::ShiftRight => ">>",
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::Not => "!",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NumericOperation {
    pub operand_type: Type,
    pub operation: NumericOpcode,
    pub overflow: Overflow,
}

impl NumericOperation {
    pub fn scalar_name(&self) -> &'static str {
        match self.operand_type {
            Type::Bool => "#bool",
            Type::Char => "#char",
            Type::I8 => "#i8",
            Type::I16 => "#i16",
            Type::I32 => "#i32",
            Type::I64 => "#i64",
            Type::I128 => "#i128",
            Type::Isize => "#isize",
            Type::U8 => "#u8",
            Type::U16 => "#u16",
            Type::U32 => "#u32",
            Type::U64 => "#u64",
            Type::U128 => "#u128",
            Type::Usize => "#usize",
            Type::F32 => "#f32",
            Type::F64 => "#f64",
            _ => unreachable!("numeric node has a scalar operand type"),
        }
    }

    pub fn overflow_mode(&self) -> Option<&'static str> {
        match self.overflow {
            Overflow::NotApplicable => None,
            Overflow::Wrap => Some("wrap"),
            Overflow::Saturate => Some("saturate"),
        }
    }

    fn spelling(&self) -> String {
        let mode = self
            .overflow_mode()
            .map_or_else(String::new, |mode| format!(".{mode}"));
        let scalar = self.scalar_name();
        format!(
            "{}.{}{mode}",
            scalar.strip_prefix('#').unwrap_or(scalar),
            self.operation.as_str()
        )
    }
    pub fn parse(name: &str) -> Option<Self> {
        let (qualifier, rest) = name.split_once('.')?;
        let operand_type = Type::from_name(qualifier);
        if !matches!(
            operand_type,
            Type::Bool
                | Type::Char
                | Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::Isize
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::U128
                | Type::Usize
                | Type::F32
                | Type::F64
        ) {
            return None;
        }
        let (operation, mode) = rest.split_once('.').unwrap_or((rest, ""));
        let operation = NumericOpcode::parse(operation)?;
        let overflow = match mode {
            "wrap" => Overflow::Wrap,
            "saturate" => Overflow::Saturate,
            "" => Overflow::NotApplicable,
            _ => return None,
        };
        Some(Self {
            operand_type,
            operation,
            overflow,
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) enum NodeKind {
    Declaration(DeclarationId),
    Symbol {
        name: String,
        binding: Option<BindingId>,
    },
    Literal(Expr),
    Form {
        /// Builtin spelling, or the neutral `call` marker for a resolved
        /// function. User names come only from the callee declaration ID.
        head: String,
        children: Vec<NodeId>,
        numeric: Option<NumericOperation>,
        callee: Option<FunctionId>,
        /// Declaration-order argument indices in their written order. Absent
        /// for synthesized calls without complete source spans.
        argument_source_order: Option<Vec<usize>>,
    },
    If {
        head: NodeId,
        condition: NodeId,
        then_value: NodeId,
        else_value: Option<NodeId>,
    },
    Match {
        head: NodeId,
        value: NodeId,
        arms: Vec<NodeId>,
    },
    MatchArm {
        pattern: NodeId,
        values: Vec<NodeId>,
    },
    Block(Vec<Instruction>),
    Loop(Vec<Instruction>),
    Labeled(String, NodeId),
    Syntax(Vec<NodeId>),
    Quoted(&'static str, NodeId),
}

#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub expression_id: Option<ExpressionId>,
    /// None only for syntax data (operator names, type expressions, patterns).
    pub ty: Option<Type>,
    pub span: Option<Span>,
    pub kind: NodeKind,
}

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub name: String,
    pub ty: Type,
    pub span: Option<Span>,
}

#[derive(Clone, Debug)]
pub(crate) enum Control {
    Bind(BindingId, NodeId, bool),
    Destructure {
        pattern: NodeId,
        value: NodeId,
        ty: Type,
        mutable: bool,
        otherwise: Option<Vec<Instruction>>,
        failure_pattern: Option<NodeId>,
    },
    Assign(PlaceRoot, Projection, NodeId),
    While(NodeId, Vec<Instruction>),
    Loop(Vec<Instruction>),
    For(Box<Instruction>, NodeId, Box<Instruction>, Vec<Instruction>),
    Labeled(String, Box<Instruction>),
    Return(Option<NodeId>),
    Break(Option<String>, Option<NodeId>),
    Continue(Option<String>),
    Evaluate(NodeId),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PlaceRoot {
    Local(BindingId),
    /// Abstract referent identity for a reference supplied at the function
    /// boundary; distinct from the local slot that stores the reference.
    Parameter(BindingId),
    Global(GlobalId),
    /// Stationary heap storage, independent of the local owner handle. A call
    /// site and output slot distinguish allocations returned by a callee.
    Allocation(NodeId, Vec<usize>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub(crate) struct ParameterLoanSummary {
    pub fresh_allocation: Option<Vec<usize>>,
    pub owned_allocation: bool,
    /// When present, this is a static origin; `parameter` is unused.
    pub global: Option<crate::typed_ir::GlobalId>,
    pub parameter: usize,
    pub mutable: bool,
    pub pinned: bool,
    pub lifetime_only: bool,
    /// The callee creates a child loan, rather than transferring a stored
    /// reference value out of its owner. Caller slot ancestry needs this
    /// distinction even when both results have identical pointee origins.
    pub reborrow: bool,
    pub referent_projection: Vec<crate::typed_place::Segment>,
    /// Slot supplying the returned loan. Dereference segments cross from a
    /// reference value to reference-bearing storage inside its referent;
    /// these are loads, not projections of the container's physical address.
    pub input_storage: Vec<crate::typed_place::Segment>,
    pub storage: Vec<crate::typed_place::Segment>,
    /// Correspondence from output storage positions to input_storage
    /// positions, used to specialize symbolic array slots at caller sites.
    /// Positions introduced by constructors have no input correspondence.
    pub storage_inputs: Vec<Option<usize>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ParameterLoanSeed {
    pub owned_allocation: bool,
    pub mutable: bool,
    pub pinned: bool,
    pub storage: Vec<crate::typed_place::Segment>,
}

/// Reference contents after normal returns, plus whether every such path
/// writes this physical destination. This is not an ownership contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParameterStoreSummary {
    pub destination: ParameterLoanSummary,
    pub sources: Vec<ParameterLoanSummary>,
    pub definitely_written: bool,
    /// The physical tag write can be definite even when substituting every
    /// possible incoming loan source is incomplete at this call site.
    pub variants_definitely_written: bool,
    /// Must-known constructors inside the written value, relative to its root.
    /// An empty loan set does not imply any constructor.
    pub variants: HashMap<Vec<crate::typed_place::Segment>, crate::typed_ir::VariantId>,
}

#[derive(Clone, Debug)]
pub(crate) enum Projection {
    Local,
    Array(NodeId),
    Field(FieldId),
    Tuple(usize),
    Payload(VariantId, usize),
}

#[derive(Clone, Debug)]
pub(crate) struct Instruction {
    pub statement_id: Option<crate::typed_ir::StatementId>,
    pub span: Option<Span>,
    pub control: Control,
}

pub(crate) type OutputVariantMap<T> =
    HashMap<crate::typed_ir::FunctionId, HashMap<(Vec<crate::typed_place::Segment>, VariantId), T>>;

#[derive(Default)]
pub(crate) struct Body {
    /// Flat-word offsets of typed memory operations. A schema describes where
    /// existing loans may be stored or loaded; it never initializes a loan.
    pub word_layouts: HashMap<NodeId, crate::word_loans::Layout>,
    pub nodes: Vec<Node>,
    pub bindings: Vec<Binding>,
    pub instructions: Vec<Instruction>,
    /// Failure patterns retain their success pattern for mismatch-only cleanup checks.
    pub let_else_failures: HashMap<NodeId, (NodeId, Type)>,
    /// Function parameters occupy the first `parameter_count` binding slots.
    /// Keeping this boundary in typed IR lets ownership analyses distinguish
    /// externally supplied reference roots from references to local owners.
    pub parameter_count: usize,
    /// Explicitly mutable parameter bindings, retained for owner projections.
    pub mutable_parameters: std::collections::HashSet<BindingId>,
    /// Staged move classification; Copy-valued pinned reads do not consume.
    pub consuming_pin_reads: std::collections::HashSet<NodeId>,
    pub consuming_releases: std::collections::HashSet<NodeId>,
    /// Every-normal-return contents clearing, not an initialization contract.
    pub call_parameter_clears: Arc<HashMap<crate::typed_ir::FunctionId, Vec<ParameterLoanSummary>>>,
    /// Verified direct callees with no physical discriminant writes. Unknown
    /// operations and unchecked callees never appear in this prepared table.
    pub call_preserves_variant_tags: Arc<std::collections::HashSet<crate::typed_ir::FunctionId>>,
    /// Complete may-mutate footprints of checked callees. Absence means an
    /// unknown/global effect. These invalidate tags; they never establish
    /// ownership, initialization, consumption, or a new constructor.
    pub call_tag_mutations: Arc<HashMap<crate::typed_ir::FunctionId, Vec<ParameterLoanSummary>>>,
    /// Destruction facts conditioned on an explicitly matched return variant.
    pub call_clear_variants:
        Arc<HashMap<crate::typed_ir::FunctionId, HashMap<VariantId, Vec<ParameterLoanSummary>>>>,
    pub call_output_store_variants: Arc<OutputVariantMap<Vec<ParameterStoreSummary>>>,
    pub call_output_clear_variants: Arc<OutputVariantMap<Vec<ParameterLoanSummary>>>,
    /// Direct callee outcome contracts supplied by the staged ownership pass.
    /// Replaced for each analysis run, never reused across entry assumptions.
    pub call_variant_exits: std::cell::RefCell<
        HashMap<
            crate::typed_ir::FunctionId,
            HashMap<VariantId, crate::typed_flow::ReferentVariantExit>,
        >,
    >,
    /// Actual outcomes inside owned call output storage, not task captures.
    /// Rebuilt with the root contracts for each staged inference run.
    pub call_output_variant_exits:
        std::cell::RefCell<OutputVariantMap<crate::typed_flow::ReferentVariantExit>>,
    /// Select actual parameter contents when preparing initialized-referent
    /// contracts. The production gate and its test entry points share this mode.
    pub staged_parameter_contents: bool,
    /// Constant enum facts proved on every normal return, relative to output.
    pub call_return_variants: Arc<
        HashMap<
            crate::typed_ir::FunctionId,
            HashMap<Vec<crate::typed_place::Segment>, crate::typed_ir::VariantId>,
        >,
    >,
    /// Conservative output-relative bounds; missing paths are unknown.
    pub call_return_variant_bounds:
        Arc<HashMap<crate::typed_ir::FunctionId, crate::typed_flow::VariantBounds>>,
    /// Interprocedural return-origin summaries shared by all checked bodies.
    pub call_return_origins: Arc<HashMap<crate::typed_ir::FunctionId, Vec<ParameterLoanSummary>>>,
    /// Mandatory reference slots of real checked callees' owned returns.
    /// Used only to exclude impossible tagged outputs, not to invent loans.
    pub call_return_reference_slots:
        Arc<HashMap<crate::typed_ir::FunctionId, Vec<Vec<crate::typed_place::Segment>>>>,
    pub call_store_origins: Arc<HashMap<crate::typed_ir::FunctionId, Vec<ParameterStoreSummary>>>,
    pub call_store_variants:
        Arc<HashMap<crate::typed_ir::FunctionId, HashMap<VariantId, Vec<ParameterStoreSummary>>>>,
    /// Reference-bearing slots in each parameter value, indexed by binding ID.
    pub parameter_loan_slots: Vec<Vec<ParameterLoanSeed>>,
    /// Slot schema beyond reference boundaries. These describe loads;
    /// unlike value slots, they must never seed initialized physical loans.
    pub parameter_referent_loan_slots: Vec<Vec<ParameterLoanSeed>>,
    /// Inferred entry loans required by typed interpretations of word memory.
    /// Callers must supply actual stored origins; these are not initialized bits.
    pub word_input_requirements: Vec<ParameterLoanSummary>,
    /// Candidate numeric value slots, used only to infer abstract entry
    /// requirements. Contents-aware/native analyses never seed these slots.
    pub word_parameter_candidates: Vec<Vec<ParameterLoanSeed>>,
    pub call_word_input_requirements:
        Arc<HashMap<crate::typed_ir::FunctionId, Vec<ParameterLoanSummary>>>,
    emission_nodes: Vec<NodeId>,
    callees: HashMap<FunctionId, String>,
    declaration_names: HashMap<DeclarationId, String>,
    aggregate_names: HashMap<crate::typed_ir::AggregateId, String>,
}

#[derive(Default)]
pub(crate) struct EmissionTypes {
    /// Checked metadata is authoritative under deterministic source identities.
    pub by_id: HashMap<ExpressionId, EmissionNode>,
    /// Local names in BindingId order, used only to bridge existing storage
    /// allocation into the checked backend identity space.
    pub binding_names: Vec<String>,
    /// Checked local types in the same identity order.
    pub binding_types: Vec<Type>,
    /// Checked destinations for bind/assignment RHS expressions. An RHS
    /// identity is distinct from the bindings it may introduce in inner scopes.
    pub statement_targets: HashMap<ExpressionId, BindingId>,
    /// Owner names needed to validate aggregate declaration identities.
    pub aggregate_names: HashMap<crate::typed_ir::AggregateId, String>,
    /// Global names addressed by checked declaration identity.
    pub global_names: HashMap<GlobalId, String>,
    /// Temporary bridge for legacy codegen, which still visits AST references.
    pub address_to_id: HashMap<usize, ExpressionId>,
    /// Backend-created expressions have no source identity and retain a narrow
    /// address-based compatibility path.
    pub synthesized_by_address: HashMap<usize, EmissionNode>,
}

#[derive(Default)]
pub(crate) struct EmissionNode {
    pub ty: Option<Type>,
    pub span: Option<Span>,
    pub binding: Option<BindingId>,
    pub declaration: Option<DeclarationId>,
    pub literal: Option<Expr>,
    pub numeric: Option<NumericOperation>,
    pub callee: Option<FunctionId>,
}

impl EmissionTypes {
    pub fn statement_target(&self, expression: &Expr) -> Option<BindingId> {
        self.address_to_id
            .get(&(std::ptr::from_ref(expression) as usize))
            .and_then(|id| self.statement_targets.get(id))
            .copied()
    }

    pub fn has_checked_identity(&self, expression: &Expr) -> bool {
        self.address_to_id
            .contains_key(&(std::ptr::from_ref(expression) as usize))
    }

    pub fn get(&self, expression: &Expr) -> Option<&EmissionNode> {
        let address = std::ptr::from_ref(expression) as usize;
        self.address_to_id
            .get(&address)
            .and_then(|id| self.by_id.get(id))
            .or_else(|| self.synthesized_by_address.get(&address))
    }

    #[cfg(test)]
    pub fn insert_synthesized(&mut self, expression: &Expr, node: EmissionNode) {
        self.synthesized_by_address
            .insert(std::ptr::from_ref(expression) as usize, node);
    }

    #[cfg(test)]
    pub fn get_mut_synthesized(&mut self, expression: &Expr) -> Option<&mut EmissionNode> {
        self.synthesized_by_address
            .get_mut(&(std::ptr::from_ref(expression) as usize))
    }
}

impl Body {
    pub fn declaration_name(&self, id: DeclarationId) -> Option<&str> {
        self.declaration_names.get(&id).map(String::as_str)
    }

    fn emission_node_order(&self) -> Vec<NodeId> {
        let mut order = Vec::new();
        self.walk_emission_instructions(&self.instructions, &mut order);
        order
    }

    fn walk_emission_instructions(&self, instructions: &[Instruction], order: &mut Vec<NodeId>) {
        for instruction in instructions {
            match &instruction.control {
                Control::Bind(_, value, _)
                | Control::Return(Some(value))
                | Control::Break(_, Some(value))
                | Control::Evaluate(value) => self.walk_emission_node(*value, order),
                Control::Destructure {
                    pattern,
                    value,
                    otherwise,
                    failure_pattern,
                    ..
                } => {
                    self.walk_emission_node(*pattern, order);
                    self.walk_emission_node(*value, order);
                    if let Some(pattern) = failure_pattern {
                        self.walk_emission_node(*pattern, order);
                    }
                    if let Some(otherwise) = otherwise {
                        self.walk_emission_instructions(otherwise, order);
                    }
                }
                Control::Assign(_, projection, value) => {
                    if let Projection::Array(index) = projection {
                        self.walk_emission_node(*index, order);
                    }
                    self.walk_emission_node(*value, order);
                }
                Control::While(condition, body) => {
                    self.walk_emission_node(*condition, order);
                    self.walk_emission_instructions(body, order);
                }
                Control::Loop(body) => self.walk_emission_instructions(body, order),
                Control::For(init, condition, step, body) => {
                    self.walk_emission_instructions(std::slice::from_ref(init.as_ref()), order);
                    self.walk_emission_node(*condition, order);
                    self.walk_emission_instructions(std::slice::from_ref(step.as_ref()), order);
                    self.walk_emission_instructions(body, order);
                }
                Control::Labeled(_, statement) => {
                    self.walk_emission_instructions(
                        std::slice::from_ref(statement.as_ref()),
                        order,
                    );
                }
                Control::Return(None) | Control::Break(_, None) | Control::Continue(_) => {}
            }
        }
    }

    fn walk_emission_node(&self, id: NodeId, order: &mut Vec<NodeId>) {
        match &self.nodes[id.0].kind {
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                for child in children {
                    self.walk_emission_node(*child, order);
                }
            }
            NodeKind::If {
                head,
                condition,
                then_value,
                else_value,
            } => {
                for child in [
                    Some(*head),
                    Some(*condition),
                    Some(*then_value),
                    *else_value,
                ]
                .into_iter()
                .flatten()
                {
                    self.walk_emission_node(child, order);
                }
            }
            NodeKind::Match { head, value, arms } => {
                self.walk_emission_node(*head, order);
                self.walk_emission_node(*value, order);
                for arm in arms {
                    self.walk_emission_node(*arm, order);
                }
            }
            NodeKind::MatchArm { pattern, values } => {
                self.walk_emission_node(*pattern, order);
                for value in values {
                    self.walk_emission_node(*value, order);
                }
            }
            NodeKind::Block(body) | NodeKind::Loop(body) => {
                self.walk_emission_instructions(body, order);
            }
            NodeKind::Labeled(_, child) | NodeKind::Quoted(_, child) => {
                self.walk_emission_node(*child, order);
            }
            NodeKind::Declaration(_) | NodeKind::Symbol { .. } | NodeKind::Literal(_) => {}
        }
        order.push(id);
    }

    /// Bridge stable nodes into the legacy instruction selector after
    /// call-name normalization. No semantic analysis is repeated.
    pub fn emission_types(&self, lowered: &Function) -> Result<EmissionTypes, String> {
        let mut after = Vec::new();
        walk_statements(&lowered.body, &mut after);
        if self.emission_nodes.len() != after.len() {
            return Err(format!(
                "internal error: typed body shape changed for '{}'",
                lowered.name
            ));
        }
        let mut emission = EmissionTypes::default();
        emission.binding_names = self
            .bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect();
        emission.binding_types = self
            .bindings
            .iter()
            .map(|binding| binding.ty.clone())
            .collect();
        let mut pending = vec![self.instructions.as_slice()];
        for node in &self.nodes {
            if let NodeKind::Block(body) | NodeKind::Loop(body) = &node.kind {
                pending.push(body.as_slice());
            }
        }
        while let Some(instructions) = pending.pop() {
            for instruction in instructions {
                match &instruction.control {
                    Control::Bind(binding, value, _)
                    | Control::Assign(PlaceRoot::Local(binding), _, value) => {
                        let id = self.nodes[value.0].expression_id.ok_or_else(|| {
                            "internal error: statement RHS lost its checked identity".to_owned()
                        })?;
                        emission.statement_targets.insert(id, *binding);
                    }
                    Control::While(_, body) | Control::Loop(body) => pending.push(body),
                    Control::For(init, _, step, body) => {
                        pending.push(std::slice::from_ref(init.as_ref()));
                        pending.push(std::slice::from_ref(step.as_ref()));
                        pending.push(body);
                    }
                    Control::Labeled(_, statement) => {
                        pending.push(std::slice::from_ref(statement.as_ref()));
                    }
                    Control::Destructure {
                        otherwise: Some(body),
                        ..
                    } => pending.push(body),
                    _ => {}
                }
            }
        }
        emission.aggregate_names = self.aggregate_names.clone();
        emission.global_names = self
            .declaration_names
            .iter()
            .filter_map(|(id, name)| match id {
                DeclarationId::Global(id) => Some((*id, name.clone())),
                _ => None,
            })
            .collect();
        for (id, target) in self.emission_nodes.iter().zip(after) {
            let address = std::ptr::from_ref(target) as usize;
            let node = &self.nodes[id.0];
            let matches_shape = match (&node.kind, target) {
                (NodeKind::Literal(expected), actual) => expected == actual,
                (NodeKind::Symbol { name, binding }, Expr::Symbol(actual)) => {
                    binding
                        .map(|id| self.bindings[id.0].name.as_str())
                        .unwrap_or(name)
                        == actual
                }
                (NodeKind::Declaration(DeclarationId::Function(id)), Expr::Function(actual)) => {
                    &self.declaration_names[&DeclarationId::Function(*id)] == actual
                }
                (NodeKind::Declaration(id), Expr::Symbol(actual))
                    if !matches!(id, DeclarationId::Function(_)) =>
                {
                    &self.declaration_names[id] == actual
                }
                (
                    NodeKind::Form {
                        head,
                        numeric,
                        callee,
                        ..
                    },
                    Expr::List(items),
                ) => {
                    let expected = numeric
                        .as_ref()
                        .map(NumericOperation::spelling)
                        .or_else(|| callee.map(|id| self.callees[&id].clone()))
                        .unwrap_or_else(|| head.clone());
                    match items.first() {
                        Some(Expr::Function(actual)) => callee.is_some() && actual == &expected,
                        Some(Expr::Symbol(actual)) => callee.is_none() && actual == &expected,
                        _ => false,
                    }
                }
                (
                    NodeKind::If { .. }
                    | NodeKind::Match { .. }
                    | NodeKind::MatchArm { .. }
                    | NodeKind::Syntax(_),
                    Expr::List(_),
                ) => true,
                (NodeKind::Block(_), Expr::Block(_))
                | (NodeKind::Loop(_), Expr::Loop(_))
                | (NodeKind::Labeled(..), Expr::Labeled { .. })
                | (NodeKind::Quoted("quote", _), Expr::Quote(_))
                | (NodeKind::Quoted("quasiquote", _), Expr::QuasiQuote(_))
                | (NodeKind::Quoted("unquote", _), Expr::Unquote(_))
                | (NodeKind::Quoted("splice", _), Expr::UnquoteSplicing(_)) => true,
                _ => false,
            };
            if !matches_shape {
                return Err(format!(
                    "internal error: checked expression shape changed for '{}' at node {}",
                    lowered.name, id.0
                ));
            }
            let (numeric, callee) = match &node.kind {
                NodeKind::Form {
                    numeric, callee, ..
                } => (numeric.clone(), *callee),
                _ => (None, None),
            };
            let binding = match &node.kind {
                NodeKind::Symbol { binding, .. } => *binding,
                _ => None,
            };
            let declaration = match &node.kind {
                NodeKind::Declaration(id) => Some(*id),
                _ => None,
            };
            let literal = match &node.kind {
                NodeKind::Literal(value) => Some(value.clone()),
                NodeKind::Symbol {
                    name,
                    binding: None,
                } if matches!(name.as_str(), "true" | "false") => Some(Expr::Symbol(name.clone())),
                _ => None,
            };
            let expression_id = node.expression_id.ok_or_else(|| {
                format!("internal error: checked node {} has no expression ID", id.0)
            })?;
            if emission
                .address_to_id
                .insert(address, expression_id)
                .is_some()
            {
                return Err(format!(
                    "internal error: duplicate checked expression in emission for '{}'",
                    lowered.name
                ));
            }
            if emission
                .by_id
                .insert(
                    expression_id,
                    EmissionNode {
                        ty: node.ty.clone(),
                        span: node.span,
                        binding,
                        declaration,
                        literal,
                        numeric,
                        callee,
                    },
                )
                .is_some()
            {
                return Err(format!(
                    "internal error: duplicate checked expression ID in emission for '{}'",
                    lowered.name
                ));
            }
        }
        Ok(emission)
    }
    pub fn syntax(&self, id: NodeId, erase_unsafe: bool) -> Expr {
        match &self.nodes[id.0].kind {
            NodeKind::Declaration(id) => match id {
                DeclarationId::Function(_) => Expr::Function(self.declaration_names[id].clone()),
                _ => Expr::Symbol(self.declaration_names[id].clone()),
            },
            NodeKind::Symbol { name, binding } => Expr::Symbol(
                binding
                    .map(|id| self.bindings[id.0].name.clone())
                    .unwrap_or_else(|| name.clone()),
            ),
            NodeKind::Literal(value) => value.clone(),
            NodeKind::Form {
                head,
                children,
                numeric,
                callee,
                ..
            } => {
                if erase_unsafe && head == "unsafe" && children.len() == 2 {
                    return self.syntax(children[1], true);
                }
                let mut items: Vec<_> = children
                    .iter()
                    .map(|id| self.syntax(*id, erase_unsafe))
                    .collect();
                if let Some(operation) = numeric {
                    items[0] = Expr::Symbol(operation.spelling());
                }
                if let Some(callee) = callee {
                    items[0] = Expr::Function(self.callees[callee].clone());
                }
                Expr::List(items)
            }
            NodeKind::If {
                head,
                condition,
                then_value,
                else_value,
            } => {
                let mut items = vec![
                    self.syntax(*head, erase_unsafe),
                    self.syntax(*condition, erase_unsafe),
                    self.syntax(*then_value, erase_unsafe),
                ];
                if let Some(value) = else_value {
                    items.push(self.syntax(*value, erase_unsafe));
                }
                Expr::List(items)
            }
            NodeKind::Match { head, value, arms } => {
                let mut items = vec![
                    self.syntax(*head, erase_unsafe),
                    self.syntax(*value, erase_unsafe),
                ];
                items.extend(arms.iter().map(|arm| self.syntax(*arm, erase_unsafe)));
                Expr::List(items)
            }
            NodeKind::MatchArm { pattern, values } => {
                let mut items = vec![self.syntax(*pattern, erase_unsafe)];
                items.extend(values.iter().map(|value| self.syntax(*value, erase_unsafe)));
                Expr::List(items)
            }
            NodeKind::Syntax(children) => Expr::List(
                children
                    .iter()
                    .map(|id| self.syntax(*id, erase_unsafe))
                    .collect(),
            ),
            NodeKind::Block(instructions) => {
                Expr::Block(self.statements(instructions, erase_unsafe))
            }
            NodeKind::Loop(instructions) => Expr::Loop(self.statements(instructions, erase_unsafe)),
            NodeKind::Labeled(label, expression) => Expr::Labeled {
                label: label.clone(),
                expression: Box::new(self.syntax(*expression, erase_unsafe)),
            },
            NodeKind::Quoted(kind, expression) => {
                let expression = Box::new(self.syntax(*expression, erase_unsafe));
                match *kind {
                    "quote" => Expr::Quote(expression),
                    "quasiquote" => Expr::QuasiQuote(expression),
                    "unquote" => Expr::Unquote(expression),
                    "splice" => Expr::UnquoteSplicing(expression),
                    _ => unreachable!(),
                }
            }
        }
    }

    pub fn statements(&self, instructions: &[Instruction], erase_unsafe: bool) -> Vec<Statement> {
        instructions
            .iter()
            .map(|instruction| self.statement(instruction, erase_unsafe))
            .collect()
    }

    fn statement(&self, instruction: &Instruction, erase: bool) -> Statement {
        let expr = |id| self.syntax(id, erase);
        match &instruction.control {
            Control::Bind(binding, value, mutable) => {
                let binding = &self.bindings[binding.0];
                Statement::Let {
                    name: binding.name.clone(),
                    ty: binding.ty.clone(),
                    value: expr(*value),
                    mutable: *mutable,
                }
            }
            Control::Destructure {
                pattern,
                value,
                ty,
                mutable,
                otherwise,
                failure_pattern,
            } => match otherwise {
                Some(body) => Statement::LetElse {
                    pattern: expr(*pattern),
                    failure_pattern: failure_pattern.map(expr),
                    value: expr(*value),
                    ty: ty.clone(),
                    else_body: self.statements(body, erase),
                },
                None => Statement::Destructure {
                    pattern: expr(*pattern),
                    value: expr(*value),
                    ty: ty.clone(),
                    mutable: *mutable,
                },
            },
            Control::Assign(root, projection, value) => {
                let name = match root {
                    PlaceRoot::Allocation(_, _) => {
                        unreachable!("allocation identities are not lexical assignment targets")
                    }
                    PlaceRoot::Local(id) => self.bindings[id.0].name.clone(),
                    PlaceRoot::Parameter(id) => self.bindings[id.0].name.clone(),
                    PlaceRoot::Global(id) => {
                        self.declaration_names[&DeclarationId::Global(*id)].clone()
                    }
                };
                let value = expr(*value);
                match projection {
                    Projection::Local => Statement::Assign { name, value },
                    Projection::Array(index) => Statement::ArrayAssign {
                        name,
                        value,
                        index: expr(*index),
                    },
                    Projection::Field(field) => Statement::FieldAssign {
                        name,
                        value,
                        field: self.declaration_names[&DeclarationId::Field(*field)].clone(),
                    },
                    Projection::Tuple(index) => Statement::TupleAssign {
                        name,
                        value,
                        index: *index,
                    },
                    Projection::Payload(variant, index) => Statement::EnumPayloadAssign {
                        name,
                        value,
                        variant: self.declaration_names[&DeclarationId::Variant(*variant)].clone(),
                        index: *index,
                    },
                }
            }
            Control::While(condition, body) => Statement::While {
                condition: expr(*condition),
                body: self.statements(body, erase),
            },
            Control::Loop(body) => Statement::Loop {
                body: self.statements(body, erase),
            },
            Control::For(init, condition, step, body) => Statement::For {
                init: Box::new(self.statement(init, erase)),
                condition: expr(*condition),
                step: Box::new(self.statement(step, erase)),
                body: self.statements(body, erase),
            },
            Control::Labeled(label, statement) => Statement::Labeled {
                label: label.clone(),
                statement: Box::new(self.statement(statement, erase)),
            },
            Control::Return(value) => Statement::Return(value.map(expr)),
            Control::Break(None, None) => Statement::Break,
            Control::Break(None, Some(value)) => Statement::BreakValue(expr(*value)),
            Control::Break(Some(label), None) => Statement::BreakTo(label.clone()),
            Control::Break(Some(label), Some(value)) => Statement::BreakToValue {
                label: label.clone(),
                value: expr(*value),
            },
            Control::Continue(None) => Statement::Continue,
            Control::Continue(Some(label)) => Statement::ContinueTo(label.clone()),
            Control::Evaluate(value) => Statement::Expr(expr(*value)),
        }
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();
        let mut declarations: Vec<_> = self.declaration_names.iter().collect();
        declarations.sort_by_key(|(id, _)| **id);
        for (id, name) in declarations {
            writeln!(output, "  declaration {id:?}: {name}").unwrap();
        }
        for (id, binding) in self.bindings.iter().enumerate() {
            writeln!(output, "  binding {id}: {} {:?}", binding.name, binding.ty).unwrap();
        }
        for (id, node) in self.nodes.iter().enumerate() {
            writeln!(
                output,
                "  node {id}: {:?} {:?} {:?}",
                node.ty, node.span, node.kind
            )
            .unwrap();
            if let NodeKind::Form {
                argument_source_order: Some(order),
                ..
            } = &node.kind
            {
                writeln!(output, "    argument source order: {order:?}").unwrap();
            }
        }
        for instruction in &self.instructions {
            writeln!(
                output,
                "  statement {:?} {:?}: {:?}",
                instruction.statement_id, instruction.span, instruction.control
            )
            .unwrap();
        }
        output
    }

    pub fn lower(
        function: &Function,
        declarations: &Declarations,
        types: &HashMap<ExpressionId, Type>,
        expression_ids: &HashMap<usize, ExpressionId>,
        expression_spans: &HashMap<ExpressionId, Span>,
        statement_spans: &HashMap<crate::typed_ir::StatementId, Span>,
        statement_ids: &HashMap<usize, crate::typed_ir::StatementId>,
        binding_spans: &[Option<Span>],
        parameter_spans: &[Option<Span>],
    ) -> Self {
        let expression_order = lowering_expression_order(&function.body, expression_ids);
        let mut builder = Builder {
            body: Body::default(),
            names: HashMap::new(),
            declarations,
            types,
            expression_order: expression_order.into(),
            expression_spans,
            statement_spans,
            statement_ids,
            binding_spans: binding_spans.iter().copied().collect(),
        };
        builder.body.parameter_count = function.parameters.len();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let binding = builder.binding(
                &parameter.name,
                resolve_type(&parameter.ty, &declarations.aliases).expect("checked parameter"),
                parameter_spans.get(index).copied().flatten(),
            );
            if parameter.mutable {
                builder.body.mutable_parameters.insert(binding);
            }
        }
        builder.body.instructions = builder.statements(&function.body);
        debug_assert!(
            builder.expression_order.is_empty(),
            "typed body traversal left source expressions unlowered"
        );
        builder.body.emission_nodes = builder.body.emission_node_order();
        builder.body
    }
}

fn walk_expression<'a>(expression: &'a Expr, output: &mut Vec<&'a Expr>) {
    match expression {
        Expr::List(items) => {
            for item in items {
                walk_expression(item, output);
            }
        }
        Expr::Block(body) | Expr::Loop(body) => walk_statements(body, output),
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => walk_expression(expression, output),
        _ => {}
    }
    output.push(expression);
}

fn walk_statements<'a>(statements: &'a [Statement], output: &mut Vec<&'a Expr>) {
    for statement in statements {
        match statement {
            Statement::Let { value, .. }
            | Statement::Assign { value, .. }
            | Statement::FieldAssign { value, .. }
            | Statement::TupleAssign { value, .. }
            | Statement::EnumPayloadAssign { value, .. }
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. }
            | Statement::Return(Some(value))
            | Statement::Expr(value) => walk_expression(value, output),
            Statement::Destructure { pattern, value, .. } => {
                walk_expression(pattern, output);
                walk_expression(value, output);
            }
            Statement::LetElse {
                pattern,
                value,
                failure_pattern,
                else_body,
                ..
            } => {
                walk_expression(pattern, output);
                walk_expression(value, output);
                if let Some(pattern) = failure_pattern {
                    walk_expression(pattern, output);
                }
                walk_statements(else_body, output);
            }
            Statement::ArrayAssign { index, value, .. } => {
                walk_expression(index, output);
                walk_expression(value, output);
            }
            Statement::While { condition, body } => {
                walk_expression(condition, output);
                walk_statements(body, output);
            }
            Statement::Loop { body } => walk_statements(body, output),
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                walk_statements(std::slice::from_ref(init), output);
                walk_expression(condition, output);
                walk_statements(std::slice::from_ref(step), output);
                walk_statements(body, output);
            }
            Statement::Labeled { statement, .. } => {
                walk_statements(std::slice::from_ref(statement), output)
            }
            _ => {}
        }
    }
}

fn lowering_expression_order(
    statements: &[Statement],
    identities: &HashMap<usize, ExpressionId>,
) -> VecDeque<ExpressionId> {
    fn expression(
        value: &Expr,
        ids: &HashMap<usize, ExpressionId>,
        output: &mut VecDeque<ExpressionId>,
    ) {
        output.push_back(ids[&(std::ptr::from_ref(value) as usize)]);
        match value {
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "match") =>
            {
                if let Some(head) = items.first() {
                    expression(head, ids, output);
                }
                if let Some(scrutinee) = items.get(1) {
                    expression(scrutinee, ids, output);
                }
                for arm in items.iter().skip(2) {
                    output.push_back(ids[&(std::ptr::from_ref(arm) as usize)]);
                    if let Expr::List(parts) = arm {
                        for part in parts {
                            expression(part, ids, output);
                        }
                    }
                }
            }
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "if") => {
                for item in items {
                    expression(item, ids, output);
                }
            }
            Expr::List(items) => {
                for item in items {
                    expression(item, ids, output);
                }
            }
            Expr::Block(body) | Expr::Loop(body) => statements_order(body, ids, output),
            Expr::Labeled {
                expression: inner, ..
            }
            | Expr::Quote(inner)
            | Expr::QuasiQuote(inner)
            | Expr::Unquote(inner)
            | Expr::UnquoteSplicing(inner) => expression(inner, ids, output),
            _ => {}
        }
    }

    fn statements_order(
        statements: &[Statement],
        ids: &HashMap<usize, ExpressionId>,
        output: &mut VecDeque<ExpressionId>,
    ) {
        for statement in statements {
            use Statement as S;
            match statement {
                S::Let { value, .. }
                | S::Assign { value, .. }
                | S::FieldAssign { value, .. }
                | S::TupleAssign { value, .. }
                | S::EnumPayloadAssign { value, .. }
                | S::BreakValue(value)
                | S::BreakToValue { value, .. }
                | S::Return(Some(value))
                | S::Expr(value) => expression(value, ids, output),
                S::Destructure { pattern, value, .. } => {
                    expression(value, ids, output);
                    expression(pattern, ids, output);
                }
                S::LetElse {
                    pattern,
                    value,
                    failure_pattern,
                    else_body,
                    ..
                } => {
                    expression(value, ids, output);
                    if let Some(pattern) = failure_pattern {
                        expression(pattern, ids, output);
                    }
                    statements_order(else_body, ids, output);
                    expression(pattern, ids, output);
                }
                S::ArrayAssign { index, value, .. } => {
                    expression(index, ids, output);
                    expression(value, ids, output);
                }
                S::While { condition, body } => {
                    expression(condition, ids, output);
                    statements_order(body, ids, output);
                }
                S::Loop { body } => statements_order(body, ids, output),
                S::For {
                    init,
                    condition,
                    step,
                    body,
                } => {
                    statements_order(std::slice::from_ref(init), ids, output);
                    expression(condition, ids, output);
                    statements_order(body, ids, output);
                    statements_order(std::slice::from_ref(step), ids, output);
                }
                S::Labeled { statement, .. } => {
                    statements_order(std::slice::from_ref(statement), ids, output)
                }
                S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) | S::Return(None) => {}
            }
        }
    }

    let mut output = VecDeque::new();
    statements_order(statements, identities, &mut output);
    output
}

struct Builder<'a> {
    body: Body,
    names: HashMap<String, BindingId>,
    declarations: &'a Declarations,
    types: &'a HashMap<ExpressionId, Type>,
    expression_order: VecDeque<ExpressionId>,
    expression_spans: &'a HashMap<ExpressionId, Span>,
    statement_spans: &'a HashMap<crate::typed_ir::StatementId, Span>,
    statement_ids: &'a HashMap<usize, crate::typed_ir::StatementId>,
    binding_spans: VecDeque<Option<Span>>,
}

impl Builder<'_> {
    fn expression_span(&self, id: ExpressionId) -> Option<Span> {
        self.expression_spans.get(&id).copied()
    }

    fn binding(&mut self, name: &str, ty: Type, span: Option<Span>) -> BindingId {
        let id = BindingId(self.body.bindings.len());
        self.body.bindings.push(Binding {
            name: name.into(),
            ty,
            span,
        });
        self.names.insert(name.into(), id);
        id
    }

    fn declaration(&mut self, id: DeclarationId) -> NodeKind {
        let owner = match id {
            DeclarationId::Field(field) => Some(field.owner),
            DeclarationId::Variant(variant) => Some(variant.owner),
            DeclarationId::Function(_) | DeclarationId::Global(_) | DeclarationId::Aggregate(_) => {
                None
            }
        };
        self.body
            .declaration_names
            .entry(id)
            .or_insert_with(|| self.declarations.declaration_name(id).to_owned());
        if let Some(owner) = owner {
            self.body.aggregate_names.entry(owner).or_insert_with(|| {
                self.declarations
                    .declaration_name(DeclarationId::Aggregate(owner))
                    .to_owned()
            });
        }
        NodeKind::Declaration(id)
    }

    fn resolve_node(&mut self, node: NodeId, id: DeclarationId) {
        self.body.nodes[node.0].kind = self.declaration(id);
    }

    fn place_type(&self, name: &str) -> &Type {
        match self.names.get(name) {
            Some(id) => &self.body.bindings[id.0].ty,
            None => &self.declarations.globals[name],
        }
    }

    fn field_projection(&mut self, name: &str, field: &str) -> Projection {
        let id = self
            .declarations
            .field_id(self.place_type(name), field)
            .expect("checked struct field assignment");
        self.declaration(DeclarationId::Field(id));
        Projection::Field(id)
    }

    fn payload_projection(&mut self, name: &str, variant: &str, index: usize) -> Projection {
        let id = self
            .declarations
            .variant_id(self.place_type(name), variant)
            .expect("checked enum payload assignment");
        self.declaration(DeclarationId::Variant(id));
        Projection::Payload(id, index)
    }

    fn place(&mut self, name: &str) -> PlaceRoot {
        if let Some(id) = self.names.get(name) {
            PlaceRoot::Local(*id)
        } else {
            let id = self
                .declarations
                .global_id(name)
                .expect("checked global assignment target");
            self.declaration(DeclarationId::Global(id));
            PlaceRoot::Global(id)
        }
    }

    // Pattern nodes retain their original syntax, but declaration occurrences
    // carry the same identity as uses in the successful scope. Never discover
    // a binding from its first use: unused bindings must exist too.
    fn pattern_bindings(&mut self, pattern: &Expr, node: NodeId, ty: &Type, enum_pattern: bool) {
        let ty = resolve_type(ty, &self.declarations.aliases).expect("checked pattern type");
        let children = match &self.body.nodes[node.0].kind {
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => children.clone(),
            _ => Vec::new(),
        };
        if enum_pattern {
            if let Type::Named(name) = &ty {
                if self.declarations.enums.contains_key(name) {
                    if let Expr::List(items) = pattern {
                        if let Some(Expr::Symbol(head)) = items.first() {
                            if head == "or" {
                                for (alternative, child) in items[1..].iter().zip(&children[1..]) {
                                    self.pattern_bindings(alternative, *child, &ty, true);
                                }
                            } else if let Some(id) = self.declarations.variant_id(&ty, head) {
                                let fields = self.declarations.variant(id).fields.clone();
                                self.resolve_node(children[0], DeclarationId::Variant(id));
                                for ((pattern, child), field) in
                                    items[1..].iter().zip(&children[1..]).zip(fields)
                                {
                                    self.pattern_bindings(pattern, *child, &field, false);
                                }
                            }
                        }
                    } else if let Expr::Symbol(head) = pattern {
                        if let Some(id) = self.declarations.variant_id(&ty, head) {
                            self.resolve_node(node, DeclarationId::Variant(id));
                        }
                    }
                    return;
                }
            }
        }
        match pattern {
            Expr::Symbol(name) if !matches!(name.as_str(), "_" | "true" | "false") => {
                let binding = self.binding(name, ty, self.body.nodes[node.0].span);
                self.body.nodes[node.0].kind = NodeKind::Symbol {
                    name: name.clone(),
                    binding: Some(binding),
                };
            }
            Expr::List(items) => {
                let Some(Expr::Symbol(head)) = items.first() else {
                    return;
                };
                let fields = match &ty {
                    Type::Tuple(fields) if head == "tuple" => fields.clone(),
                    Type::Array(element, length) if head == "array" => {
                        vec![*element.clone(); *length]
                    }
                    Type::Named(name) if head == name => self
                        .declarations
                        .structs
                        .get(name)
                        .map(|fields| fields.iter().map(|f| f.ty.clone()).collect())
                        .unwrap_or_default(),
                    _ => return, // Literal, range, and or patterns bind nothing.
                };
                if let Some(id) = self.declarations.aggregate_id(&ty) {
                    self.resolve_node(children[0], DeclarationId::Aggregate(id));
                }
                for ((pattern, child), field) in items[1..].iter().zip(&children[1..]).zip(fields) {
                    self.pattern_bindings(pattern, *child, &field, false);
                }
            }
            _ => {}
        }
    }

    fn match_arm(&mut self, arm: &Expr, ty: &Type) -> NodeId {
        let expression_id = self
            .expression_order
            .pop_front()
            .expect("checked match arm has a stable expression ID");
        let expression_type = self.types.get(&expression_id).cloned();
        let saved = self.names.clone();
        let Expr::List(parts) = arm else {
            unreachable!("checked match arm");
        };
        let pattern = self.expression(&parts[0]);
        self.pattern_bindings(&parts[0], pattern, ty, true);
        let values = parts[1..]
            .iter()
            .map(|part| self.expression(part))
            .collect();
        self.names = saved;
        self.record(
            expression_id,
            expression_type,
            NodeKind::MatchArm { pattern, values },
        )
    }

    fn resolve_form(&mut self, items: &[Expr], children: &[NodeId], ty: Option<&Type>) {
        let Some(Expr::Symbol(head)) = items.first() else {
            return;
        };
        // Only runtime forms have checked result types. A syntax constructor
        // or pattern with the same spelling must not be treated as a call.
        let Some(ty) = ty else {
            return;
        };
        if head == "struct-literal" {
            if let Some(owner) = self.declarations.aggregate_id(ty) {
                self.resolve_node(children[1], DeclarationId::Aggregate(owner));
            }
        } else if matches!(
            head.as_str(),
            "get"
                | "get-payload"
                | "pin-get-payload"
                | "pin-get-payload-mut"
                | "pin-get-payload-unchecked"
                | "pin-get-payload-unchecked-mut"
                | "pin-set-field"
                | "#variant-is"
        ) {
            let owner = self.body.nodes[children[1].0]
                .ty
                .as_ref()
                .and_then(|owner| {
                    if matches!(
                        head.as_str(),
                        "pin-get-payload"
                            | "pin-get-payload-mut"
                            | "pin-get-payload-unchecked"
                            | "pin-get-payload-unchecked-mut"
                            | "#variant-is"
                    ) {
                        match owner {
                            Type::PinnedReference { target, .. } => Some(target.as_ref()),
                            Type::Reference { target, .. } if head == "#variant-is" => {
                                Some(target.as_ref())
                            }
                            _ => None,
                        }
                    } else {
                        Some(owner)
                    }
                });
            if let (Some(owner), Some(Expr::Symbol(name))) = (owner, items.get(2)) {
                let id = if matches!(head.as_str(), "get" | "pin-set-field") {
                    self.declarations
                        .field_id(owner, name)
                        .map(DeclarationId::Field)
                } else {
                    self.declarations
                        .variant_id(owner, name)
                        .map(DeclarationId::Variant)
                }
                .expect("checked named projection");
                self.resolve_node(children[2], id);
            }
        } else if let Some(id) = self.declarations.variant_id(ty, head) {
            self.resolve_node(children[0], DeclarationId::Variant(id));
        } else if matches!(ty, Type::Named(name) if name == head)
            && self.declarations.structs.contains_key(head)
        {
            let id = self
                .declarations
                .aggregate_id(ty)
                .expect("checked constructor");
            self.resolve_node(children[0], DeclarationId::Aggregate(id));
        }
    }

    fn expression(&mut self, expression: &Expr) -> NodeId {
        let expression_id = self
            .expression_order
            .pop_front()
            .expect("checked expression has a stable expression ID");
        let expression_type = self.types.get(&expression_id).cloned();
        let kind = match expression {
            Expr::Function(name) => {
                let id = self
                    .declarations
                    .function_id(name)
                    .expect("checked explicit call target");
                self.declaration(DeclarationId::Function(id))
            }
            Expr::Symbol(name) => {
                let binding = expression_type
                    .is_some()
                    .then(|| self.names.get(name).copied())
                    .flatten();
                let declaration = if binding.is_none() {
                    expression_type.as_ref().and_then(|ty| {
                        self.declarations
                            .global_id(name)
                            .map(DeclarationId::Global)
                            .or_else(|| {
                                self.declarations
                                    .variant_id(ty, name)
                                    .map(DeclarationId::Variant)
                            })
                    })
                } else {
                    None
                };
                match declaration {
                    Some(id) => self.declaration(id),
                    None => NodeKind::Symbol {
                        name: name.clone(),
                        binding,
                    },
                }
            }
            Expr::List(items) => {
                if matches!(items.first(), Some(Expr::Symbol(head)) if head == "match") {
                    let head = self.expression(&items[0]);
                    let value = self.expression(&items[1]);
                    let ty = self.body.nodes[value.0]
                        .ty
                        .clone()
                        .expect("checked match scrutinee type");
                    let arms = items[2..]
                        .iter()
                        .map(|arm| self.match_arm(arm, &ty))
                        .collect();
                    NodeKind::Match { head, value, arms }
                } else if matches!(items.first(), Some(Expr::Symbol(head)) if head == "if") {
                    let head = self.expression(&items[0]);
                    let condition = self.expression(&items[1]);
                    let then_value = self.expression(&items[2]);
                    let else_value = items.get(3).map(|value| self.expression(value));
                    NodeKind::If {
                        head,
                        condition,
                        then_value,
                        else_value,
                    }
                } else {
                    let children = items
                        .iter()
                        .map(|child| self.expression(child))
                        .collect::<Vec<_>>();
                    if let Some(Expr::Symbol(head) | Expr::Function(head)) = items.first() {
                        if matches!(items.first(), Some(Expr::Symbol(_)))
                            && matches!(
                                head.as_str(),
                                "borrow"
                                    | "borrow-mut"
                                    | "borrow-slice"
                                    | "borrow-slice-mut"
                                    | "pin"
                                    | "pin-shared"
                                    | "pin-borrow"
                                    | "pin-borrow-mut"
                            )
                        {
                            if let Some(Expr::Symbol(name)) = items.get(1) {
                                if let Some(binding) = self.names.get(name).copied() {
                                    self.body.nodes[children[1].0].kind = NodeKind::Symbol {
                                        name: name.clone(),
                                        binding: Some(binding),
                                    };
                                    self.body.nodes[children[1].0].ty =
                                        Some(self.body.bindings[binding.0].ty.clone());
                                } else if let Some(id) = self.declarations.global_id(name) {
                                    self.resolve_node(children[1], DeclarationId::Global(id));
                                    self.body.nodes[children[1].0].ty =
                                        Some(self.declarations.global_type(id).clone());
                                }
                            }
                        }
                        let ty = expression_type.clone();
                        self.resolve_form(items, &children, ty.as_ref());
                        let explicit = matches!(items.first(), Some(Expr::Function(_)));
                        let callee = if explicit || !crate::is_builtin_head(head) {
                            self.declarations.function_id(head)
                        } else {
                            None
                        };
                        if let Some(callee) = callee {
                            self.body.callees.insert(callee, head.clone());
                        }
                        let argument_source_order = callee.and_then(|_| {
                            let arguments = &children[1..];
                            let spans = arguments
                                .iter()
                                .map(|id| self.body.nodes[id.0].span)
                                .collect::<Option<Vec<_>>>()?;
                            if spans
                                .iter()
                                .any(|span| span.source_id != spans[0].source_id)
                            {
                                return None;
                            }
                            let mut order = (0..arguments.len()).collect::<Vec<_>>();
                            order.sort_by_key(|&index| (spans[index].start, index));
                            Some(order)
                        });
                        NodeKind::Form {
                            head: if callee.is_some() {
                                "call".into()
                            } else {
                                head.clone()
                            },
                            children,
                            numeric: if callee.is_none() {
                                NumericOperation::parse(head)
                            } else {
                                None
                            },
                            callee,
                            argument_source_order,
                        }
                    } else {
                        NodeKind::Syntax(children)
                    }
                }
            }
            Expr::Block(body) => NodeKind::Block(self.statements(body)),
            Expr::Loop(body) => NodeKind::Loop(self.statements(body)),
            Expr::Labeled { label, expression } => {
                NodeKind::Labeled(label.clone(), self.expression(expression))
            }
            Expr::Quote(inner) => NodeKind::Quoted("quote", self.expression(inner)),
            Expr::QuasiQuote(inner) => NodeKind::Quoted("quasiquote", self.expression(inner)),
            Expr::Unquote(inner) => NodeKind::Quoted("unquote", self.expression(inner)),
            Expr::UnquoteSplicing(inner) => NodeKind::Quoted("splice", self.expression(inner)),
            _ => NodeKind::Literal(expression.clone()),
        };
        self.record(expression_id, expression_type, kind)
    }

    fn record(&mut self, expression_id: ExpressionId, ty: Option<Type>, kind: NodeKind) -> NodeId {
        let id = NodeId(self.body.nodes.len());
        self.body.nodes.push(Node {
            expression_id: Some(expression_id),
            ty,
            span: self.expression_span(expression_id),
            kind,
        });
        id
    }

    fn statements(&mut self, statements: &[Statement]) -> Vec<Instruction> {
        let saved = self.names.clone();
        let instructions = statements
            .iter()
            .map(|statement| self.statement(statement))
            .collect();
        self.names = saved;
        instructions
    }

    fn statement(&mut self, statement: &Statement) -> Instruction {
        let control = match statement {
            Statement::Let {
                name,
                ty,
                value,
                mutable,
            } => {
                let value = self.expression(value);
                let binding_span = self.binding_spans.pop_front().flatten();
                let binding = self.binding(
                    name,
                    resolve_type(ty, &self.declarations.aliases).expect("checked local"),
                    binding_span,
                );
                Control::Bind(binding, value, *mutable)
            }
            Statement::Destructure {
                pattern,
                ty,
                value,
                mutable,
            } => {
                let value = self.expression(value);
                let pattern_id = self.expression(pattern);
                let ty = resolve_type(ty, &self.declarations.aliases).expect("checked pattern");
                self.pattern_bindings(pattern, pattern_id, &ty, false);
                Control::Destructure {
                    pattern: pattern_id,
                    value,
                    ty,
                    mutable: *mutable,
                    otherwise: None,
                    failure_pattern: None,
                }
            }
            Statement::LetElse {
                pattern,
                ty,
                value,
                failure_pattern,
                else_body,
            } => {
                let value = self.expression(value);
                let ty = resolve_type(ty, &self.declarations.aliases).expect("checked pattern");
                let saved = self.names.clone();
                let failure_pattern = failure_pattern.as_ref().map(|pattern| {
                    let node = self.expression(pattern);
                    self.pattern_bindings(pattern, node, &ty, true);
                    node
                });
                let otherwise = Some(self.statements(else_body));
                self.names = saved;
                let pattern_id = self.expression(pattern);
                self.pattern_bindings(pattern, pattern_id, &ty, true);
                if let Some(failure) = failure_pattern {
                    self.body
                        .let_else_failures
                        .insert(failure, (pattern_id, ty.clone()));
                }
                Control::Destructure {
                    pattern: pattern_id,
                    value,
                    ty,
                    mutable: false,
                    otherwise,
                    failure_pattern,
                }
            }
            Statement::Assign { name, value } => {
                Control::Assign(self.place(name), Projection::Local, self.expression(value))
            }
            Statement::FieldAssign { name, field, value } => Control::Assign(
                self.place(name),
                self.field_projection(name, field),
                self.expression(value),
            ),
            Statement::TupleAssign { name, index, value } => Control::Assign(
                self.place(name),
                Projection::Tuple(*index),
                self.expression(value),
            ),
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => Control::Assign(
                self.place(name),
                self.payload_projection(name, variant, *index),
                self.expression(value),
            ),
            Statement::ArrayAssign { name, index, value } => Control::Assign(
                self.place(name),
                Projection::Array(self.expression(index)),
                self.expression(value),
            ),
            Statement::While { condition, body } => {
                Control::While(self.expression(condition), self.statements(body))
            }
            Statement::Loop { body } => Control::Loop(self.statements(body)),
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                let saved = self.names.clone();
                let init = Box::new(self.statement(init));
                let condition = self.expression(condition);
                // The checker permits the step to use body declarations.
                let body = body
                    .iter()
                    .map(|statement| self.statement(statement))
                    .collect();
                let step = Box::new(self.statement(step));
                self.names = saved;
                Control::For(init, condition, step, body)
            }
            Statement::Labeled { label, statement } => {
                Control::Labeled(label.clone(), Box::new(self.statement(statement)))
            }
            Statement::Return(value) => {
                Control::Return(value.as_ref().map(|value| self.expression(value)))
            }
            Statement::Break => Control::Break(None, None),
            Statement::BreakValue(value) => Control::Break(None, Some(self.expression(value))),
            Statement::BreakTo(label) => Control::Break(Some(label.clone()), None),
            Statement::BreakToValue { label, value } => {
                Control::Break(Some(label.clone()), Some(self.expression(value)))
            }
            Statement::Continue => Control::Continue(None),
            Statement::ContinueTo(label) => Control::Continue(Some(label.clone())),
            Statement::Expr(value) => Control::Evaluate(self.expression(value)),
        };
        let statement_id = self
            .statement_ids
            .get(&(std::ptr::from_ref(statement) as usize))
            .copied();
        Instruction {
            statement_id,
            span: statement_id.and_then(|id| self.statement_spans.get(&id).copied()),
            control,
        }
    }
}
