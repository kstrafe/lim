//! Typed, source-located body arena. Dense IDs survive copying and lowering;
//! checked type/span capture still bridges through the borrowed legacy AST.
use std::collections::HashMap;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emission_order_is_reconstructed_from_stable_nodes() {
        let source = "(#fn main () u64
          (#let-mut total u64 0u64)
          (#for (#let-mut i u64 0u64) (#u64.< i 3u64)
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
    fn match_arms_use_the_checked_scrutinee_node_type() {
        let source = "(#enum Choice ((Value u64) Empty))
          (#fn main () u64
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
        let source = "(#fn main () u64
          (#let u64 u64 42u64)
          (#let view (#ref u64) (#borrow u64))
          (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let owner = body
            .nodes
            .iter()
            .find(|node| {
                matches!(&node.kind,
            NodeKind::Symbol { name, binding: Some(_) } if name == "u64")
            })
            .unwrap();
        assert_eq!(owner.ty, Some(Type::U64));
        let NodeKind::Symbol {
            binding: Some(id), ..
        } = owner.kind
        else {
            unreachable!()
        };
        assert_eq!(body.bindings[id.0].name, "u64");
        assert_eq!(body.bindings.len(), 2, "syntax must not create bindings");
    }

    #[test]
    fn nodes_keep_contextual_types_numeric_modes_and_reordered_call_spans() {
        let source = "(#fn add ((left u32) (right u32)) u32 (#return (#u32.+.saturate left right)))
          (#fn main () u32 (#let x u32 40) (#return (#call add (: right 2 : left x))))";
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
        let source = "(#gn make (name) `((#fn ,name () u64 (#return 5u64))))
          (@make generated)
          (#fn main () u64 (#return (#call generated (:))))";
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
    fn call_argument_order_is_separate_from_parameter_order() {
        let source = "(#fn combine ((first u64) (second u64) (third u64)) u64 (#return first))
          (#fn main () u64
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
            "(#fn value () u64 (#return 42u64))
             (#fn main () u64 (#return (#call value (:))))",
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
        let source = "(#fn increment ((value u32)) u32 (#return (#u32.+.wrap value 1u32)))\n\
          (#fn main () u32\n\
            (#let value u32 40)\n\
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
    fn emission_overlay_keeps_shadowed_local_binding_ids_distinct() {
        let source = "(#fn main () u64
          (#let value u64 1u64)
          (#block (#let value u64 2u64) value)
          (#return value))";
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
    }

    #[test]
    fn checked_node_metadata_survives_unsafe_erasure() {
        let source = "(#fn main () u64\n\
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
        lowered.body = body.statements(&body.instructions, true);
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
        assert!(!format!("{:?}", lowered.body).contains("unsafe"));
    }

    #[test]
    fn emission_bridge_rejects_reordered_literals_with_the_same_node_count() {
        let source = "(#fn main () u64
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
        lowered.body = body.statements(&body.instructions, true);
        body.emission_types(&lowered).unwrap();
        let Statement::Return(Some(Expr::List(operands))) = &mut lowered.body[0] else {
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
        let source = "(#fn main () u64
          (#let first u64 1u64)
          (#let second u64 2u64)
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
        let source = "(#fn main () u64
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
            "(#fn main () u64 (#let-mut value u64 0u64) (#while (#u64.< value 2u64) (#set value (#u64.+.wrap value 1u64))) (#return value))",
            "(#struct Pair ((a u64) (b u64))) (#fn main () u64 (#let-mut value Pair (#struct-literal Pair ((a 1u64) (b 2u64)))) (#set-field value b 42u64) (#return (#get value b)))",
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
        let source = "(#enum Maybe ((Some u64) None))\n\
          (#fn choose ((flag bool) (input Maybe)) u64\n\
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
            Type::Bool => "bool",
            Type::Char => "char",
            Type::I8 => "i8",
            Type::I16 => "i16",
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::I128 => "i128",
            Type::Isize => "isize",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::U64 => "u64",
            Type::U128 => "u128",
            Type::Usize => "usize",
            Type::F32 => "f32",
            Type::F64 => "f64",
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
        format!("{}.{}{mode}", self.scalar_name(), self.operation.as_str())
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
    Global(GlobalId),
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
    pub span: Option<Span>,
    pub control: Control,
}

#[derive(Default)]
pub(crate) struct Body {
    pub nodes: Vec<Node>,
    pub bindings: Vec<Binding>,
    pub instructions: Vec<Instruction>,
    emission_nodes: Vec<NodeId>,
    callees: HashMap<FunctionId, String>,
    declaration_names: HashMap<DeclarationId, String>,
}

#[derive(Default)]
pub(crate) struct EmissionTypes {
    /// Checked metadata is authoritative under deterministic source identities.
    pub by_id: HashMap<ExpressionId, EmissionNode>,
    /// Temporary bridge for legacy codegen, which still visits AST references.
    pub address_to_id: HashMap<usize, ExpressionId>,
    /// Backend-created expressions have no source identity and retain a narrow
    /// address-based compatibility path.
    pub synthesized_by_address: HashMap<usize, EmissionNode>,
}

#[derive(Default)]
pub(crate) struct EmissionNode {
    pub ty: Option<Type>,
    /// Retained for the upcoming BindingId-keyed local-slot migration.
    #[allow(dead_code)]
    pub binding: Option<BindingId>,
    pub numeric: Option<NumericOperation>,
    pub callee: Option<FunctionId>,
}

impl EmissionTypes {
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
                    ..
                } => {
                    self.walk_emission_node(*pattern, order);
                    self.walk_emission_node(*value, order);
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
            NodeKind::Form { head, children, .. } if head == "unsafe" && children.len() == 2 => {
                self.walk_emission_node(children[1], order);
                return;
            }
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

    /// Bridge stable nodes into the legacy instruction selector after unsafe
    /// erasure and call-name specialization. No semantic analysis is repeated.
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
                (NodeKind::Declaration(id), Expr::Symbol(actual)) => {
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
                    matches!(items.first(), Some(Expr::Symbol(actual)) if actual == &expected)
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
                        binding,
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
            NodeKind::Declaration(id) => Expr::Symbol(self.declaration_names[id].clone()),
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
                    items[0] = Expr::Symbol(self.callees[callee].clone());
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
            } => match otherwise {
                Some(body) => Statement::LetElse {
                    pattern: expr(*pattern),
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
                    PlaceRoot::Local(id) => self.bindings[id.0].name.clone(),
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
                "  statement {:?}: {:?}",
                instruction.span, instruction.control
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
        spans: &HashMap<usize, Span>,
    ) -> Self {
        let mut builder = Builder {
            body: Body::default(),
            names: HashMap::new(),
            declarations,
            types,
            expression_ids,
            spans,
        };
        for parameter in &function.parameters {
            builder.binding(
                &parameter.name,
                resolve_type(&parameter.ty, &declarations.aliases).expect("checked parameter"),
            );
        }
        builder.body.instructions = builder.statements(&function.body);
        builder.body.emission_nodes = builder.body.emission_node_order();
        builder.body
    }
}

fn walk_expression<'a>(expression: &'a Expr, output: &mut Vec<&'a Expr>) {
    match expression {
        Expr::List(items) => {
            if items.len() == 2 && matches!(&items[0], Expr::Symbol(head) if head == "unsafe") {
                walk_expression(&items[1], output);
                return;
            }
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
                else_body,
                ..
            } => {
                walk_expression(pattern, output);
                walk_expression(value, output);
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

struct Builder<'a> {
    body: Body,
    names: HashMap<String, BindingId>,
    declarations: &'a Declarations,
    types: &'a HashMap<ExpressionId, Type>,
    expression_ids: &'a HashMap<usize, ExpressionId>,
    spans: &'a HashMap<usize, Span>,
}

impl Builder<'_> {
    fn expression_type(&self, expression: &Expr) -> Option<&Type> {
        let address = std::ptr::from_ref(expression) as usize;
        self.expression_ids
            .get(&address)
            .and_then(|id| self.types.get(id))
    }

    fn binding(&mut self, name: &str, ty: Type) -> BindingId {
        let id = BindingId(self.body.bindings.len());
        self.body.bindings.push(Binding {
            name: name.into(),
            ty,
        });
        self.names.insert(name.into(), id);
        id
    }

    fn declaration(&mut self, id: DeclarationId) -> NodeKind {
        self.body
            .declaration_names
            .entry(id)
            .or_insert_with(|| self.declarations.declaration_name(id).to_owned());
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
                let binding = self.binding(name, ty);
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
        self.record(arm, NodeKind::MatchArm { pattern, values })
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
        } else if matches!(head.as_str(), "get" | "get-payload") {
            if let (Some(owner), Some(Expr::Symbol(name))) =
                (self.body.nodes[children[1].0].ty.as_ref(), items.get(2))
            {
                let id = if head == "get" {
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
        let kind = match expression {
            Expr::Symbol(name) => {
                let binding = self
                    .expression_type(expression)
                    .is_some()
                    .then(|| self.names.get(name).copied())
                    .flatten();
                let declaration = if binding.is_none() {
                    self.expression_type(expression).and_then(|ty| {
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
                    if let Some(Expr::Symbol(head)) = items.first() {
                        if matches!(head.as_str(), "borrow" | "borrow-mut") {
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
                        let ty = self.expression_type(expression).cloned();
                        self.resolve_form(items, &children, ty.as_ref());
                        let callee = self.declarations.function_id(head);
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
                            head: head.clone(),
                            children,
                            numeric: NumericOperation::parse(head),
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
        self.record(expression, kind)
    }

    fn record(&mut self, expression: &Expr, kind: NodeKind) -> NodeId {
        let address = std::ptr::from_ref(expression) as usize;
        let id = NodeId(self.body.nodes.len());
        self.body.nodes.push(Node {
            expression_id: self.expression_ids.get(&address).copied(),
            ty: self.expression_type(expression).cloned(),
            span: self.spans.get(&address).copied(),
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
                let binding = self.binding(
                    name,
                    resolve_type(ty, &self.declarations.aliases).expect("checked local"),
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
                }
            }
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
            } => {
                let value = self.expression(value);
                let otherwise = Some(self.statements(else_body));
                let pattern_id = self.expression(pattern);
                let ty = resolve_type(ty, &self.declarations.aliases).expect("checked pattern");
                self.pattern_bindings(pattern, pattern_id, &ty, true);
                Control::Destructure {
                    pattern: pattern_id,
                    value,
                    ty,
                    mutable: false,
                    otherwise,
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
        Instruction {
            span: self
                .spans
                .get(&(std::ptr::from_ref(statement) as usize))
                .copied(),
            control,
        }
    }
}
