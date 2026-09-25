//! Typed, source-located body arena. Dense IDs survive copying and lowering;
//! the address index is only a bridge to the immutably borrowed legacy AST.
use std::collections::HashMap;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nodes_keep_contextual_types_numeric_modes_and_reordered_call_spans() {
        let source = "(#fn add ((left u32) (right u32)) u32 (#return (#u32.+.saturate left right)))
          (#fn main () u32 (#let x u32 40) (#return (#call add (#fn-args (right 2) (left x)))))";
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
        let NodeKind::Form { children, .. } = &call.kind else {
            unreachable!()
        };
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
}

use crate::typed_ir::{resolve_type, Declarations, FunctionId};
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NumericOperation {
    pub operand_type: Type,
    pub operation: String,
    pub overflow: Overflow,
}

impl NumericOperation {
    fn spelling(&self) -> String {
        let scalar = match self.operand_type {
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
        };
        let mode = match self.overflow {
            Overflow::NotApplicable => "",
            Overflow::Wrap => ".wrap",
            Overflow::Saturate => ".saturate",
        };
        format!("{scalar}.{}{mode}", self.operation)
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
        if !matches!(
            operation,
            "+" | "-"
                | "*"
                | "/"
                | "%"
                | "&"
                | "|"
                | "^"
                | "<<"
                | ">>"
                | "<"
                | "<="
                | ">"
                | ">="
                | "=="
                | "!="
                | "!"
                | "&&"
                | "||"
        ) {
            return None;
        }
        let overflow = match mode {
            "wrap" => Overflow::Wrap,
            "saturate" => Overflow::Saturate,
            "" => Overflow::NotApplicable,
            _ => return None,
        };
        Some(Self {
            operand_type,
            operation: operation.into(),
            overflow,
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) enum NodeKind {
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
    },
    Block(Vec<Instruction>),
    Loop(Vec<Instruction>),
    Labeled(String, NodeId),
    Syntax(Vec<NodeId>),
    Quoted(&'static str, NodeId),
}

#[derive(Clone, Debug)]
pub(crate) struct Node {
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
    Assign(String, Projection, NodeId),
    While(NodeId, Vec<Instruction>),
    Loop(Vec<Instruction>),
    For(Box<Instruction>, NodeId, Box<Instruction>, Vec<Instruction>),
    Labeled(String, Box<Instruction>),
    Return(Option<NodeId>),
    Break(Option<String>, Option<NodeId>),
    Continue(Option<String>),
    Evaluate(NodeId),
}

#[derive(Clone, Debug)]
pub(crate) enum Projection {
    Local,
    Array(NodeId),
    Field(String),
    Tuple(usize),
    Payload(String, usize),
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
    by_address: HashMap<usize, NodeId>,
    emission_nodes: Vec<NodeId>,
    callees: HashMap<FunctionId, String>,
}

impl Body {
    /// Bridge stable nodes into the legacy instruction selector after unsafe
    /// erasure and call-name specialization. No semantic analysis is repeated.
    pub fn emission_types(&self, lowered: &Function) -> Result<HashMap<usize, Type>, String> {
        let mut after = Vec::new();
        walk_statements(&lowered.body, &mut after);
        if self.emission_nodes.len() != after.len() {
            return Err(format!(
                "internal error: typed body shape changed for '{}'",
                lowered.name
            ));
        }
        Ok(self
            .emission_nodes
            .iter()
            .zip(after)
            .filter_map(|(id, target)| {
                self.nodes[id.0]
                    .ty
                    .clone()
                    .map(|ty| (std::ptr::from_ref(target) as usize, ty))
            })
            .collect())
    }
    pub fn syntax(&self, id: NodeId, erase_unsafe: bool) -> Expr {
        match &self.nodes[id.0].kind {
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
            Control::Assign(name, projection, value) => {
                let name = name.clone();
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
                        field: field.clone(),
                    },
                    Projection::Tuple(index) => Statement::TupleAssign {
                        name,
                        value,
                        index: *index,
                    },
                    Projection::Payload(variant, index) => Statement::EnumPayloadAssign {
                        name,
                        value,
                        variant: variant.clone(),
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

    pub fn node_for(&self, expression: &Expr) -> Option<(NodeId, &Node)> {
        let id = *self
            .by_address
            .get(&(std::ptr::from_ref(expression) as usize))?;
        Some((id, &self.nodes[id.0]))
    }

    pub fn lower(
        function: &Function,
        declarations: &Declarations,
        types: &HashMap<usize, Type>,
        spans: &HashMap<usize, Span>,
    ) -> Self {
        let mut builder = Builder {
            body: Body::default(),
            names: HashMap::new(),
            declarations,
            types,
            spans,
        };
        for parameter in &function.parameters {
            builder.binding(
                &parameter.name,
                resolve_type(&parameter.ty, &declarations.aliases).expect("checked parameter"),
            );
        }
        builder.body.instructions = builder.statements(&function.body);
        let mut expressions = Vec::new();
        walk_statements(&function.body, &mut expressions);
        builder.body.emission_nodes = expressions
            .iter()
            .map(|expression| {
                builder
                    .body
                    .node_for(expression)
                    .expect("lowered expression")
                    .0
            })
            .collect();
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
    types: &'a HashMap<usize, Type>,
    spans: &'a HashMap<usize, Span>,
}

impl Builder<'_> {
    fn binding(&mut self, name: &str, ty: Type) -> BindingId {
        if let Some(id) = self.names.get(name) {
            return *id;
        }
        let id = BindingId(self.body.bindings.len());
        self.body.bindings.push(Binding {
            name: name.into(),
            ty,
        });
        self.names.insert(name.into(), id);
        id
    }

    fn expression(&mut self, expression: &Expr) -> NodeId {
        let address = std::ptr::from_ref(expression) as usize;
        let ty = self.types.get(&address).cloned();
        let kind = match expression {
            Expr::Symbol(name) => {
                let binding = if let Some(ty) = ty.as_ref().filter(|_| {
                    !self.declarations.globals.contains_key(name)
                        && name != "true"
                        && name != "false"
                        && !self
                            .declarations
                            .enums
                            .values()
                            .any(|variants| variants.iter().any(|v| v.name == *name))
                }) {
                    Some(self.binding(name, ty.clone()))
                } else {
                    None
                };
                NodeKind::Symbol {
                    name: name.clone(),
                    binding,
                }
            }
            Expr::List(items) => {
                let children = items.iter().map(|child| self.expression(child)).collect();
                if let Some(Expr::Symbol(head)) = items.first() {
                    if let Some(callee) = self.declarations.function_id(head) {
                        self.body.callees.insert(callee, head.clone());
                    }
                    NodeKind::Form {
                        head: head.clone(),
                        children,
                        numeric: NumericOperation::parse(head),
                        callee: self.declarations.function_id(head),
                    }
                } else {
                    NodeKind::Syntax(children)
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
        let id = NodeId(self.body.nodes.len());
        self.body.nodes.push(Node {
            ty,
            span: self.spans.get(&address).copied(),
            kind,
        });
        self.body.by_address.insert(address, id);
        id
    }

    fn statements(&mut self, statements: &[Statement]) -> Vec<Instruction> {
        statements
            .iter()
            .map(|statement| self.statement(statement))
            .collect()
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
            } => Control::Destructure {
                pattern: self.expression(pattern),
                value: self.expression(value),
                ty: resolve_type(ty, &self.declarations.aliases).expect("checked pattern"),
                mutable: *mutable,
                otherwise: None,
            },
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
            } => Control::Destructure {
                pattern: self.expression(pattern),
                value: self.expression(value),
                ty: resolve_type(ty, &self.declarations.aliases).expect("checked pattern"),
                mutable: false,
                otherwise: Some(self.statements(else_body)),
            },
            Statement::Assign { name, value } => {
                Control::Assign(name.clone(), Projection::Local, self.expression(value))
            }
            Statement::FieldAssign { name, field, value } => Control::Assign(
                name.clone(),
                Projection::Field(field.clone()),
                self.expression(value),
            ),
            Statement::TupleAssign { name, index, value } => Control::Assign(
                name.clone(),
                Projection::Tuple(*index),
                self.expression(value),
            ),
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => Control::Assign(
                name.clone(),
                Projection::Payload(variant.clone(), *index),
                self.expression(value),
            ),
            Statement::ArrayAssign { name, index, value } => Control::Assign(
                name.clone(),
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
            } => Control::For(
                Box::new(self.statement(init)),
                self.expression(condition),
                Box::new(self.statement(step)),
                self.statements(body),
            ),
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
