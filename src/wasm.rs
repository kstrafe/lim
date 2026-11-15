//! Small, dependency-free WebAssembly backend for the teaching playground.
//! It emits from validated typed bodies and rejects unsupported operations.
use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::typed_body::{
    Body, Control, Instruction, NodeId, NodeKind, NumericOpcode as Op, NumericOperation, Overflow,
    PlaceRoot, Projection,
};
use crate::typed_ir::{Declarations, FunctionId};
use crate::{
    CheckedProgram, CompileConfig, Diagnostic, DiagnosticCode, Expr, Item, Program, Span, Type,
};

pub const MAX_SOURCE_BYTES: usize = 32 * 1024;
const MAX_FUNCTIONS: usize = 64;
const MAX_NODES: usize = 16_384;
const FILENAME: &str = "/playground/main.lim";

type Error = (String, Option<Span>);
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnType {
    Unit,
    Bool,
    Unsigned64,
    Signed64,
}

pub struct Module {
    pub bytes: Vec<u8>,
    pub return_type: ReturnType,
}

fn source_program(source: &str) -> std::result::Result<Program, Diagnostic> {
    if source.len() > MAX_SOURCE_BYTES {
        return Err(Diagnostic::new(
            DiagnosticCode::Parse,
            "playground source exceeds 32 KiB",
        ));
    }
    // The browser interface is deliberately a single in-memory source file.
    // Reject authored file access on native hosts too, before the loader runs.
    fn files(node: &crate::SpannedExpr) -> Option<Span> {
        if matches!(&node.expr, Expr::Symbol(name) if name == "#alias" || name.contains(".lim::") || name.starts_with("project::"))
        {
            return Some(node.span);
        }
        node.children.iter().find_map(files)
    }
    let tokens = crate::lex(source).map_err(|error| {
        crate::source_error::SourceError::new(error.message, DiagnosticCode::Lex)
            .at(error.span)
            .diagnostic()
            .with_source(FILENAME, source)
    })?;
    let forms = crate::Parser::new(&tokens)
        .with_source(source)
        .run()
        .map_err(|error| {
            crate::source_error::SourceError::new(error.message, DiagnosticCode::Parse)
                .at(error.span)
                .diagnostic()
                .with_source(FILENAME, source)
        })?;
    if let Some(span) = forms.iter().find_map(files) {
        let mut diagnostic = Diagnostic::new(
            DiagnosticCode::Parse,
            "the playground accepts one source file; file imports are unavailable",
        )
        .with_source(FILENAME, source);
        diagnostic.span = Some(span);
        return Err(diagnostic);
    }
    let mut config = CompileConfig::default();
    config.set("contracts", "check");
    crate::parse_program_in_directory(
        source,
        Path::new("/playground"),
        Some(Path::new(FILENAME)),
        &config,
        None,
    )
    .map_err(|error| error.diagnostic())
}

fn validation(program: &Program) -> std::result::Result<CheckedProgram<'_>, Diagnostic> {
    CheckedProgram::validate_with_span(program).map_err(|(message, code, span, labels)| {
        let mut error = crate::source_error::SourceError::new(message, code);
        if let Some(span) = span {
            error = error.at(span);
        }
        for (span, message) in labels {
            error = error.with_label(span, message);
        }
        error.attach(&program.source_files).diagnostic()
    })
}

/// Run the normal type, contract, ownership and borrow checker without a filesystem cache.
pub fn check(source: &str) -> std::result::Result<(), Diagnostic> {
    let program = source_program(source)?;
    validation(&program).map(|_| ())
}

/// Compile a checked scalar program to a standalone module exporting `main`.
/// The generated program has no imports, memory, WASI or host capabilities.
/// Contract audit assertions are enabled. Unsupported features fail explicitly.
pub fn compile(source: &str) -> std::result::Result<Module, Diagnostic> {
    let program = source_program(source)?;
    let checked = validation(&program)?;
    emit(&checked).map_err(|(message, span)| {
        let mut error = crate::source_error::SourceError::new(message, DiagnosticCode::Codegen);
        if let Some(span) = span {
            error = error.at(span);
        }
        error.attach(&program.source_files).diagnostic()
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Value {
    Unit,
    Bool,
    Signed,
    Unsigned,
    Never,
}
impl Value {
    fn byte(self) -> u8 {
        match self {
            Self::Bool => 0x7f,
            Self::Signed | Self::Unsigned => 0x7e,
            _ => 0x40,
        }
    }
    fn scalar(self) -> bool {
        !matches!(self, Self::Unit | Self::Never)
    }
}
fn value(ty: &Type, declarations: &Declarations) -> Result<Value> {
    let ty = crate::typed_ir::resolve_type(ty, &declarations.aliases).map_err(|e| (e, None))?;
    match ty {
        Type::Unit => Ok(Value::Unit), Type::Never => Ok(Value::Never), Type::Bool => Ok(Value::Bool),
        Type::U64 | Type::Usize => Ok(Value::Unsigned), Type::I64 | Type::Isize => Ok(Value::Signed),
        _ => Err((format!("WebAssembly teaching backend does not yet support type {}; use #u64, #i64, #usize, #isize, #bool or ()", crate::type_source(&ty)), None)),
    }
}
fn unsigned(mut n: usize, bytes: &mut Vec<u8>) {
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        bytes.push(b | if n == 0 { 0 } else { 128 });
        if n == 0 {
            break;
        }
    }
}
fn signed(mut n: i64, bytes: &mut Vec<u8>) {
    loop {
        let b = (n & 127) as u8;
        n >>= 7;
        let done = (n == 0 && b & 64 == 0) || (n == -1 && b & 64 != 0);
        bytes.push(b | if done { 0 } else { 128 });
        if done {
            break;
        }
    }
}
fn section(id: u8, content: Vec<u8>, module: &mut Vec<u8>) {
    module.push(id);
    unsigned(content.len(), module);
    module.extend(content);
}
fn emit(checked: &CheckedProgram<'_>) -> Result<Module> {
    let p = checked.program();
    let d = checked.declarations();
    let entry = p
        .items
        .iter()
        .find_map(|item| match item {
            Item::Function(f) if crate::file_access::local_name(&f.name) == "main" => Some(f),
            _ => None,
        })
        .ok_or_else(|| {
            (
                "a runnable playground program needs a main function".into(),
                None,
            )
        })?;
    if !entry.parameters.is_empty() || entry.external || entry.unsafe_call {
        return Err((
            "playground main must be a safe, defined function with no parameters".into(),
            None,
        ));
    }
    let main_value = value(&entry.return_type, d)?;
    let return_type = match main_value {
        Value::Unit => ReturnType::Unit,
        Value::Bool => ReturnType::Bool,
        Value::Unsigned => ReturnType::Unsigned64,
        Value::Signed => ReturnType::Signed64,
        Value::Never => return Err(("playground main must return a value or ()".into(), None)),
    };
    let entry_id = d.function_id(&entry.name).unwrap();
    let mut needed = HashSet::new();
    let mut queue = vec![entry_id];
    while let Some(id) = queue.pop() {
        if !needed.insert(id) {
            continue;
        }
        if needed.len() > MAX_FUNCTIONS {
            return Err((
                "playground output exceeds 64 reachable functions".into(),
                None,
            ));
        }
        let name = d.function_name(id).unwrap();
        let body = d.bodies.get(name).ok_or_else(|| {
            (
                format!("WebAssembly teaching backend cannot call external function '{name}'"),
                None,
            )
        })?;
        if body.nodes.len() > MAX_NODES {
            return Err(("playground function exceeds 16384 typed nodes".into(), None));
        }
        queue.extend(body.nodes.iter().filter_map(|node| match node.kind {
            NodeKind::Form {
                callee: Some(id), ..
            } => Some(id),
            _ => None,
        }));
    }
    let functions: Vec<_> = p
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(f) => d
                .function_id(&f.name)
                .filter(|id| needed.contains(id))
                .map(|id| (id, f)),
            _ => None,
        })
        .collect();
    let indices: HashMap<_, _> = functions
        .iter()
        .enumerate()
        .map(|(index, (id, _))| (*id, index))
        .collect();
    let mut types = Vec::new();
    let mut declarations = Vec::new();
    let mut code = Vec::new();
    unsigned(functions.len(), &mut types);
    unsigned(functions.len(), &mut declarations);
    unsigned(functions.len(), &mut code);
    for (index, (_, function)) in functions.iter().enumerate() {
        let parameters = function
            .parameters
            .iter()
            .map(|p| value(&p.ty, d))
            .collect::<Result<Vec<_>>>()?;
        let result = value(&function.return_type, d)?;
        types.push(0x60);
        unsigned(parameters.iter().filter(|v| v.scalar()).count(), &mut types);
        types.extend(parameters.iter().filter(|v| v.scalar()).map(|v| v.byte()));
        unsigned(usize::from(result.scalar()), &mut types);
        if result.scalar() {
            types.push(result.byte());
        }
        unsigned(index, &mut declarations);
        let body = &d.bodies[&function.name];
        let mut emitter = Emitter::new(body, d, &indices)?;
        emitter.instructions(&body.instructions, false)?;
        // Explicit returns are checked above; keep the fallthrough polymorphic.
        emitter.code.extend([0x00, 0x0b]);
        let mut locals = Vec::new();
        unsigned(emitter.locals.len(), &mut locals);
        for ty in emitter.locals {
            locals.extend([1, ty]);
        }
        locals.extend(emitter.code);
        unsigned(locals.len(), &mut code);
        code.extend(locals);
    }
    let mut bytes = b"\0asm\x01\0\0\0".to_vec();
    section(1, types, &mut bytes);
    section(3, declarations, &mut bytes);
    let mut exports = vec![1, 4, b'm', b'a', b'i', b'n', 0];
    unsigned(indices[&entry_id], &mut exports);
    section(7, exports, &mut bytes);
    section(10, code, &mut bytes);
    Ok(Module { bytes, return_type })
}

#[derive(Clone, Copy)]
enum Label {
    Other,
    Break,
    Continue,
}
struct Emitter<'a> {
    body: &'a Body,
    declarations: &'a Declarations,
    functions: &'a HashMap<FunctionId, usize>,
    bindings: Vec<Option<usize>>,
    locals: Vec<u8>,
    parameter_count: usize,
    labels: Vec<Label>,
    code: Vec<u8>,
}
impl<'a> Emitter<'a> {
    fn new(
        body: &'a Body,
        declarations: &'a Declarations,
        functions: &'a HashMap<FunctionId, usize>,
    ) -> Result<Self> {
        let mut bindings = Vec::new();
        let mut locals = Vec::new();
        let mut parameters = 0;
        let mut index = 0;
        for (i, binding) in body.bindings.iter().enumerate() {
            let v = value(&binding.ty, declarations).map_err(|(e, _)| (e, binding.span))?;
            if v.scalar() {
                bindings.push(Some(index));
                index += 1;
                if i < body.parameter_count {
                    parameters += 1;
                } else {
                    locals.push(v.byte());
                }
            } else {
                bindings.push(None);
            }
        }
        Ok(Self {
            body,
            declarations,
            functions,
            bindings,
            locals,
            parameter_count: parameters,
            labels: Vec::new(),
            code: Vec::new(),
        })
    }
    fn error(&self, id: NodeId, message: impl Into<String>) -> Error {
        (message.into(), self.body.nodes[id.0].span)
    }
    fn kind(&self, id: NodeId) -> Result<Value> {
        self.body.nodes[id.0]
            .ty
            .as_ref()
            .map_or(Ok(Value::Unit), |ty| value(ty, self.declarations))
            .map_err(|(e, _)| self.error(id, e))
    }
    fn indexed(&mut self, opcode: u8, index: usize) {
        self.code.push(opcode);
        unsigned(index, &mut self.code);
    }
    fn constant(&mut self, n: i64, v: Value) {
        self.code.push(if v == Value::Bool { 0x41 } else { 0x42 });
        signed(n, &mut self.code);
    }
    fn temporary(&mut self, v: Value) -> usize {
        let id = self.parameter_count + self.locals.len();
        self.locals.push(v.byte());
        id
    }
    fn open(&mut self, opcode: u8, v: Value, label: Label) {
        self.code.extend([opcode, v.byte()]);
        self.labels.push(label);
    }
    fn close(&mut self) {
        self.code.push(0x0b);
        self.labels.pop();
    }
    fn branch(&mut self, label: Label) -> Result<()> {
        let depth = self
            .labels
            .iter()
            .rev()
            .position(|l| {
                matches!(
                    (l, label),
                    (Label::Break, Label::Break) | (Label::Continue, Label::Continue)
                )
            })
            .ok_or_else(|| ("WebAssembly loop branch has no target".into(), None))?;
        self.indexed(0x0c, depth);
        Ok(())
    }
    fn instructions(&mut self, instructions: &[Instruction], result: bool) -> Result<()> {
        for (i, instruction) in instructions.iter().enumerate() {
            match &instruction.control {
                Control::Bind(binding, node, _) => { self.expression(*node)?; if let Some(index) = self.bindings[binding.0] { self.indexed(0x21, index); } }
                Control::Destructure { pattern, value, otherwise: None, failure_pattern: None, .. } => self.destructure(*pattern, *value)?,
                Control::Assign(PlaceRoot::Local(binding), Projection::Local, node) => { self.expression(*node)?; if let Some(index) = self.bindings[binding.0] { self.indexed(0x21, index); } }
                Control::Return(node) => { if let Some(node) = node { self.expression(*node)?; } self.code.push(0x0f); }
                Control::Evaluate(node) => { self.expression(*node)?; if !(result && i + 1 == instructions.len()) && self.kind(*node)?.scalar() { self.code.push(0x1a); } }
                Control::While(condition, body) => self.loop_body(Some(*condition), body, None)?,
                Control::Loop(body) => self.loop_body(None, body, None)?,
                Control::For(init, condition, step, body) => { self.instructions(std::slice::from_ref(init), false)?; self.loop_body(Some(*condition), body, Some(step))?; }
                Control::Break(None, None) => self.branch(Label::Break)?,
                Control::Continue(None) => self.branch(Label::Continue)?,
                _ => return Err(("WebAssembly teaching backend does not yet support this statement (destructuring, aggregate mutation, labels or value-carrying break)".into(), instruction.span)),
            }
        }
        Ok(())
    }
    // #for-range binds its once-evaluated bounds using a scalar tuple. Lower
    // that immediate constructor directly to locals, without aggregate memory.
    fn destructure(&mut self, pattern: NodeId, node: NodeId) -> Result<()> {
        let NodeKind::Form { head, children, .. } = &self.body.nodes[node.0].kind else {
            return Err(self.error(
                node,
                "WebAssembly tuple binding needs an immediate constructor",
            ));
        };
        if head != "tuple" {
            return Err(self.error(node, "unsupported WebAssembly destructuring"));
        }
        let parts = match &self.body.nodes[pattern.0].kind {
            NodeKind::Form { head, children, .. } if head == "tuple" => &children[1..],
            NodeKind::Syntax(children) => &children[1..],
            _ => return Err(self.error(pattern, "unsupported WebAssembly tuple pattern")),
        };
        let args = &children[2..];
        if args.len() != parts.len() {
            return Err(self.error(pattern, "unsupported WebAssembly tuple shape"));
        }
        let mut staged = Vec::new();
        for arg in args {
            let v = self.kind(*arg)?;
            self.expression(*arg)?;
            let temp = if v.scalar() {
                let temp = self.temporary(v);
                self.indexed(0x21, temp);
                Some(temp)
            } else {
                None
            };
            staged.push(temp);
        }
        for (part, temp) in parts.iter().zip(staged) {
            match self.body.nodes[part.0].kind {
                NodeKind::Symbol {
                    binding: Some(binding),
                    ..
                } => {
                    if let (Some(temp), Some(local)) = (temp, self.bindings[binding.0]) {
                        self.indexed(0x20, temp);
                        self.indexed(0x21, local);
                    }
                }
                NodeKind::Symbol { ref name, .. } if name == "_" => {}
                _ => {
                    return Err(self.error(*part, "WebAssembly tuple patterns need scalar bindings"))
                }
            }
        }
        Ok(())
    }
    fn loop_body(
        &mut self,
        condition: Option<NodeId>,
        body: &[Instruction],
        step: Option<&Instruction>,
    ) -> Result<()> {
        self.open(0x02, Value::Unit, Label::Break);
        self.open(
            0x03,
            Value::Unit,
            if step.is_some() {
                Label::Other
            } else {
                Label::Continue
            },
        );
        if let Some(condition) = condition {
            self.expression(condition)?;
            self.code.push(0x45);
            self.indexed(0x0d, 1);
        }
        if step.is_some() {
            self.open(0x02, Value::Unit, Label::Continue);
        }
        self.instructions(body, false)?;
        if let Some(step) = step {
            self.close();
            self.instructions(std::slice::from_ref(step), false)?;
        }
        self.indexed(0x0c, 0);
        self.close();
        self.close();
        Ok(())
    }
    fn expression(&mut self, id: NodeId) -> Result<()> {
        let node = &self.body.nodes[id.0];
        let kind = self.kind(id)?;
        match &node.kind {
            NodeKind::Symbol { binding: Some(binding), .. } => { if let Some(index) = self.bindings[binding.0] { self.indexed(0x20, index); } }
            NodeKind::Symbol { name, .. } if matches!(name.as_str(), "true" | "false") => self.constant(i64::from(name == "true"), Value::Bool),
            NodeKind::Literal(literal) => self.literal(literal, kind, id)?,
            NodeKind::Syntax(children) if children.is_empty() && kind == Value::Unit => {},
            NodeKind::Block(instructions) => { self.open(0x02, kind, Label::Other); self.instructions(instructions, kind.scalar())?; self.close(); }
            NodeKind::Loop(instructions) if !kind.scalar() => self.loop_body(None, instructions, None)?,
            NodeKind::If { condition, then_value, else_value, .. } => {
                self.expression(*condition)?; self.open(0x04, kind, Label::Other); self.expression(*then_value)?;
                if let Some(other) = else_value { self.code.push(0x05); self.expression(*other)?; }
                self.close();
            }
            NodeKind::Form { children, numeric: Some(operation), .. } => self.numeric(id, operation, &children[1..])?,
            NodeKind::Form { children, callee: Some(callee), argument_source_order, .. } => {
                let mut slots = vec![None; children.len() - 1];
                for index in 0..slots.len() {
                    let index = argument_source_order.as_ref().map_or(index, |order| order[index]);
                    let argument = children[index + 1];
                    self.expression(argument)?;
                    let kind = self.kind(argument)?;
                    if kind.scalar() {
                        let slot = self.temporary(kind);
                        self.indexed(0x21, slot);
                        slots[index] = Some(slot);
                    }
                }
                for slot in slots.into_iter().flatten() { self.indexed(0x20, slot); }
                let index = self.functions.get(callee).copied().ok_or_else(|| self.error(id, "unsupported WebAssembly callee"))?;
                self.indexed(0x10, index);
            }
            NodeKind::Form { head, children, .. } => match head.as_str() {
                "+" | "<" => {
                    let operand_type = self.body.nodes[children[1].0].ty.clone().ok_or_else(|| self.error(id, "missing checked range operand type"))?;
                    let operation = NumericOperation { operand_type, operation: if head == "+" { Op::Add } else { Op::Less }, overflow: if head == "+" { Overflow::Wrap } else { Overflow::NotApplicable } };
                    self.numeric(id, &operation, &children[1..])?;
                }
                "literal" => { let child = children.last().ok_or_else(|| self.error(id, "malformed literal"))?; if let NodeKind::Literal(literal) = &self.body.nodes[child.0].kind { self.literal(literal, kind, id)?; } else { return Err(self.error(id, "unsupported literal")); } }
                "panic" | "unreachable" => self.code.push(0x00),
                "assert" => { self.expression(children[1])?; self.code.push(0x45); self.open(0x04, Value::Unit, Label::Other); self.code.push(0x00); self.close(); }
                "forget" | "drop" => { self.expression(children[1])?; if self.kind(children[1])?.scalar() { self.code.push(0x1a); } }
                "unsafe" | "clone" => self.expression(children[1])?,
                "as" => { let from = self.kind(children[1])?; self.expression(children[1])?; if from == Value::Bool && matches!(kind, Value::Signed | Value::Unsigned) { self.code.push(0xad); } else if from.byte() != kind.byte() { return Err(self.error(id, "unsupported WebAssembly scalar conversion")); } }
                _ => return Err(self.error(id, format!("WebAssembly teaching backend does not yet support #{head}"))),
            },
            _ => return Err(self.error(id, "WebAssembly teaching backend does not yet support this expression (globals, aggregates, references or matching)")),
        }
        // A structured block's `end` restores its declared stack shape even
        // when every branch returns. Retain the checker's never type in the
        // enclosing Wasm expression as well.
        if kind == Value::Never {
            self.code.push(0x00);
        }
        Ok(())
    }
    fn literal(&mut self, literal: &Expr, kind: Value, id: NodeId) -> Result<()> {
        match literal {
            Expr::Integer(n) => self.constant(*n as i64, kind),
            Expr::UnsignedInteger(n) => self.constant(*n as i64, kind),
            Expr::Symbol(name) if matches!(name.as_str(), "true" | "false") => {
                self.constant(i64::from(name == "true"), Value::Bool)
            }
            _ => return Err(self.error(id, "unsupported WebAssembly literal")),
        }
        Ok(())
    }
    fn numeric(&mut self, id: NodeId, op: &NumericOperation, args: &[NodeId]) -> Result<()> {
        let v = value(&op.operand_type, self.declarations).map_err(|(e, _)| self.error(id, e))?;
        if op.overflow == Overflow::Saturate {
            return Err(self.error(
                id,
                "WebAssembly teaching backend does not yet support saturating arithmetic",
            ));
        }
        if matches!(op.operation, Op::LogicalAnd | Op::LogicalOr) {
            self.expression(args[0])?;
            self.open(0x04, Value::Bool, Label::Other);
            if op.operation == Op::LogicalAnd {
                self.expression(args[1])?;
                self.code.push(0x05);
                self.constant(0, Value::Bool);
            } else {
                self.constant(1, Value::Bool);
                self.code.push(0x05);
                self.expression(args[1])?;
            }
            self.close();
            return Ok(());
        }
        if op.operation == Op::Not {
            self.expression(args[0])?;
            if v == Value::Bool {
                self.code.push(0x45);
            } else {
                self.constant(-1, v);
                self.code.push(0x85);
            }
            return Ok(());
        }
        if op.operation == Op::Subtract && args.len() == 1 {
            self.constant(0, v);
            self.expression(args[0])?;
            self.code.push(0x7d);
            return Ok(());
        }
        let reverse = matches!(&self.body.nodes[id.0].kind, NodeKind::Form { argument_source_order: Some(order), .. } if order == &[1, 0]);
        if reverse {
            self.expression(args[1])?;
            let right = self.temporary(v);
            self.indexed(0x21, right);
            self.expression(args[0])?;
            self.indexed(0x20, right);
        } else {
            self.expression(args[0])?;
            self.expression(args[1])?;
        }
        if matches!(op.operation, Op::ShiftLeft | Op::ShiftRight) {
            let right = self.temporary(v);
            self.indexed(0x22, right);
            self.constant(64, v);
            self.code.push(0x5a); // i64.ge_u
            self.open(0x04, Value::Unit, Label::Other);
            self.code.push(0x00);
            self.close();
            self.indexed(0x20, right);
        }
        // Wrapping signed division defines MIN / -1; plain Wasm division traps.
        if v == Value::Signed && matches!(op.operation, Op::Divide | Op::Remainder) {
            let right = self.temporary(v);
            self.indexed(0x21, right);
            let left = self.temporary(v);
            self.indexed(0x21, left);
            self.indexed(0x20, left);
            self.constant(i64::MIN, v);
            self.code.push(0x51);
            self.indexed(0x20, right);
            self.constant(-1, v);
            self.code.extend([0x51, 0x71]);
            self.open(0x04, v, Label::Other);
            if op.overflow == Overflow::Wrap {
                self.constant(
                    if op.operation == Op::Divide {
                        i64::MIN
                    } else {
                        0
                    },
                    v,
                );
            } else {
                self.code.push(0x00);
            }
            self.code.push(0x05);
            self.indexed(0x20, left);
            self.indexed(0x20, right);
            self.code.push(if op.operation == Op::Divide {
                0x7f
            } else {
                0x81
            });
            self.close();
            return Ok(());
        }
        if v == Value::Bool
            && !matches!(
                op.operation,
                Op::Equal | Op::NotEqual | Op::BitAnd | Op::BitOr | Op::BitXor
            )
        {
            return Err(self.error(id, "unsupported WebAssembly Boolean operation"));
        }
        let signed = v == Value::Signed;
        let opcode = match (v, op.operation) {
            (Value::Bool, Op::Equal) => 0x46,
            (Value::Bool, Op::NotEqual) => 0x47,
            (Value::Bool, Op::BitAnd) => 0x71,
            (Value::Bool, Op::BitOr) => 0x72,
            (Value::Bool, Op::BitXor) => 0x73,
            (_, Op::Add) => 0x7c,
            (_, Op::Subtract) => 0x7d,
            (_, Op::Multiply) => 0x7e,
            (_, Op::Divide) => 0x80,
            (_, Op::Remainder) => 0x82,
            (_, Op::BitAnd) => 0x83,
            (_, Op::BitOr) => 0x84,
            (_, Op::BitXor) => 0x85,
            (_, Op::ShiftLeft) => 0x86,
            (_, Op::ShiftRight) => {
                if signed {
                    0x87
                } else {
                    0x88
                }
            }
            (_, Op::Equal) => 0x51,
            (_, Op::NotEqual) => 0x52,
            (_, Op::Less) => {
                if signed {
                    0x53
                } else {
                    0x54
                }
            }
            (_, Op::Greater) => {
                if signed {
                    0x55
                } else {
                    0x56
                }
            }
            (_, Op::LessEqual) => {
                if signed {
                    0x57
                } else {
                    0x58
                }
            }
            (_, Op::GreaterEqual) => {
                if signed {
                    0x59
                } else {
                    0x5a
                }
            }
            _ => return Err(self.error(id, "unsupported WebAssembly numeric operation")),
        };
        self.code.push(opcode);
        Ok(())
    }
}
