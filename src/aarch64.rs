//! Direct checked-IR lowering to static AArch64 Linux code.
//!
//! Scalars use AAPCS64 integer registers/stack alignment. Lim aggregates use
//! private indirect parameters and x8 results; this is not a foreign C ABI.
//! Every unsupported operation is an error, never an x86 fallback.
use crate::typed_body::{
    Body, Control, Instruction, NodeId, NodeKind, NumericOpcode as Op, NumericOperation, Overflow,
    PlaceRoot, Projection,
};
use crate::typed_ir::{resolve_type, DeclarationId, Declarations, FunctionId};
use crate::{CheckedProgram, Expr, Item, Type};
use std::collections::{HashMap, HashSet};

#[path = "aarch64_elf.rs"]
mod elf;
#[path = "aarch64_encoder.rs"]
pub mod encoder;
use encoder::{Condition as C, Encoder, Label};

const MAGIC: &str = "// lim-aarch64-v1\n";
const MAX_FRAME: usize = 16 * 1024 * 1024;
type Result<T> = std::result::Result<T, BackendError>;

struct BackendError {
    message: String,
    span: Option<crate::Span>,
}
impl BackendError {
    fn at(mut self, span: Option<crate::Span>) -> Self {
        if self.span.is_none() {
            self.span = span;
        }
        self
    }
}
impl From<String> for BackendError {
    fn from(message: String) -> Self {
        Self {
            message,
            span: None,
        }
    }
}
impl From<&str> for BackendError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}
impl From<BackendError> for String {
    fn from(error: BackendError) -> Self {
        error.message
    }
}

pub fn compile(program: &crate::Program) -> std::result::Result<String, String> {
    let checked = CheckedProgram::validate(program)?;
    generate_checked_assembly(&checked, None).map_err(String::from)
}

pub(crate) fn generate_checked_assembly(
    checked: &CheckedProgram<'_>,
    retained: Option<&HashSet<String>>,
) -> std::result::Result<String, crate::source_error::SourceError> {
    generate(checked, retained).map_err(|error| {
        let mut source =
            crate::source_error::SourceError::new(error.message, crate::DiagnosticCode::Codegen);
        if let Some(span) = error
            .span
            .or_else(|| checked.program().declaration_spans.get("main").copied())
        {
            source = source.at(span);
        }
        source
    })
}

fn unsupported(what: impl std::fmt::Display) -> BackendError {
    format!("AArch64 Linux backend does not support {what}").into()
}

fn scalar(ty: &Type) -> Option<(usize, bool)> {
    Some(match ty {
        Type::Bool => (1, false),
        Type::Char | Type::U32 => (32, false),
        Type::I8 => (8, true),
        Type::U8 => (8, false),
        Type::I16 => (16, true),
        Type::U16 => (16, false),
        Type::I32 => (32, true),
        Type::I64 | Type::Isize => (64, true),
        Type::U64 | Type::Usize => (64, false),
        Type::Reference { .. } | Type::PinnedReference { .. } | Type::RawPointer { .. } => {
            (64, false)
        }
        _ => return None,
    })
}

struct Layout<'a> {
    declarations: &'a Declarations,
}
impl Layout<'_> {
    fn resolve(&self, ty: &Type) -> Result<Type> {
        resolve_type(ty, &self.declarations.aliases).map_err(Into::into)
    }
    fn fields(&self, ty: &Type) -> Result<Vec<Type>> {
        match self.resolve(ty)? {
            Type::Tuple(fields) => Ok(fields),
            Type::Named(name) => self
                .declarations
                .structs
                .get(&name)
                .map(|fields| fields.iter().map(|f| f.ty.clone()).collect())
                .ok_or_else(|| unsupported(format!("struct layout {name}"))),
            other => Err(unsupported(format!("field layout {other:?}"))),
        }
    }
    fn words(&self, ty: &Type) -> Result<usize> {
        self.words_inner(ty, 0)
    }
    fn words_inner(&self, ty: &Type, depth: usize) -> Result<usize> {
        if depth > 128 {
            return Err(unsupported("recursive or deeply nested layout"));
        }
        let ty = self.resolve(ty)?;
        if scalar(&ty).is_some() {
            return Ok(1);
        }
        let sum = |fields: &[Type]| -> Result<usize> {
            fields.iter().try_fold(0usize, |n, field| {
                n.checked_add(self.words_inner(field, depth + 1)?)
                    .ok_or_else(|| unsupported("layout size overflow"))
            })
        };
        let words = match &ty {
            Type::Unit | Type::Never => 0,
            Type::Tuple(fields) => sum(fields)?,
            Type::Array(element, length) => {
                if *length > MAX_FRAME / 8 {
                    return Err(unsupported("array length beyond backend limit"));
                }
                self.words_inner(element, depth + 1)?
                    .checked_mul(*length)
                    .ok_or_else(|| unsupported("array layout overflow"))?
            }
            Type::Named(name) => {
                if let Some(fields) = self.declarations.structs.get(name) {
                    sum(&fields.iter().map(|f| f.ty.clone()).collect::<Vec<_>>())?
                } else if let Some(variants) = self.declarations.enums.get(name) {
                    let maximum = variants
                        .iter()
                        .map(|v| sum(&v.fields))
                        .collect::<Result<Vec<_>>>()?
                        .into_iter()
                        .max()
                        .unwrap_or(0);
                    maximum
                        .checked_add(1)
                        .ok_or_else(|| unsupported("enum layout overflow"))?
                } else {
                    return Err(unsupported(format!("type {ty:?}")));
                }
            }
            _ => return Err(unsupported(format!("type {ty:?}"))),
        };
        if words > MAX_FRAME / 8 {
            return Err(unsupported("layout larger than 16 MiB"));
        }
        Ok(words)
    }
    fn indirect(&self, ty: &Type) -> Result<bool> {
        let ty = self.resolve(ty)?;
        Ok(!matches!(ty, Type::Unit | Type::Never) && scalar(&ty).is_none())
    }
    fn field_offset(&self, ty: &Type, index: usize) -> Result<usize> {
        let fields = self.fields(ty)?;
        if index >= fields.len() {
            return Err("invalid checked AArch64 field index".into());
        }
        fields[..index]
            .iter()
            .try_fold(0, |sum, ty| Ok(sum + self.words(ty)? * 8))
    }
}

fn align16(bytes: usize) -> Result<usize> {
    bytes
        .checked_add(15)
        .map(|n| n & !15)
        .filter(|n| *n <= MAX_FRAME)
        .ok_or_else(|| unsupported("frame larger than 16 MiB"))
}

fn generate(checked: &CheckedProgram<'_>, retained: Option<&HashSet<String>>) -> Result<String> {
    let declarations = checked.declarations();
    let mut encoder = Encoder::default();
    let mut labels = HashMap::new();
    let mut functions = Vec::new();
    for item in &checked.program().items {
        let Item::Function(function) = item else {
            continue;
        };
        if retained.is_some_and(|names| !names.contains(&function.name)) {
            continue;
        }
        if function.external || function.calling_convention != crate::CallingConvention::Lim {
            return Err(
                unsupported(format!("foreign function '{}'", function.name)).at(checked
                    .program()
                    .declaration_spans
                    .get(&function.name)
                    .copied()),
            );
        }
        let id = declarations
            .function_id(&function.name)
            .ok_or("missing checked function identity")?;
        labels.insert(id, encoder.label());
        functions.push((id, function));
    }
    let main = declarations
        .function_id("main")
        .and_then(|id| labels.get(&id).copied());
    // An assembly-only library can lack main. ELF emission fails closed then.
    let mut metadata = String::new();
    if let Some(main) = main {
        let signature = &declarations
            .function(declarations.function_id("main").unwrap())
            .signature;
        let layout = Layout { declarations };
        if !signature.parameters.is_empty() || layout.indirect(&signature.return_type)? {
            return Err(unsupported("main arguments or aggregate main result"));
        }
        encoder.branch(main, None, true);
        encoder.constant(8, 94); // Linux AArch64 exit_group.
        encoder.syscall();
        encoder.trap();
        metadata.push_str("// lim-entry 0\n");
    }
    for (id, function) in functions {
        let body = declarations
            .bodies
            .get(&function.name)
            .ok_or("missing checked function body")?;
        encoder.bind(labels[&id])?;
        let function_span = declarations.function(id).span;
        let mut emitter = FunctionEmitter::new(
            &mut encoder,
            declarations,
            body,
            &labels,
            &declarations.function(id).signature.return_type,
        )
        .map_err(|error| error.at(function_span))?;
        emitter
            .prologue()
            .map_err(|error| error.at(function_span))?;
        emitter.instructions(&body.instructions)?;
        // Reaching an unrepresented return is an explicit runtime fault.
        emitter.encoder.trap();
        emitter.encoder.bind(emitter.epilogue)?;
        emitter.restore();
        let name = if function.name == "main" {
            "main".into()
        } else {
            format!("f{}", labels[&id].0)
        };
        let calls = emitter
            .calls
            .iter()
            .map(|id| {
                if declarations.function_name(*id) == Some("main") {
                    "main".into()
                } else {
                    format!("f{}", labels[id].0)
                }
            })
            .collect::<Vec<String>>()
            .join(",");
        metadata.push_str(&format!(
            "// lim-frame {name} {} {calls}\n",
            emitter.frame + 16
        ));
    }
    encoder.finish()?;
    let mut listing = format!("{MAGIC}.arch armv8-a\n.text\n{metadata}");
    for (word, description) in encoder.words.iter().zip(&encoder.descriptions) {
        listing.push_str(&format!("    .inst 0x{word:08x} // {description}\n"));
    }
    Ok(listing)
}

struct LoopTarget {
    label: Option<String>,
    again: Label,
    end: Label,
    result: Option<usize>,
}
struct FunctionEmitter<'a, 'b> {
    encoder: &'a mut Encoder,
    layout: Layout<'b>,
    body: &'b Body,
    functions: &'b HashMap<FunctionId, Label>,
    bindings: Vec<usize>,
    nodes: Vec<usize>,
    frame: usize,
    saved_result: usize,
    result_type: &'b Type,
    epilogue: Label,
    loops: Vec<LoopTarget>,
    calls: std::collections::BTreeSet<FunctionId>,
}

impl<'a, 'b> FunctionEmitter<'a, 'b> {
    fn new(
        encoder: &'a mut Encoder,
        declarations: &'b Declarations,
        body: &'b Body,
        functions: &'b HashMap<FunctionId, Label>,
        result_type: &'b Type,
    ) -> Result<Self> {
        let layout = Layout { declarations };
        layout.words(result_type)?;
        let max_arguments = body
            .nodes
            .iter()
            .filter_map(|n| match &n.kind {
                NodeKind::Form {
                    callee: Some(id), ..
                } => Some(declarations.function(*id).signature.parameters.len()),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        let outgoing = align16(
            max_arguments
                .saturating_sub(8)
                .checked_mul(8)
                .ok_or("outgoing frame overflow")?,
        )?;
        let mut next = outgoing;
        let mut allocate = |words: usize| -> Result<usize> {
            let slot = next;
            next = next
                .checked_add(words.max(1).checked_mul(8).ok_or("frame overflow")?)
                .ok_or("frame overflow")?;
            Ok(slot)
        };
        let saved_result = allocate(1)?;
        let bindings = body
            .bindings
            .iter()
            .map(|b| {
                let words = layout.words(&b.ty).map_err(|error| error.at(b.span))?;
                allocate(words).map_err(|error| error.at(b.span))
            })
            .collect::<Result<Vec<_>>>()?;
        let nodes = body
            .nodes
            .iter()
            .map(|n| {
                allocate(
                    1 + match &n.ty {
                        Some(ty) => layout.words(ty).map_err(|error| error.at(n.span))?,
                        None => 0,
                    }
                    .max(1),
                )
                .map_err(|error| error.at(n.span))
            })
            .collect::<Result<Vec<_>>>()?;
        let frame = align16(next)?;
        let epilogue = encoder.label();
        Ok(Self {
            encoder,
            layout,
            body,
            functions,
            bindings,
            nodes,
            frame,
            saved_result,
            result_type,
            epilogue,
            loops: Vec::new(),
            calls: Default::default(),
        })
    }
    fn ty(&self, id: NodeId) -> Result<Type> {
        self.layout.resolve(
            self.body.nodes[id.0]
                .ty
                .as_ref()
                .ok_or("untyped AArch64 value")?,
        )
    }
    fn words(&self, id: NodeId) -> Result<usize> {
        self.layout.words(&self.ty(id)?)
    }
    fn address_slot(&mut self, register: u8, slot: usize) {
        if slot <= 4095 {
            self.encoder.immediate(false, register, 29, slot);
        } else {
            self.encoder.constant(register, slot as u64);
            self.encoder
                .three(0x8b000000, register, 29, register, "add");
        }
    }
    fn load(&mut self, register: u8, slot: usize) {
        if slot / 8 < 4096 {
            self.encoder.memory(true, register, 29, slot);
        } else {
            self.address_slot(17, slot);
            self.encoder.memory(true, register, 17, 0);
        }
    }
    fn store(&mut self, register: u8, slot: usize) {
        if slot / 8 < 4096 {
            self.encoder.memory(false, register, 29, slot);
        } else {
            self.address_slot(17, slot);
            self.encoder.memory(false, register, 17, 0);
        }
    }
    fn copy(&mut self, source: usize, destination: usize, words: usize) {
        for word in 0..words {
            self.load(9, source + word * 8);
            self.store(9, destination + word * 8);
        }
    }
    fn from_pointer(&mut self, pointer: u8, destination: usize, words: usize) {
        for word in 0..words {
            self.encoder.memory(true, 9, pointer, 0);
            self.store(9, destination + word * 8);
            if word + 1 < words {
                self.encoder.immediate(false, pointer, pointer, 8);
            }
        }
    }
    fn to_pointer(&mut self, source: usize, pointer: u8, words: usize) {
        for word in 0..words {
            self.load(9, source + word * 8);
            self.encoder.memory(false, 9, pointer, 0);
            if word + 1 < words {
                self.encoder.immediate(false, pointer, pointer, 8);
            }
        }
    }
    fn prologue(&mut self) -> Result<()> {
        self.encoder.stack_adjust(true, 16);
        self.encoder.memory(false, 29, 31, 0);
        self.encoder.memory(false, 30, 31, 8);
        self.encoder.stack_adjust(true, self.frame);
        self.encoder.immediate(false, 29, 31, 0);
        self.store(8, self.saved_result);
        for index in 0..self.body.parameter_count {
            let ty = &self.body.bindings[index].ty;
            if index < 8 {
                self.encoder.mov(10, index as u8);
            } else {
                self.load(10, self.frame + 16 + (index - 8) * 8);
            }
            if self.layout.indirect(ty)? {
                self.from_pointer(10, self.bindings[index], self.layout.words(ty)?);
            } else {
                self.store(10, self.bindings[index]);
            }
        }
        Ok(())
    }
    fn restore(&mut self) {
        self.encoder.stack_adjust(false, self.frame);
        self.encoder.memory(true, 29, 31, 0);
        self.encoder.memory(true, 30, 31, 8);
        self.encoder.stack_adjust(false, 16);
        self.encoder.ret();
    }
    fn instructions(&mut self, instructions: &[Instruction]) -> Result<Option<NodeId>> {
        let mut last = None;
        for instruction in instructions {
            let result: Result<()> = (|| {
                match &instruction.control {
                    Control::Bind(binding, value, _) => {
                        self.expression(*value)?;
                        self.copy(
                            self.nodes[value.0],
                            self.bindings[binding.0],
                            self.words(*value)?,
                        );
                        last = None;
                    }
                    Control::Assign(root, projection, value) => {
                        // Evaluate a dynamic destination index before the RHS.
                        self.assignment_address(root, projection)?;
                        let destination = self.nodes[value.0] + self.words(*value)?.max(1) * 8;
                        self.store(10, destination);
                        self.expression(*value)?;
                        self.load(10, destination);
                        self.to_pointer(self.nodes[value.0], 10, self.words(*value)?);
                        last = None;
                    }
                    Control::Return(value) => {
                        if let Some(value) = value {
                            self.expression(*value)?;
                            if self.layout.indirect(self.result_type)? {
                                self.load(10, self.saved_result);
                                self.to_pointer(
                                    self.nodes[value.0],
                                    10,
                                    self.layout.words(self.result_type)?,
                                );
                            } else if self.layout.words(self.result_type)? != 0 {
                                self.load(0, self.nodes[value.0]);
                            } else {
                                self.encoder.constant(0, 0);
                            }
                        } else {
                            self.encoder.constant(0, 0);
                        }
                        self.encoder.branch(self.epilogue, None, false);
                        last = None;
                    }
                    Control::Evaluate(value) => {
                        self.expression(*value)?;
                        last = Some(*value);
                    }
                    Control::While(condition, instructions) => {
                        self.loop_body(None, Some(*condition), instructions, None, None)?;
                        last = None;
                    }
                    Control::Loop(instructions) => {
                        self.loop_body(None, None, instructions, None, None)?;
                        last = None;
                    }
                    Control::For(init, condition, step, instructions) => {
                        self.instructions(std::slice::from_ref(init.as_ref()))?;
                        self.loop_body(None, Some(*condition), instructions, Some(step), None)?;
                        last = None;
                    }
                    Control::Labeled(label, inner) => match &inner.control {
                        Control::While(condition, body) => {
                            self.loop_body(Some(label.clone()), Some(*condition), body, None, None)?
                        }
                        Control::Loop(body) => {
                            self.loop_body(Some(label.clone()), None, body, None, None)?
                        }
                        _ => return Err(unsupported("labeled non-loop statement")),
                    },
                    Control::Break(label, value) => {
                        let target = self
                            .loops
                            .iter()
                            .rev()
                            .find(|target| label.is_none() || target.label == *label)
                            .ok_or("missing checked AArch64 break target")?;
                        let end = target.end;
                        let destination = target.result;
                        if let Some(value) = value {
                            self.expression(*value)?;
                            let destination = destination
                                .ok_or_else(|| unsupported("break value in statement loop"))?;
                            self.copy(self.nodes[value.0], destination, self.words(*value)?);
                        }
                        self.encoder.branch(end, None, false);
                        last = None;
                    }
                    Control::Continue(label) => {
                        let target = self
                            .loops
                            .iter()
                            .rev()
                            .find(|target| label.is_none() || target.label == *label)
                            .ok_or("missing checked AArch64 continue target")?;
                        self.encoder.branch(target.again, None, false);
                        last = None;
                    }
                    Control::Destructure {
                        pattern,
                        value,
                        ty,
                        otherwise,
                        failure_pattern,
                        ..
                    } => {
                        if failure_pattern.is_some() {
                            return Err(unsupported("let-else failure bindings"));
                        }
                        self.expression(*value)?;
                        let failure = self.encoder.label();
                        let done = self.encoder.label();
                        self.pattern(*pattern, ty, self.nodes[value.0], failure)?;
                        self.encoder.branch(done, None, false);
                        self.encoder.bind(failure)?;
                        if let Some(body) = otherwise {
                            self.instructions(body)?;
                        } else {
                            self.encoder.trap();
                        }
                        self.encoder.bind(done)?;
                        last = None;
                    }
                }
                Ok(())
            })();
            result.map_err(|error| error.at(instruction.span))?;
        }
        Ok(last)
    }
    fn loop_body(
        &mut self,
        label: Option<String>,
        condition: Option<NodeId>,
        body: &[Instruction],
        step: Option<&Instruction>,
        result: Option<usize>,
    ) -> Result<()> {
        let top = self.encoder.label();
        let again = self.encoder.label();
        let end = self.encoder.label();
        self.encoder.bind(top)?;
        if let Some(condition) = condition {
            self.expression(condition)?;
            self.load(9, self.nodes[condition.0]);
            self.encoder.compare(9, 31);
            self.encoder.branch(end, Some(C::Eq), false);
        }
        self.loops.push(LoopTarget {
            label,
            again,
            end,
            result,
        });
        self.instructions(body)?;
        self.encoder.bind(again)?;
        if let Some(step) = step {
            self.instructions(std::slice::from_ref(step))?;
        }
        self.encoder.branch(top, None, false);
        self.encoder.bind(end)?;
        self.loops.pop();
        Ok(())
    }
    fn assignment_address(&mut self, root: &PlaceRoot, projection: &Projection) -> Result<()> {
        let PlaceRoot::Local(binding) = root else {
            return Err(unsupported("nonlocal assignment"));
        };
        let ty = self.layout.resolve(&self.body.bindings[binding.0].ty)?;
        self.address_slot(10, self.bindings[binding.0]);
        match projection {
            Projection::Local => {}
            Projection::Field(field) => {
                let offset = self.layout.field_offset(&ty, field.index)?;
                self.add_offset(10, offset);
            }
            Projection::Tuple(index) => {
                let offset = self.layout.field_offset(&ty, *index)?;
                self.add_offset(10, offset);
            }
            Projection::Array(index) => {
                self.expression(*index)?;
                self.address_slot(10, self.bindings[binding.0]);
                self.array_offset(&ty, *index, false)?;
            }
            Projection::Payload(_, _) => return Err(unsupported("enum payload assignment")),
        }
        Ok(())
    }
    fn add_offset(&mut self, register: u8, offset: usize) {
        if offset <= 4095 {
            self.encoder.immediate(false, register, register, offset);
        } else {
            self.encoder.constant(16, offset as u64);
            self.encoder
                .three(0x8b000000, register, register, 16, "add");
        }
    }
    fn array_offset(&mut self, ty: &Type, index: NodeId, proven: bool) -> Result<()> {
        let Type::Array(element, length) = self.layout.resolve(ty)? else {
            return Err(unsupported("non-array indexing"));
        };
        self.load(11, self.nodes[index.0]);
        if !proven {
            self.encoder.constant(12, length as u64);
            self.encoder.compare(11, 12);
            self.require(C::Lo)?;
        }
        self.encoder
            .constant(12, (self.layout.words(&element)? * 8) as u64);
        self.encoder.three(0x9b007c00, 11, 11, 12, "mul");
        self.encoder.three(0x8b000000, 10, 10, 11, "add");
        Ok(())
    }
    fn require(&mut self, condition: C) -> Result<()> {
        let good = self.encoder.label();
        self.encoder.branch(good, Some(condition), false);
        self.encoder.trap();
        self.encoder.bind(good).map_err(Into::into)
    }
    fn address(&mut self, id: NodeId) -> Result<()> {
        match self.body.nodes[id.0].kind.clone() {
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => self.address_slot(10, self.bindings[binding.0]),
            NodeKind::Form { head, children, .. } if head == "deref" => {
                self.expression(children[1])?;
                self.load(10, self.nodes[children[1].0]);
            }
            NodeKind::Form { head, children, .. }
                if head == "get" || crate::is_array_index_head(&head) =>
            {
                let owner_ty = self.ty(children[1])?;
                let target = match owner_ty.clone() {
                    Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                        self.expression(children[1])?;
                        self.load(10, self.nodes[children[1].0]);
                        *target
                    }
                    _ => {
                        self.address(children[1])?;
                        owner_ty
                    }
                };
                if crate::is_array_index_head(&head) {
                    // Keep the place's base without reevaluating side effects.
                    let scratch = self.nodes[id.0] + self.words(id)?.max(1) * 8;
                    self.store(10, scratch);
                    self.expression(children[2])?;
                    self.load(10, scratch);
                    self.array_offset(&target, children[2], head == "index-proven")?;
                } else {
                    let index = match self.body.nodes[children[2].0].kind {
                        NodeKind::Declaration(DeclarationId::Field(field)) => field.index,
                        _ => self.literal_usize(children[2])?,
                    };
                    let offset = self.layout.field_offset(&target, index)?;
                    self.add_offset(10, offset);
                }
            }
            _ => return Err(unsupported("address of a temporary or global place")),
        }
        Ok(())
    }
    fn literal_usize(&self, id: NodeId) -> Result<usize> {
        match &self.body.nodes[id.0].kind {
            NodeKind::Literal(Expr::Integer(n)) => {
                usize::try_from(*n).map_err(|_| "AArch64 index overflow".into())
            }
            NodeKind::Literal(Expr::UnsignedInteger(n)) => {
                usize::try_from(*n).map_err(|_| "AArch64 index overflow".into())
            }
            _ => Err(unsupported("nonliteral tuple index")),
        }
    }
    fn expression(&mut self, id: NodeId) -> Result<()> {
        self.expression_inner(id)
            .map_err(|error| error.at(self.body.nodes[id.0].span))
    }
    fn expression_inner(&mut self, id: NodeId) -> Result<()> {
        let destination = self.nodes[id.0];
        let words = self.words(id)?;
        match self.body.nodes[id.0].kind.clone() {
            NodeKind::Literal(Expr::Integer(value)) => {
                self.encoder.constant(9, value as u64);
                self.store(9, destination);
            }
            NodeKind::Literal(Expr::UnsignedInteger(value)) => {
                self.encoder.constant(9, value as u64);
                self.store(9, destination);
            }
            NodeKind::Literal(Expr::Char(value)) => {
                self.encoder.constant(9, value as u64);
                self.store(9, destination);
            }
            NodeKind::Syntax(children) if children.is_empty() && words == 0 => {}
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => self.copy(self.bindings[binding.0], destination, words),
            NodeKind::Symbol {
                name,
                binding: None,
            } if name == "true" || name == "false" => {
                self.encoder.constant(9, u64::from(name == "true"));
                self.store(9, destination);
            }
            NodeKind::Declaration(DeclarationId::Variant(variant)) => {
                let tag = self.layout.declarations.variant(variant).discriminant;
                self.zero(destination, words);
                self.encoder.constant(9, tag);
                self.store(9, destination);
            }
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                self.expression(condition)?;
                self.load(9, self.nodes[condition.0]);
                self.encoder.compare(9, 31);
                let otherwise = self.encoder.label();
                let done = self.encoder.label();
                self.encoder.branch(otherwise, Some(C::Eq), false);
                self.expression(then_value)?;
                self.copy(self.nodes[then_value.0], destination, words);
                self.encoder.branch(done, None, false);
                self.encoder.bind(otherwise)?;
                if let Some(value) = else_value {
                    self.expression(value)?;
                    self.copy(self.nodes[value.0], destination, words);
                }
                self.encoder.bind(done)?;
            }
            NodeKind::Block(instructions) => {
                if let Some(value) = self.instructions(&instructions)? {
                    self.copy(self.nodes[value.0], destination, words);
                }
            }
            NodeKind::Loop(instructions) => {
                self.loop_body(None, None, &instructions, None, Some(destination))?
            }
            NodeKind::Labeled(label, inner) => match self.body.nodes[inner.0].kind.clone() {
                NodeKind::Loop(instructions) => {
                    self.loop_body(Some(label), None, &instructions, None, Some(destination))?
                }
                _ => return Err(unsupported("labeled non-loop expression")),
            },
            NodeKind::Match { value, arms, .. } => {
                self.expression(value)?;
                let done = self.encoder.label();
                for arm in arms {
                    let NodeKind::MatchArm { pattern, values } =
                        self.body.nodes[arm.0].kind.clone()
                    else {
                        return Err("invalid checked match arm".into());
                    };
                    let next = self.encoder.label();
                    self.pattern(pattern, &self.ty(value)?, self.nodes[value.0], next)?;
                    let mut result = None;
                    for value in values {
                        if let NodeKind::Form { head, children, .. } =
                            &self.body.nodes[value.0].kind
                        {
                            if head == "when" {
                                let guard = children[1];
                                self.expression(guard)?;
                                self.load(9, self.nodes[guard.0]);
                                self.encoder.compare(9, 31);
                                self.encoder.branch(next, Some(C::Eq), false);
                                continue;
                            }
                        }
                        self.expression(value)?;
                        result = Some(value);
                    }
                    if let Some(result) = result {
                        self.copy(self.nodes[result.0], destination, words);
                    }
                    self.encoder.branch(done, None, false);
                    self.encoder.bind(next)?;
                }
                self.encoder.trap();
                self.encoder.bind(done)?;
            }
            NodeKind::Form {
                head,
                children,
                numeric,
                callee,
                argument_source_order,
            } => {
                if let Some(callee) = callee {
                    self.call(id, callee, &children[1..], argument_source_order.as_deref())?;
                } else if let Some(numeric) = numeric {
                    self.numeric(id, &numeric, &children[1..])?;
                } else {
                    self.form(id, &head, &children)?;
                }
            }
            other => return Err(unsupported(format!("expression {other:?}"))),
        }
        Ok(())
    }
    fn zero(&mut self, destination: usize, words: usize) {
        for word in 0..words {
            self.store(31, destination + word * 8);
        }
    }
    fn call(
        &mut self,
        id: NodeId,
        callee: FunctionId,
        arguments: &[NodeId],
        order: Option<&[usize]>,
    ) -> Result<()> {
        let label = *self.functions.get(&callee).ok_or_else(|| {
            unsupported(format!(
                "unemitted or foreign call '{}'",
                self.layout.declarations.function(callee).name
            ))
        })?;
        let order = order
            .map(<[usize]>::to_vec)
            .unwrap_or_else(|| (0..arguments.len()).collect());
        for index in order {
            self.expression(arguments[index])?;
        }
        for (index, argument) in arguments.iter().enumerate() {
            if self.layout.indirect(&self.ty(*argument)?)? {
                self.address_slot(9, self.nodes[argument.0]);
            } else {
                self.load(9, self.nodes[argument.0]);
            }
            if index < 8 {
                self.encoder.mov(index as u8, 9);
            } else {
                self.store(9, (index - 8) * 8);
            }
        }
        self.address_slot(8, self.nodes[id.0]);
        self.encoder.branch(label, None, true);
        self.calls.insert(callee);
        if !self.layout.indirect(&self.ty(id)?)? {
            self.store(0, self.nodes[id.0]);
        }
        Ok(())
    }
    fn form(&mut self, id: NodeId, head: &str, children: &[NodeId]) -> Result<()> {
        let destination = self.nodes[id.0];
        let ty = self.ty(id)?;
        let words = self.words(id)?;
        match head {
            "" if words == 0 => {}
            "literal" => {
                let value = self.literal_bits(children[2])?;
                self.encoder.constant(9, value);
                self.normalize(9, &ty)?;
                self.store(9, destination);
            }
            "linux-syscall" => {
                // Numbers are target-specific Linux AArch64 numbers supplied
                // by the source; x86 wrappers are not translated.
                let arguments = self.syntax_children(children[3])?;
                if arguments.len() > 6 || (scalar(&ty).is_none() && ty != Type::Unit) {
                    return Err(unsupported("Linux syscall argument/result shape"));
                }
                self.expression(children[2])?;
                for argument in &arguments {
                    if scalar(&self.ty(*argument)?).is_none() {
                        return Err(unsupported("aggregate Linux syscall argument"));
                    }
                    self.expression(*argument)?;
                }
                for (index, argument) in arguments.iter().enumerate() {
                    self.load(index as u8, self.nodes[argument.0]);
                }
                self.load(8, self.nodes[children[2].0]);
                self.encoder.syscall();
                if ty != Type::Unit {
                    self.normalize(0, &ty)?;
                    self.store(0, destination);
                }
            }
            "io-input-byte" | "io-output-byte" => {
                let input = head == "io-input-byte";
                self.expression(children[1])?;
                let buffer = if input {
                    self.encoder.constant(9, 0);
                    self.store(9, destination + 8);
                    destination + 8
                } else {
                    self.expression(children[2])?;
                    self.nodes[children[2].0]
                };
                self.load(0, self.nodes[children[1].0]);
                self.address_slot(1, buffer);
                self.encoder.constant(2, 1);
                // Linux AArch64 read/write; source cannot select another call.
                self.encoder.constant(8, if input { 63 } else { 64 });
                self.encoder.syscall();
                self.store(0, destination);
            }
            "unsafe" | "as" => {
                let value = children[1];
                self.expression(value)?;
                let source_ty = self.ty(value)?;
                if head == "as" && (scalar(&source_ty).is_none() || scalar(&ty).is_none()) {
                    return Err(unsupported("non-scalar cast"));
                }
                self.copy(self.nodes[value.0], destination, words);
                if head == "as" {
                    self.load(9, destination);
                    self.normalize(9, &ty)?;
                    self.store(9, destination);
                }
            }
            "clone" => {
                if self
                    .layout
                    .declarations
                    .clone_hook_name(self.body, id)
                    .is_some()
                {
                    return Err(unsupported("custom clone hooks"));
                }
                self.expression(children[1])?;
                self.copy(self.nodes[children[1].0], destination, words);
            }
            "drop" | "forget" => {
                self.expression(children[1])?;
            }
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" => {
                self.address(children[1])?;
                if children.len() == 3 {
                    self.expression(children[2])?;
                    self.copy(self.nodes[children[2].0], destination, words);
                } else {
                    self.store(10, destination);
                }
            }
            "ref-ptr" | "ptr-address" | "ptr-borrow" | "ptr-borrow-mut" | "pin-ptr-borrow"
            | "pin-ptr-borrow-mut" => {
                self.expression(children[1])?;
                let value = if children.len() == 3 {
                    self.expression(children[2])?;
                    children[2]
                } else {
                    children[1]
                };
                self.copy(self.nodes[value.0], destination, words);
            }
            "deref" => {
                self.expression(children[1])?;
                self.load(10, self.nodes[children[1].0]);
                self.from_pointer(10, destination, words);
            }
            "deref-set" => {
                self.expression(children[1])?;
                self.expression(children[2])?;
                self.load(10, self.nodes[children[1].0]);
                self.to_pointer(self.nodes[children[2].0], 10, self.words(children[2])?);
            }
            "get" | "index" | "index-proven" => {
                // Value projections may also target aggregate expressions.
                self.expression(children[1])?;
                let owner_ty = self.ty(children[1])?;
                let target = if let Type::Reference { target, .. }
                | Type::PinnedReference { target, .. } = owner_ty
                {
                    self.load(10, self.nodes[children[1].0]);
                    *target
                } else {
                    self.address_slot(10, self.nodes[children[1].0]);
                    owner_ty
                };
                if head == "get" {
                    let index = match self.body.nodes[children[2].0].kind {
                        NodeKind::Declaration(DeclarationId::Field(field)) => field.index,
                        _ => self.literal_usize(children[2])?,
                    };
                    let offset = self.layout.field_offset(&target, index)?;
                    self.add_offset(10, offset);
                } else {
                    self.expression(children[2])?;
                    if matches!(
                        self.ty(children[1])?,
                        Type::Reference { .. } | Type::PinnedReference { .. }
                    ) {
                        self.load(10, self.nodes[children[1].0]);
                    } else {
                        self.address_slot(10, self.nodes[children[1].0]);
                    }
                    self.array_offset(&target, children[2], head == "index-proven")?;
                }
                self.from_pointer(10, destination, words);
            }
            "panic" => self.encoder.trap(),
            "assert" => {
                self.expression(children[1])?;
                self.load(9, self.nodes[children[1].0]);
                self.encoder.compare(9, 31);
                self.require(C::Ne)?;
            }
            "unreachable" => self.encoder.trap(),
            "struct-literal" => {
                self.zero(destination, words);
                let fields = self.layout.fields(&ty)?;
                let entries = self.syntax_children(children[2])?;
                for entry in entries {
                    let pair = self.syntax_children(entry)?;
                    let name = self.symbol(pair[0])?;
                    let Type::Named(owner) = &ty else {
                        return Err("invalid checked struct literal".into());
                    };
                    let index = self.layout.declarations.structs[owner]
                        .iter()
                        .position(|f| f.name == name)
                        .ok_or("missing checked struct field")?;
                    self.expression(pair[1])?;
                    self.copy(
                        self.nodes[pair[1].0],
                        destination + self.layout.field_offset(&ty, index)?,
                        self.layout.words(&fields[index])?,
                    );
                }
            }
            "tuple" | "array" | "array-of" => {
                let arity = match &ty {
                    Type::Array(_, length) => *length,
                    Type::Tuple(fields) => fields.len(),
                    _ => return Err("invalid checked aggregate constructor type".into()),
                };
                let start = if children.len() == arity + 1 { 1 } else { 2 };
                let mut offset = 0;
                for value in &children[start..] {
                    self.expression(*value)?;
                    let count = self.words(*value)?;
                    self.copy(self.nodes[value.0], destination + offset, count);
                    offset += count * 8;
                }
                if offset != words * 8 {
                    return Err("invalid checked aggregate constructor layout".into());
                }
            }
            "array-repeat" => {
                let value = *children.last().ok_or("invalid repeat constructor")?;
                self.expression(value)?;
                let Type::Array(element, length) = &ty else {
                    return Err("invalid checked array repeat".into());
                };
                let count = self.layout.words(element)?;
                if count != 0 {
                    for index in 0..*length {
                        self.copy(self.nodes[value.0], destination + index * count * 8, count);
                    }
                }
            }
            _ if scalar(&Type::from_name(head)).is_some() && children.len() == 2 => {
                self.expression(children[1])?;
                self.copy(self.nodes[children[1].0], destination, words);
                self.load(9, destination);
                self.normalize(9, &ty)?;
                self.store(9, destination);
            }
            _ => match self.body.nodes[children[0].0].kind {
                NodeKind::Declaration(DeclarationId::Variant(variant)) => {
                    self.zero(destination, words);
                    self.encoder
                        .constant(9, self.layout.declarations.variant(variant).discriminant);
                    self.store(9, destination);
                    let mut offset = 8;
                    for value in &children[1..] {
                        self.expression(*value)?;
                        let count = self.words(*value)?;
                        self.copy(self.nodes[value.0], destination + offset, count);
                        offset += count * 8;
                    }
                }
                NodeKind::Declaration(DeclarationId::Aggregate(_)) => {
                    let order = match &self.body.nodes[id.0].kind {
                        NodeKind::Form {
                            argument_source_order: Some(order),
                            ..
                        } => order.clone(),
                        _ => (0..children.len() - 1).collect(),
                    };
                    for index in order {
                        self.expression(children[index + 1])?;
                    }
                    let mut offset = 0;
                    for value in &children[1..] {
                        let count = self.words(*value)?;
                        self.copy(self.nodes[value.0], destination + offset, count);
                        offset += count * 8;
                    }
                    if offset != words * 8 {
                        return Err("invalid checked struct constructor layout".into());
                    }
                }
                _ => return Err(unsupported(format!("primitive '{head}'"))),
            },
        }
        Ok(())
    }
    fn syntax_children(&self, id: NodeId) -> Result<Vec<NodeId>> {
        match &self.body.nodes[id.0].kind {
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => Ok(children.clone()),
            _ => Err("invalid checked AArch64 syntax list".into()),
        }
    }
    fn symbol(&self, id: NodeId) -> Result<String> {
        match &self.body.nodes[id.0].kind {
            NodeKind::Symbol { name, .. } => Ok(name.clone()),
            NodeKind::Declaration(declaration) => Ok(self
                .layout
                .declarations
                .declaration_name(*declaration)
                .into()),
            _ => Err("invalid checked AArch64 symbol".into()),
        }
    }
    fn normalize(&mut self, register: u8, ty: &Type) -> Result<()> {
        let (bits, signed) = scalar(&self.layout.resolve(ty)?)
            .ok_or_else(|| unsupported("non-scalar normalization"))?;
        self.encoder.normalize(register, bits, signed);
        Ok(())
    }
    fn literal_bits(&self, id: NodeId) -> Result<u64> {
        match &self.body.nodes[id.0].kind {
            NodeKind::Literal(Expr::Integer(value)) => Ok(*value as u64),
            NodeKind::Literal(Expr::UnsignedInteger(value)) => Ok(*value as u64),
            NodeKind::Literal(Expr::Char(value)) => Ok(*value as u64),
            NodeKind::Symbol { name, .. } if name == "true" || name == "false" => {
                Ok(u64::from(name == "true"))
            }
            _ => Err(unsupported("non-integer literal")),
        }
    }
    fn numeric(&mut self, id: NodeId, operation: &NumericOperation, args: &[NodeId]) -> Result<()> {
        if operation.overflow == Overflow::Saturate {
            return Err(unsupported("saturating arithmetic"));
        }
        let ty = self.layout.resolve(&operation.operand_type)?;
        let (bits, signed) =
            scalar(&ty).ok_or_else(|| unsupported(format!("numeric type {ty:?}")))?;
        let opcode = operation.operation;
        let reverse = matches!(&self.body.nodes[id.0].kind, NodeKind::Form { argument_source_order: Some(order), .. } if order == &[1, 0]);
        self.expression(args[usize::from(reverse)])?;
        if matches!(opcode, Op::LogicalAnd | Op::LogicalOr) {
            let done = self.encoder.label();
            self.load(9, self.nodes[args[0].0]);
            self.store(9, self.nodes[id.0]);
            self.encoder.compare(9, 31);
            self.encoder.branch(
                done,
                Some(if opcode == Op::LogicalAnd {
                    C::Eq
                } else {
                    C::Ne
                }),
                false,
            );
            self.expression(args[1])?;
            self.copy(self.nodes[args[1].0], self.nodes[id.0], 1);
            self.encoder.bind(done)?;
            return Ok(());
        }
        if args.len() == 2 {
            self.expression(args[usize::from(!reverse)])?;
            self.load(11, self.nodes[args[1].0]);
        }
        self.load(9, self.nodes[args[0].0]);
        if args.len() == 1 {
            match opcode {
                Op::Subtract => self.encoder.three(0xcb000000, 9, 31, 9, "neg"),
                Op::Not if ty == Type::Bool => {
                    self.encoder.compare(9, 31);
                    self.encoder.cset(9, C::Eq);
                }
                Op::Not => self.encoder.three(0xaa200000, 9, 31, 9, "mvn"),
                _ => return Err(unsupported("unary numeric operation")),
            }
        } else {
            match opcode {
                Op::Add => self.encoder.three(0x8b000000, 9, 9, 11, "add"),
                Op::Subtract => self.encoder.three(0xcb000000, 9, 9, 11, "sub"),
                Op::Multiply => self.encoder.three(0x9b007c00, 9, 9, 11, "mul"),
                Op::BitAnd => self.encoder.three(0x8a000000, 9, 9, 11, "and"),
                Op::BitOr => self.encoder.three(0xaa000000, 9, 9, 11, "orr"),
                Op::BitXor => self.encoder.three(0xca000000, 9, 9, 11, "eor"),
                Op::Divide | Op::Remainder => {
                    self.encoder.compare(11, 31);
                    self.require(C::Ne)?;
                    self.encoder.three(
                        if signed { 0x9ac00c00 } else { 0x9ac00800 },
                        12,
                        9,
                        11,
                        "div",
                    );
                    if opcode == Op::Remainder {
                        self.encoder.three(0x9b007c00, 12, 12, 11, "mul");
                        self.encoder.three(0xcb000000, 9, 9, 12, "sub");
                    } else {
                        self.encoder.mov(9, 12);
                    }
                }
                Op::ShiftLeft | Op::ShiftRight => {
                    self.encoder.constant(12, bits as u64);
                    self.encoder.compare(11, 12);
                    self.require(C::Lo)?;
                    self.encoder.three(
                        if opcode == Op::ShiftLeft {
                            0x9ac02000
                        } else if signed {
                            0x9ac02800
                        } else {
                            0x9ac02400
                        },
                        9,
                        9,
                        11,
                        "shift",
                    );
                }
                Op::Less
                | Op::LessEqual
                | Op::Greater
                | Op::GreaterEqual
                | Op::Equal
                | Op::NotEqual => {
                    self.encoder.compare(9, 11);
                    self.encoder.cset(
                        9,
                        match opcode {
                            Op::Less => {
                                if signed {
                                    C::Lt
                                } else {
                                    C::Lo
                                }
                            }
                            Op::LessEqual => {
                                if signed {
                                    C::Le
                                } else {
                                    C::Ls
                                }
                            }
                            Op::Greater => {
                                if signed {
                                    C::Gt
                                } else {
                                    C::Hi
                                }
                            }
                            Op::GreaterEqual => {
                                if signed {
                                    C::Ge
                                } else {
                                    C::Hs
                                }
                            }
                            Op::Equal => C::Eq,
                            Op::NotEqual => C::Ne,
                            _ => unreachable!(),
                        },
                    );
                }
                _ => return Err(unsupported("numeric operation")),
            }
        }
        self.normalize(9, &self.ty(id)?)?;
        self.store(9, self.nodes[id.0]);
        Ok(())
    }
    fn pattern(&mut self, id: NodeId, ty: &Type, source: usize, failure: Label) -> Result<()> {
        match self.body.nodes[id.0].kind.clone() {
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => self.copy(source, self.bindings[binding.0], self.layout.words(ty)?),
            NodeKind::Symbol { name, .. } if name == "_" => {}
            NodeKind::Symbol { name, .. } if name == "true" || name == "false" => {
                self.load(9, source);
                self.encoder.constant(11, u64::from(name == "true"));
                self.encoder.compare(9, 11);
                self.encoder.branch(failure, Some(C::Ne), false);
            }
            NodeKind::Literal(Expr::Integer(value)) => {
                self.load(9, source);
                self.encoder.constant(11, value as u64);
                self.encoder.compare(9, 11);
                self.encoder.branch(failure, Some(C::Ne), false);
            }
            NodeKind::Literal(Expr::UnsignedInteger(value)) => {
                self.load(9, source);
                self.encoder.constant(11, value as u64);
                self.encoder.compare(9, 11);
                self.encoder.branch(failure, Some(C::Ne), false);
            }
            NodeKind::Literal(Expr::Char(value)) => {
                self.load(9, source);
                self.encoder.constant(11, value as u64);
                self.encoder.compare(9, 11);
                self.encoder.branch(failure, Some(C::Ne), false);
            }
            NodeKind::Declaration(DeclarationId::Variant(variant)) => {
                self.load(9, source);
                self.encoder
                    .constant(11, self.layout.declarations.variant(variant).discriminant);
                self.encoder.compare(9, 11);
                self.encoder.branch(failure, Some(C::Ne), false);
            }
            NodeKind::Form { head, children, .. } => {
                if head == "literal" {
                    self.load(9, source);
                    self.encoder.constant(11, self.literal_bits(children[2])?);
                    self.encoder.compare(9, 11);
                    self.encoder.branch(failure, Some(C::Ne), false);
                } else if head == "or" {
                    let matched = self.encoder.label();
                    for alternative in &children[1..] {
                        let next = self.encoder.label();
                        self.pattern(*alternative, ty, source, next)?;
                        self.encoder.branch(matched, None, false);
                        self.encoder.bind(next)?;
                    }
                    self.encoder.branch(failure, None, false);
                    self.encoder.bind(matched)?;
                } else {
                    let resolved = self.layout.resolve(ty)?;
                    let (fields, mut offset) = match self.body.nodes[children[0].0].kind {
                        NodeKind::Declaration(DeclarationId::Variant(variant)) => {
                            self.pattern(children[0], ty, source, failure)?;
                            (self.layout.declarations.variant(variant).fields.clone(), 8)
                        }
                        _ => match &resolved {
                            Type::Array(element, length) => (vec![*element.clone(); *length], 0),
                            _ => (self.layout.fields(&resolved)?, 0),
                        },
                    };
                    if fields.len() != children.len() - 1 {
                        return Err(unsupported("pattern arity"));
                    }
                    for (pattern, field) in children[1..].iter().zip(fields) {
                        self.pattern(*pattern, &field, source + offset, failure)?;
                        offset += self.layout.words(&field)? * 8;
                    }
                }
            }
            _ => return Err(unsupported("match/destructure pattern")),
        }
        Ok(())
    }
}

/// Encode this backend's resolved `.inst` listing into a static Linux ELF.
pub fn executable(assembly: &str) -> std::result::Result<Vec<u8>, String> {
    let (words, entry) = parse_listing(assembly)?;
    elf::executable(&words, entry.ok_or("AArch64 executable requires main")?)
}

fn parse_listing(assembly: &str) -> Result<(Vec<u32>, Option<usize>)> {
    if !assembly.starts_with(MAGIC) {
        return Err("expected Lim AArch64 native listing".into());
    }
    let mut words = Vec::new();
    let mut entry = None;
    for line in assembly.lines().skip(1) {
        let line = line.trim();
        if let Some(value) = line.strip_prefix("// lim-entry ") {
            if entry.is_some() {
                return Err("duplicate AArch64 entry".into());
            }
            entry = Some(value.parse().map_err(|_| "invalid AArch64 entry")?);
        } else if let Some(instruction) = line.strip_prefix(".inst ") {
            let value = instruction.split("//").next().unwrap().trim();
            let value = value
                .strip_prefix("0x")
                .ok_or("expected hexadecimal AArch64 instruction")?;
            words.push(u32::from_str_radix(value, 16).map_err(|_| "invalid AArch64 instruction")?);
        } else if line == ".arch armv8-a"
            || line == ".text"
            || line.starts_with("// lim-frame ")
            || line.is_empty()
        {
        } else {
            return Err(format!("unsupported AArch64 listing line '{line}'").into());
        }
    }
    Ok((words, entry))
}

/// Conservative generated stack bound from fixed frame sizes and direct calls.
/// Unknown, missing, and cyclic callees fail closed.
pub fn stack_usage_report(assembly: &str) -> std::result::Result<String, String> {
    parse_listing(assembly)?;
    let mut frames = HashMap::<String, (usize, Vec<String>)>::new();
    for line in assembly.lines() {
        if let Some(metadata) = line.trim().strip_prefix("// lim-frame ") {
            let mut parts = metadata.split_whitespace();
            let name = parts.next().ok_or("missing AArch64 frame name")?.to_owned();
            let bytes = parts
                .next()
                .ok_or("missing AArch64 frame size")?
                .parse::<usize>()
                .map_err(|_| "invalid AArch64 frame size")?;
            let calls = parts
                .next()
                .unwrap_or("")
                .split(',')
                .filter(|s| !s.is_empty())
                .map(str::to_owned)
                .collect();
            if parts.next().is_some() || frames.insert(name, (bytes, calls)).is_some() {
                return Err("invalid/duplicate AArch64 frame metadata".into());
            }
        }
    }
    fn bound(
        name: &str,
        frames: &HashMap<String, (usize, Vec<String>)>,
        active: &mut HashSet<String>,
    ) -> Result<usize> {
        if !active.insert(name.into()) {
            return Err("AArch64 stack bound unavailable for recursive calls".into());
        }
        let (local, calls) = frames
            .get(name)
            .ok_or("AArch64 stack bound unavailable for unknown callee")?;
        let mut maximum = 0;
        for callee in calls {
            maximum = maximum.max(bound(callee, frames, active)?);
        }
        active.remove(name);
        local
            .checked_add(maximum)
            .ok_or_else(|| "AArch64 stack bound overflow".into())
    }
    let bytes = bound("main", &frames, &mut HashSet::new())?;
    Ok(format!("Lim AArch64 generated-code stack usage (bytes from incoming SP):\n  main: at most {bytes} bytes\nBounds include fixed frames, saved FP/LR, locals, expression temporaries, and outgoing arguments. Startup/kernel stack and emulator internals are excluded.\n"))
}
