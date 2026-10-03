//! Ordinary-code emission from the executable async graph.
//!
//! The dispatcher, rather than a collection of body-shape rewrites, defines
//! execution order. Every owning storage cell has an explicit Empty/Full tag.
//! This module proposes code; graph validation is not ownership permission.
//! The original model and generated ordinary program must both be checked.
#![allow(dead_code)] // The default frontend switches after all storage modes land.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use crate::async_exec::{
    Action, AddressProjection, AddressRoot, Argument, BlockId, Compute, Edge, Graph, LoadKind,
    PlaceDescriptor, ReleaseKind, Terminator, ValueId,
};
use crate::async_prepare::{Function, Planning};
use crate::source_error::SourceError;
use crate::typed_body::{BindingId, Body};
use crate::{DiagnosticCode, Expr, Item, Program, Span, Type};

#[derive(Clone, Debug)]
pub(crate) struct Error {
    pub message: String,
    pub span: Span,
}

pub(crate) struct Generated {
    pub frame: String,
    pub source: String,
    pub origin: Span,
}

struct Slot {
    field: String,
    name: String,
    empty: String,
    full: String,
    take: String,
    put: String,
    peek: String,
    clear: String,
    finish: String,
    ty: Type,
    copy: bool,
    linear: bool,
}

struct Emitter<'a> {
    planning: &'a Planning,
    function: &'a Function,
    body: &'a Body,
    frame: String,
    poll_type: String,
    pending: String,
    ready: String,
    poll: String,
    finish: String,
    result: Type,
    slots: Vec<Slot>,
    bindings: HashMap<BindingId, usize>,
    values: HashMap<ValueId, usize>,
    reserved: RefCell<HashSet<String>>,
    next: Cell<usize>,
    types: crate::linearcheck::LinearTypes,
    render: crate::async_render::RenderContext<'a>,
    retirement: Option<crate::async_retire::Plan>,
    lending: Option<crate::async_lend::Plan>,
    reference_cells: Option<crate::async_cells::Plan>,
}

fn atom(name: &str) -> Expr {
    Expr::Symbol(name.into())
}
fn fail(function: &Function, message: impl Into<String>) -> Error {
    Error {
        message: message.into(),
        span: function.source.function.span,
    }
}

impl<'a> Emitter<'a> {
    fn new(planning: &'a Planning, function: &'a Function) -> Result<Self, Error> {
        let source = planning
            .interfaces
            .function(&function.model.source_name)
            .ok_or_else(|| {
                fail(
                    function,
                    "async start interface disappeared before emission",
                )
            })?;
        let Type::Named(frame) = &source.return_type else {
            return Err(fail(
                function,
                "async start interface has no concrete frame name",
            ));
        };
        let body = &planning.declarations.bodies[&function.model.body_name];
        function
            .graph
            .validate()
            .and_then(|_| function.graph.validate_against(body))
            .map_err(|error| fail(function, error.message))?;
        let poll = planning.interfaces.functions.values().find(|interface|
            interface.provenance == crate::async_interfaces::Provenance::AsyncPoll
            && interface.declaration.parameters.first().is_some_and(|parameter|
                parameter.ty == Type::Named(frame.clone())
                || matches!(&parameter.ty, Type::PinnedReference { target, .. } if target.as_ref() == &Type::Named(frame.clone()))))
            .ok_or_else(|| fail(function, "async poll interface disappeared before emission"))?;
        let Type::Named(poll_type) = &poll.declaration.return_type else {
            return Err(fail(function, "async poll interface has no protocol enum"));
        };
        let variants = &planning.interfaces.protocols[poll_type];
        let mut reserved = planning
            .interfaces
            .generated_names
            .keys()
            .cloned()
            .collect::<HashSet<_>>();
        for item in &planning.program.items {
            reserved.extend(crate::item_declared_names(item));
            if let Item::Enum { variants, .. } = item {
                reserved.extend(variants.iter().map(|variant| variant.name.clone()));
            }
        }
        let mut emitter = Self {
            planning,
            function,
            body,
            frame: frame.clone(),
            poll_type: poll_type.clone(),
            pending: variants[0].name.clone(),
            ready: variants[1].name.clone(),
            poll: poll.declaration.name.clone(),
            finish: String::new(),
            result: variants[1].fields[0].clone(),
            slots: Vec::new(),
            bindings: HashMap::new(),
            values: HashMap::new(),
            reserved: RefCell::new(reserved),
            next: Cell::new(0),
            types: crate::linearcheck::LinearTypes::from_program(&planning.program),
            render: crate::async_render::RenderContext::new(
                body,
                &planning.declarations,
                &function.graph,
            )
            .map_err(|error| fail(function, error.message))?,
            retirement: None,
            lending: crate::async_lend::Plan::new(
                body,
                &planning.declarations.flows[&function.model.body_name],
                &crate::linearcheck::LinearTypes::from_program(&planning.program),
            )
            .map_err(|error| fail(function, error.message))?,
            reference_cells: None,
        };
        emitter.finish = emitter.fresh("frame-finish");
        // Each scope/declaration activates its own cell. The factory installs
        // only initial arguments; it must never execute source declarations.
        for (index, binding) in function.graph.bindings.iter().enumerate() {
            if binding.name == function.model.waker_binding
                || matches!(binding.ty, Type::Unit | Type::Never)
            {
                continue;
            }
            let slot = emitter.add_slot(format!("binding.{index}"), binding.ty.clone());
            emitter.bindings.insert(BindingId(index), slot);
        }
        for (index, value) in function.graph.values.iter().enumerate() {
            if matches!(value.ty, Type::Unit | Type::Never) {
                continue;
            }
            let slot = emitter.add_slot(format!("value.{index}"), value.ty.clone());
            emitter.values.insert(ValueId(index), slot);
        }
        emitter.retirement = crate::async_retire::Plan::new(&function.graph, &emitter.types);
        if let Some(plan) = &emitter.retirement {
            plan.validate(&function.graph)
                .map_err(|error| fail(function, error.message))?;
        }
        emitter.reference_cells = crate::async_cells::Plan::new(
            &function.graph,
            &emitter.types,
            emitter.retirement.as_ref(),
            emitter.lending.as_ref(),
        );
        Ok(emitter)
    }

    fn fresh(&self, role: &str) -> String {
        loop {
            let name = format!("{}.graph.{}.{role}", self.frame, self.next.get());
            self.next.set(self.next.get() + 1);
            if self.reserved.borrow_mut().insert(name.clone()) {
                return name;
            }
        }
    }

    fn add_slot(&mut self, field: String, ty: Type) -> usize {
        let slot = Slot {
            field,
            name: self.fresh("Slot"),
            empty: self.fresh("Empty"),
            full: self.fresh("Full"),
            take: self.fresh("take"),
            put: self.fresh("put"),
            peek: self.fresh("peek"),
            clear: self.fresh("clear"),
            finish: self.fresh("finish"),
            copy: self.types.can_repeat(&ty),
            linear: self.types.is_linear(&ty),
            ty,
        };
        let index = self.slots.len();
        self.slots.push(slot);
        index
    }

    fn slot_ref(slot: &Slot, mutable: bool) -> String {
        format!(
            "(#pin-borrow{} (#get task {}))",
            if mutable { "-mut" } else { "" },
            slot.field
        )
    }

    fn read(&self, slot: usize, transfer: bool) -> String {
        let slot = &self.slots[slot];
        if slot.copy && (!transfer || self.types.contains_reference(&slot.ty)) {
            format!(
                "(#call {} (: slot {}))",
                slot.peek,
                Self::slot_ref(slot, false)
            )
        } else if self.types.contains_reference(&slot.ty) {
            // An owned transfer must make Empty visible before any later
            // suspension. A returned reference does not itself describe the
            // input cell's definite tag; retain its pre-move provenance.
            format!(
                "(#block
                  (#let {cell} (#pin-ref-mut {name}) {reference})
                  (#let {previous} {name} (#unsafe (#pin-read {cell})))
                  (#unsafe (#pin-write {cell} ({empty})))
                  (#drop {cell})
                  (#match {previous}
                    (#case {empty} (#unreachable))
                    (#case ({full} {value}) {value})))",
                cell = self.fresh("taken-cell"),
                previous = self.fresh("taken-storage"),
                value = self.fresh("taken-value"),
                name = slot.name,
                reference = Self::slot_ref(slot, true),
                empty = slot.empty,
                full = slot.full,
            )
        } else {
            format!(
                "(#unsafe (#call {} (: slot {})))",
                slot.take,
                Self::slot_ref(slot, true)
            )
        }
    }

    fn value(&self, value: ValueId, transfer: bool) -> String {
        self.values
            .get(&value)
            .map_or_else(|| "()".into(), |slot| self.read(*slot, transfer))
    }

    fn put(&self, slot: usize, value: &str) -> String {
        let slot = &self.slots[slot];
        if !slot.copy && self.types.contains_reference(&slot.ty) {
            let old = self.fresh("stored-occupied");
            // Stage the input before touching the destination, as a normal
            // call would. Keep the actual stored enum tags visible: a unit
            // helper's invalidation summary cannot establish the child's
            // newly selected payload in the returned Pending frame.
            let occupied = if slot.linear {
                format!("(#block (#forget {old}) (#assert false))")
            } else {
                format!("(#forget {old})")
            };
            return format!(
                "(#block
                  (#let {incoming} {ty} {value})
                  (#let {cell} (#pin-ref-mut {name}) {reference})
                  (#let {previous} {name} (#unsafe (#pin-read {cell})))
                  (#match {previous}
                    (#case {empty} ())
                    (#case ({full} {old}) {occupied}))
                  (#unsafe (#pin-write {cell} ({empty})))
                  (#unsafe (#forget (#pin-read {cell})))
                  (#unsafe (#pin-write {cell} ({full} {incoming})))
                  (#drop {cell}) ())",
                incoming = self.fresh("stored-value"),
                ty = crate::type_source(&slot.ty),
                cell = self.fresh("stored-cell"),
                name = slot.name,
                reference = Self::slot_ref(slot, true),
                previous = self.fresh("stored-storage"),
                empty = slot.empty,
                full = slot.full,
            );
        }
        format!(
            "(#call {} (: slot {} : value {value}))",
            slot.put,
            Self::slot_ref(slot, true)
        )
    }

    fn put_value(&self, value: ValueId, expression: &str) -> String {
        self.values
            .get(&value)
            .map_or_else(|| expression.to_owned(), |slot| self.put(*slot, expression))
    }

    fn slot_definitions(&self) -> String {
        self.slots.iter().map(|slot| {
            let ty = crate::type_source(&slot.ty);
            let occupied = if slot.linear {
                // This branch is a violated compiler/source invariant, not an
                // invented destructor for a live owner. It traps explicitly.
                "(#block (#forget occupied) (#assert false))"
            } else { "(#forget occupied)" };
            let peek = if slot.copy {
                format!("(#fn {} ((slot (#pin-ref {}))) {ty}\n  (#return (#deref (#pin-get-payload slot {} 0))))", slot.peek, slot.name, slot.full)
            } else { String::new() };
            if slot.copy && self.types.contains_reference(&slot.ty) {
                // A shared handle is copied, not extracted through a moving
                // cell helper. End all old loaded aliases before restoration.
                // Full source checking and ordinary call contracts still
                // determine which incoming referents the cell retains.
                return format!("(#enum {name} (({empty}) ({full} {ty})))\n(#linear {name})\n\
                  (#fn {put} ((slot (#pin-ref-mut {name})) (value {ty})) ()\n\
                    (#let previous {name} (#unsafe (#pin-read slot)))\n\
                    (#match previous (#case {empty} ()) (#case ({full} occupied) (#forget occupied)))\n\
                    (#unsafe (#pin-write slot ({full} value)))\n\
                    (#return ()))\n\
                  (#fn {finish} ((slot {name})) ()\n\
                    (#match slot (#case {empty} ()) (#case ({full} occupied) (#forget occupied)))\n\
                    (#return ()))\n\
                  (#fn {clear} ((slot (#pin-ref-mut {name}))) ()\n\
                    (#let previous {name} (#unsafe (#pin-read slot)))\n\
                    (#call {finish} (: slot previous))\n\
                    (#unsafe (#pin-write slot ({empty})))\n\
                    (#return ()))\n{peek}\n",
                    name=slot.name, empty=slot.empty, full=slot.full,
                    put=slot.put, finish=slot.finish, clear=slot.clear);
            }
            if self.types.contains_reference(&slot.ty) {
                // Owned reference transfers are emitted at the actual local
                // cell, where input-slot identities and Empty/Full tags stay
                // visible. Do not emit unused abstract take/put helpers.
                return format!("(#enum {name} (({empty}) ({full} {ty})))\n(#linear {name})\n\
                  (#fn {finish} ((slot {name})) ()\n\
                    (#match slot (#case {empty} ()) (#case ({full} occupied) {occupied}))\n\
                    (#return ()))\n\
                  (#fn {clear} ((slot (#pin-ref-mut {name}))) ()\n\
                    (#let previous {name} (#unsafe (#pin-read slot)))\n\
                    (#call {finish} (: slot previous))\n\
                    (#unsafe (#pin-write slot ({empty})))\n\
                    (#return ()))\n",
                    name=slot.name, empty=slot.empty, full=slot.full,
                    finish=slot.finish, clear=slot.clear);
            }
            format!("(#enum {name} (({empty}) ({full} {ty})))\n(#linear {name})\n\
              (#unsafe-fn {take} ((slot (#pin-ref-mut {name}))) {ty}\n\
                (#let previous {name} (#unsafe (#pin-read slot)))\n\
                (#unsafe (#pin-write slot ({empty})))\n\
                (#return (#match previous\n\
                  (#case {empty} (#unreachable))\n\
                  (#case ({full} value) value))))\n\
              (#fn {put} ((slot (#pin-ref-mut {name})) (value {ty})) ()\n\
                (#let previous {name} (#unsafe (#pin-read slot)))\n\
                (#unsafe (#pin-write slot ({empty})))\n\
                (#match previous (#case {empty} ()) (#case ({full} occupied) {occupied}))\n\
                (#unsafe (#forget (#pin-read slot)))\n\
                (#unsafe (#pin-write slot ({full} value)))\n\
                (#return ()))\n\
              (#fn {finish} ((slot {name})) ()\n\
                (#match slot (#case {empty} ()) (#case ({full} occupied) {occupied}))\n\
                (#return ()))\n\
              (#fn {clear} ((slot (#pin-ref-mut {name}))) ()\n\
                (#let previous {name} (#unsafe (#pin-read slot)))\n\
                (#unsafe (#pin-write slot ({empty})))\n\
                (#call {finish} (: slot previous))\n\
                (#return ()))\n{peek}\n",
                name=slot.name, empty=slot.empty, full=slot.full, take=slot.take,
                put=slot.put, finish=slot.finish, clear=slot.clear)
        }).collect::<Vec<_>>().join("\n")
    }

    fn clear_binding(&self, binding: BindingId) -> String {
        self.bindings
            .get(&binding)
            .map_or_else(String::new, |slot| {
                let slot = &self.slots[*slot];
                format!(
                    "(#call {} (: slot {}))",
                    slot.clear,
                    Self::slot_ref(slot, true)
                )
            })
    }

    fn clear_values(&mut self, values: &[ValueId]) -> String {
        let slots = values
            .iter()
            .map(|value| self.values[value])
            .collect::<Vec<_>>();
        self.clear_handle_slots(&slots)
    }

    fn clear_handle_slots(&mut self, slots: &[usize]) -> String {
        let mut clears = Vec::new();
        for &index in slots {
            let handle = self.fresh("retired-handle");
            let reference = self.fresh("retired-cell");
            let previous = self.fresh("retired-storage");
            let slot = &self.slots[index];
            let occupied = if slot.linear {
                format!("(#block (#forget {handle}) (#assert false))")
            } else {
                format!("(#forget {handle})")
            };
            // Keep Empty visible to ordinary stored-variant facts; a helper's
            // unit return does not describe that definite tag yet. Reference
            // fields retain their checked unsafe-write restoration protocol.
            clears.push(format!(
                "(#block\n\
              (#let {reference} (#pin-ref-mut {}) {})\n\
              (#let {previous} {} (#unsafe (#pin-read {reference})))\n\
              (#match {previous} (#case {} ()) (#case ({} {handle}) {occupied}))\n\
              (#unsafe (#pin-write {reference} ({})))\n\
              (#drop {reference}) ())",
                slot.name,
                Self::slot_ref(slot, true),
                slot.name,
                slot.empty,
                slot.full,
                slot.empty
            ));
        }
        clears.join("\n")
    }

    fn retire_edge(&mut self, block: BlockId, index: usize) -> String {
        let values = self
            .retirement
            .as_ref()
            .map_or_else(Vec::new, |plan| plan.edge[block.0][index].clone());
        self.clear_values(&values)
    }

    fn expose_empty_reference_cells(&mut self, block: BlockId, exit: bool) -> String {
        let cells = self
            .reference_cells
            .as_ref()
            .and_then(|plan| {
                if exit {
                    plan.exit_empty.get(&block).cloned()
                } else {
                    plan.pending_empty.get(&block).cloned()
                }
            })
            .unwrap_or_default();
        let slots = cells
            .iter()
            .filter_map(|cell| match cell {
                crate::async_cells::Cell::Binding(binding) => self.bindings.get(binding).copied(),
                crate::async_cells::Cell::Value(value) => {
                    // Copy retirement already makes this particular Empty write
                    // visible on Pending; do not emit it a second time.
                    if !exit
                        && self
                            .retirement
                            .as_ref()
                            .is_some_and(|plan| plan.edge[block.0][1].contains(value))
                    {
                        None
                    } else {
                        self.values.get(value).copied()
                    }
                }
            })
            .collect::<Vec<_>>();
        self.clear_handle_slots(&slots)
    }

    fn pattern_value(&self, pattern: &crate::async_exec::Pattern) -> Result<String, Error> {
        let ty = &self.function.graph.values[pattern.scrutinee.0].ty;
        if !self.types.can_repeat(ty) {
            return Err(fail(
                self.function,
                "move-only pattern inspection requires stationary storage aliases",
            ));
        }
        Ok(self.value(pattern.scrutinee, false))
    }

    fn pattern_source(
        &self,
        pattern: &crate::async_exec::Pattern,
        names: &HashMap<BindingId, String>,
    ) -> Result<String, Error> {
        let rendered = self
            .render
            .render_pattern(pattern.source, names)
            .map_err(|error| Error {
                message: error.message,
                span: error.span.unwrap_or(self.function.source.function.span),
            })?;
        crate::expression_source(&rendered).map_err(|message| fail(self.function, message))
    }

    fn pattern_bind(
        &mut self,
        pattern: &crate::async_exec::Pattern,
        commit: bool,
    ) -> Result<String, Error> {
        // Repetition is allowed only by the ordinary checked type. This is
        // deliberately not an alias representation for exclusive handles or
        // linear payloads. Those must remain stationary until Commit.
        if !commit {
            self.pattern_value(pattern)?;
        }
        let value = self.value(pattern.scrutinee, commit);
        let mut names = HashMap::new();
        let mut stores = Vec::new();
        for &binding in &pattern.bindings {
            let name = self.fresh("pattern");
            if let Some(slot) = self.bindings.get(&binding) {
                stores.push(self.put(*slot, &name));
            }
            names.insert(binding, name);
        }
        let source = self.pattern_source(pattern, &names)?;
        if source == "_" {
            return Ok(if commit {
                format!("(#forget {value})")
            } else {
                String::new()
            });
        }
        Ok(format!(
            "(#match {value} (#case {source} (#block {} ())) (#case _ (#unreachable)))",
            stores.join("\n")
        ))
    }

    fn owned_projection_place(
        &self,
        descriptor: &PlaceDescriptor,
        mutable: bool,
    ) -> Result<(String, Type), Error> {
        let reject = |message: &str| fail(self.function, message);
        let AddressRoot::Local(binding) = descriptor.root else {
            return Err(reject("projected loads need a checked owned local root"));
        };
        let slot = &self.slots[*self
            .bindings
            .get(&binding)
            .ok_or_else(|| reject("projected owner has no owning cell"))?];
        let mut ty = crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases)
            .map_err(|message| fail(self.function, message))?;
        // This reference exists only during the immediate leaf read. It is
        // neither a captured address nor an independently copied owner.
        let mut place = format!(
            "(#pin-get-payload{} {} {} 0)",
            if mutable { "-mut" } else { "" },
            Self::slot_ref(slot, mutable),
            slot.full
        );
        for projection in &descriptor.projections {
            match projection {
                AddressProjection::Field(field) => {
                    let declaration = self.planning.declarations.field(*field);
                    if self.planning.declarations.field_id(&ty, &declaration.name) != Some(*field)
                        || !matches!(ty, Type::Named(_))
                    {
                        return Err(reject("projected field lost its checked owned identity"));
                    }
                    place = format!("(#get {place} {})", declaration.name);
                    ty = crate::typed_ir::resolve_type(
                        &declaration.ty,
                        &self.planning.declarations.aliases,
                    )
                    .map_err(|message| fail(self.function, message))?;
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = ty else {
                        return Err(reject("projected tuple lost its checked owned type"));
                    };
                    ty = fields
                        .get(*index)
                        .cloned()
                        .ok_or_else(|| reject("projected tuple index is out of bounds"))?;
                    place = format!("(#get {place} {index})");
                }
                _ => {
                    return Err(reject(
                        "projected loads with handles or effectful checks need address snapshots",
                    ))
                }
            }
        }
        if ty != descriptor.ty {
            return Err(reject("projected leaf disagrees with its checked type"));
        }
        if !self.types.can_repeat(&ty) || self.types.contains_reference(&ty) {
            return Err(reject(
                "projected moves or reference holders need checked lending and restoration storage",
            ));
        }
        Ok((place, ty))
    }

    fn owned_projection_read(&self, descriptor: &PlaceDescriptor) -> Result<String, Error> {
        let (place, ty) = self.owned_projection_place(descriptor, false)?;
        if ty == Type::Unit {
            // Unit projections have no bytes and cannot be borrowed. The
            // owned field/tuple path above is still structurally validated.
            return Ok("()".into());
        }
        Ok(format!("(#deref (#pin-borrow {place}))"))
    }

    fn shared_handle_read(&mut self, descriptor: &PlaceDescriptor) -> Result<String, Error> {
        let function = self.function;
        let reject = |message: &str| fail(function, message);
        let AddressRoot::Value(value) = descriptor.root else {
            return Err(reject("shared handle load has no evaluated root"));
        };
        let handle_ty = crate::typed_ir::resolve_type(
            &self.function.graph.values[value.0].ty,
            &self.planning.declarations.aliases,
        )
        .map_err(|message| fail(self.function, message))?;
        let (mut ty, pinned) = match &handle_ty {
            Type::Reference {
                mutable: false,
                target,
            } => (target.as_ref().clone(), false),
            Type::PinnedReference {
                mutable: false,
                target,
            } => (target.as_ref().clone(), true),
            _ => {
                return Err(reject(
                    "address loads require a checked shared reference handle",
                ))
            }
        };
        let Some((AddressProjection::Dereference, projections)) =
            descriptor.projections.split_first()
        else {
            return Err(reject(
                "shared handle load has no checked dereference boundary",
            ));
        };
        if !self.types.can_repeat(&descriptor.ty) {
            return Err(reject(
                "shared handle loads require Copy leaves; exclusive handles need lending storage",
            ));
        }
        // Keep the evaluated handle, including its incoming loan provenance.
        // Only immediate shared reborrows are made while following its path.
        let name = self.fresh("shared-handle");
        let mut steps = vec![format!(
            "(#let {name} {} {})",
            crate::type_source(&handle_ty),
            self.value(value, false)
        )];
        let mut reference = name.clone();
        for (index, projection) in projections.iter().enumerate() {
            let field = match projection {
                AddressProjection::Field(field) => {
                    let declaration = self.planning.declarations.field(*field);
                    if self.planning.declarations.field_id(&ty, &declaration.name) != Some(*field)
                        || !matches!(ty, Type::Named(_))
                    {
                        return Err(reject("shared field lost its checked declaration identity"));
                    }
                    ty = declaration.ty.clone();
                    declaration.name.clone()
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = ty else {
                        return Err(reject("shared tuple lost its checked type"));
                    };
                    ty = fields
                        .get(*index)
                        .cloned()
                        .ok_or_else(|| reject("shared tuple index is out of bounds"))?;
                    index.to_string()
                }
                _ => return Err(reject(
                    "shared projections with effectful checks require selected address snapshots",
                )),
            };
            ty = crate::typed_ir::resolve_type(&ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?;
            if ty != Type::Unit {
                let projected = format!(
                    "(#{}borrow (#get {reference} {field}))",
                    if pinned { "pin-" } else { "" }
                );
                let next = self.fresh("shared-projection");
                let next_ty = if pinned {
                    Type::PinnedReference {
                        mutable: false,
                        target: Box::new(ty.clone()),
                    }
                } else {
                    Type::Reference {
                        mutable: false,
                        target: Box::new(ty.clone()),
                    }
                };
                steps.push(format!(
                    "(#let {next} {} {projected})",
                    crate::type_source(&next_ty)
                ));
                reference = next;
            } else if index + 1 != projections.len() {
                return Err(reject("cannot project through a unit field"));
            }
        }
        if ty != descriptor.ty {
            return Err(reject("shared leaf disagrees with its checked type"));
        }
        Ok(format!(
            "(#block {} {})",
            steps.join("\n"),
            if ty == Type::Unit {
                "()".into()
            } else {
                format!("(#deref {reference})")
            },
        ))
    }

    /// Verify the representation, not source ownership: a partial write can
    /// restore a source leaf, but cannot construct a Full owning cell from
    /// Empty. Source borrowing/linearity must still pass ordinary validation.
    fn check_owned_cells(&self) -> Result<(), Error> {
        let graph = &self.function.graph;
        if !graph.places.iter().any(|descriptor| {
            matches!(descriptor.root, AddressRoot::Local(_)) && !descriptor.projections.is_empty()
        }) {
            return Ok(());
        }
        let mut live = graph.reachable().into_iter().collect::<Vec<_>>();
        live.sort_by_key(|block| block.0);
        let mut predecessors = vec![Vec::new(); graph.blocks.len()];
        for &block in &live {
            for next in graph.successors(block) {
                predecessors[next.0].push(block);
            }
        }
        let initial = (0..graph.bindings.len())
            .map(|index| index < graph.parameter_count)
            .collect::<Vec<_>>();
        let top = vec![true; graph.bindings.len()];
        let mut before = vec![top.clone(); graph.blocks.len()];
        let mut after = before.clone();
        let transfer = |action: &Action, full: &mut Vec<bool>| match action {
            Action::Bind { binding, .. } => full[binding.0] = true,
            Action::Preview(pattern) | Action::Commit(pattern) => {
                for binding in &pattern.bindings {
                    full[binding.0] = true;
                }
            }
            Action::ScopeEnter(bindings) | Action::ScopeExit(bindings) => {
                for binding in bindings {
                    full[binding.0] = false;
                }
            }
            Action::EndPreview(pattern) => {
                for binding in &pattern.bindings {
                    full[binding.0] = false;
                }
            }
            Action::Store { place, .. }
            | Action::Release { place, .. }
            | Action::Load { place, .. } => {
                let descriptor = &graph.places[place.0];
                if let AddressRoot::Local(binding) = descriptor.root {
                    if descriptor.projections.is_empty() {
                        match action {
                            Action::Store { .. } => full[binding.0] = true,
                            Action::Release { .. } => full[binding.0] = false,
                            Action::Load {
                                kind: LoadKind::Read,
                                ..
                            } if !self.types.can_repeat(&graph.bindings[binding.0].ty) => {
                                full[binding.0] = false;
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        };
        loop {
            let mut changed = false;
            for &block in &live {
                let mut incoming = if block == graph.entry {
                    initial.clone()
                } else {
                    top.clone()
                };
                for previous in &predecessors[block.0] {
                    for (full, available) in incoming.iter_mut().zip(&after[previous.0]) {
                        *full &= available;
                    }
                }
                let mut outgoing = incoming.clone();
                for located in &graph.blocks[block.0].actions {
                    transfer(&located.action, &mut outgoing);
                }
                changed |= before[block.0] != incoming || after[block.0] != outgoing;
                before[block.0] = incoming;
                after[block.0] = outgoing;
            }
            if !changed {
                break;
            }
        }
        for block in live {
            let mut full = before[block.0].clone();
            for located in &graph.blocks[block.0].actions {
                let descriptor = match &located.action {
                    Action::Place { descriptor, .. } => Some(descriptor),
                    Action::Load { place, .. }
                    | Action::Store { place, .. }
                    | Action::Release { place, .. }
                    | Action::Borrow { place, .. } => Some(&graph.places[place.0]),
                    _ => None,
                };
                if let Some(PlaceDescriptor {
                    root: AddressRoot::Local(binding),
                    projections,
                    ..
                }) = descriptor
                {
                    if !projections.is_empty() && !full[binding.0] {
                        return Err(Error {
                            message: "projected access requires a definitely Full owning cell; partial reconstruction needs leaf-aware storage".into(),
                            span: located.span.unwrap_or(self.function.source.function.span),
                        });
                    }
                }
                transfer(&located.action, &mut full);
            }
        }
        Ok(())
    }

    fn clone_read(&mut self, ty: &Type, read: &str) -> String {
        // Stage the value once before ordinary clone dispatch. This also
        // gives aggregate hooks a real checked argument binding, rather than
        // requiring native staging to reconstruct nested borrowed projections.
        let temporary = self.fresh("clone-source");
        format!(
            "(#block (#let {temporary} {} {read}) (#clone {temporary}))",
            crate::type_source(ty)
        )
    }

    fn action(&mut self, located: &crate::async_exec::LocatedAction) -> Result<String, Error> {
        let graph = &self.function.graph;
        let error = |message: &str| Error {
            message: message.into(),
            span: located.span.unwrap_or(self.function.source.function.span),
        };
        match &located.action {
            Action::Compute { dst, operation } => {
                let mut inputs = HashMap::new();
                let ids = match operation {
                    Compute::Checked(operation) => operation
                        .operands
                        .iter()
                        .map(|operand| operand.value)
                        .collect::<Vec<_>>(),
                    Compute::Identity(value) => vec![*value],
                    _ => Vec::new(),
                };
                for id in ids {
                    inputs.insert(
                        id,
                        crate::parse(&self.value(id, true))
                            .map_err(|_| error("stored value expression did not parse"))?
                            .remove(0)
                            .expr,
                    );
                }
                let rendered = self
                    .render
                    .render_compute(operation, &inputs)
                    .map_err(|error| Error {
                        message: error.message,
                        span: error.span.unwrap_or(self.function.source.function.span),
                    })?;
                let mut text = crate::expression_source(&rendered)
                    .map_err(|_| error("computed operation did not serialize"))?;
                if located.unsafe_context {
                    text = format!("(#unsafe {text})");
                }
                Ok(self.put_value(*dst, &text))
            }
            Action::Place { descriptor, .. } => {
                let simple_owned = matches!(descriptor.root, AddressRoot::Local(_))
                    && descriptor.projections.iter().all(|projection| {
                        matches!(
                            projection,
                            AddressProjection::Field(_) | AddressProjection::Tuple(_)
                        )
                    });
                let simple_handle = matches!(descriptor.root, AddressRoot::Value(_))
                    && matches!(
                        descriptor.projections.first(),
                        Some(AddressProjection::Dereference)
                    )
                    && descriptor.projections[1..].iter().all(|projection| {
                        matches!(
                            projection,
                            AddressProjection::Field(_) | AddressProjection::Tuple(_)
                        )
                    });
                if (!simple_owned && !simple_handle) || !descriptor.checks().is_empty() {
                    return Err(error(
                        "projected addresses need checked storage and immediate place checks",
                    ));
                }
                Ok(String::new())
            }
            Action::Load { dst, place, kind } => {
                let descriptor = &graph.places[place.0];
                if matches!(descriptor.root, AddressRoot::Value(_)) {
                    let read = self.shared_handle_read(descriptor)?;
                    let read = if *kind == LoadKind::Clone {
                        self.clone_read(&descriptor.ty, &read)
                    } else {
                        read
                    };
                    return Ok(self.put_value(*dst, &read));
                }
                let AddressRoot::Local(binding) = descriptor.root else {
                    return Err(error(
                        "address-handle and global loads need their checked address representation",
                    ));
                };
                if !descriptor.projections.is_empty() {
                    let read = self.owned_projection_read(descriptor)?;
                    let read = if *kind == LoadKind::Clone {
                        self.clone_read(&descriptor.ty, &read)
                    } else {
                        read
                    };
                    return Ok(self.put_value(*dst, &read));
                }
                let Some(slot) = self.bindings.get(&binding) else {
                    return Ok(self.put_value(*dst, "()"));
                };
                if *kind == LoadKind::Read
                    && !self.slots[*slot].copy
                    && self.types.contains_reference(&self.slots[*slot].ty)
                {
                    let access = located.source.and_then(|source| {
                        self.lending.as_ref().and_then(|plan| plan.access(source))
                    });
                    match access {
                        Some(crate::async_lend::Access::Move(place))
                            if place
                                == &crate::typed_place::Place::root(
                                    crate::typed_body::PlaceRoot::Local(binding),
                                ) => {}
                        Some(crate::async_lend::Access::Lend(_)) => {
                            return Err(error(
                                "nonmoving exclusive handle reads require a checked lending lease",
                            ));
                        }
                        _ => {
                            return Err(error(
                                "reference holder move has no matching checked source transfer",
                            ));
                        }
                    }
                }
                let read = match kind {
                    LoadKind::Read => self.read(*slot, false),
                    LoadKind::Clone if self.slots[*slot].copy => {
                        // Copy types may still supply an observable clone
                        // hook. Preserve the ordinary #clone dispatch.
                        let read = self.read(*slot, false);
                        let ty = self.slots[*slot].ty.clone();
                        self.clone_read(&ty, &read)
                    }
                    LoadKind::Clone => return Err(error(
                        "linear clone must call its checked clone hook through a borrowed place",
                    )),
                };
                Ok(self.put_value(*dst, &read))
            }
            Action::Bind { binding, value, .. } => Ok(self.bindings.get(binding).map_or_else(
                || self.value(*value, true),
                |slot| self.put(*slot, &self.value(*value, true)),
            )),
            Action::Store { place, value } => {
                let descriptor = &graph.places[place.0];
                let AddressRoot::Local(binding) = descriptor.root else {
                    return Err(error(
                        "nonlocal stores need their checked address representation",
                    ));
                };
                if !descriptor.projections.is_empty() {
                    let (target, ty) = self.owned_projection_place(descriptor, true)?;
                    let value = self.value(*value, true);
                    return Ok(if ty == Type::Unit {
                        value
                    } else {
                        // Only Copy, reference-free leaves reach this point.
                        // No owner or borrowed handle is moved or captured.
                        format!("(#unsafe (#pin-write (#pin-borrow-mut {target}) {value}))")
                    });
                }
                Ok(self.bindings.get(&binding).map_or_else(
                    || self.value(*value, true),
                    |slot| self.put(*slot, &self.value(*value, true)),
                ))
            }
            Action::Release { place, kind } => {
                let descriptor = &graph.places[place.0];
                let AddressRoot::Local(binding) = descriptor.root else {
                    return Err(error(
                        "nonlocal releases need their checked address representation",
                    ));
                };
                if !descriptor.projections.is_empty() {
                    return Err(error(
                        "partial releases need leaf-aware initialization storage",
                    ));
                }
                if self.bindings.get(&binding).is_some_and(|slot| {
                    self.slots[*slot].copy && self.types.contains_reference(&self.slots[*slot].ty)
                }) {
                    // Copying a shared handle is not ending its stored loan.
                    // Explicit release must actually empty the binding cell.
                    return Ok(self.clear_binding(binding));
                }
                let value = self
                    .bindings
                    .get(&binding)
                    .map_or_else(|| "()".into(), |slot| self.read(*slot, true));
                Ok(format!(
                    "(#{} {value})",
                    match kind {
                        ReleaseKind::Drop => "drop",
                        ReleaseKind::Forget => "forget",
                    }
                ))
            }
            Action::ScopeEnter(_) => Ok(String::new()),
            Action::ScopeExit(bindings) => Ok(bindings
                .iter()
                .map(|binding| self.clear_binding(*binding))
                .collect::<Vec<_>>()
                .join("\n")),
            Action::Borrow { .. } | Action::EndBorrow { .. } => Err(error(
                "borrow/address tokens must retain their checked lifetime and ownership mode",
            )),
            Action::Preview(pattern) => self.pattern_bind(pattern, false),
            Action::Commit(pattern) => self.pattern_bind(pattern, true),
            Action::EndPreview(pattern) => {
                self.pattern_value(pattern)?;
                Ok(pattern
                    .bindings
                    .iter()
                    .map(|binding| self.clear_binding(*binding))
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
        }
    }

    fn edge(
        &mut self,
        block: BlockId,
        index: usize,
        edge: &Edge,
        ready: Option<&str>,
    ) -> Result<String, Error> {
        let parameters = &self.function.graph.blocks[edge.target.0].parameters;
        // Parallel edge transfer: read every source before overwriting a
        // destination. A backedge must not clobber another selected input.
        let mut stages = Vec::new();
        let mut stores = Vec::new();
        for (parameter, argument) in parameters.iter().zip(&edge.arguments) {
            let ty = &self.function.graph.values[parameter.0].ty;
            let value = match argument {
                Argument::Value(value) => self.value(*value, true),
                Argument::Ready(_) => ready
                    .ok_or_else(|| fail(self.function, "Ready edge has no producing payload"))?
                    .into(),
            };
            let name = self.fresh("edge");
            stages.push(format!("(#let {name} {} {value})", crate::type_source(ty)));
            stores.push(self.put_value(*parameter, &name));
        }
        Ok(format!(
            "{}\n{}\n{}\n(#set-field task pc {}u32)\n(#continue)",
            stages.join("\n"),
            self.retire_edge(block, index),
            stores.join("\n"),
            edge.target.0
        ))
    }

    fn terminal(&mut self, block: BlockId, terminal: &Terminator) -> Result<String, Error> {
        match terminal {
            Terminator::Goto(edge) => self.edge(block, 0, edge, None),
            Terminator::Branch { condition, yes, no } => {
                let condition = self.value(*condition, true);
                let yes = self.edge(block, 0, yes, None)?;
                let no = self.edge(block, 1, no, None)?;
                Ok(format!(
                    "(#if {condition} (#block {yes} (#unreachable)) (#block {no} (#unreachable)))"
                ))
            }
            Terminator::Await {
                site,
                child,
                ready,
                pending,
            } => {
                let protocol = &self.function.model.awaits[*site];
                let child_value = self.value(*child, true);
                let polled = self.fresh("polled");
                let next = self.fresh("child");
                let result = self.fresh("ready");
                let poll_type = &self
                    .planning
                    .declarations
                    .function(
                        self.planning
                            .declarations
                            .function_id(&protocol.poll)
                            .unwrap(),
                    )
                    .signature
                    .return_type;
                let mut call = format!(
                    "(#call {} (: task {child_value} : waker waker))",
                    protocol.poll
                );
                if self
                    .planning
                    .interfaces
                    .function(&protocol.poll)
                    .is_some_and(|poll| poll.unsafe_call || poll.external)
                {
                    call = format!("(#unsafe {call})");
                }
                let store = self.put_value(*child, &next);
                let edge = self.edge(block, 0, ready, Some(&result))?;
                let retired = self.retire_edge(block, 1);
                let empty = self.expose_empty_reference_cells(block, false);
                Ok(format!("(#let {polled} {} {call})\n\
                  (#match {polled}\n\
                    (#case ({} {next}) (#block {store} {retired} {empty} (#set-field task pc {}u32) (#return ({} task)) (#unreachable)))\n\
                    (#case ({} {result}) (#block {edge} (#unreachable))))", crate::type_source(poll_type), protocol.pending, pending.0, self.pending, protocol.ready))
            }
            Terminator::Return(value) => {
                let value = value.map_or_else(|| "()".into(), |value| self.value(value, true));
                let name = self.fresh("result");
                let empty = self.expose_empty_reference_cells(block, true);
                let finish = &self.finish;
                Ok(format!("(#let {name} {} {value})\n{empty}\n(#call {finish} (: task task))\n(#return ({} {name}))", crate::type_source(&self.result), self.ready))
            }
            Terminator::Diverge => Ok("(#unreachable)".into()),
            Terminator::PatternTest { pattern, yes, no } => {
                // Wildcards test structure/literals without activating an
                // arm's lexical bindings. Preview or Commit does that later.
                let names = pattern
                    .bindings
                    .iter()
                    .map(|&binding| (binding, "_".into()))
                    .collect();
                let source = self.pattern_source(pattern, &names)?;
                let ty = self.function.graph.values[pattern.scrutinee.0].ty.clone();
                let test = if self.types.can_repeat(&ty) {
                    let value = self.pattern_value(pattern)?;
                    if source == "_" {
                        "true".into()
                    } else {
                        format!("(#match {value} (#case {source} true) (#case _ false))")
                    }
                } else {
                    let slot =
                        &self.slots[*self.values.get(&pattern.scrutinee).ok_or_else(|| {
                            fail(self.function, "stationary scrutinee has no owning cell")
                        })?];
                    let reference = format!(
                        "(#pin-get-payload {} {} 0)",
                        Self::slot_ref(slot, false),
                        slot.full
                    );
                    let reference = crate::parse(&reference)
                        .map_err(|error| fail(self.function, error.to_string()))?
                        .remove(0)
                        .expr;
                    let source = crate::parse(&source)
                        .map_err(|error| fail(self.function, error.to_string()))?
                        .remove(0)
                        .expr;
                    let prefix = self.fresh("pattern-inspect");
                    let test = crate::async_pattern::test(
                        &self.planning.declarations,
                        &source,
                        &ty,
                        reference,
                        &prefix,
                        &mut self.reserved.borrow_mut(),
                    )
                    .map_err(|message| fail(self.function, message))?;
                    crate::expression_source(&test)
                        .map_err(|message| fail(self.function, message))?
                };
                let yes = self.edge(block, 0, yes, None)?;
                let no = self.edge(block, 1, no, None)?;
                Ok(format!(
                    "(#if {test}\n\
                  (#block {yes} (#unreachable)) (#block {no} (#unreachable)))"
                ))
            }
        }
    }

    fn emit(mut self) -> Result<Generated, Error> {
        if self.function.source.pinned_frame.is_some() {
            return Err(fail(
                self.function,
                "pinned dispatch needs stable alias slots and a checked owner storage map",
            ));
        }
        if self
            .planning
            .interfaces
            .functions
            .values()
            .any(|interface| {
                interface.provenance == crate::async_interfaces::Provenance::CancelDispatcher
                    && interface
                        .declaration
                        .parameters
                        .first()
                        .is_some_and(|parameter| parameter.ty == Type::Named(self.frame.clone()))
            })
        {
            return Err(fail(
                self.function,
                "graph cancellation requires state-specific checked cleanup contracts",
            ));
        }
        self.check_owned_cells()?;
        let graph: &Graph = &self.function.graph;
        let mut cases = Vec::new();
        let mut live = graph.reachable().into_iter().collect::<Vec<_>>();
        live.sort_by_key(|block| block.0);
        for BlockId(index) in live {
            let block = &graph.blocks[index];
            let mut actions = Vec::new();
            let retired = self
                .retirement
                .as_ref()
                .map_or_else(Vec::new, |plan| plan.entry[index].clone());
            actions.push(self.clear_values(&retired));
            for (action_index, action) in block.actions.iter().enumerate() {
                actions.push(self.action(action)?);
                let retired = self.retirement.as_ref().map_or_else(Vec::new, |plan| {
                    plan.after_action[index][action_index].clone()
                });
                actions.push(self.clear_values(&retired));
            }
            let terminal = self.terminal(BlockId(index), &block.terminator)?;
            cases.push(format!(
                "(#case {index}u32 (#block {} {terminal} (#unreachable)))",
                actions.join("\n")
            ));
        }
        let fields = self
            .slots
            .iter()
            .map(|slot| format!("({} {})", slot.field, slot.name))
            .collect::<Vec<_>>()
            .join(" ");
        let start_parameters = &self
            .planning
            .interfaces
            .function(&self.function.model.source_name)
            .unwrap()
            .parameters;
        let mut initial = Vec::new();
        for (index, slot) in self.slots.iter().enumerate() {
            let parameter = self.bindings.iter().find_map(|(binding, actual)| {
                (*actual == index && binding.0 < start_parameters.len())
                    .then(|| &start_parameters[binding.0])
            });
            initial.push(format!(
                "({} {})",
                slot.field,
                parameter.map_or_else(
                    || format!("({})", slot.empty),
                    |parameter| format!("({} {})", slot.full, parameter.name)
                )
            ));
        }
        let signature = start_parameters
            .iter()
            .map(|parameter| format!("({} {})", parameter.name, crate::type_source(&parameter.ty)))
            .collect::<Vec<_>>()
            .join(" ");
        let finish_fields = self
            .slots
            .iter()
            .map(|slot| {
                format!(
                    "(#call {} (: slot (#get task {})))",
                    slot.finish, slot.field
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let source = format!(
            "{}\n\
          (#struct {} ((pc u32) {fields}))\n(#linear {})\n\
          (#enum {} (({} {}) ({} {})))\n\
          (#fn {} ({signature}) {}\n\
            (#return (#struct-literal {} ((pc {}u32) {}))))\n\
          (#fn {} ((task {})) ()\n\
            {finish_fields}\n(#forget task)\n(#return ()))\n\
          (#fn {} ((#mut task {}) (waker (#ref {}))) {}\n\
            (#loop (#match (#get task pc) {} (#case _ (#unreachable))))\n\
            (#return (#unreachable)))\n",
            self.slot_definitions(),
            self.frame,
            self.frame,
            self.poll_type,
            self.pending,
            self.frame,
            self.ready,
            crate::type_source(&self.result),
            self.function.model.source_name,
            self.frame,
            self.frame,
            graph.entry.0,
            initial.join(" "),
            self.finish,
            self.frame,
            self.poll,
            self.frame,
            crate::type_source(&self.function.source.waker),
            self.poll_type,
            cases.join("\n")
        );
        let source = crate::generator::format_generated_source(&source)
            .map_err(|message| fail(self.function, message))?;
        Ok(Generated {
            frame: self.frame,
            source,
            origin: self.function.source.function.span,
        })
    }
}

pub(crate) fn generate(planning: &Planning) -> Result<Vec<Generated>, Error> {
    planning
        .functions
        .iter()
        .map(|function| Emitter::new(planning, function)?.emit())
        .collect()
}

/// Complete the proposed declarations in a fresh ordinary program. Neither
/// planning IDs nor header-only interface descriptors become emitted items.
pub(crate) fn program(
    planning: &Planning,
    generated: &[Generated],
) -> Result<Program, SourceError> {
    let witnesses = planning
        .declarations
        .bodies
        .keys()
        .cloned()
        .collect::<HashSet<_>>();
    let mut program = planning.program.clone();
    program.items.retain(
        |item| !matches!(item, Item::Function(function) if witnesses.contains(&function.name)),
    );
    for generated in generated {
        let source_id = u32::try_from(program.source_files.len())
            .map_err(|_| "too many async generated source files")?;
        program.source_files.push(crate::SourceFile {
            path: format!("<async graph {}>", generated.frame).into(),
            source: generated.source.clone(),
        });
        program
            .generated_source_invocations
            .insert(source_id, generated.origin);
        for mut source in crate::parse(&generated.source)? {
            crate::set_source_id(&mut source, source_id);
            crate::normalize_match_case_forms(&mut source).map_err(|(message, span)| {
                SourceError::new(message, DiagnosticCode::Parse).at(span)
            })?;
            crate::collect_function_statement_spans(
                &source,
                &mut program.statement_spans,
                &mut program.statement_expressions,
            );
            let mut expression = crate::normalize_keywords(source.expr.clone());
            crate::normalize_match_cases_expr(&mut expression);
            let item = crate::parse_item(&expression).map_err(|message| {
                SourceError::new(message, DiagnosticCode::Parse).at(source.span)
            })?;
            for name in crate::item_declared_names(&item) {
                program.declaration_spans.insert(name.clone(), source.span);
                program
                    .declaration_expressions
                    .insert(name.clone(), source.clone());
                program
                    .declaration_occurrences
                    .insert(name, vec![source.clone()]);
            }
            program.items.push(item);
        }
    }
    crate::normalize_function_calls(
        &mut program.items,
        &program.statement_spans,
        &program.statement_expressions,
        &program.declaration_spans,
        &program.declaration_expressions,
        &program.source_files,
    )?;
    crate::normalize_struct_literals(
        &mut program.items,
        &program.statement_spans,
        &program.statement_expressions,
        &program.declaration_spans,
        &program.declaration_expressions,
        &program.source_files,
    )?;
    // Full validation appends/checks original source witnesses with real
    // generated interfaces, before inspecting generated unsafe storage code.
    program.async_functions = planning
        .functions
        .iter()
        .map(|function| function.source.clone())
        .collect();
    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        process::Command,
        sync::atomic::{AtomicUsize, Ordering},
        time::{Duration, Instant},
    };

    const CONTEXT: &str = "
      (#enum Child ((Start u64) (Resume u64))) (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Start value) (ChildPending (Resume value)))
          (#case (Resume value) (ChildReady value)))))";

    fn prepare(body: &str, main: &str) -> Planning {
        prepare_function(&format!("(#fn work ((seed u64)) u64 {body})"), main)
    }

    fn prepare_function(function: &str, main: &str) -> Planning {
        let source = format!(
            "{CONTEXT}
          (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64
            : function {function}))
          {main}"
        );
        let syntax = crate::prepare_program_syntax(
            &source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        crate::async_prepare::prepare(&syntax).unwrap()
    }

    fn runtime(body: &str, main: &str, expected: i32) -> Vec<Generated> {
        let planning = prepare(body, main);
        runtime_planned(planning, expected)
    }

    fn runtime_planned(planning: Planning, expected: i32) -> Vec<Generated> {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let generated = generate(&planning).unwrap();
        for output in &generated {
            assert_eq!(
                crate::generator::format_generated_source(&output.source).unwrap(),
                output.source,
                "graph output uses the shared inspectable-source formatter"
            );
        }
        let program = program(&planning, &generated).unwrap();
        let checked = crate::CheckedProgram::validate_with_span(&program).unwrap_or_else(
            |(message, code, span, labels)| {
                let mut error = SourceError::new(message, code);
                if let Some(span) = span {
                    error = error.at(span);
                }
                for (span, label) in labels {
                    error = error.with_label(span, label);
                }
                panic!(
                    "{}\n{}",
                    error.attach(&program.source_files),
                    generated[0].source
                );
            },
        );
        let assembly = crate::codegen::generate_checked_executable_assembly(
            &checked,
            crate::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let binary = std::env::temp_dir().join(format!(
            "lim-async-graph-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        crate::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            crate::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let mut child = Command::new(&binary).spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                fs::remove_file(&binary).unwrap();
                panic!(
                    "async graph execution exceeded five seconds\n{}",
                    generated[0].source
                );
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        fs::remove_file(&binary).unwrap();
        assert_eq!(
            status.code(),
            Some(expected),
            "{status:?}\n{}",
            generated[0].source
        );
        generated
    }

    const RUN: &str = "
      (#fn main () u64
        (#let waker u64 0u64)
        (#let-mut task Frame (#call work (: seed 40u64)))
        (#loop
          (#match (#call poll (: task task : waker (#borrow waker)))
            (#case (Pending next) (#block (#set task next) ()))
            (#case (Ready value) (#block (#return value) (#unreachable)))))
        (#return (#unreachable)))";

    #[test]
    fn dispatcher_executes_nested_branches_and_loops_across_pending() {
        let generated = runtime(
            "
          (#let-mut total u64 seed)
          (#for (#let-mut index u64 0u64) (#u64.< index 2u64) (#set index (#u64.+.wrap index 1u64))
            (#set total (#u64.+.wrap total
              (#if (#u64.== index 0u64)
                (#await Child ChildPending ChildReady child-poll (Start 1u64))
                (#await Child ChildPending ChildReady child-poll (Start 1u64))))))
          (#return total)",
            RUN,
            42,
        );
        assert!(generated[0].source.contains("(#loop"));
        assert!(generated[0].source.contains("(#match (#get task pc)"));
        assert!(!generated[0].source.contains("poll-resume-"));
    }

    #[test]
    fn linear_locals_are_consumed_and_not_implicitly_destroyed() {
        let body = "
          (#let resource Child (Start seed))
          (#let result u64 (#await Child ChildPending ChildReady child-poll resource))
          (#return (#u64.+.wrap result 2u64))";
        runtime(body, RUN, 42);
        let planning = prepare(
            "
          (#let resource Child (Start seed))
          (#let result u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
          (#return result)",
            RUN,
        );
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Linear);
        let span = error.2.unwrap();
        assert_eq!(span.source_id, 0);
        assert_eq!(
            &program.source_files[0].source[span.start..span.end],
            "resource"
        );
    }

    #[test]
    fn value_break_and_outer_transfer_paths_reach_selected_continuations() {
        runtime(
            "
          (#let result u64 (#label outer (#loop
            (#let result u64 (#await Child ChildPending ChildReady child-poll (Start seed)))
            (#loop (#break-to outer (#u64.+.wrap result 2u64))))))
          (#return result)",
            RUN,
            42,
        );
    }

    #[test]
    fn pending_retries_polling_without_repeating_child_construction() {
        let main = "
          (#fn main () u64
            (#let waker u64 0u64)
            (#let first Poll (#call poll (: task (#call work (: seed 40u64)) : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#return (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready value) value)
              (#case (Pending bad) (#block (#forget bad) (#unreachable))))))";
        runtime("(#return (#u64.+.wrap seed (#await Child ChildPending ChildReady child-poll (Start 2u64))))", main, 42);
    }

    #[test]
    fn guarded_copy_patterns_keep_scrutinees_across_rejected_awaits() {
        runtime(
            "
          (#return (#match (#tuple (#tuple u64) seed)
            (#case (#tuple value) (#when (#u64.==
              (#await Child ChildPending ChildReady child-poll (Start 1u64)) 0u64))
              (#u64.+.wrap value 100u64))
            (#case (#tuple value) (#u64.+.wrap value
              (#await Child ChildPending ChildReady child-poll (Start 2u64))))
            (#case _ (#unreachable))))",
            RUN,
            42,
        );
    }

    #[test]
    fn copy_destructuring_and_if_let_bind_selected_values() {
        runtime(
            "
          (#let pair (#tuple u64 u64) (#tuple (#tuple u64 u64) seed 2u64))
          (#let (#tuple first second) (#tuple u64 u64) pair)
          (#return (#if-let (#tuple value) (#tuple (#tuple u64) first)
            (#u64.+.wrap value (#await Child ChildPending ChildReady child-poll (Start second)))
            99u64))",
            RUN,
            42,
        );
    }

    #[test]
    fn linear_enum_patterns_inspect_in_place_then_commit_once() {
        let generated = runtime(
            "(#let task Child (Start seed))
          (#return (#match task
            (#case (Resume _) 0u64)
            (#case (Start value) (#u64.+.wrap value
              (#await Child ChildPending ChildReady child-poll (Start 2u64))))))",
            RUN,
            42,
        );
        assert!(generated[0].source.contains("#variant-is"));
        assert!(generated[0].source.contains("pattern-inspect"));
    }

    #[test]
    fn linear_nested_aggregate_patterns_only_load_copy_leaves() {
        let main = format!(
            "(#struct Leaf ((number u64) (enabled bool))) (#linear Leaf)
          (#struct Container ((leaf Leaf) (items (#array u64 2)))) (#linear Container)
          (#enum Owned ((Packed Container) Absent)) (#linear Owned)
          {RUN}"
        );
        runtime(
            "(#let owned Owned (Packed (#struct-literal Container
              (: leaf (#struct-literal Leaf (: number seed : enabled true))
               : items (#array-of (#array u64 2) 1u64 2u64)))))
          (#return (#match owned
            (#case Absent 0u64)
            (#case (Packed (Container (Leaf value true) (#array 1u64 2u64)))
              (#u64.+.wrap value (#await Child ChildPending ChildReady child-poll (Start 2u64))))
            (#case _ 3u64)))",
            &main,
            42,
        );
    }

    #[test]
    fn linear_tuple_destructuring_and_if_let_commit_after_inspection() {
        runtime(
            "(#let tuple (#tuple Child u64)
              (#tuple (#tuple Child u64) (Start seed) 2u64))
          (#let (#tuple child bias) (#tuple Child u64) tuple)
          (#return (#if-let (Start value) child
            (#u64.+.wrap bias (#await Child ChildPending ChildReady child-poll (Start value)))
            0u64))",
            RUN,
            42,
        );
    }

    #[test]
    fn rejected_linear_tests_retain_owners_and_short_circuit_payload_access() {
        let main = format!("(#type OwnedTuple (#tuple Child u64)) {RUN}");
        for (number, expected) in [(3u64, 42), (8, 42), (9, 41)] {
            runtime(
                &format!(
                    "(#let owner OwnedTuple
                  (#tuple OwnedTuple (Start seed) {number}u64))
                (#return (#match owner
                  (#case (#tuple _ (#or (#range 2u64 4u64) 8u64))
                    (#await Child ChildPending ChildReady child-poll (Start 42u64)))
                  (#case _ (#await Child ChildPending ChildReady child-poll (Start 41u64)))))"
                ),
                &main,
                expected,
            );
        }
        runtime(
            "(#let owner Child (Start seed))
          (#return (#match owner
            (#case (Resume 9u64) 0u64)
            (#case (Start 39u64) 1u64)
            (#case _ (#await Child ChildPending ChildReady child-poll (Start 42u64)))))",
            RUN,
            42,
        );
    }

    #[test]
    fn copy_fields_are_read_in_place_and_staged_before_later_awaits() {
        let main = format!(
            "(#type Pair (#tuple u64 u64))
          (#struct Inner ((padding u64) (empty ()) (pair Pair))) (#linear Inner)
          (#struct Owner ((padding u64) (inner Inner))) (#linear Owner)
          {RUN}"
        );
        runtime(
            "(#let owner Owner (#struct-literal Owner
              (: padding 99u64 : inner (#struct-literal Inner
                (: padding 88u64 : empty () : pair (#tuple Pair seed 1u64))))))
          (#let empty () (#get (#get owner inner) empty))
          (#let first u64 (#get (#get (#get owner inner) pair) 0))
          (#let second u64 (#get (#get (#get owner inner) pair) 1))
          (#forget owner)
          (#return (#u64.+.wrap first
            (#await Child ChildPending ChildReady child-poll (Start (#u64.+.wrap second 1u64)))))",
            &main,
            42,
        );
    }

    #[test]
    fn suspended_array_constructors_use_array_of_not_array_type_syntax() {
        let main = format!(
            "(#type Pair (#array u64 2))
          (#fn sum ((items Pair)) u64
            (#return (#u64.+.wrap (#index items 0usize) (#index items 1usize))))
          {RUN}"
        );
        let generated = runtime(
            "(#let items Pair (#array-of Pair seed
              (#await Child ChildPending ChildReady child-poll (Start 2u64))))
          (#return (#call sum (: items items)))",
            &main,
            42,
        );
        fn constructor_heads(expression: &Expr, heads: &mut Vec<String>) {
            if let Expr::List(items) = expression {
                if let [Expr::Symbol(head), Expr::List(ty), ..] = items.as_slice() {
                    if matches!(ty.first(), Some(Expr::Symbol(name)) if name == "#array") {
                        heads.push(head.clone());
                    }
                }
                for child in items {
                    constructor_heads(child, heads);
                }
            }
        }
        let mut heads = Vec::new();
        for expression in crate::parse(&generated[0].source).unwrap() {
            constructor_heads(&expression.expr, &mut heads);
        }
        assert!(heads.iter().any(|head| head == "#array-of"));
        assert!(!heads.iter().any(|head| head == "#array"));
    }

    #[test]
    fn incoming_shared_handles_are_read_without_losing_their_loans() {
        for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
            let main = format!(
                "(#fn main () u64
                (#let waker u64 0u64) (#let value u64 40u64)
                (#let view ({ty} u64) ({borrow} value))
                (#let task Frame (#call work (: value view)))
                (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                (#let-else (Pending next) Poll first (#unreachable))
                (#assert (#u64.== (#deref view) 40u64))
                (#return (#match (#call poll (: task next : waker (#borrow waker)))
                  (#case (Ready result) result)
                  (#case (Pending bad) (#block (#forget bad) (#unreachable))))))"
            );
            runtime_planned(
                prepare_function(
                    &format!(
                        "(#fn work ((value ({ty} u64))) u64
                        (#let loaded u64 (#deref value))
                        (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                        (#assert (#u64.== loaded (#deref value)))
                        (#return (#u64.+.wrap loaded child)))"
                    ),
                    &main,
                ),
                42,
            );
        }
    }

    #[test]
    fn releasing_one_incoming_handle_does_not_retire_its_live_alias() {
        let main = "(#fn main () u64
          (#let waker u64 0u64) (#let value u64 20u64)
          (#let task Frame (#call work (: value (#borrow value))))
          (#let first Poll (#call poll (: task task : waker (#borrow waker))))
          (#let-else (Pending next) Poll first (#unreachable))
          (#return (#match (#call poll (: task next : waker (#borrow waker)))
            (#case (Ready result) result)
            (#case (Pending bad) (#block (#forget bad) (#unreachable))))))";
        let generated = runtime_planned(
            prepare_function(
                "(#fn work (: value (#ref u64)) u64
              (#let alias (#ref u64) value)
              (#let first u64 (#deref value)) (#drop value)
              (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#u64.+.wrap first (#deref alias)) child)))",
                main,
            ),
            42,
        );
        assert!(generated[0].source.contains("retired-storage"));
    }

    #[test]
    fn selected_shared_handles_survive_branch_transfers_and_loop_retries() {
        let main = "(#fn main () u64
          (#let waker u64 0u64) (#let left u64 20u64) (#let right u64 99u64)
          (#let-mut task Frame (#call work (: choose true : left (#borrow left) : right (#borrow right))))
          (#loop
            (#let result Poll (#call poll (: task task : waker (#borrow waker))))
            (#match result
              (#case (Pending next) (#block (#set task next) ()))
              (#case (Ready answer) (#block (#return answer) ()))))
          (#return (#unreachable)))";
        runtime_planned(
            prepare_function(
                "(#fn work (: choose bool : left (#ref u64) : right (#ref u64)) u64
              (#let selected (#ref u64) (#if choose left right))
              (#drop left) (#drop right)
              (#let-mut count u64 0u64) (#let-mut sum u64 0u64)
              (#while (#u64.< count 2u64)
                (#let before u64 (#deref selected))
                (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
                (#assert (#u64.== before (#deref selected)))
                (#set sum (#u64.+.wrap sum (#u64.+.wrap before child)))
                (#set count (#u64.+.wrap count 1u64)))
              (#return sum))",
                main,
            ),
            42,
        );
    }

    #[test]
    fn copy_children_keep_shared_loans_and_transfer_ready_references() {
        let extra =
            "(#enum ReferenceStep ((ReferenceStart (#ref u64)) (ReferenceResume (#ref u64))))
          (#enum ReferencePoll ((ReferencePending ReferenceStep) (ReferenceReady (#ref u64))))
          (#fn reference-poll (: task ReferenceStep : waker (#ref u64)) ReferencePoll
            (#return (#match task
              (#case (ReferenceStart value) (ReferencePending (ReferenceResume value)))
              (#case (ReferenceResume value) (ReferenceReady value)))))";
        let function = "(#fn work (: value (#ref u64)) u64
          (#let before u64 (#deref value))
          (#let step ReferenceStep (ReferenceStart value)) (#drop value)
          (#let after (#ref u64)
            (#await ReferenceStep ReferencePending ReferenceReady reference-poll
              (#block (#let sending ReferenceStep step) (#drop step) sending)))
          (#return (#u64.+.wrap (#u64.+.wrap before (#deref after)) 2u64)))";
        let main = format!(
            "{extra}
          (#fn main () u64
            (#let waker u64 0u64) (#let value u64 20u64)
            (#let task Frame (#call work (: value (#borrow value))))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#return (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready result) result)
              (#case (Pending bad) (#block (#forget bad) (#unreachable))))))"
        );
        let planning = prepare_function(function, &main);
        for checked in &planning.functions {
            let plan = crate::async_retire::Plan::new(
                &checked.graph,
                &crate::linearcheck::LinearTypes::from_program(&planning.program),
            )
            .unwrap();
            for (index, block) in checked.graph.blocks.iter().enumerate() {
                if let Terminator::Await { child, .. } = block.terminator {
                    assert!(
                        crate::linearcheck::LinearTypes::from_program(&planning.program)
                            .can_repeat(&checked.graph.values[child.0].ty)
                    );
                    assert!(
                        !plan.edge[index][1].contains(&child),
                        "the restored Copy child is not retired before Pending"
                    );
                }
            }
        }
        runtime_planned(planning, 42);

        // The source handle and its named child copy have both been released.
        // Only the actual suspended child keeps the referent borrowed now.
        let bad_main = format!(
            "{extra}
          (#fn main () u64
            (#let waker u64 0u64) (#let-mut value u64 20u64)
            (#let task Frame (#call work (: value (#borrow value))))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#set value 21u64) (#forget next) (#return 0u64))"
        );
        let planning = prepare_function(function, &bad_main);
        let generated = generate(&planning).unwrap();
        let proposed = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&proposed)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Borrow);
        let span = error.2.unwrap();
        let source = &proposed.source_files[span.source_id as usize].source;
        assert_eq!(&source[span.start..span.end], "#set");
    }

    #[test]
    fn owned_exclusive_children_transfer_without_copying_their_handles() {
        let extra = "(#enum ExclusiveChild ((ExclusiveStart (#ref-mut u64)) (ExclusiveResume (#ref-mut u64))))
          (#linear ExclusiveChild)
          (#enum ExclusivePoll ((ExclusivePending ExclusiveChild) (ExclusiveReady u64)))
          (#fn exclusive-poll (: task ExclusiveChild : waker (#ref u64)) ExclusivePoll
            (#return (#match task
              (#case (ExclusiveStart view) (#block
                (#deref-set view (#u64.+.wrap (#deref view) 1u64))
                (ExclusivePending (ExclusiveResume view))))
              (#case (ExclusiveResume view) (#block
                (#deref-set view (#u64.+.wrap (#deref view) 1u64))
                (ExclusiveReady (#deref view)))))))";
        let function = "(#fn work (: view (#ref-mut u64)) u64
          (#let child ExclusiveChild (ExclusiveStart view))
          (#return (#await ExclusiveChild ExclusivePending ExclusiveReady exclusive-poll child)))";
        let main = format!(
            "{extra}
              (#fn main () u64
                (#let waker u64 0u64) (#let-mut value u64 40u64)
                (#let task Frame (#call work (: view (#borrow-mut value))))
                (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                (#let-else (Pending next) Poll first (#unreachable))
                (#let answer u64 (#match (#call poll (: task next : waker (#borrow waker)))
                  (#case (Ready answer) answer)
                  (#case (Pending bad) (#block (#forget bad) (#unreachable)))))
                (#assert (#u64.== value 42u64)) (#return answer))"
        );
        runtime_planned(prepare_function(function, &main), 42);
        let bad_main = main.replace(
            "(#let-else (Pending next)",
            "(#set value 0u64) (#let-else (Pending next)",
        );
        let planning = prepare_function(function, &bad_main);
        let generated = generate(&planning).unwrap();
        let proposed = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&proposed)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Borrow);
        let span = error.2.unwrap();
        let source = &proposed.source_files[span.source_id as usize].source;
        assert_eq!(&source[span.start..span.end], "#set");
    }

    #[test]
    fn exclusive_handle_reads_fail_closed_until_lending_is_emitted() {
        let planning = prepare_function(
            "(#fn work (: view (#ref-mut u64)) u64
              (#let before u64 (#deref view))
              (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap before (#deref view))))",
            "(#fn main () u64 (#return 0u64))",
        );
        let error = generate(&planning).err().unwrap();
        assert!(
            error.message.contains("checked lending lease"),
            "{}",
            error.message
        );
        let source = &planning.program.source_files[error.span.source_id as usize].source;
        assert_eq!(&source[error.span.start..error.span.end], "view");
    }

    #[test]
    fn shared_reference_fields_survive_outer_handle_release() {
        for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
            let extra = "(#struct Holder (: padding u64 : view (#ref u64)))";
            let function = format!(
                "(#fn work (: holder ({ty} Holder)) u64
                  (#let loaded (#ref u64) (#get holder view)) (#drop holder)
                  (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#deref loaded) child)))"
            );
            let main = format!(
                "{extra}
                  (#fn main () u64
                    (#let waker u64 0u64) (#let value u64 40u64)
                    (#let holder Holder (#struct-literal Holder (: padding 99u64 : view (#borrow value))))
                    (#let task Frame (#call work (: holder ({borrow} holder))))
                    (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                    (#let-else (Pending next) Poll first (#unreachable))
                    (#let result u64 (#match (#call poll (: task next : waker (#borrow waker)))
                      (#case (Ready result) result)
                      (#case (Pending bad) (#block (#forget bad) (#unreachable)))))
                    (#forget holder) (#return result))"
            );
            runtime_planned(prepare_function(&function, &main), 42);

            let bad_main = format!(
                "{extra}
                  (#fn main () u64
                    (#let waker u64 0u64) (#let-mut value u64 40u64)
                    (#let holder Holder (#struct-literal Holder (: padding 99u64 : view (#borrow value))))
                    (#let task Frame (#call work (: holder ({borrow} holder))))
                    (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                    (#let-else (Pending next) Poll first (#unreachable))
                    (#set value 99u64) (#forget next) (#return 0u64))"
            );
            // Only the copied leaf remains live after the outer handle was
            // dropped. Empty-cell witnesses now expose that distinction to
            // the ordinary checker: releasing the container is valid, but
            // mutating the copied reference's pointee remains forbidden.
            let release_main = main
                .replace(
                    "(#let-else (Pending next) Poll first (#unreachable))",
                    "(#let-else (Pending next) Poll first (#unreachable)) (#forget holder)",
                )
                .replace("(#forget holder) (#return result)", "(#return result)");
            runtime_planned(prepare_function(&function, &release_main), 42);
            for (main, keyword) in [
                (bad_main.clone(), "#set"),
                (
                    bad_main.replace("(#set value 99u64)", "(#forget holder) (#set value 99u64)"),
                    "#set",
                ),
            ] {
                let planning = prepare_function(&function, &main);
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                let error = crate::CheckedProgram::validate_with_span(&proposed)
                    .err()
                    .unwrap();
                assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
                let span = error.2.unwrap();
                let source = &proposed.source_files[span.source_id as usize].source;
                assert_eq!(&source[span.start..span.end], keyword);
            }
        }
    }

    #[test]
    fn shared_copy_aggregate_fields_keep_nested_references_across_pending() {
        let main = "(#struct Stored (: view (#ref u64)))
          (#struct Holder (: padding u64 : stored Stored)) (#linear Holder)
          (#fn read-stored (: value Stored) u64 (#return (#deref (#get value view))))
          (#fn main () u64
            (#let waker u64 0u64) (#let value u64 40u64)
            (#let holder Holder (#struct-literal Holder (: padding 99u64
              : stored (#struct-literal Stored (: view (#borrow value))))))
            (#let task Frame (#call work (: holder (#borrow holder))))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#let result u64 (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready result) result)
              (#case (Pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget holder) (#return result))";
        runtime_planned(
            prepare_function(
                "(#fn work (: holder (#ref Holder)) u64
                  (#let loaded Stored (#get holder stored)) (#drop holder)
                  (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#call read-stored (: value loaded)) child)))",
                main,
            ),
            42,
        );
    }

    #[test]
    fn shared_nested_fields_are_read_without_copying_linear_referents() {
        for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
            let main = format!(
                "(#type Pair (#tuple u64 u64))
                (#struct Inner ((padding u64) (pair Pair))) (#linear Inner)
                (#struct Owner ((padding u64) (inner Inner))) (#linear Owner)
                (#fn main () u64
                  (#let waker u64 0u64)
                  (#let owner Owner (#struct-literal Owner (: padding 77u64
                    : inner (#struct-literal Inner (: padding 88u64
                      : pair (#tuple (#tuple u64 u64) 40u64 99u64))))))
                  (#let view ({ty} Owner) ({borrow} owner))
                  (#let task Frame (#call work (: view view)))
                  (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                  (#let-else (Pending next) Poll first (#unreachable))
                  (#assert (#u64.== (#get view padding) 77u64))
                  (#let result u64 (#match (#call poll (: task next : waker (#borrow waker)))
                    (#case (Ready result) result)
                    (#case (Pending bad) (#block (#forget bad) (#unreachable)))))
                  (#drop view) (#forget owner) (#return result))"
            );
            runtime_planned(
                prepare_function(
                    &format!(
                        "(#fn work ((view ({ty} Owner))) u64
                        (#return (#u64.+.wrap (#get (#get (#get view inner) pair) 0)
                          (#await Child ChildPending ChildReady child-poll (Start 2u64)))))"
                    ),
                    &main,
                ),
                42,
            );
        }
    }

    #[test]
    fn pending_shared_handles_keep_the_original_callers_borrow() {
        let planning = prepare_function(
            "(#fn work ((view (#ref u64))) u64
              (#let child u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#deref view) child)))",
            "(#fn main () u64
              (#let waker u64 0u64) (#let-mut value u64 40u64)
              (#let task Frame (#call work (: view (#borrow value))))
              (#let first Poll (#call poll (: task task : waker (#borrow waker))))
              (#let-else (Pending next) Poll first (#unreachable))
              (#set value 99u64)
              (#return (#match (#call poll (: task next : waker (#borrow waker)))
                (#case (Ready result) result)
                (#case (Pending bad) (#block (#forget bad) (#unreachable))))))",
        );
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("Pending still retains a reference to value");
        assert_eq!(code, DiagnosticCode::Borrow, "{message}");
        assert!(
            message.contains("value") && message.contains("borrow"),
            "{message}"
        );
        let span = span.expect("caller mutation has an exact span");
        let source = &program.source_files[span.source_id as usize].source;
        assert_eq!(span.source_id, 0);
        assert_eq!(&source[span.start..span.end], "#set");
    }

    #[test]
    fn shared_handle_frames_cannot_escape_a_callers_local_referent() {
        let planning = prepare_function(
            "(#fn work ((view (#ref u64))) u64
              (#return (#u64.+.wrap (#deref view)
                (#await Child ChildPending ChildReady child-poll (Start 2u64)))))",
            "(#fn escape () Frame
              (#let value u64 40u64)
              (#return (#call work (: view (#borrow value)))))
              (#fn main () u64 (#return 42u64))",
        );
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("frame retains a borrow of a caller local");
        assert_eq!(code, DiagnosticCode::Borrow, "{message}");
        assert!(message.contains("local 'value'"), "{message}");
        let span = span.expect("escape is located in caller source");
        assert_eq!(span.source_id, 0);
    }

    #[test]
    fn computed_shared_receivers_are_evaluated_once_before_later_awaits() {
        let planning = prepare_function(
            "(#fn work ((view (#ref Owner)) (count (#ptr-mut u64))) u64
              (#return (#u64.+.wrap
                (#get (#unsafe (#call select (: view view : count count))) value)
                (#await Child ChildPending ChildReady child-poll (Start 2u64)))))",
            "(#struct Owner ((padding u64) (value u64))) (#linear Owner)
              (#unsafe-fn select ((view (#ref Owner)) (count (#ptr-mut u64))) (#ref Owner)
                (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
                (#return view))
              (#fn main () u64
                (#let waker u64 0u64) (#let-mut count u64 0u64)
                (#let pointer (#ptr-mut u64) (#unsafe (#asm (#ptr-mut u64)
                  ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
                (#let owner Owner (#struct-literal Owner (: padding 77u64 : value 40u64)))
                (#let task Frame (#call work (: view (#borrow owner) : count pointer)))
                (#assert (#u64.== count 0u64))
                (#let first Poll (#call poll (: task task : waker (#borrow waker))))
                (#let-else (Pending next) Poll first (#unreachable))
                (#assert (#u64.== count 1u64))
                (#let result u64 (#match (#call poll (: task next : waker (#borrow waker)))
                  (#case (Ready result) result)
                  (#case (Pending bad) (#block (#forget bad) (#unreachable)))))
                (#assert (#u64.== count 1u64))
                (#forget owner) (#return result))",
        );
        runtime_planned(planning, 42);
    }

    #[test]
    fn copy_projected_operands_survive_pending_without_moving_the_owner() {
        let main = format!("(#struct Owner ((value u64))) (#linear Owner) {RUN}");
        runtime(
            "(#let owner Owner (#struct-literal Owner (: value seed)))
          (#let result u64 (#u64.+.wrap (#get owner value)
            (#await Child ChildPending ChildReady child-poll (Start 2u64))))
          (#assert (#u64.== (#get owner value) seed))
          (#forget owner) (#return result)",
            &main,
            42,
        );
    }

    #[test]
    fn copy_fields_are_updated_after_rhs_awaits_without_moving_the_owner() {
        let main =
            format!("(#struct Owner ((padding u64) (empty ()) (value u64))) (#linear Owner) {RUN}");
        let generated = runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : empty () : value 0u64)))
          (#set-field owner value (#await Child ChildPending ChildReady child-poll (Start seed)))
          (#assert (#u64.== (#get owner padding) 77u64))
          (#let-mut pair (#tuple u64 u64) (#tuple (#tuple u64 u64) (#get owner value) 0u64))
          (#set-field pair 1 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#set-field owner empty (#block (#assert true) ()))
          (#let result u64 (#u64.+.wrap (#get pair 0) (#get pair 1)))
          (#forget owner) (#return result)",
            &main,
            42,
        );
        assert!(generated[0].source.contains("#pin-borrow-mut"));
    }

    #[test]
    fn projected_write_rhs_is_evaluated_once_before_pending_retries() {
        let main = "(#struct Owner ((padding u64) (value u64))) (#linear Owner)
          (#fn counted ((count (#ptr-mut u64))) Child
            (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
            (#return (Start 2u64)))
          (#fn main () u64
            (#let waker u64 0u64) (#let-mut count u64 0u64)
            (#let pointer (#ptr-mut u64) (#unsafe (#asm (#ptr-mut u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Frame (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#assert (#u64.== count 1u64))
            (#return (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready value) (#block (#assert (#u64.== count 1u64)) value))
              (#case (Pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed u64) (count (#ptr-mut u64))) u64
            (#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : value seed)))
            (#set-field owner value (#u64.+.wrap (#get owner value)
              (#await Child ChildPending ChildReady child-poll (#call counted (: count count)))))
            (#assert (#u64.== (#get owner padding) 77u64))
            (#let result u64 (#get owner value)) (#forget owner) (#return result))",
            main,
        );
        runtime_planned(planning, 42);
    }

    #[test]
    fn projected_access_does_not_reconstruct_an_empty_owner_cell() {
        // Representation verification must fail even before the proposed
        // ordinary program is checked. It is not a source ownership exemption.
        for body in [
            "(#forget owner) (#set-field owner value 42u64)",
            "(#if (#u64.== seed 0u64) (#forget owner) ())
              (#set-field owner value 42u64)",
            "(#while (#u64.== seed 0u64) (#forget owner))
              (#set-field owner value 42u64)",
            "(#set-field owner value (#block (#forget owner)
              (#await Child ChildPending ChildReady child-poll (Start 42u64))))",
        ] {
            let planning = prepare(
                &format!(
                    "(#let-mut owner Owner (#struct-literal Owner (: value seed)))
                    {body} (#forget owner) (#return 42u64)"
                ),
                &format!("(#struct Owner ((value u64))) (#linear Owner) {RUN}"),
            );
            let error = generate(&planning).err().expect("owner cell may be Empty");
            assert!(
                error.message.contains("definitely Full"),
                "{}",
                error.message
            );
        }

        // A genuine whole-cell reconstruction remains supported.
        runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: value 0u64)))
          (#forget owner)
          (#set owner (#struct-literal Owner (: value seed)))
          (#set-field owner value (#u64.+.wrap (#get owner value)
            (#await Child ChildPending ChildReady child-poll (Start 2u64))))
          (#let result u64 (#get owner value)) (#forget owner) (#return result)",
            &format!("(#struct Owner ((value u64))) (#linear Owner) {RUN}"),
            42,
        );
    }

    #[test]
    fn projected_copy_writes_preserve_full_cells_around_loop_backedges() {
        runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : value seed)))
          (#for (#let-mut index u64 0u64) (#u64.< index 2u64)
            (#set index (#u64.+.wrap index 1u64))
            (#set-field owner value (#u64.+.wrap (#get owner value)
              (#await Child ChildPending ChildReady child-poll (Start 1u64)))))
          (#assert (#u64.== (#get owner padding) 77u64))
          (#let result u64 (#get owner value)) (#forget owner) (#return result)",
            &format!("(#struct Owner ((padding u64) (value u64))) (#linear Owner) {RUN}"),
            42,
        );
    }

    #[test]
    fn copy_clone_hooks_run_once_for_projected_and_plain_loads() {
        let main = "(#struct Value ((number u64) (count (#ptr-mut u64))))
          (#fn Value-clone ((value Value)) Value
            (#unsafe (#ptr-write (#get value count)
              (#u64.+.wrap (#ptr-read (#get value count)) 1u64)))
            (#return value))
          (#fn main () u64
            (#let waker u64 0u64)
            (#let-mut count u64 0u64)
            (#let pointer (#ptr-mut u64) (#unsafe (#asm (#ptr-mut u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Frame (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#assert (#u64.== count 2u64))
            (#return (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready value) (#block
                (#assert (#u64.== count 2u64)) value))
              (#case (Pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed u64) (count (#ptr-mut u64))) u64
            (#let owner (#tuple Value u64) (#tuple (#tuple Value u64)
              (#struct-literal Value (: number seed : count count)) 0u64))
            (#let projected Value (#clone (#get owner 0)))
            (#let plain Value (#clone projected))
            (#return (#u64.+.wrap (#get plain number)
              (#await Child ChildPending ChildReady child-poll (Start 2u64)))))",
            main,
        );
        runtime_planned(planning, 42);
    }

    #[test]
    fn unsupported_storage_modes_fail_before_proposing_unsafe_code() {
        let planning = prepare(
            "(#let items (#array u64 1) (#array-of (#array u64 1) seed))
          (#return (#index items (#as
            (#await Child ChildPending ChildReady child-poll (Start 0u64)) usize)))",
            RUN,
        );
        let error = generate(&planning).err().unwrap();
        assert!(error.message.contains("immediate place checks"));
        let planning = prepare(
            "
          (#let owner (#tuple u64 u64) (#tuple (#tuple u64 u64) seed 2u64))
          (#let view (#ref u64) (#borrow (#get owner 0)))
          (#return (#u64.+.wrap (#deref view)
            (#await Child ChildPending ChildReady child-poll (Start 2u64))))",
            RUN,
        );
        let error = generate(&planning).err().unwrap();
        assert!(
            error.message.contains("projected addresses")
                || error.message.contains("borrow/address")
        );
        let planning = prepare(
            "
          (#let task Child (Start seed))
          (#return (#match task (#case (Start value)
            (#when (#bool.! (#u64.==
              (#await Child ChildPending ChildReady child-poll (Start 0u64)) 1u64)))
            (#await Child ChildPending ChildReady child-poll (Start value)))
            (#case (Resume value) value) (#case _ 0u64)))",
            RUN,
        );
        let error = generate(&planning).err().unwrap();
        assert!(error.message.contains("stationary storage aliases"));
    }

    #[test]
    fn constructors_run_on_execution_not_creation_or_pending_retry() {
        let main = "
          (#unsafe-fn make-child ((seed u64) (count (#ptr-mut u64))) Child
            (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
            (#return (Start seed)))
          (#fn main () u64
            (#let waker u64 0u64)
            (#let-mut count u64 0u64)
            (#let pointer (#ptr-mut u64) (#unsafe (#asm (#ptr-mut u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Frame (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Poll (#call poll (: task task : waker (#borrow waker))))
            (#let-else (Pending next) Poll first (#unreachable))
            (#assert (#u64.== count 1u64))
            (#return (#match (#call poll (: task next : waker (#borrow waker)))
              (#case (Ready value) (#block
                (#assert (#u64.== count 1u64)) value))
              (#case (Pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed u64) (count (#ptr-mut u64))) u64
          (#return (#u64.+.wrap seed (#await Child ChildPending ChildReady child-poll
            (#unsafe (#call make-child (: seed 2u64 : count count)))))))",
            main,
        );
        runtime_planned(planning, 42);
    }
}
