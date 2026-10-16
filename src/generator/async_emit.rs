//! Ordinary-code emission from the executable async graph.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! The dispatcher, rather than a collection of body-shape rewrites, defines
//! execution order. Dispatcher states track occupancy of untagged word regions;
//! reference-bearing cells retain their typed Empty/Full representation.
//! Source ownership, loans, pinning and initialization establish the safety
//! obligations of generated unsafe operations; pinning alone is insufficient.
//! Graph validation is not ownership permission. Ordinary emitted-code checking
//! remains mandatory, but cannot independently prove raw accesses sound.
#![allow(dead_code)] // Internal emission helpers also support structural tests.

use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{HashMap, HashSet};

use crate::generator::async_exec::{
    Action, AddressProjection, AddressRoot, Argument, BlockId, Compute, Edge, Graph, LoadKind,
    PlaceDescriptor, PlaceId, ReleaseKind, Terminator, ValueId,
};
use crate::generator::async_prepare::{Function, Planning};
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
    words: Option<WordRegion>,
    constant: Option<String>,
    field: String,
    name: String,
    empty: String,
    full: String,
    take: String,
    put: String,
    peek: String,
    clear: String,
    finish: String,
    lend: String,
    lend_argument: String,
    recover: String,
    recover_argument: String,
    ty: Type,
    storage: Type,
    raw: bool,
    anchor: Option<Vec<crate::typed_place::Place>>,
    dependencies: Vec<BindingId>,
    copy: bool,
    linear: bool,
    borrowed_slice_snapshot: bool,
}

#[derive(Clone)]
struct WordRegion {
    field: String,
    marker: String,
    owner: Type,
    capacity: usize,
    start: usize,
    length: usize,
}

// Planning interfaces name generated child frames before their executable
// layouts exist. A signature is not permission to guess their storage width.
fn deferred_word_layout(
    ty: &Type,
    declarations: &crate::typed_ir::Declarations,
) -> Result<bool, String> {
    let ty = crate::typed_ir::resolve_type(ty, &declarations.aliases)?;
    match &ty {
        Type::Named(name) => {
            if declarations.deferred_layouts.contains_key(name) {
                return Ok(true);
            }
            if let Some(fields) = declarations.structs.get(name) {
                for field in fields {
                    if deferred_word_layout(&field.ty, declarations)? {
                        return Ok(true);
                    }
                }
            }
            if let Some(variants) = declarations.enums.get(name) {
                for variant in variants {
                    for field in &variant.fields {
                        if deferred_word_layout(field, declarations)? {
                            return Ok(true);
                        }
                    }
                }
            }
            Ok(false)
        }
        Type::Array(_, 0) => Ok(false),
        Type::Array(element, _) => deferred_word_layout(element, declarations),
        Type::Tuple(fields) => {
            for field in fields {
                if deferred_word_layout(field, declarations)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        // References and pointers have fixed-width descriptors, irrespective
        // of the referent's eventual generated layout.
        _ => Ok(false),
    }
}

impl WordRegion {
    fn slice(&self, mutable: bool, anchor: &str, view: &str) -> String {
        self.slice_bounds(
            mutable,
            anchor,
            view,
            &format!("{}usize", self.start),
            &format!("{}usize", self.start + self.length),
        )
    }

    fn slice_bounds(
        &self,
        mutable: bool,
        anchor: &str,
        view: &str,
        start: &str,
        end: &str,
    ) -> String {
        let suffix = if mutable { "-mut" } else { "" };
        format!(
            "(#block
          (#let {anchor} (#pin-ref{suffix} (#array #u64 {}))
            (#pin-borrow{suffix} (#get task {})))
          (#let {view} (#ref{suffix} (#array #u64 {}))
            (#unsafe (#ptr-borrow{suffix} {anchor} (#ref-ptr {anchor}))))
          (#borrow-slice{suffix} (#deref {view})
            {start} {end}))",
            self.capacity, self.field, self.capacity
        )
    }
}

struct OwnedIndex {
    projection: usize,
    value: ValueId,
    bound: usize,
    slot: usize,
}

/// Assignments to real frame cells, recorded by the same helpers that emit
/// their writes. Reads and alias permissions remain separate obligations.
#[derive(Default)]
struct OccupancyTrace {
    writes: Vec<(usize, bool)>,
    edges: HashMap<usize, Vec<(usize, bool)>>,
}

struct AggregateField {
    path: Vec<crate::typed_ir::FieldId>,
    name: String,
    slot: usize,
}

struct AggregateShell {
    path: Vec<crate::typed_ir::FieldId>,
    name: String,
    slot: usize,
    alive: String,
}

struct Aggregate {
    shape: crate::generator::async_aggregate::Shape,
    fields: Vec<AggregateField>,
    shells: Vec<AggregateShell>,
}

impl Aggregate {
    fn cells(&self) -> impl Iterator<Item = usize> + '_ {
        self.fields
            .iter()
            .map(|field| field.slot)
            .chain(self.shells.iter().map(|shell| shell.slot))
    }

    fn shape(
        &self,
        path: &[crate::typed_ir::FieldId],
    ) -> Option<&crate::generator::async_aggregate::Shape> {
        let mut shape = &self.shape;
        for id in path {
            shape = shape
                .fields
                .iter()
                .find(|field| field.id == *id)?
                .nested
                .as_deref()?;
        }
        Some(shape)
    }
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
    pinned: bool,
    slots: Vec<Slot>,
    bindings: HashMap<BindingId, usize>,
    aggregates: HashMap<BindingId, Aggregate>,
    external_captures: HashMap<BindingId, usize>,
    values: HashMap<ValueId, usize>,
    scopes: HashMap<crate::typed_body::NodeId, usize>,
    reserved: RefCell<HashSet<String>>,
    next: Cell<usize>,
    types: &'a crate::linearcheck::LinearTypes,
    render: crate::generator::async_render::RenderContext<'a>,
    retirement: Option<crate::generator::async_retire::Plan>,
    physical_uses: crate::generator::async_retire::PhysicalUses<'a>,
    lending: Option<crate::generator::async_lend::Plan>,
    leases: crate::generator::async_lease::Plan,
    immediate: crate::generator::async_immediate::Plan,
    reference_cells: Option<crate::generator::async_cells::Plan>,
    cleanup_occupied_cache: OnceCell<HashSet<usize>>,
    projections: Vec<String>,
    cell_snapshots: HashMap<usize, (String, String)>,
    array_anchors: crate::generator::async_array_anchor::Recipes,
    slice_anchors: crate::generator::async_slice_anchor::Recipes,
    addresses: HashMap<PlaceId, usize>,
    owned_indices: HashMap<PlaceId, Vec<OwnedIndex>>,
    address_retirement: Option<crate::generator::async_addresses::Plan>,
    initialization: Option<crate::generator::async_initialization::Specialization>,
    current_state: usize,
    occupancy_trace: RefCell<Option<OccupancyTrace>>,
    physical_current: RefCell<Option<Vec<bool>>>,
    preview_aliases: crate::generator::async_preview_alias::Plan,
    active_preview_aliases: HashSet<BindingId>,
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
        let mut self_borrows = crate::generator::async_self_borrow::Plan::new(
            &function.graph,
            body,
            &planning.declarations.flows[&function.model.body_name],
            &planning.declarations,
            function.source.pinned_frame.is_some(),
        )
        .map_err(|error| Error {
            message: error.message,
            span: error.span.unwrap_or(function.source.function.span),
        })?;
        self_borrows.retain_async_captures(
            &function.graph,
            &planning.declarations,
            &planning.interfaces,
        );
        function
            .graph
            .validate()
            .and_then(|_| function.graph.validate_against(body))
            .map_err(|error| fail(function, error.message))?;
        if u32::try_from(function.graph.blocks.len()).is_err() {
            return Err(fail(
                function,
                "async graph exceeds the #u32 program-counter range",
            ));
        }
        let poll = planning.interfaces.functions.values().find(|interface|
            interface.provenance == crate::generator::async_interfaces::Provenance::AsyncPoll
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
        let types = planning.linear_types();
        let lending = crate::generator::async_lend::Plan::new(
            body,
            &planning.declarations.flows[&function.model.body_name],
            types,
        )
        .map_err(|error| fail(function, error.message))?;
        let leases = crate::generator::async_lease::Plan::new(
            &function.graph,
            lending.as_ref(),
            types,
            &planning.declarations.aliases,
        )
        .map_err(|error| fail(function, error.message))?;
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
            pinned: function.source.pinned_frame.is_some(),
            slots: Vec::new(),
            bindings: HashMap::new(),
            aggregates: HashMap::new(),
            external_captures: HashMap::new(),
            values: HashMap::new(),
            scopes: HashMap::new(),
            reserved: RefCell::new(reserved),
            next: Cell::new(0),
            initialization: None,
            occupancy_trace: RefCell::new(None),
            physical_current: RefCell::new(None),
            current_state: 0,
            preview_aliases: crate::generator::async_preview_alias::Plan::new(
                &function.graph,
                types,
                &planning.declarations,
            )
            .map_err(|message| fail(function, message))?,
            active_preview_aliases: HashSet::new(),
            types,
            render: crate::generator::async_render::RenderContext::new(
                body,
                &planning.declarations,
                &function.graph,
            )
            .map_err(|error| fail(function, error.message))?,
            retirement: None,
            physical_uses: crate::generator::async_retire::PhysicalUses::new(&function.graph),
            lending,
            leases,
            immediate: crate::generator::async_immediate::Plan::new(&function.graph)
                .map_err(|error| fail(function, error.message))?,
            reference_cells: None,
            cleanup_occupied_cache: OnceCell::new(),
            projections: Vec::new(),
            cell_snapshots: HashMap::new(),
            array_anchors: Default::default(),
            slice_anchors: Default::default(),
            addresses: HashMap::new(),
            owned_indices: HashMap::new(),
            address_retirement: None,
        };
        emitter.finish = emitter.fresh("frame-finish");
        let mut external_parameters = self_borrows
            .external_parameters
            .iter()
            .copied()
            .collect::<Vec<_>>();
        external_parameters.sort_by_key(|binding| binding.0);
        for binding in external_parameters {
            let slot = emitter.add_slot(
                format!("external.{}", binding.0),
                function.graph.bindings[binding.0].ty.clone(),
            );
            emitter.external_captures.insert(binding, slot);
        }
        // Each scope/declaration activates its own cell. The factory installs
        // only initial arguments; it must never execute source declarations.
        for (index, binding) in function.graph.bindings.iter().enumerate() {
            if binding.name == function.model.waker_binding
                || matches!(binding.ty, Type::Unit | Type::Never)
            {
                continue;
            }
            let slot = emitter.add_slot(format!("binding.{index}"), binding.ty.clone());
            emitter.slots[slot].dependencies = self_borrows
                .dependent_bindings
                .get(&BindingId(index))
                .cloned()
                .unwrap_or_default();
            if let Some(anchor) = self_borrows.bindings.get(&BindingId(index)) {
                emitter.plan_reference_storage(slot, anchor.clone())?;
            }
            emitter.bindings.insert(BindingId(index), slot);
        }
        for layout in crate::generator::async_aggregate::layouts(
            &function.graph,
            &planning.declarations,
            emitter.lending.as_ref(),
            types,
        )
        .map_err(|message| fail(function, message))?
        {
            let word_buffer = {
                let capacity = crate::codegen::storage_word_count(
                    &layout.shape.ty,
                    &planning.declarations.structs,
                    &planning.declarations.enums,
                )
                .map_err(|message| fail(function, message))?;
                Some(WordRegion {
                    field: emitter.fresh("aggregate-words"),
                    marker: emitter.fresh("aggregate-type"),
                    owner: layout.shape.ty.clone(),
                    capacity,
                    start: 0,
                    length: capacity,
                })
            };
            if let Some(region) = &word_buffer {
                emitter.slots[emitter.bindings[&layout.binding]].words = Some(region.clone());
            }
            let mut fields = Vec::new();
            let mut offset = 0;
            for field in layout.fields {
                let slot = emitter.add_slot(
                    format!(
                        "binding.{}.field.{}",
                        layout.binding.0,
                        field
                            .path
                            .iter()
                            .map(|id| id.index.to_string())
                            .collect::<Vec<_>>()
                            .join(".")
                    ),
                    field.ty,
                );
                if let Some(region) = &word_buffer {
                    let length = crate::codegen::storage_word_count(
                        &emitter.slots[slot].ty,
                        &planning.declarations.structs,
                        &planning.declarations.enums,
                    )
                    .map_err(|message| fail(function, message))?;
                    emitter.slots[slot].words = Some(WordRegion {
                        start: offset,
                        length,
                        ..region.clone()
                    });
                    offset += length;
                }
                if types.contains_reference(&emitter.slots[slot].ty) {
                    emitter.slots[slot].dependencies = emitter.slots
                        [emitter.bindings[&layout.binding]]
                        .dependencies
                        .clone();
                }
                fields.push(AggregateField {
                    path: field.path,
                    name: field.name,
                    slot,
                });
            }
            if word_buffer
                .as_ref()
                .is_some_and(|region| offset != region.capacity)
            {
                return Err(fail(
                    function,
                    "aggregate leaves disagree with their contiguous layout",
                ));
            }
            let shells = emitter.aggregate_shells(layout.binding, &layout.shape)?;
            if let Some(region) = &word_buffer {
                for shell in &shells {
                    emitter.slots[shell.slot].words = Some(WordRegion {
                        length: 0,
                        ..region.clone()
                    });
                    emitter.slots[shell.slot].constant = Some(format!("({})", shell.alive));
                }
            }
            emitter.aggregates.insert(
                layout.binding,
                Aggregate {
                    shape: layout.shape,
                    fields,
                    shells,
                },
            );
        }
        for (index, value) in function.graph.values.iter().enumerate() {
            if matches!(value.ty, Type::Unit | Type::Never)
                || emitter.leases.get(ValueId(index)).is_some()
                || emitter.leases.handle_leaf(ValueId(index)).is_some()
                || emitter.immediate.skips_storage(ValueId(index))
            {
                continue;
            }
            let slot = emitter.add_slot(format!("value.{index}"), value.ty.clone());
            emitter.slots[slot].borrowed_slice_snapshot = matches!(value.ty, Type::MutableSlice(_))
                && emitter.leases.snapshot(ValueId(index)).is_some();
            emitter.slots[slot].dependencies = self_borrows
                .dependent_values
                .get(&ValueId(index))
                .cloned()
                .unwrap_or_default();
            if let Some(anchor) = self_borrows.values.get(&ValueId(index)) {
                emitter.plan_reference_storage(slot, anchor.clone())?;
            }
            emitter.values.insert(ValueId(index), slot);
        }
        for located in function
            .graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
        {
            if let Action::Borrow {
                scope: Some(scope),
                place,
                mutable,
                pinned,
                ..
            } = located.action
            {
                if emitter.scopes.contains_key(&scope) {
                    continue;
                }
                let target = Box::new(function.graph.places[place.0].ty.clone());
                let ty = if pinned {
                    Type::PinnedReference { mutable, target }
                } else {
                    Type::Reference { mutable, target }
                };
                let slot = emitter.add_slot(format!("scope.{}", scope.0), ty);
                if !pinned && matches!(function.graph.places[place.0].root, AddressRoot::Local(_)) {
                    let anchor = crate::generator::async_self_borrow::direct_place(
                        &function.graph,
                        body,
                        place,
                    )
                    .map_err(|message| fail(function, message))?;
                    emitter.erase_reference(slot, vec![anchor])?;
                }
                emitter.scopes.insert(scope, slot);
            }
        }
        // Effectful checked selections and their descendants are actual
        // addresses. Only literal, provably in-bounds owned array paths can
        // be re-formed after moving a frame without replaying a selection.
        let mut selected = HashSet::new();
        for (index, descriptor) in function.graph.places.iter().enumerate() {
            if (!descriptor.checks().is_empty() && !emitter.static_owned_projection(descriptor))
                || descriptor
                    .parent
                    .is_some_and(|parent| selected.contains(&parent))
            {
                selected.insert(PlaceId(index));
            }
        }
        let mut mutable = HashSet::new();
        for block in &function.graph.blocks {
            for action in &block.actions {
                match action.action {
                    Action::Store { place, .. }
                    | Action::Borrow {
                        place,
                        mutable: true,
                        ..
                    } => {
                        mutable.insert(place);
                    }
                    _ => {}
                }
            }
        }
        for index in (0..function.graph.places.len()).rev() {
            if mutable.contains(&PlaceId(index)) {
                if let Some(parent) = function.graph.places[index].parent {
                    mutable.insert(parent);
                }
            }
        }
        for index in 0..function.graph.places.len() {
            let place = PlaceId(index);
            if !selected.contains(&place) {
                continue;
            }
            let descriptor = &function.graph.places[index];
            if let Some(indices) = emitter.owned_array_indices(descriptor) {
                let recipe = indices
                    .into_iter()
                    .map(|(projection, value, bound)| {
                        let slot =
                            emitter.add_slot(format!("index.{index}.{projection}"), Type::Usize);
                        OwnedIndex {
                            projection,
                            value,
                            bound,
                            slot,
                        }
                    })
                    .collect();
                emitter.owned_indices.insert(place, recipe);
                continue;
            }
            let selection_error = |message: &str| Error {
                message: message.into(),
                span: descriptor
                    .source
                    .and_then(|source| body.nodes[source.0].span)
                    .unwrap_or(function.source.function.span),
            };
            let pinned = match descriptor.root {
                AddressRoot::Local(_) if emitter.pinned => true,
                AddressRoot::Value(value) => match crate::typed_ir::resolve_type(
                    &function.graph.values[value.0].ty,
                    &planning.declarations.aliases,
                )
                .map_err(|message| fail(function, message))?
                {
                    Type::PinnedReference { .. } => true,
                    Type::Reference { .. } | Type::Slice(_) | Type::MutableSlice(_) => false,
                    _ => {
                        return Err(selection_error(
                            "selected addresses require safe checked references",
                        ))
                    }
                },
                _ => {
                    return Err(selection_error(
                        "selected owned addresses require a pinned frame",
                    ))
                }
            };
            let ty = if pinned {
                Type::PinnedReference {
                    mutable: mutable.contains(&place),
                    target: Box::new(descriptor.ty.clone()),
                }
            } else {
                Type::Reference {
                    mutable: mutable.contains(&place),
                    target: Box::new(descriptor.ty.clone()),
                }
            };
            let slot = emitter.add_slot(format!("address.{index}"), ty);
            emitter.addresses.insert(place, slot);
        }
        emitter.address_retirement = Some(crate::generator::async_addresses::Plan::new(
            &function.graph,
            &selected,
        ));
        let mut exclusive_handles = HashSet::new();
        for (value, slot) in &emitter.values {
            let ty = crate::typed_ir::resolve_type(
                &emitter.slots[*slot].ty,
                &planning.declarations.aliases,
            )
            .map_err(|message| fail(function, message))?;
            if matches!(
                ty,
                Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. }
            ) {
                exclusive_handles.insert(*value);
            }
        }
        emitter.retirement = crate::generator::async_retire::Plan::with_lending_snapshots(
            &function.graph,
            &emitter.types,
            &exclusive_handles,
            &planning.declarations.aliases,
            Some(&emitter.leases),
        );
        if let Some(plan) = &mut emitter.retirement {
            let mut anchors = HashSet::new();
            for slot in &emitter.slots {
                anchors.extend(slot.dependencies.iter().copied());
                for place in slot.anchor.iter().flatten() {
                    if let crate::typed_body::PlaceRoot::Local(binding) = place.root {
                        anchors.insert(binding);
                    }
                }
            }
            plan.protect_binding_anchors(&function.graph, &anchors);
        }
        if let Some(plan) = &emitter.retirement {
            plan.validate(&function.graph)
                .map_err(|error| fail(function, error.message))?;
        }
        emitter.reference_cells = crate::generator::async_cells::Plan::new(
            &function.graph,
            &emitter.types,
            emitter.retirement.as_ref(),
            emitter.lending.as_ref(),
        );
        emitter.validate_movable_reference_boundaries()?;
        let places = emitter
            .slots
            .iter()
            .filter_map(|slot| slot.anchor.as_ref())
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let mut recipes = crate::generator::async_array_anchor::Recipes::new(
            places
                .iter()
                .filter(|place| {
                    crate::generator::async_slice_anchor::parameter(
                        place,
                        &function.graph,
                        &planning.declarations,
                    )
                    .is_none()
                })
                .cloned(),
            &function.graph,
            &planning.declarations,
            |role| emitter.fresh(role),
        );
        emitter.projections.append(&mut recipes.declarations);
        emitter.array_anchors = recipes;
        let mut recipes = crate::generator::async_slice_anchor::Recipes::new(
            places,
            &function.graph,
            &planning.declarations,
            |role| emitter.fresh(role),
        )
        .map_err(|message| fail(function, message))?;
        emitter.projections.append(&mut recipes.declarations);
        emitter.slice_anchors = recipes;
        // Reference-free bindings and temporaries need only their payload
        // words. The specialized dispatcher carries ownership and initialization
        // facts, including for whole aggregate values. Actual reference
        // holders and deferred generated layouts retain their typed path.
        // Erased thin handles store physical pointer words, but reads still
        // reconstruct references from their checked source anchors.
        let value_slots = emitter.values.values().copied().collect::<HashSet<_>>();
        let binding_slots = emitter.bindings.values().copied().collect::<HashSet<_>>();
        for index in 0..emitter.slots.len() {
            let slot = &emitter.slots[index];
            // Nested reference provenance still uses the typed recovery helper.
            // Pointer bits alone must not replace that lifetime-bearing path.
            if slot.raw
                && matches!(
                    crate::typed_ir::resolve_type(&slot.ty, &planning.declarations.aliases),
                    Ok(Type::Reference { target, .. } | Type::PinnedReference { target, .. })
                        if types.contains_reference(&target)
                )
            {
                continue;
            }
            let ty = crate::typed_ir::resolve_type(&slot.storage, &planning.declarations.aliases)
                .map_err(|message| fail(function, message))?;
            let word_backed_value = (value_slots.contains(&index)
                || binding_slots.contains(&index))
                && !matches!(ty, Type::Unit | Type::Never)
                && (!types.contains_reference(&ty)
                    || matches!(&ty, Type::Tuple(_))
                    || matches!(&ty, Type::Named(name) if planning.declarations.structs.contains_key(name)));
            if slot.words.is_some()
                || (!slot.raw
                    && !word_backed_value
                    && !matches!(
                        ty,
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
                    ))
            {
                continue;
            }
            if deferred_word_layout(&ty, &planning.declarations)
                .map_err(|message| fail(function, message))?
            {
                continue;
            }
            let capacity = crate::codegen::storage_word_count(
                &ty,
                &planning.declarations.structs,
                &planning.declarations.enums,
            )
            .map_err(|message| fail(function, message))?;
            let storage_field = emitter.slots[index].field.clone();
            emitter.slots[index].words = Some(WordRegion {
                field: emitter.fresh(&format!("{storage_field}-words")),
                marker: emitter.fresh(&format!("{storage_field}-type")),
                owner: ty,
                capacity,
                start: 0,
                length: capacity,
            });
        }
        let mut aliases = emitter
            .preview_aliases
            .patterns
            .keys()
            .copied()
            .collect::<Vec<_>>();
        aliases.sort_by_key(|binding| binding.0);
        for binding in aliases {
            emitter.try_preview_alias_reference(binding, false)?;
            emitter.try_preview_alias_reference(binding, true)?;
        }
        Ok(emitter)
    }

    fn validate_movable_reference_boundaries(&self) -> Result<(), Error> {
        use crate::generator::async_cells::Cell;
        use crate::typed_body::PlaceRoot;
        if self.pinned {
            return Ok(());
        }
        let internal = |slot: &Slot| {
            !slot.dependencies.is_empty()
                || slot.anchor.as_ref().is_some_and(|anchors| {
                    anchors
                        .iter()
                        .any(|anchor| matches!(anchor.root, PlaceRoot::Local(_)))
                })
        };
        let mut cells = self
            .bindings
            .iter()
            .map(|(binding, index)| (Cell::Binding(*binding), *index))
            .chain(
                self.values
                    .iter()
                    .map(|(value, index)| (Cell::Value(*value), *index)),
            )
            .chain(
                self.scopes
                    .iter()
                    .map(|(scope, index)| (Cell::Scope(*scope), *index)),
            )
            .filter(|(_, index)| internal(&self.slots[*index]))
            .collect::<Vec<_>>();
        cells.sort_by_key(|(_, index)| *index);
        if cells.is_empty() {
            return Ok(());
        }
        let reachable = self.function.graph.reachable();
        for (block, descriptor) in self.function.graph.blocks.iter().enumerate() {
            if !reachable.contains(&BlockId(block))
                || !matches!(descriptor.terminator, Terminator::Await { .. })
            {
                continue;
            }
            let plan = self.reference_cells.as_ref().ok_or_else(|| {
                fail(
                    self.function,
                    "movable internal references require physical suspension-cell facts",
                )
            })?;
            let Some(empty) = plan.pending_empty.get(&BlockId(block)) else {
                return Err(fail(self.function,
                    "movable internal references require facts for every reachable Pending boundary"));
            };
            if let Some((cell, index)) = cells.iter().find(|(cell, _)| !empty.contains(cell)) {
                let span = match cell {
                    Cell::Binding(binding) => self.function.graph.bindings[binding.0].span,
                    Cell::Value(value) => self.function.graph.values[value.0].span,
                    Cell::Scope(scope) => self.body.nodes[scope.0].span,
                };
                // Prefer the actual formation of an internal address to the
                // enclosing declaration when source origins identify it.
                let formation = self.slots[*index].anchor.as_ref().and_then(|anchors| {
                    self.function
                        .graph
                        .blocks
                        .iter()
                        .flat_map(|block| &block.actions)
                        .find_map(|action| match action.action {
                            Action::Borrow { place, .. } => {
                                crate::generator::async_self_borrow::direct_place(
                                    &self.function.graph,
                                    self.body,
                                    place,
                                )
                                .ok()
                                .filter(|place| anchors.contains(place))
                                .and(action.span)
                            }
                            _ => None,
                        })
                });
                return Err(Error {
                    message: "local references surviving suspension require a pinned async frame"
                        .into(),
                    span: formation
                        .or(span)
                        .unwrap_or(self.function.source.function.span),
                });
            }
        }
        Ok(())
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
        self.cleanup_occupied_cache.take();
        let slot = Slot {
            words: None,
            constant: None,
            field,
            name: self.fresh("Slot"),
            empty: self.fresh("Empty"),
            full: self.fresh("Full"),
            take: self.fresh("take"),
            put: self.fresh("put"),
            peek: self.fresh("peek"),
            clear: self.fresh("clear"),
            finish: self.fresh("finish"),
            lend: self.fresh("lend"),
            lend_argument: self.fresh("lend-input"),
            recover: self.fresh("recover-reference"),
            recover_argument: self.fresh("recover-anchor"),
            copy: self.types.can_repeat(&ty),
            linear: self.types.is_linear(&ty),
            borrowed_slice_snapshot: false,
            storage: ty.clone(),
            raw: false,
            anchor: None,
            dependencies: Vec::new(),
            ty,
        };
        let index = self.slots.len();
        self.slots.push(slot);
        index
    }

    fn plan_reference_storage(
        &mut self,
        index: usize,
        anchor: Vec<crate::typed_place::Place>,
    ) -> Result<(), Error> {
        if matches!(self.slots[index].ty, Type::PinnedReference { .. })
            && anchor.iter().any(|place| {
                matches!(place.root, crate::typed_body::PlaceRoot::Local(binding)
                    if self.types.contains_reference(&self.function.graph.bindings[binding.0].ty)
                        || deferred_word_layout(&self.function.graph.bindings[binding.0].ty,
                            &self.planning.declarations).unwrap_or(true))
            })
        {
            // Reference-bearing owners still use their native provenance path.
            for place in &anchor {
                if let crate::typed_body::PlaceRoot::Local(binding) = place.root {
                    if !self.slots[index].dependencies.contains(&binding) {
                        self.slots[index].dependencies.push(binding);
                    }
                }
            }
            return Ok(());
        }
        // Aggregate word owners are initialized in an earlier dispatcher arm.
        // Keep their checked address rather than retaining a typed ownership
        // loan into opaque words across arms. This includes whole aggregates,
        // not only selected array elements. Restrict this to direct owned
        // paths and retain the mandatory Empty boundary proof for movable polls.
        let owned_aggregate = matches!(
            crate::typed_ir::resolve_type(&self.slots[index].ty, &self.planning.declarations.aliases),
            Ok(Type::Reference { target, .. })
                if (!self.types.can_repeat(&target)
                    || matches!(target.as_ref(), Type::Named(_) | Type::Array(_, _) | Type::Tuple(_)))
                    && !self.types.contains_reference(&target)
        ) && anchor.iter().all(|place| {
            matches!(place.root, crate::typed_body::PlaceRoot::Local(_))
                && place.segments.iter().all(|segment| {
                    matches!(
                        segment,
                        crate::typed_place::Segment::Field(_)
                            | crate::typed_place::Segment::Tuple(_)
                            | crate::typed_place::Segment::Index(_)
                            | crate::typed_place::Segment::DynamicIndex
                    )
                })
        });
        // Single-target poll-local references can keep their actual lending capability.
        // Reconstructing a pointer from the backing array would bypass a live
        // slice's exclusive borrow. Retain anchors for the physical Empty
        // boundary proof even when no pointer erasure is necessary. Multi-target
        // handles use the selected-address representation: retaining a real
        // reference across dispatcher arms otherwise joins its loan into the
        // initialization arm of every possible referent. Movable frames still
        // require all such handles Empty before returning Pending.
        if !self.pinned
            && !owned_aggregate
            && anchor.len() == 1
            && anchor
                .iter()
                .all(|place| matches!(place.root, crate::typed_body::PlaceRoot::Local(_)))
        {
            self.slots[index].anchor = Some(anchor);
            Ok(())
        } else {
            self.erase_reference(index, anchor)
        }
    }

    fn erase_reference(
        &mut self,
        index: usize,
        anchor: Vec<crate::typed_place::Place>,
    ) -> Result<(), Error> {
        let slot = &mut self.slots[index];
        let (mutable, target) =
            match crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?
            {
                Type::Reference { mutable, target } | Type::PinnedReference { mutable, target } => {
                    (mutable, target)
                }
                _ => {
                    return Err(fail(
                        self.function,
                        "internal pointer storage requires a thin reference",
                    ))
                }
            };
        slot.storage = Type::RawPointer { mutable, target };
        slot.raw = true;
        slot.anchor = Some(anchor);
        Ok(())
    }

    fn internal_anchor(
        &self,
        place: &crate::typed_place::Place,
        mutable: bool,
        pointer: &str,
    ) -> String {
        if let Some(binding) = crate::generator::async_slice_anchor::parameter(
            place,
            &self.function.graph,
            &self.planning.declarations,
        ) {
            return self.slice_anchors.materialize(
                place,
                &self.slice_holder(binding),
                pointer,
                mutable,
            );
        }
        let mut indices = HashMap::new();
        let mut statements = Vec::new();
        for (position, segment) in place.segments.iter().enumerate() {
            if *segment != crate::typed_place::Segment::DynamicIndex {
                continue;
            }
            let array = self.anchor_project(place, position, false, &indices);
            let index = self.fresh("anchor-index");
            statements.push(format!(
                "(#let {index} #usize {})",
                self.array_anchors
                    .get(place, position)
                    .index(&array, pointer)
            ));
            indices.insert(position, index);
        }
        let anchor = self.anchor_project(place, place.segments.len(), mutable, &indices);
        if statements.is_empty() {
            anchor
        } else {
            format!("(#block {} {anchor})", statements.join("\n"))
        }
    }

    fn anchor_project(
        &self,
        place: &crate::typed_place::Place,
        prefix: usize,
        mutable: bool,
        indices: &HashMap<usize, String>,
    ) -> String {
        use crate::typed_place::Segment;
        let (binding, external) = match place.root {
            crate::typed_body::PlaceRoot::Local(binding) => (binding, false),
            crate::typed_body::PlaceRoot::Parameter(binding) => (binding, true),
            _ => unreachable!(),
        };
        let preview = !external && self.active_preview_aliases.contains(&binding);
        if !external && !preview {
            let root = &self.slots[self.bindings[&binding]];
            if let Some(region) = &root.words {
                // Form only the initialized selected referent, never a typed
                // reference to an ancestor with a moved-out sibling.
                let resolve = |ty: &Type| {
                    crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases)
                        .expect("checked anchor type")
                };
                let count = |ty: &Type| {
                    crate::codegen::storage_word_count(
                        ty,
                        &self.planning.declarations.structs,
                        &self.planning.declarations.enums,
                    )
                    .expect("checked anchor layout")
                };
                let mut ty = resolve(&root.ty);
                let mut offset = region.start;
                let mut terms = Vec::new();
                for (position, segment) in place.segments[..prefix].iter().enumerate() {
                    ty = match segment {
                        Segment::Field(field) => {
                            let Type::Named(name) = &ty else {
                                unreachable!()
                            };
                            for sibling in self.planning.declarations.structs[name]
                                .iter()
                                .take(field.index)
                            {
                                offset += count(&resolve(&sibling.ty));
                            }
                            resolve(&self.planning.declarations.field(*field).ty)
                        }
                        Segment::Tuple(index) => {
                            let Type::Tuple(fields) = &ty else {
                                unreachable!()
                            };
                            for sibling in fields.iter().take(*index) {
                                offset += count(&resolve(sibling));
                            }
                            resolve(&fields[*index])
                        }
                        Segment::Payload(variant, index) => {
                            let declaration = self.planning.declarations.variant(*variant);
                            assert_eq!(
                                self.planning
                                    .declarations
                                    .variant_id(&ty, &declaration.name),
                                Some(*variant)
                            );
                            offset += 1;
                            for sibling in declaration.fields.iter().take(*index) {
                                offset += count(&resolve(sibling));
                            }
                            resolve(&declaration.fields[*index])
                        }
                        Segment::Index(_) | Segment::DynamicIndex => {
                            let Type::Array(element, _) = &ty else {
                                unreachable!()
                            };
                            let element = resolve(element);
                            let stride = count(&element);
                            if let Segment::Index(index) = segment {
                                offset += usize::try_from(*index)
                                    .expect("checked array index fits usize")
                                    * stride;
                            } else {
                                terms.push(format!(
                                    "(#usize.*.wrap {} {stride}usize)",
                                    indices[&position]
                                ));
                            }
                            element
                        }
                        _ => unreachable!("checked word anchor projection"),
                    };
                }
                let length = count(&ty);
                // A #u64 word is already the declared numeric backing type.
                // Borrow its actual slot instead of manufacturing an opaque
                // typed view, which would retain only a lifetime anchor.
                if ty == Type::U64 && terms.is_empty() {
                    return format!(
                        "(#pin-borrow{} (#index (#get task {}) {offset}usize))",
                        if mutable { "-mut" } else { "" },
                        region.field
                    );
                }
                let slice = if terms.is_empty() {
                    self.word_slice(
                        &WordRegion {
                            start: offset,
                            length,
                            ..region.clone()
                        },
                        mutable,
                    )
                } else {
                    let mut expression = format!("{offset}usize");
                    for term in terms {
                        expression = format!("(#usize.+.wrap {expression} {term})");
                    }
                    let start = self.fresh("anchor-offset");
                    let slice = region.slice_bounds(
                        mutable,
                        &self.fresh("word-anchor"),
                        &self.fresh("word-view"),
                        &start,
                        &format!("(#usize.+.wrap {start} {length}usize)"),
                    );
                    format!("(#block (#let {start} #usize {expression}) {slice})")
                };
                return format!(
                    "(#unsafe (#word-view (#pin-ref{} {}) {slice}))",
                    if mutable { "-mut" } else { "" },
                    crate::type_source(&ty)
                );
            }
        }
        let part = if !external && !preview && prefix > 0 {
            self.anchor_field(binding, &place.segments[..prefix])
        } else {
            None
        };
        let skip = part.map_or(0, |part| part.path.len());
        let owner = &self.slots[if let Some(part) = part {
            part.slot
        } else if external {
            self.external_captures[&binding]
        } else {
            self.bindings[&binding]
        }];
        let suffix = if mutable { "-mut" } else { "" };
        let mut anchor = self.payload_ref(owner, mutable);
        if external {
            anchor = format!("(#deref {anchor})");
            if !mutable {
                // Geometry probes borrow the target immutably; reading an
                // exclusive handle out of a shared holder cannot transfer its
                // exclusive permission to a helper.
                let shared = self.fresh("external-shared-anchor");
                let target = crate::generator::async_array_anchor::target_type(
                    place,
                    0,
                    &self.function.graph,
                    &self.planning.declarations,
                );
                anchor = if matches!(
                    self.function.graph.bindings[binding.0].ty,
                    Type::PinnedReference { .. }
                ) {
                    format!("(#borrow (#deref {anchor}))")
                } else {
                    format!(
                        "(#block (#let {shared} (#pin-ref {}) (#borrow (#deref {anchor})))
                     (#unsafe (#ptr-borrow {shared} (#ref-ptr {shared}))))",
                        crate::type_source(&target)
                    )
                };
            }
        }
        if let Some(projected) = (skip == 0)
            .then(|| {
                self.array_anchors
                    .project(place, prefix, mutable, &anchor, indices)
            })
            .flatten()
        {
            return projected;
        }
        if external {
            if prefix != 0 {
                let base = self.fresh("external-anchor");
                let mut projected = base.clone();
                for (position, segment) in place.segments[..prefix].iter().enumerate() {
                    projected = match segment {
                        Segment::Field(id) => format!(
                            "(#get {projected} {})",
                            self.planning.declarations.field(*id).name
                        ),
                        Segment::Tuple(index) => format!("(#get {projected} {index})"),
                        Segment::Index(index) => format!("(#index {projected} {index}usize)"),
                        Segment::DynamicIndex => {
                            format!("(#index {projected} {})", indices[&position])
                        }
                        _ => unreachable!("external anchors have checked static projections"),
                    };
                }
                return format!(
                    "(#block (#let {base} {} {anchor}) (#borrow{suffix} {projected}))",
                    crate::type_source(&if matches!(
                        self.function.graph.bindings[binding.0].ty,
                        Type::PinnedReference { .. }
                    ) {
                        Type::PinnedReference {
                            mutable,
                            target: Box::new(crate::generator::async_array_anchor::target_type(
                                place,
                                0,
                                &self.function.graph,
                                &self.planning.declarations,
                            )),
                        }
                    } else {
                        Type::Reference {
                            mutable,
                            target: Box::new(crate::generator::async_array_anchor::target_type(
                                place,
                                0,
                                &self.function.graph,
                                &self.planning.declarations,
                            )),
                        }
                    })
                );
            }
        }
        let mut steps = Vec::new();
        for (position, segment) in place.segments[..prefix].iter().enumerate().skip(skip) {
            // A decomposed leaf already supplies the stable parent capability.
            // Keep its suffix as one reborrow expression: a temporary named
            // parent would end before the returned raw-pointer reborrow is read.
            // Non-decomposed anchor recipes still stage their parent handles.
            if position != 0 && part.is_none() {
                let parent = self.fresh("anchor-parent");
                let target = crate::generator::async_array_anchor::target_type(
                    place,
                    position,
                    &self.function.graph,
                    &self.planning.declarations,
                );
                let ty = Type::PinnedReference {
                    mutable,
                    target: Box::new(target),
                };
                steps.push(format!(
                    "(#let {parent} {} {anchor})",
                    crate::type_source(&ty)
                ));
                anchor = parent;
            }
            let projected = match segment {
                Segment::Field(id) => format!(
                    "(#get {anchor} {})",
                    self.planning.declarations.field(*id).name
                ),
                Segment::Tuple(index) => format!("(#get {anchor} {index})"),
                Segment::Payload(variant, index) => format!(
                    "(#deref (#pin-get-payload{suffix} {anchor} {} {index}))",
                    self.planning.declarations.variant(*variant).name
                ),
                Segment::Index(index) => format!("(#index {anchor} {index}usize)"),
                Segment::DynamicIndex => format!("(#index {anchor} {})", indices[&position]),
                _ => unreachable!("internal anchors were checked before emission"),
            };
            anchor = if part.is_some() && position + 1 != prefix {
                projected
            } else {
                format!("(#pin-borrow{suffix} {projected})")
            };
        }
        if steps.is_empty() {
            anchor
        } else {
            format!("(#block {} {anchor})", steps.join("\n"))
        }
    }

    /// A dormant source branch may have a constant out-of-bounds access.
    /// It cannot supply a selected address, so never probe that payload when
    /// materializing a reference formed by another branch.
    fn anchor_in_bounds(&self, place: &crate::typed_place::Place) -> bool {
        use crate::typed_place::Segment;
        let (binding, external) = match place.root {
            crate::typed_body::PlaceRoot::Local(binding) => (binding, false),
            crate::typed_body::PlaceRoot::Parameter(binding) => (binding, true),
            _ => unreachable!(),
        };
        let resolve = |ty: &Type| {
            crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases)
                .expect("anchor types were resolved before emission")
        };
        let mut ty = resolve(&self.function.graph.bindings[binding.0].ty);
        let mut skip = 0;
        if external {
            ty = match ty {
                Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                    resolve(&target)
                }
                Type::Slice(target) | Type::MutableSlice(target) => {
                    // Runtime slice bounds are checked by the slice recipe.
                    // Its static suffix still has ordinary aggregate bounds;
                    // never sample an impossible dormant array projection.
                    skip = 1;
                    resolve(&target)
                }
                _ => unreachable!("external captures have checked reference types"),
            };
        }
        for segment in place.segments.iter().skip(skip) {
            ty = match (segment, ty) {
                (Segment::Field(id), _) => resolve(&self.planning.declarations.field(*id).ty),
                (Segment::Payload(variant, index), _) => {
                    resolve(&self.planning.declarations.variant(*variant).fields[*index])
                }
                (Segment::Tuple(index), Type::Tuple(fields)) => resolve(&fields[*index]),
                (
                    segment @ (Segment::Index(_) | Segment::DynamicIndex),
                    Type::Array(element, length),
                ) => {
                    if length == 0
                        || matches!(segment, Segment::Index(index) if *index >= length as u128)
                    {
                        return false;
                    }
                    resolve(&element)
                }
                _ => unreachable!("anchor projections were checked before emission"),
            };
        }
        true
    }

    fn anchor_probe(&self, place: &crate::typed_place::Place, pointer: &str) -> String {
        if let Some(binding) = crate::generator::async_slice_anchor::parameter(
            place,
            &self.function.graph,
            &self.planning.declarations,
        ) {
            return self
                .slice_anchors
                .probe(place, &self.slice_holder(binding), pointer);
        }
        fn probe(
            emitter: &Emitter<'_>,
            place: &crate::typed_place::Place,
            pointer: &str,
            start: usize,
            indices: &mut HashMap<usize, String>,
        ) -> String {
            if let Some(position) = (start..place.segments.len()).find(|position| {
                matches!(
                    place.segments[*position],
                    crate::typed_place::Segment::DynamicIndex
                        | crate::typed_place::Segment::Payload(_, _)
                )
            }) {
                if let crate::typed_place::Segment::Payload(variant, _) = place.segments[position] {
                    let owner = emitter.anchor_project(place, position, false, indices);
                    return format!(
                        "(#bool.&& (#variant-is {owner} {}) {})",
                        emitter.planning.declarations.variant(variant).name,
                        probe(emitter, place, pointer, position + 1, indices)
                    );
                }
                let array = emitter.anchor_project(place, position, false, indices);
                let recipe = emitter.array_anchors.get(place, position);
                let index = emitter.fresh("probe-index");
                indices.insert(position, index.clone());
                let rest = probe(emitter, place, pointer, position + 1, indices);
                format!(
                    "(#bool.&& {} (#block (#let {index} #usize {}) {rest}))",
                    recipe.probe(&array, pointer),
                    recipe.index(&array, pointer)
                )
            } else {
                format!(
                    "(#usize.== (#ptr-address {pointer}) (#ptr-address (#ref-ptr {})))",
                    emitter.anchor_project(place, place.segments.len(), false, indices)
                )
            }
        }
        probe(self, place, pointer, 0, &mut HashMap::new())
    }

    fn materialize_internal_reference(
        &self,
        slot: &Slot,
        pointer: &str,
        mutable: bool,
        pinned: bool,
    ) -> String {
        let places = slot
            .anchor
            .as_ref()
            .expect("raw internal slot has checked anchors");
        let materialize = |place| {
            if self.recover_nested_reference(slot) {
                return format!(
                    "(#call {} (: {} {}))",
                    slot.recover,
                    slot.recover_argument,
                    self.internal_anchor(place, mutable, pointer)
                );
            }
            format!(
                "(#unsafe (#{}ptr-borrow{} {} {pointer}))",
                if pinned { "pin-" } else { "" },
                if mutable { "-mut" } else { "" },
                self.internal_anchor(place, mutable, pointer)
            )
        };
        if let [place] = places.as_slice() {
            if !self.anchor_in_bounds(place) {
                return "(#unreachable)".into();
            }
            // One statically selected local word names its referent exactly.
            // Recover it from an exact address round trip, not by trusting a
            // saved raw address. Dynamic, external and tagged selections keep the
            // existing pointer/selection protocol.
            let static_word = !pinned
                && matches!(place.root,
                crate::typed_body::PlaceRoot::Local(binding)
                    if self.slots[self.bindings[&binding]].words.is_some())
                && place.segments.iter().all(|segment| {
                    matches!(
                        segment,
                        crate::typed_place::Segment::Field(_)
                            | crate::typed_place::Segment::Tuple(_)
                            | crate::typed_place::Segment::Index(_)
                    )
                })
                && matches!(&slot.storage,
                    Type::RawPointer { target, .. } if **target == Type::U64);
            if static_word {
                let anchor = self.internal_anchor(place, mutable, pointer);
                let name = self.fresh("exact-word-anchor");
                return format!(
                        "(#block (#let {name} (#pin-ref{} #u64) {anchor}) (#unsafe (#ptr-borrow{} {name} (#ref-ptr {name}))))",
                        if mutable { "-mut" } else { "" },
                        if mutable { "-mut" } else { "" }
                    );
            }
            return materialize(place);
        }
        // The raw address retains the choice made by the source expression.
        // Probe only occupied owners, then reconstruct from that owner's
        // checked projection. Short-circuiting must precede payload access:
        // an unselected branch may never have initialized its owner cell.
        let mut selected = "(#unreachable)".to_owned();
        for place in places.iter().rev() {
            if !self.anchor_in_bounds(place) {
                continue;
            }
            let index = match place.root {
                crate::typed_body::PlaceRoot::Local(binding) => self
                    .anchor_field(binding, &place.segments)
                    .map(|field| field.slot)
                    .unwrap_or(self.bindings[&binding]),
                crate::typed_body::PlaceRoot::Parameter(binding) => self
                    .external_captures
                    .get(&binding)
                    .copied()
                    .unwrap_or(self.bindings[&binding]),
                _ => unreachable!(),
            };
            let owner = &self.slots[index];
            if owner.words.is_some() {
                let selected_cells =
                    if let crate::typed_body::PlaceRoot::Local(binding) = place.root {
                        if self.aggregates.contains_key(&binding)
                            && self.anchor_field(binding, &place.segments).is_none()
                        {
                            let path = place
                                .segments
                                .iter()
                                .map(|segment| match segment {
                                    crate::typed_place::Segment::Field(field) => *field,
                                    _ => unreachable!(
                                        "whole word anchor has checked struct projections"
                                    ),
                                })
                                .collect::<Vec<_>>();
                            let aggregate = &self.aggregates[&binding];
                            aggregate
                                .fields
                                .iter()
                                .filter(|field| field.path.starts_with(&path))
                                .map(|field| field.slot)
                                .chain(
                                    aggregate
                                        .shells
                                        .iter()
                                        .filter(|shell| shell.path.starts_with(&path))
                                        .map(|shell| shell.slot),
                                )
                                .collect::<Vec<_>>()
                        } else {
                            vec![index]
                        }
                    } else {
                        vec![index]
                    };
                let current = self.physical_current.borrow();
                if current
                    .as_ref()
                    .is_some_and(|cells| selected_cells.iter().any(|index| !cells[*index]))
                {
                    continue;
                }
                let guard = if current.is_some() || self.occupancy_trace.borrow().is_some() {
                    "true".into()
                } else {
                    let states = &self
                        .initialization
                        .as_ref()
                        .expect("production word view requires state facts")
                        .states;
                    let cases = states
                        .iter()
                        .enumerate()
                        .map(|(pc, state)| {
                            let start = state.before.len() - self.slots.len();
                            format!(
                                "(#case {pc}u32 {})",
                                selected_cells
                                    .iter()
                                    .all(|index| state.before[start + index])
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("(#match (#get task pc) {cases} (#case _ false))")
                };
                selected = format!(
                    "(#if (#bool.&& {guard} {}) {} {selected})",
                    self.anchor_probe(place, pointer),
                    materialize(place)
                );
                continue;
            }
            selected = format!(
                "(#if (#bool.&& (#variant-is {} {})
                {})
                {} {selected})",
                Self::slot_ref(owner, false),
                owner.full,
                self.anchor_probe(place, pointer),
                materialize(place)
            );
        }
        selected
    }

    fn recover_nested_reference(&self, slot: &Slot) -> bool {
        slot.raw
            && matches!(crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases),
                Ok(Type::Reference { mutable: false, target }) if self.types.contains_reference(&target))
            && slot.anchor.as_ref().is_some_and(|places| {
                places.iter().all(|place| {
                    matches!(place.root, crate::typed_body::PlaceRoot::Local(_))
                        && place.segments.is_empty()
                })
            })
    }

    fn slot_ref(slot: &Slot, mutable: bool) -> String {
        format!(
            "(#pin-borrow{} (#get task {}))",
            if mutable { "-mut" } else { "" },
            slot.field
        )
    }

    fn word_slice(&self, region: &WordRegion, mutable: bool) -> String {
        region.slice(
            mutable,
            &self.fresh("word-anchor"),
            &self.fresh("word-view"),
        )
    }

    fn forget_word_region(&self, region: &WordRegion) -> String {
        format!(
            "(#unsafe (#word-forget (#array #u64 {}) {}))",
            region.length,
            self.word_slice(region, true)
        )
    }

    fn payload_ref(&self, slot: &Slot, mutable: bool) -> String {
        if let Some(binding) = self.active_preview_aliases.iter().find(|binding| {
            self.bindings
                .get(binding)
                .is_some_and(|index| std::ptr::eq(&self.slots[*index], slot))
        }) {
            return self.preview_alias_reference(*binding, mutable);
        }
        if let Some(region) = &slot.words {
            let ty = crate::type_source(&slot.ty);
            return format!(
                "(#unsafe (#word-view (#pin-ref{} {ty}) {}))",
                if mutable { "-mut" } else { "" },
                self.word_slice(region, mutable)
            );
        }
        format!(
            "(#pin-get-payload{} {} {} 0)",
            if mutable { "-mut" } else { "" },
            Self::slot_ref(slot, mutable),
            slot.full
        )
    }

    fn preview_alias_reference(&self, binding: BindingId, mutable: bool) -> String {
        self.try_preview_alias_reference(binding, mutable)
            .expect("stationary alias projection validated before emission")
    }

    fn try_preview_alias_reference(
        &self,
        binding: BindingId,
        mutable: bool,
    ) -> Result<String, Error> {
        let error = |message| Error {
            message,
            span: self.function.graph.bindings[binding.0]
                .span
                .unwrap_or(self.function.source.function.span),
        };
        let pattern = &self.preview_aliases.patterns[&binding];
        let names = pattern
            .bindings
            .iter()
            .map(|binding| (*binding, self.fresh("preview-alias")))
            .collect::<HashMap<_, _>>();
        let bindings = names
            .iter()
            .map(|(binding, name)| {
                (
                    name.clone(),
                    self.function.graph.bindings[binding.0].ty.clone(),
                )
            })
            .collect::<HashMap<_, _>>();
        let aliases = names.values().cloned().collect::<HashSet<_>>();
        // For alias leaves this map only marks the exclusive projection path;
        // preview_with_aliases returns the reference before consulting helpers.
        // No identity call (and no owned aggregate read) is emitted here.
        let lenders = if mutable {
            HashMap::from([(names[&binding].clone(), (String::new(), String::new()))])
        } else {
            HashMap::new()
        };
        let source = crate::parse(&self.pattern_source(pattern, &names)?)
            .map_err(|failure| error(failure.to_string()))?
            .remove(0)
            .expr;
        let owner = &self.slots[*self
            .values
            .get(&pattern.scrutinee)
            .ok_or_else(|| error("stationary alias scrutinee has no owning cell".into()))?];
        let reference = crate::parse(&self.payload_ref(owner, mutable))
            .map_err(|failure| error(failure.to_string()))?
            .remove(0)
            .expr;
        let projected = crate::generator::async_pattern::preview_with_aliases(
            &self.planning.declarations,
            &source,
            &self.function.graph.values[pattern.scrutinee.0].ty,
            reference,
            &bindings,
            &lenders,
            &aliases,
        )
        .map_err(error)?;
        let (_, reference) = projected
            .into_iter()
            .find(|(name, _)| name == &names[&binding])
            .ok_or_else(|| error("stationary alias binding has no projection".into()))?;
        crate::expression_source(&reference).map_err(error)
    }

    fn word_buffers(&self) -> Vec<&WordRegion> {
        let mut seen = HashSet::new();
        self.slots
            .iter()
            .filter_map(|slot| slot.words.as_ref())
            .filter(|region| seen.insert(region.field.clone()))
            .collect()
    }

    fn frame_fields(&self) -> String {
        self.slots
            .iter()
            .filter(|slot| slot.words.is_none())
            .map(|slot| format!("({} {})", slot.field, slot.name))
            .chain(self.word_buffers().into_iter().map(|region| {
                format!(
                    "({} (#array #u64 {})) ({} (#array {} 0))",
                    region.field,
                    region.capacity,
                    region.marker,
                    crate::type_source(&region.owner)
                )
            }))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn slice_holder(&self, binding: BindingId) -> String {
        let slot = &self.slots[self.bindings[&binding]];
        let mutable = matches!(
            crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases),
            Ok(Type::MutableSlice(_))
        );
        format!(
            "(#pin-get-payload{} {} {} 0)",
            if mutable { "-mut" } else { "" },
            Self::slot_ref(slot, mutable),
            slot.full
        )
    }

    fn occupancy_write(&self, slot: usize, initialized: bool) {
        if let Some(cells) = self.physical_current.borrow_mut().as_mut() {
            cells[slot] = initialized;
        }
        if let Some(trace) = self.occupancy_trace.borrow_mut().as_mut() {
            trace.writes.push((slot, initialized));
        }
    }

    fn occupancy_fork(&self) -> Option<usize> {
        self.occupancy_trace
            .borrow()
            .as_ref()
            .map(|trace| trace.writes.len())
    }

    fn occupancy_edge(&self, edge: usize, start: Option<usize>) {
        if let Some(start) = start {
            let mut trace = self.occupancy_trace.borrow_mut();
            let trace = trace.as_mut().unwrap();
            let writes = trace.writes.drain(start..).collect();
            assert!(trace.edges.insert(edge, writes).is_none());
        }
    }

    fn read(&self, slot: usize, transfer: bool) -> String {
        let descriptor = &self.slots[slot];
        let takes = if descriptor.raw {
            transfer && !descriptor.copy
        } else {
            !(descriptor.copy && (!transfer || self.types.contains_reference(&descriptor.ty)))
        };
        if takes {
            self.occupancy_write(slot, false);
        }
        let slot = &self.slots[slot];
        if let Some(value) = &slot.constant {
            return value.clone();
        }
        if let Some(region) = &slot.words {
            if slot.raw {
                let pointer = self.fresh("self-pointer");
                let mutable = matches!(slot.storage, Type::RawPointer { mutable: true, .. });
                let pinned = matches!(
                    crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases),
                    Ok(Type::PinnedReference { .. })
                );
                return format!(
                    "(#block (#let {pointer} {} (#unsafe (#word-read {} {})))\n{})",
                    crate::type_source(&slot.storage),
                    crate::type_source(&slot.storage),
                    self.word_slice(region, false),
                    self.materialize_internal_reference(slot, &pointer, mutable, pinned)
                );
            }
            if slot.ty == Type::Unit {
                return "()".into();
            }
            return format!(
                "(#unsafe (#{operation} {} {}))",
                crate::type_source(&slot.ty),
                self.word_slice(
                    region,
                    takes
                        || self
                            .planning
                            .declarations
                            .reference_storage_slots(&slot.ty)
                            .iter()
                            .any(|loan| loan.mutable)
                ),
                operation = if takes { "word-take" } else { "word-read" }
            );
        }
        if slot.raw {
            let pointer = self.fresh("self-pointer");
            let read = if transfer && !slot.copy {
                format!(
                    "(#unsafe (#call {} (: slot {})))",
                    slot.take,
                    Self::slot_ref(slot, true)
                )
            } else {
                format!(
                    "(#unsafe (#call {} (: slot {})))",
                    slot.peek,
                    Self::slot_ref(slot, false)
                )
            };
            let mutable = matches!(slot.storage, Type::RawPointer { mutable: true, .. });
            let pinned = matches!(
                crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases),
                Ok(Type::PinnedReference { .. })
            );
            return format!(
                "(#block (#let {pointer} {} {read})\n{})",
                crate::type_source(&slot.storage),
                self.materialize_internal_reference(slot, &pointer, mutable, pinned)
            );
        }
        if slot.copy && (!transfer || self.types.contains_reference(&slot.ty)) {
            format!(
                "(#unsafe (#call {} (: slot {})))",
                slot.peek,
                Self::slot_ref(slot, false)
            )
        } else if self.types.contains_reference(&slot.ty) {
            // Preserve the pre-move whole-cell provenance while publishing
            // Empty. Checked source and physical occupancy prove the moved
            // cell Full; only the subsequent local payload read is unchecked.
            format!(
                "(#block
                  (#let {cell} (#pin-ref-mut {name}) {reference})
                  (#let-mut {previous} {name} (#unsafe (#pin-read {cell})))
                  (#unsafe (#pin-write {cell} ({empty})))
                  (#drop {cell})
                  (#let {payload} (#pin-ref-mut {ty})
                    (#unsafe (#pin-get-payload-unchecked-mut
                      (#pin-borrow-mut {previous}) {full} 0)))
                  (#let {value} {ty} (#unsafe (#pin-read {payload})))
                  (#forget {payload}) (#forget {previous}) {value})",
                cell = self.fresh("taken-cell"),
                previous = self.fresh("taken-storage"),
                payload = self.fresh("taken-payload"),
                value = self.fresh("taken-value"),
                ty = crate::type_source(&slot.ty),
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
        if let Some(lease) = self.leases.get(value) {
            // Only certified immediate readers/calls may use this recipe.
            // It must never become an owned reference value.
            assert!(
                !transfer,
                "an in-place read lease cannot transfer ownership"
            );
            let slot = &self.slots[self.bindings[&lease.binding]];
            if slot.raw {
                return self.read(self.bindings[&lease.binding], false);
            }
            let descriptor = &self.function.graph.places[lease.place.0];
            if !descriptor.projections.is_empty() {
                let address = self
                    .owned_projection_address(lease.place, true)
                    .expect("a projected lease must have a checked owning address")
                    .0;
                return if self.is_word_place(lease.place) {
                    format!("(#deref {address})")
                } else {
                    address
                };
            }
            return format!("(#deref {})", self.payload_ref(slot, true));
        }
        self.values
            .get(&value)
            .map_or_else(|| "()".into(), |slot| self.read(*slot, transfer))
    }

    fn put(&self, slot: usize, value: &str) -> String {
        self.occupancy_write(slot, true);
        let slot = &self.slots[slot];
        if slot.constant.is_some() {
            return format!("(#forget {value})");
        }
        if let Some(region) = &slot.words {
            if slot.raw {
                let pointer = self.fresh("stored-self-pointer");
                let ty = crate::type_source(&slot.storage);
                return format!(
                    "(#block (#let {pointer} {ty} (#ref-ptr {value}))\n(#unsafe (#word-write {ty} {} {pointer})))",
                    self.word_slice(region, true)
                );
            }
            if slot.ty == Type::Unit {
                return format!("(#forget {value})");
            }
            let incoming = self.fresh("word-value");
            let ty = crate::type_source(&slot.ty);
            return format!(
                "(#block (#let {incoming} {ty} {value})
                (#unsafe (#word-write {ty} {} {incoming})))",
                self.word_slice(region, true)
            );
        }
        if slot.raw {
            let pointer = self.fresh("stored-self-pointer");
            // Evaluate and erase the incoming temporary loan before obtaining
            // exclusive access to the destination pointer cell.
            return format!("(#block (#let {pointer} {} (#ref-ptr {value}))\n(#call {} (: slot {} : value {pointer})) ())",
                crate::type_source(&slot.storage), slot.put, Self::slot_ref(slot, true));
        }
        if !slot.copy && self.types.contains_reference(&slot.ty) {
            // Stage the input before touching the destination, as a normal
            // call would. Keep the actual stored enum tags visible: a unit
            // helper's invalidation summary cannot establish the child's
            // newly selected payload in the returned Pending frame.
            // Check the tag before extracting a pinned owner. Even an invalid
            // dispatcher state must not move an occupied, potentially borrowed
            // payload and only then discover that initialization was illegal.
            let cell = self.fresh("stored-cell");
            let empty_guard = if slot.linear {
                format!("(#assert (#variant-is {cell} {}))", slot.empty)
            } else {
                String::new()
            };
            return format!(
                "(#block
                  (#let {incoming} {ty} {value})
                  (#let {cell} (#pin-ref-mut {name}) {reference})
                  {empty_guard}
                  (#unsafe (#forget (#pin-read {cell})))
                  (#unsafe (#pin-write {cell} ({empty})))
                  (#unsafe (#forget (#pin-read {cell})))
                  (#unsafe (#pin-write {cell} ({full} {incoming})))
                  (#drop {cell}) ())",
                incoming = self.fresh("stored-value"),
                ty = crate::type_source(&slot.ty),
                cell = cell,
                name = slot.name,
                reference = Self::slot_ref(slot, true),
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

    fn put_binding(&self, binding: BindingId, expression: &str) -> String {
        let Some(aggregate) = self.aggregates.get(&binding) else {
            return self
                .bindings
                .get(&binding)
                .map_or_else(|| expression.to_owned(), |slot| self.put(*slot, expression));
        };
        self.put_aggregate(aggregate, &[], expression)
    }

    fn aggregate_shells(
        &mut self,
        binding: BindingId,
        shape: &crate::generator::async_aggregate::Shape,
    ) -> Result<Vec<AggregateShell>, Error> {
        fn visit<'a>(
            shape: &'a crate::generator::async_aggregate::Shape,
            path: Vec<crate::typed_ir::FieldId>,
            name: String,
            output: &mut Vec<(Vec<crate::typed_ir::FieldId>, String, &'a Type)>,
        ) {
            output.push((path.clone(), name.clone(), &shape.ty));
            for field in &shape.fields {
                if let Some(nested) = &field.nested {
                    let mut path = path.clone();
                    path.push(field.id);
                    let name = if name.is_empty() {
                        field.name.clone()
                    } else {
                        format!("{name}.{}", field.name)
                    };
                    visit(nested, path, name, output);
                }
            }
        }
        let mut shapes = Vec::new();
        visit(shape, Vec::new(), String::new(), &mut shapes);
        let mut shells = Vec::new();
        for (path, prefix, ty) in shapes {
            if !self
                .types
                .linear_obligation_paths(ty)
                .iter()
                .any(Vec::is_empty)
            {
                continue;
            }
            let suffix = if prefix.is_empty() {
                "shell".into()
            } else {
                format!("{prefix}.shell")
            };
            let name = format!(
                "{}-{}-{suffix}",
                self.frame, self.function.graph.bindings[binding.0].name
            );
            if !self.reserved.borrow_mut().insert(name.clone()) {
                return Err(fail(
                    self.function,
                    format!(
                        "async ownership marker '{name}' conflicts with an existing declaration"
                    ),
                ));
            }
            let alive = self.fresh("AggregateAlive");
            self.projections
                .push(format!("(#enum {name} (#linear) ({alive}))"));
            let slot = self.add_slot(format!("binding.{}.{suffix}", binding.0), Type::Named(name));
            self.slots[slot].copy = false;
            self.slots[slot].linear = true;
            shells.push(AggregateShell {
                path,
                name: suffix,
                slot,
                alive,
            });
        }
        Ok(shells)
    }

    fn aggregate_pattern(
        &self,
        aggregate: &Aggregate,
        path: &[crate::typed_ir::FieldId],
        names: &mut HashMap<usize, String>,
    ) -> String {
        let shape = aggregate.shape(path).expect("checked aggregate subtree");
        let fields = shape
            .fields
            .iter()
            .map(|field| {
                let mut path = path.to_vec();
                path.push(field.id);
                if field.nested.is_some() {
                    self.aggregate_pattern(aggregate, &path, names)
                } else {
                    let slot = aggregate
                        .fields
                        .iter()
                        .find(|part| part.path == path)
                        .unwrap()
                        .slot;
                    let name = self.fresh("aggregate-part");
                    names.insert(slot, name.clone());
                    name
                }
            })
            .collect::<Vec<_>>()
            .join(" ");
        format!("({} {fields})", shape.constructor)
    }

    fn put_aggregate(
        &self,
        aggregate: &Aggregate,
        path: &[crate::typed_ir::FieldId],
        expression: &str,
    ) -> String {
        let mut names = HashMap::new();
        let pattern = self.aggregate_pattern(aggregate, path, &mut names);
        let stores = aggregate
            .fields
            .iter()
            .filter_map(|field| {
                names
                    .get(&field.slot)
                    .map(|name| self.put(field.slot, name))
            })
            .chain(
                aggregate
                    .shells
                    .iter()
                    .filter(|shell| shell.path.starts_with(path))
                    .map(|shell| self.put(shell.slot, &format!("({})", shell.alive))),
            )
            .collect::<Vec<_>>()
            .join("\n");
        let ty = crate::type_source(&aggregate.shape(path).unwrap().ty);
        format!("(#block (#let {pattern} {ty} {expression})\n{stores}\n())")
    }

    fn read_binding(&self, binding: BindingId, transfer: bool) -> String {
        let Some(aggregate) = self.aggregates.get(&binding) else {
            return self
                .bindings
                .get(&binding)
                .map_or_else(|| "()".into(), |slot| self.read(*slot, transfer));
        };
        self.read_aggregate(aggregate, &[], transfer)
    }

    fn read_aggregate(
        &self,
        aggregate: &Aggregate,
        path: &[crate::typed_ir::FieldId],
        transfer: bool,
    ) -> String {
        let shape = aggregate.shape(path).unwrap();
        let fields = shape
            .fields
            .iter()
            .map(|field| {
                let mut path = path.to_vec();
                path.push(field.id);
                let value = if field.nested.is_some() {
                    self.read_aggregate(aggregate, &path, transfer)
                } else {
                    self.read(
                        aggregate
                            .fields
                            .iter()
                            .find(|part| part.path == path)
                            .unwrap()
                            .slot,
                        transfer,
                    )
                };
                format!("({} {value})", field.name)
            })
            .collect::<Vec<_>>()
            .join(" ");
        let value = format!("(#struct-literal {} ({fields}))", shape.constructor);
        let clear_refs = if transfer {
            aggregate
                .fields
                .iter()
                .filter(|field| {
                    let slot = &self.slots[field.slot];
                    field.path.starts_with(path)
                        && field.path.len() == path.len() + 1
                        && slot.copy
                        && self.types.contains_reference(&slot.ty)
                })
                .map(|field| {
                    self.occupancy_write(field.slot, false);
                    let slot = &self.slots[field.slot];
                    if slot.words.is_some() {
                        return String::new();
                    }
                    format!(
                        "(#call {} (: slot {}))",
                        slot.clear,
                        Self::slot_ref(slot, true)
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            String::new()
        };
        let shell = if transfer {
            aggregate
                .shells
                .iter()
                .filter(|shell| shell.path == path)
                .map(|shell| format!("(#forget {})", self.read(shell.slot, true)))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            String::new()
        };
        if clear_refs.is_empty() && shell.is_empty() {
            return value;
        }
        let result = self.fresh("reconstructed-owner");
        let ty = crate::type_source(&shape.ty);
        format!("(#block (#let {result} {ty} {value}) {clear_refs} {shell} {result})")
    }

    fn aggregate_field(&self, descriptor: &PlaceDescriptor) -> Option<&AggregateField> {
        if matches!(descriptor.root, AddressRoot::Local(binding)
            if self.active_preview_aliases.contains(&binding))
        {
            return None;
        }
        let AddressRoot::Local(binding) = descriptor.root else {
            return None;
        };
        self.aggregates
            .get(&binding)?
            .fields
            .iter()
            .find(|field| Self::projection_starts_with(&descriptor.projections, &field.path))
    }

    /// Clone is a by-value snapshot, not a borrow of a reconstructed owner.
    /// Copy each storage cell without invoking its payload's clone hook, then
    /// perform exactly one ordinary clone dispatch on the assembled value.
    /// Original cells (and live references into them) remain stationary/Full.
    fn clone_aggregate(
        &mut self,
        binding: BindingId,
        path: &[crate::typed_ir::FieldId],
    ) -> Result<String, Error> {
        let aggregate = &self.aggregates[&binding];
        let shape = aggregate
            .shape(path)
            .ok_or_else(|| fail(self.function, "aggregate clone lost its checked shape"))?
            .clone();
        let fields = aggregate
            .fields
            .iter()
            .map(|field| (field.path.clone(), field.slot))
            .collect::<HashMap<_, _>>();
        let snapshot = self.snapshot_aggregate(&shape, path, &fields)?;
        let temporary = self.fresh("aggregate-clone-source");
        let result = self.fresh("aggregate-clone-result");
        let ty = crate::type_source(&shape.ty);
        Ok(format!(
            "(#block (#let {temporary} {ty} {snapshot})\n\
             (#let {result} {ty} (#clone {temporary}))\n\
             (#forget {temporary}) {result})"
        ))
    }

    fn snapshot_aggregate(
        &mut self,
        shape: &crate::generator::async_aggregate::Shape,
        path: &[crate::typed_ir::FieldId],
        fields: &HashMap<Vec<crate::typed_ir::FieldId>, usize>,
    ) -> Result<String, Error> {
        let mut values = Vec::new();
        for field in &shape.fields {
            let mut child = path.to_vec();
            child.push(field.id);
            let value = if let Some(nested) = &field.nested {
                self.snapshot_aggregate(nested, &child, fields)?
            } else {
                let index = *fields.get(&child).ok_or_else(|| {
                    fail(self.function, "aggregate clone lost its checked field cell")
                })?;
                self.snapshot_cell(index)?
            };
            values.push(format!("({} {value})", field.name));
        }
        Ok(format!(
            "(#struct-literal {} ({}))",
            shape.constructor,
            values.join(" ")
        ))
    }

    fn snapshot_cell(&mut self, index: usize) -> Result<String, Error> {
        if self.slots[index].raw {
            return Ok(self.read(index, false));
        }
        if let Some(region) = &self.slots[index].words {
            // This is an implementation-only bit snapshot for one checked
            // clone invocation, not a transfer of the original linear owner.
            // clone_aggregate explicitly forgets the temporary afterwards.
            // In particular, cancellation must still see the original Full.
            let ty = &self.slots[index].ty;
            return Ok(if *ty == Type::Unit {
                "()".into()
            } else {
                format!(
                    "(#unsafe (#word-read {} {}))",
                    crate::type_source(ty),
                    self.word_slice(region, false)
                )
            });
        }
        if self.slots[index].copy || self.slots[index].raw {
            return Ok(self.read(index, false));
        }
        if !self.cell_snapshots.contains_key(&index) {
            // Clone the enum cell, not the payload. An explicit identity
            // hook reserves dispatch against user hooks on generated cells.
            let clone = format!("{}-clone", self.slots[index].name);
            if !self.reserved.borrow_mut().insert(clone.clone()) {
                return Err(fail(
                    self.function,
                    format!("aggregate snapshot clone conflicts with '{clone}'"),
                ));
            }
            let argument = self.fresh("cell-clone-input");
            let input = self.fresh("cell-snapshot-input");
            let snapshot = self.fresh("cell-snapshot-storage");
            let value = self.fresh("cell-snapshot-value");
            let helper = self.fresh("cell-snapshot");
            let slot = &self.slots[index];
            let ty = &slot.name;
            self.projections.push(format!(
                "(#fn {clone} (: {argument} {ty}) {ty} (#return {argument}))\n\
                 (#fn {helper} (: {input} (#pin-ref {ty})) {}\n\
                 (#let {snapshot} {ty} (#clone (#deref {input})))\n\
                 (#return (#match {snapshot}\n\
                 (#case {} (#unreachable))\n\
                 (#case ({} {value}) {value}))))",
                crate::type_source(&slot.storage),
                slot.empty,
                slot.full
            ));
            self.cell_snapshots.insert(index, (helper, input));
        }
        let (helper, input) = &self.cell_snapshots[&index];
        Ok(format!(
            "(#call {helper} (: {input} {}))",
            Self::slot_ref(&self.slots[index], false)
        ))
    }

    fn aggregate_exact_field(&self, descriptor: &PlaceDescriptor) -> Option<&AggregateField> {
        if matches!(descriptor.root, AddressRoot::Local(binding)
            if self.active_preview_aliases.contains(&binding))
        {
            return None;
        }
        self.aggregate_field(descriptor)
            .filter(|field| field.path.len() == descriptor.projections.len())
    }

    fn projection_starts_with(
        projections: &[AddressProjection],
        path: &[crate::typed_ir::FieldId],
    ) -> bool {
        projections.len() >= path.len() && projections.iter().zip(path).all(|(projection, id)| matches!(projection, AddressProjection::Field(field) if field == id))
    }

    fn anchor_field(
        &self,
        binding: BindingId,
        segments: &[crate::typed_place::Segment],
    ) -> Option<&AggregateField> {
        self.aggregates.get(&binding)?.fields.iter().find(|field| {
            segments.len() >= field.path.len() && segments.iter().zip(&field.path).all(|(segment, id)| matches!(segment, crate::typed_place::Segment::Field(found) if found == id))
        })
    }

    fn aggregate_subtree(
        &self,
        descriptor: &PlaceDescriptor,
    ) -> Option<(&Aggregate, Vec<crate::typed_ir::FieldId>)> {
        if matches!(descriptor.root, AddressRoot::Local(binding)
            if self.active_preview_aliases.contains(&binding))
        {
            return None;
        }
        let AddressRoot::Local(binding) = descriptor.root else {
            return None;
        };
        let aggregate = self.aggregates.get(&binding)?;
        let path = descriptor
            .projections
            .iter()
            .map(|projection| match projection {
                AddressProjection::Field(id) => Some(*id),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        aggregate.shape(&path)?;
        Some((aggregate, path))
    }

    fn slot_definitions(&self) -> String {
        let mut lenders = self
            .bindings
            .iter()
            .filter_map(|(binding, index)| {
                self.leases.snapshots_binding(*binding).then_some(*index)
            })
            .collect::<HashSet<_>>();
        lenders.extend(
            self.values.iter().filter_map(|(value, index)| {
                self.leases.projected_snapshot(*value).map(|_| *index)
            }),
        );
        self.slots.iter().enumerate().filter(|(_, slot)| slot.words.is_none()).map(|(index, slot)| {
            let ty = crate::type_source(&slot.storage);
            let mut lend = if lenders.contains(&index) {
                if matches!(crate::typed_ir::resolve_type(&slot.storage, &self.planning.declarations.aliases), Ok(Type::MutableSlice(_))) {
                    format!("(#fn {} (: {} (#pin-ref-mut {ty})) {ty}\n  (#return (#slice-mut-range (#deref {}) 0usize (#slice-mut-len (#deref {})))))\n",
                        slot.lend, slot.lend_argument, slot.lend_argument, slot.lend_argument)
                } else {
                    format!("(#fn {} (: {} {ty}) {ty} (#return {}))\n",
                        slot.lend, slot.lend_argument, slot.lend_argument)
                }
            } else { String::new() };
            if self.recover_nested_reference(slot) {
                let Type::Reference { target, .. } = crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases).unwrap() else { unreachable!() };
                let target = crate::type_source(&target);
                lend.push_str(&format!("(#fn {} (: {} (#pin-ref {target})) (#ref {target})\n  (#return (#unsafe (#ptr-borrow {} (#ref-ptr {})))))\n",
                    slot.recover, slot.recover_argument, slot.recover_argument, slot.recover_argument));
            }
            let occupied = if slot.linear {
                // This branch is a violated compiler/source invariant, not an
                // invented destructor for a live owner. It traps explicitly.
                "(#block (#forget occupied) (#assert false))"
            } else { "(#forget occupied)" };
            let empty_guard = if slot.linear {
                format!("(#assert (#variant-is slot {}))", slot.empty)
            } else { String::new() };
            let peek = if slot.copy || slot.raw {
                // Source ownership and graph initialization justify this
                // unchecked access; frame opacity protects those invariants
                // at the safe public poll boundary. Pinning alone does not.
                let read = format!("(#deref (#pin-get-payload-unchecked slot {} 0))", slot.full);
                let read = if slot.raw { format!("(#clone {read})") } else { read };
                format!("; Caller proves this cell Full through checked async flow.\n(#unsafe-fn {} ((slot (#pin-ref {}))) {ty}\n  (#return (#unsafe {read})))", slot.peek, slot.name)
            } else { String::new() };
            let take = if slot.copy && !self.types.contains_reference(&slot.storage) {
                // Like peek, the caller must prove Full. Copy payloads carry
                // neither destruction obligations nor loans; taking one can
                // read the payload directly and publish Empty without a tag
                // branch. Use a typed pinned projection, not an untagged raw
                // address: native stack and heap layouts differ.
                format!("; Caller proves this cell Full through checked async flow.\n\
                  (#unsafe-fn {take} ((slot (#pin-ref-mut {name}))) {ty}\n\
                    (#let value {ty} (#unsafe (#deref (#pin-get-payload-unchecked slot {full} 0))))\n\
                    (#unsafe (#forget (#pin-read slot)))\n\
                    (#unsafe (#pin-write slot ({empty})))\n\
                    (#return value))",
                    name=slot.name, empty=slot.empty, full=slot.full, take=slot.take)
            } else {
                format!("(#unsafe-fn {take} ((slot (#pin-ref-mut {name}))) {ty}\n\
                    (#let previous {name} (#unsafe (#pin-read slot)))\n\
                    (#unsafe (#pin-write slot ({empty})))\n\
                    (#return (#match previous\n\
                      (#case {empty} (#unreachable))\n\
                      (#case ({full} value) value))))",
                    name=slot.name, empty=slot.empty, full=slot.full, take=slot.take)
            };
            if slot.copy && self.types.contains_reference(&slot.storage) {
                // A shared handle is copied, not extracted through a moving
                // cell helper. End all old loaded aliases before restoration.
                // Full source checking and ordinary call contracts still
                // determine which incoming referents the cell retains.
                return format!("{lend}(#enum {name} (#linear) (({empty}) ({full} {ty})))\n\
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
            if self.types.contains_reference(&slot.storage) {
                // Owned reference transfers are emitted at the actual local
                // cell, where input-slot identities and Empty/Full tags stay
                // visible. Do not emit unused abstract take/put helpers.
                return format!("{lend}(#enum {name} (#linear) (({empty}) ({full} {ty})))\n\
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
            format!("{lend}(#enum {name} (#linear) (({empty}) ({full} {ty})))\n\
              {take}\n\
              (#fn {put} ((slot (#pin-ref-mut {name})) (value {ty})) ()\n\
                {empty_guard}\n\
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
                name=slot.name, empty=slot.empty, full=slot.full,
                put=slot.put, finish=slot.finish, clear=slot.clear)
        }).collect::<Vec<_>>().join("\n")
    }

    fn clear_binding(&self, binding: BindingId) -> String {
        if self.active_preview_aliases.contains(&binding) {
            return String::new();
        }
        if let Some(aggregate) = self.aggregates.get(&binding) {
            return aggregate
                .cells()
                .map(|index| {
                    let occupied = self
                        .physical_current
                        .borrow()
                        .as_ref()
                        .is_none_or(|cells| cells[index]);
                    self.occupancy_write(index, false);
                    let slot = &self.slots[index];
                    if let Some(region) = &slot.words {
                        return if occupied && !slot.raw && self.types.contains_reference(&slot.ty) {
                            self.forget_word_region(region)
                        } else {
                            String::new()
                        };
                    }
                    format!(
                        "(#call {} (: slot {}))",
                        slot.clear,
                        Self::slot_ref(slot, true)
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
        }
        self.bindings
            .get(&binding)
            .map_or_else(String::new, |slot| {
                let occupied = self
                    .physical_current
                    .borrow()
                    .as_ref()
                    .is_none_or(|cells| cells[*slot]);
                self.occupancy_write(*slot, false);
                let index = *slot;
                let slot = &self.slots[index];
                if let Some(region) = &slot.words {
                    return if occupied && !slot.raw && self.types.contains_reference(&slot.ty) {
                        self.forget_word_region(region)
                    } else {
                        String::new()
                    };
                }
                let clear = format!(
                    "(#call {} (: slot {}))",
                    slot.clear,
                    Self::slot_ref(slot, true)
                );
                if self.pinned && self.types.contains_reference(&slot.ty) {
                    format!(
                        "{clear}\n(#assert (#variant-is {} {}))",
                        Self::slot_ref(slot, false),
                        slot.empty
                    )
                } else {
                    clear
                }
            })
    }

    fn clear_scope(&self, bindings: &[BindingId]) -> Result<String, Error> {
        let mut remaining = bindings.iter().rev().copied().collect::<Vec<_>>();
        let mut output = Vec::new();
        while !remaining.is_empty() {
            let next = remaining
                .iter()
                .position(|candidate| {
                    !remaining.iter().any(|other| {
                        other != candidate
                            && self.bindings.get(other).is_some_and(|index| {
                                let slot = &self.slots[*index];
                                slot.dependencies.contains(candidate)
                                    || slot.anchor.as_ref().is_some_and(|anchors| {
                                        anchors.iter().any(|anchor| {
                                            anchor.root
                                                == crate::typed_body::PlaceRoot::Local(*candidate)
                                        })
                                    })
                            })
                    })
                })
                .ok_or_else(|| fail(self.function, "cyclic async scope-exit dependency"))?;
            output.push(self.clear_binding(remaining.remove(next)));
        }
        Ok(output.join("\n"))
    }

    fn clear_values(&mut self, values: &[ValueId]) -> String {
        let slots = values
            .iter()
            .filter(|value| !self.immediate.skips_storage(**value))
            .map(|value| self.values[value])
            .collect::<Vec<_>>();
        self.clear_handle_slots(&slots)
    }

    fn clear_handle_slots(&self, slots: &[usize]) -> String {
        let mut clears = Vec::new();
        for &index in slots {
            self.occupancy_write(index, false);
            if let Some(region) = &self.slots[index].words {
                clears.push(self.forget_word_region(region));
                continue;
            }
            let handle = self.fresh("retired-handle");
            let reference = self.fresh("retired-cell");
            let previous = self.fresh("retired-storage");
            let slot = &self.slots[index];
            if !slot.linear || slot.borrowed_slice_snapshot {
                // Non-owning handles have no destruction obligation. Discard
                // storage in place rather than transferring a reference into
                // a temporary that would need its pointee's nested provenance.
                // A certified slice snapshot is a reborrow, not the source
                // binding's linear owner. Retiring its descriptor must not
                // require that the original slice was moved or consumed.
                clears.push(format!("(#block (#let {reference} (#pin-ref-mut {}) {})\n(#unsafe (#forget (#pin-read {reference})))\n(#unsafe (#pin-write {reference} ({})))\n(#drop {reference}) ())", slot.name, Self::slot_ref(slot, true), slot.empty));
                continue;
            }
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
        let mut slots = cells
            .iter()
            .filter_map(|cell| match cell {
                crate::generator::async_cells::Cell::Binding(binding) => {
                    self.bindings.get(binding).copied()
                }
                crate::generator::async_cells::Cell::Value(value) => {
                    // Handle retirement already makes this particular Empty write
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
                crate::generator::async_cells::Cell::Scope(scope) => {
                    self.scopes.get(scope).copied()
                }
            })
            .collect::<Vec<_>>();
        if exit {
            // Selected addresses have their own liveness plan, independent of
            // binding/value cells. Every address is retired after its last
            // consumer before Return. Later calls can invalidate the ordinary
            // checker's stored tag facts, so publish their Empty invariant as
            // well before extracting the complete frame. A checked assertion
            // catches disagreement with actual address retirement at runtime.
            slots.extend(self.addresses.values().copied());
            slots.sort_unstable();
            slots.dedup();
        }
        // These cells were proved Empty by the physical graph solver. Expose
        // that invariant with a checked tag assertion before ordinary
        // empty-cell extraction/restoration. A user cleanup call may consume
        // its referent; without this tag fact an extraction would require
        // nonexistent reference provenance. Restoration still publishes the
        // definite Empty store to callers' retained-contents contracts.
        let assertions = slots
            .iter()
            .filter(|index| self.slots[**index].words.is_none())
            .map(|index| {
                let slot = &self.slots[*index];
                format!(
                    "(#assert (#variant-is {} {}))",
                    Self::slot_ref(slot, false),
                    slot.empty
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        format!("{assertions}\n{}", self.clear_handle_slots(&slots))
    }

    fn pattern_value(
        &self,
        pattern: &crate::generator::async_exec::Pattern,
    ) -> Result<String, Error> {
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
        pattern: &crate::generator::async_exec::Pattern,
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
        pattern: &crate::generator::async_exec::Pattern,
        commit: bool,
    ) -> Result<String, Error> {
        // Repetition is allowed only by the ordinary checked type. A shared
        // reference snapshot keeps its pointee loan; it is not a borrow of the
        // scrutinee cell, including inside Copy aggregates. Exclusive handles
        // are reborrowed through ordinary identity helpers; linear payloads
        // still require stationary aliases rather than owning preview reads.
        if !commit {
            let ty = &self.function.graph.values[pattern.scrutinee.0].ty;
            if !self.types.can_repeat(ty) {
                let mut names = HashMap::new();
                let mut bindings = HashMap::new();
                let mut lenders = HashMap::new();
                for &binding in &pattern.bindings {
                    if self.preview_aliases.patterns.contains_key(&binding) {
                        names.insert(binding, self.fresh("guard-alias"));
                        self.active_preview_aliases.insert(binding);
                        continue;
                    }
                    let ty = &self.function.graph.bindings[binding.0].ty;
                    let exclusive = matches!(
                        crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases),
                        Ok(Type::Reference { mutable: true, .. }
                            | Type::PinnedReference { mutable: true, .. })
                    );
                    if !self.types.can_repeat(ty) && !exclusive {
                        return Err(fail(
                            self.function,
                            "move-only guard bindings require stationary storage aliases",
                        ));
                    }
                    let name = self.fresh("guard-preview");
                    if exclusive {
                        let helper = self.fresh("guard-lend");
                        let argument = self.fresh("guard-lend-input");
                        self.projections.push(format!(
                            "(#fn {helper} (: {argument} {}) {} (#return {argument}))",
                            crate::type_source(ty),
                            crate::type_source(ty)
                        ));
                        lenders.insert(name.clone(), (helper, argument));
                    }
                    bindings.insert(name.clone(), ty.clone());
                    names.insert(binding, name);
                }
                let source = crate::parse(&self.pattern_source(pattern, &names)?)
                    .map_err(|error| fail(self.function, error.to_string()))?
                    .remove(0)
                    .expr;
                let slot = &self.slots[*self.values.get(&pattern.scrutinee).ok_or_else(|| {
                    fail(
                        self.function,
                        "stationary guard scrutinee has no owning cell",
                    )
                })?];
                let reference = crate::parse(&self.payload_ref(slot, !lenders.is_empty()))
                    .map_err(|error| fail(self.function, error.to_string()))?
                    .remove(0)
                    .expr;
                let preview = crate::generator::async_pattern::preview(
                    &self.planning.declarations,
                    &source,
                    ty,
                    reference,
                    &bindings,
                    &lenders,
                )
                .map_err(|message| fail(self.function, message))?;
                let mut stores = Vec::new();
                for (name, value) in preview {
                    let binding = names
                        .iter()
                        .find_map(|(binding, actual)| (actual == &name).then_some(*binding))
                        .ok_or_else(|| {
                            fail(self.function, "guard preview lost its source binding")
                        })?;
                    if self.bindings.contains_key(&binding) {
                        stores.push(
                            self.put_binding(
                                binding,
                                &crate::expression_source(&value)
                                    .map_err(|message| fail(self.function, message))?,
                            ),
                        );
                    }
                }
                return Ok(stores.join("\n"));
            }
        }
        let value = self.value(pattern.scrutinee, commit);
        let mut names = HashMap::new();
        let mut stores = Vec::new();
        for &binding in &pattern.bindings {
            let name = self.fresh("pattern");
            if self.bindings.contains_key(&binding) {
                stores.push(self.put_binding(binding, &name));
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

    fn selected_reference(&self, place: PlaceId) -> String {
        let slot = &self.slots[self.addresses[&place]];
        if slot.copy {
            self.read(self.addresses[&place], false)
        } else {
            format!(
                "(#deref (#pin-get-payload-mut {} {} 0))",
                Self::slot_ref(slot, true),
                slot.full
            )
        }
    }

    fn clear_addresses(&self, places: &[PlaceId]) -> String {
        self.clear_handle_slots(
            &places
                .iter()
                .flat_map(|place| {
                    self.addresses.get(place).copied().into_iter().chain(
                        self.owned_indices
                            .get(place)
                            .into_iter()
                            .flatten()
                            .map(|index| index.slot),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }

    fn select_owned_indices(
        &self,
        place: PlaceId,
        descriptor: &PlaceDescriptor,
    ) -> Result<String, Error> {
        let mut actions = Vec::new();
        for index in &self.owned_indices[&place] {
            let inherited = descriptor
                .parent
                .and_then(|parent| self.owned_indices.get(&parent))
                .and_then(|indices| {
                    indices.iter().find(|parent| {
                        parent.projection == index.projection && parent.value == index.value
                    })
                });
            let value = if let Some(parent) = inherited {
                self.read(parent.slot, false)
            } else if let Some(literal) = self.literal_index(index.value) {
                format!("{literal}usize")
            } else {
                self.value(index.value, false)
            };
            actions.push(self.put(index.slot, &value));
            // Run bounds checks at selection, before any later index effects
            // or RHS suspension. Resumption only uses the saved numeric index.
            if index.projection >= descriptor.checked_prefix {
                actions.push(format!(
                    "(#assert (#usize.< {} {}usize))",
                    self.read(index.slot, false),
                    index.bound
                ));
            }
        }
        Ok(actions.join("\n"))
    }

    fn select_address(
        &mut self,
        place: PlaceId,
        descriptor: &PlaceDescriptor,
    ) -> Result<String, Error> {
        let slot = &self.slots[self.addresses[&place]];
        let (pinned, mutable) = match slot.ty {
            Type::PinnedReference { mutable, .. } => (true, mutable),
            Type::Reference { mutable, .. } => (false, mutable),
            _ => unreachable!(),
        };
        let borrow = format!(
            "#{}borrow{}",
            if pinned { "pin-" } else { "" },
            if mutable { "-mut" } else { "" }
        );
        let output_type = slot.ty.clone();
        let destination = self.addresses[&place];
        let (input, input_type, start) = if let Some(parent) = descriptor
            .parent
            .filter(|parent| self.addresses.contains_key(parent))
        {
            (
                self.selected_reference(parent),
                self.slots[self.addresses[&parent]].ty.clone(),
                descriptor.checked_prefix,
            )
        } else if self.is_word_place(place) {
            let (reference, target) = self.owned_projection_address(place, mutable)?;
            (
                reference,
                Type::PinnedReference {
                    mutable,
                    target: Box::new(target),
                },
                descriptor.projections.len(),
            )
        } else {
            match descriptor.root {
                AddressRoot::Local(binding) => {
                    let field = self.aggregate_field(descriptor);
                    let owner =
                        &self.slots[field.map_or(self.bindings[&binding], |field| field.slot)];
                    (
                        self.payload_ref(owner, mutable),
                        Type::PinnedReference {
                            mutable,
                            target: Box::new(owner.ty.clone()),
                        },
                        field.map_or(0, |field| field.path.len()),
                    )
                }
                AddressRoot::Value(value)
                    if matches!(
                        descriptor.projections.first(),
                        Some(AddressProjection::Dereference | AddressProjection::SliceIndex(_))
                    ) =>
                {
                    let ty = self.function.graph.values[value.0].ty.clone();
                    let resolved =
                        crate::typed_ir::resolve_type(&ty, &self.planning.declarations.aliases)
                            .map_err(|message| fail(self.function, message))?;
                    if matches!(resolved, Type::MutableSlice(_)) {
                        let index = if let Some(lease) = self.leases.get(value) {
                            self.bindings[&lease.binding]
                        } else {
                            self.values[&value]
                        };
                        let slot = &self.slots[index];
                        // Borrow the holder; extracting its linear slice through
                        // a pinned payload reference would move the pointee.
                        (
                            format!(
                                "(#pin-get-payload-mut {} {} 0)",
                                Self::slot_ref(slot, true),
                                slot.full
                            ),
                            Type::PinnedReference {
                                mutable: true,
                                target: Box::new(ty),
                            },
                            0,
                        )
                    } else {
                        (
                            self.nonmoving_handle(value, &ty)?,
                            ty,
                            usize::from(matches!(
                                descriptor.projections.first(),
                                Some(AddressProjection::Dereference)
                            )),
                        )
                    }
                }
                _ => {
                    return Err(fail(
                        self.function,
                        "selected address has no checked stable owner",
                    ))
                }
            }
        };
        // Ordinary projection builtins require a variable-rooted capability.
        // Pass the evaluated parent into a checked helper rather than borrowing
        // an accessor call or reconstructing the original owner's address.
        let helper = self.fresh("select-address");
        let base = self.fresh("select-base");
        let mut signature = vec![format!("({base} {})", crate::type_source(&input_type))];
        let mut arguments = vec![format!("({base} {input})")];
        let mut reference = base;
        let resolved =
            crate::typed_ir::resolve_type(&input_type, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?;
        let mut slice_holder = matches!(&resolved, Type::PinnedReference { target, .. }
            if matches!(crate::typed_ir::resolve_type(target, &self.planning.declarations.aliases), Ok(Type::MutableSlice(_))));
        let mut target = match resolved {
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } => *target,
            slice @ (Type::Slice(_) | Type::MutableSlice(_)) => slice,
            _ => {
                return Err(fail(
                    self.function,
                    "selected helper requires a checked reference",
                ))
            }
        };
        target = crate::typed_ir::resolve_type(&target, &self.planning.declarations.aliases)
            .map_err(|message| fail(self.function, message))?;
        let mut steps = Vec::new();
        for projection in &descriptor.projections[start..] {
            let expression = match projection {
                AddressProjection::Field(field) => format!(
                    "({borrow} (#get {reference} {}))",
                    self.planning.declarations.field(*field).name
                ),
                AddressProjection::Tuple(index) => format!("({borrow} (#get {reference} {index}))"),
                AddressProjection::Index(index) => {
                    let name = self.fresh("select-index");
                    signature.push(format!("({name} #usize)"));
                    arguments.push(format!("({name} {})", self.value(*index, false)));
                    format!("({borrow} (#index {reference} {name}))")
                }
                AddressProjection::SliceIndex(index) => {
                    let name = self.fresh("select-index");
                    signature.push(format!("({name} #usize)"));
                    arguments.push(format!("({name} {})", self.value(*index, false)));
                    let base = if slice_holder {
                        format!("(#deref {reference})")
                    } else {
                        reference.clone()
                    };
                    format!(
                        "(#slice{}-idx {base} {name})",
                        if mutable { "-mut" } else { "" }
                    )
                }
                AddressProjection::Payload(variant, index) => {
                    let name = &self.planning.declarations.variant(*variant).name;
                    if pinned {
                        format!(
                            "(#pin-get-payload{} {reference} {name} {index})",
                            if mutable { "-mut" } else { "" }
                        )
                    } else {
                        format!("({borrow} (#get-payload {reference} {name} {index}))")
                    }
                }
                _ => {
                    return Err(fail(
                        self.function,
                        "selected address projection lacks a checked reference operation",
                    ))
                }
            };
            target = match projection {
                AddressProjection::Field(field) => {
                    self.planning.declarations.field(*field).ty.clone()
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = target else {
                        return Err(fail(
                            self.function,
                            "selected tuple has no checked tuple type",
                        ));
                    };
                    fields.get(*index).cloned().ok_or_else(|| {
                        fail(self.function, "selected tuple field is out of range")
                    })?
                }
                AddressProjection::Index(_) => {
                    let Type::Array(element, _) = target else {
                        return Err(fail(
                            self.function,
                            "selected index has no checked array type",
                        ));
                    };
                    *element
                }
                AddressProjection::SliceIndex(_) => {
                    let (Type::Slice(element) | Type::MutableSlice(element)) = target else {
                        return Err(fail(
                            self.function,
                            "selected slice index has no checked slice type",
                        ));
                    };
                    *element
                }
                AddressProjection::Payload(variant, index) => self
                    .planning
                    .declarations
                    .variant(*variant)
                    .fields
                    .get(*index)
                    .cloned()
                    .ok_or_else(|| fail(self.function, "selected payload is out of range"))?,
                _ => unreachable!(),
            };
            target = crate::typed_ir::resolve_type(&target, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?;
            let selected_type = if pinned {
                Type::PinnedReference {
                    mutable,
                    target: Box::new(target.clone()),
                }
            } else {
                Type::Reference {
                    mutable,
                    target: Box::new(target.clone()),
                }
            };
            let selected = self.fresh("selected-step");
            steps.push(format!(
                "(#let {selected} {} {expression})",
                crate::type_source(&selected_type)
            ));
            reference = selected;
            slice_holder = false;
        }
        self.projections.push(format!(
            "(#fn {helper} ({}) {} {} (#return {reference}))",
            signature.join(" "),
            crate::type_source(&output_type),
            steps.join("\n")
        ));
        let slot = &self.slots[destination];
        let mut word_checks = Vec::new();
        if self.is_word_place(place) && start == descriptor.projections.len() {
            for check in descriptor.checks() {
                if let crate::generator::async_exec::PlaceCheck::ActivePayload {
                    projection,
                    variant,
                } = check
                {
                    let (slice, ty) = self
                        .word_owned_slice_prefix(place, false, projection)?
                        .ok_or_else(|| fail(self.function, "word payload check lost its owner"))?;
                    word_checks.push(format!(
                        "(#assert (#variant-is (#unsafe (#word-view (#pin-ref {}) {slice})) {}))",
                        crate::type_source(&ty),
                        self.planning.declarations.variant(variant).name
                    ));
                }
            }
        }
        // Repeated execution may select this address only after its prior
        // capability has been retired. Publish that physical tag invariant
        // before touching the owner, so ordinary call contracts distinguish
        // first-entry selection from resumed access through a retained handle.
        Ok(format!(
            "(#assert (#variant-is {} {}))\n{}\n{}",
            Self::slot_ref(slot, false),
            slot.empty,
            word_checks.join("\n"),
            self.put(
                destination,
                &format!("(#call {helper} ({}))", arguments.join(" "))
            )
        ))
    }

    fn literal_index(&self, index: ValueId) -> Option<usize> {
        fn literal(body: &Body, source: crate::typed_body::NodeId) -> Option<usize> {
            use crate::typed_body::NodeKind;
            match &body.nodes.get(source.0)?.kind {
                NodeKind::Literal(Expr::Integer(value)) => usize::try_from(*value).ok(),
                NodeKind::Literal(Expr::UnsignedInteger(value)) => usize::try_from(*value).ok(),
                NodeKind::Form { head, children, .. } if head == "literal" => {
                    literal(body, *children.last()?)
                }
                _ => None,
            }
        }
        literal(self.body, self.function.graph.values.get(index.0)?.source?)
    }

    /// Fixed-layout owned paths can retain numeric index snapshots instead of
    /// addresses. Local reads/stores still require reference-free leaves here;
    /// computed clones use typed shared helpers to retain actual loan origins.
    /// This certifies selection, not permission to copy or move its contents.
    /// Handles and variant tags still require selected capabilities.
    fn owned_array_indices(
        &self,
        descriptor: &PlaceDescriptor,
    ) -> Option<Vec<(usize, ValueId, usize)>> {
        let computed = self.computed_owned_projection(descriptor);
        if (self.pinned && !computed)
            || !descriptor
                .projections
                .iter()
                .any(|projection| matches!(projection, AddressProjection::Index(_)))
        {
            return None;
        }
        let resolve =
            |ty: &Type| crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases).ok();
        let root_ty = match descriptor.root {
            AddressRoot::Local(binding) => &self.function.graph.bindings[binding.0].ty,
            AddressRoot::Value(value) if computed => &self.function.graph.values[value.0].ty,
            _ => return None,
        };
        let Some(mut ty) = resolve(root_ty) else {
            return None;
        };
        let mut indices = Vec::new();
        for (position, projection) in descriptor.projections.iter().enumerate() {
            let next = match projection {
                AddressProjection::Field(field) => {
                    let declaration = self.planning.declarations.field(*field);
                    if self.planning.declarations.field_id(&ty, &declaration.name) != Some(*field) {
                        return None;
                    }
                    declaration.ty.clone()
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = ty else {
                        return None;
                    };
                    let Some(field) = fields.get(*index) else {
                        return None;
                    };
                    field.clone()
                }
                AddressProjection::Index(index) => {
                    let Type::Array(element, length) = ty else {
                        return None;
                    };
                    if resolve(&self.function.graph.values[index.0].ty)? != Type::Usize {
                        return None;
                    }
                    indices.push((position, *index, length));
                    *element
                }
                _ => return None,
            };
            let Some(next) = resolve(&next) else {
                return None;
            };
            ty = next;
        }
        if ty == descriptor.ty && (computed || !self.types.contains_reference(&ty)) {
            Some(indices)
        } else {
            None
        }
    }

    fn static_owned_projection(&self, descriptor: &PlaceDescriptor) -> bool {
        self.owned_array_indices(descriptor).is_some_and(|indices| {
            indices.iter().all(|(_, value, bound)| {
                self.literal_index(*value)
                    .is_some_and(|index| index < *bound)
            })
        })
    }

    fn word_owned_address(
        &self,
        id: PlaceId,
        mutable: bool,
    ) -> Result<Option<(String, Type)>, Error> {
        let Some((slice, ty)) = self.word_owned_slice(id, mutable)? else {
            return Ok(None);
        };
        Ok(Some((
            if ty == Type::Unit {
                "()".into()
            } else {
                format!(
                    "(#unsafe (#word-view (#pin-ref{} {}) {slice}))",
                    if mutable { "-mut" } else { "" },
                    crate::type_source(&ty)
                )
            },
            ty,
        )))
    }

    fn word_owned_slice(
        &self,
        id: PlaceId,
        mutable: bool,
    ) -> Result<Option<(String, Type)>, Error> {
        self.word_owned_slice_prefix(
            id,
            mutable,
            self.function.graph.places[id.0].projections.len(),
        )
    }

    fn word_owned_slice_prefix(
        &self,
        id: PlaceId,
        mutable: bool,
        prefix: usize,
    ) -> Result<Option<(String, Type)>, Error> {
        let descriptor = &self.function.graph.places[id.0];
        let AddressRoot::Local(binding) = descriptor.root else {
            return Ok(None);
        };
        if self.active_preview_aliases.contains(&binding) {
            return Ok(None);
        }
        let Some(root) = self.bindings.get(&binding).map(|slot| &self.slots[*slot]) else {
            return Ok(None);
        };
        let Some(region) = &root.words else {
            return Ok(None);
        };
        let reject = |message: &str| fail(self.function, message);
        let count = |ty: &Type| {
            crate::codegen::storage_word_count(
                ty,
                &self.planning.declarations.structs,
                &self.planning.declarations.enums,
            )
            .map_err(|message| fail(self.function, message))
        };
        let resolve = |ty: &Type| {
            crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))
        };
        let mut ty = resolve(&root.ty)?;
        let mut offset = region.start;
        let mut dynamic = Vec::new();
        for (position, projection) in descriptor.projections.iter().take(prefix).enumerate() {
            let next = match projection {
                AddressProjection::Field(field) => {
                    let declaration = self.planning.declarations.field(*field);
                    if self.planning.declarations.field_id(&ty, &declaration.name) != Some(*field) {
                        return Err(reject("word projection lost its checked field identity"));
                    }
                    let Type::Named(name) = &ty else {
                        return Err(reject("word field projection requires a struct"));
                    };
                    let fields = &self.planning.declarations.structs[name];
                    for sibling in fields.iter().take(field.index) {
                        offset += count(&resolve(&sibling.ty)?)?;
                    }
                    resolve(&declaration.ty)?
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = &ty else {
                        return Err(reject("word tuple projection lost its type"));
                    };
                    for sibling in fields.iter().take(*index) {
                        offset += count(&resolve(sibling)?)?;
                    }
                    resolve(
                        fields
                            .get(*index)
                            .ok_or_else(|| reject("word tuple index is invalid"))?,
                    )?
                }
                AddressProjection::Payload(variant, index) => {
                    let declaration = self.planning.declarations.variant(*variant);
                    if self
                        .planning
                        .declarations
                        .variant_id(&ty, &declaration.name)
                        != Some(*variant)
                    {
                        return Err(reject(
                            "word payload projection lost its checked variant identity",
                        ));
                    }
                    // Flat enum values have one discriminator word followed
                    // by the selected variant's payload, not native packed bytes.
                    offset += 1;
                    for sibling in declaration.fields.iter().take(*index) {
                        offset += count(&resolve(sibling)?)?;
                    }
                    resolve(
                        declaration
                            .fields
                            .get(*index)
                            .ok_or_else(|| reject("word payload index is invalid"))?,
                    )?
                }
                AddressProjection::Index(value) => {
                    let Type::Array(element, bound) = &ty else {
                        return Err(reject("word index projection lost its array"));
                    };
                    let element = resolve(element)?;
                    let stride = count(&element)?;
                    if let Some(index) = self.owned_indices.get(&id).and_then(|indices| {
                        indices.iter().find(|index| index.projection == position)
                    }) {
                        dynamic.push(format!(
                            "(#usize.*.wrap {} {stride}usize)",
                            self.read(index.slot, false)
                        ));
                    } else if let Some(index) =
                        self.literal_index(*value).filter(|index| index < bound)
                    {
                        offset += index * stride;
                    } else {
                        // Selection evaluates an index before it has a frozen
                        // recipe. Check the source array, not just the buffer.
                        let index = self.fresh("selected-word-index");
                        dynamic.push(format!(
                            "(#block (#let {index} #usize {})
                            (#assert (#usize.< {index} {bound}usize))
                            (#usize.*.wrap {index} {stride}usize))",
                            self.value(*value, false)
                        ));
                    }
                    element
                }
                _ => {
                    return Err(reject(
                        "word projection requires an owned field, tuple or checked array index",
                    ))
                }
            };
            ty = next;
        }
        if prefix == descriptor.projections.len() && ty != descriptor.ty {
            return Err(reject("word projection disagrees with its checked target"));
        }
        if ty == Type::Unit {
            return Ok(Some(("()".into(), ty)));
        }
        let length = count(&ty)?;
        let slice = if dynamic.is_empty() {
            self.word_slice(
                &WordRegion {
                    start: offset,
                    length,
                    ..region.clone()
                },
                mutable,
            )
        } else {
            let mut expression = format!("{offset}usize");
            for term in dynamic {
                expression = format!("(#usize.+.wrap {expression} {term})");
            }
            let start = self.fresh("word-offset");
            let slice = region.slice_bounds(
                mutable,
                &self.fresh("word-anchor"),
                &self.fresh("word-view"),
                &start,
                &format!("(#usize.+.wrap {start} {length}usize)"),
            );
            format!("(#block (#let {start} #usize {expression}) {slice})")
        };
        Ok(Some((slice, ty)))
    }

    fn is_word_place(&self, id: PlaceId) -> bool {
        matches!(self.function.graph.places[id.0].root, AddressRoot::Local(binding)
            if !self.active_preview_aliases.contains(&binding)
                && self.bindings.get(&binding).is_some_and(|slot| self.slots[*slot].words.is_some()))
    }

    fn owned_projection_address(
        &self,
        id: PlaceId,
        mutable: bool,
    ) -> Result<(String, Type), Error> {
        if let Some(address) = self.word_owned_address(id, mutable)? {
            return Ok(address);
        }
        let descriptor = &self.function.graph.places[id.0];
        let reject = |message: &str| fail(self.function, message);
        let AddressRoot::Local(binding) = descriptor.root else {
            return Err(reject("projected loads need a checked owned local root"));
        };
        let root_slot = &self.slots[*self
            .bindings
            .get(&binding)
            .ok_or_else(|| reject("projected owner has no owning cell"))?];
        let part = if self.active_preview_aliases.contains(&binding) {
            None
        } else {
            self.aggregate_field(descriptor)
        };
        let (slot, skip) = part.map_or((root_slot, 0), |field| {
            (&self.slots[field.slot], field.path.len())
        });
        if part.is_none()
            && self.aggregates.contains_key(&binding)
            && root_slot.words.is_none()
            && !self.active_preview_aliases.contains(&binding)
        {
            return Err(reject(
                "whole aggregate borrowing requires contiguous owning storage",
            ));
        }
        let mut ty = crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases)
            .map_err(|message| fail(self.function, message))?;
        // This reference exists only during the immediate leaf read. It is
        // neither a captured address nor an independently copied owner.
        let mut place = self.payload_ref(slot, mutable);
        for (position, projection) in descriptor.projections.iter().enumerate().skip(skip) {
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
                AddressProjection::Index(index)
                    if self.owned_indices.contains_key(&id)
                        || self.static_owned_projection(descriptor) =>
                {
                    let saved = self.owned_indices.get(&id).and_then(|indices| {
                        indices.iter().find(|saved| saved.projection == position)
                    });
                    let index = if let Some(saved) = saved {
                        self.read(saved.slot, false)
                    } else {
                        format!(
                            "{}usize",
                            self.literal_index(*index)
                                .ok_or_else(|| reject("static index disappeared"))?
                        )
                    };
                    let Type::Array(element, _) = ty else {
                        return Err(reject("static array projection lost its checked type"));
                    };
                    ty = crate::typed_ir::resolve_type(
                        &element,
                        &self.planning.declarations.aliases,
                    )
                    .map_err(|message| fail(self.function, message))?;
                    place = format!("(#index {place} {index})");
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
        Ok((place, ty))
    }

    fn owned_projection_place(&self, id: PlaceId, mutable: bool) -> Result<(String, Type), Error> {
        let (place, ty) = self.owned_projection_address(id, mutable)?;
        // A Copy read of a shared reference-bearing field preserves its
        // stored pointee origins through ordinary checked projection. Writes
        // still require the separate restoration protocol for those contents.
        if !self.types.can_repeat(&ty) || (mutable && self.types.contains_reference(&ty)) {
            let reject = |message: &str| fail(self.function, message);
            return Err(reject(
                "projected moves or reference holders need checked lending and restoration storage",
            ));
        }
        Ok((place, ty))
    }

    fn owned_projection_read(&self, id: PlaceId) -> Result<String, Error> {
        let (place, ty) = self.owned_projection_place(id, false)?;
        if ty == Type::Unit {
            // Unit projections have no bytes and cannot be borrowed. The
            // owned field/tuple path above is still structurally validated.
            return Ok("()".into());
        }
        Ok(if self.is_word_place(id) {
            format!("(#deref {place})")
        } else {
            format!("(#deref (#pin-borrow {place}))")
        })
    }

    fn handle_leaf_read(&mut self, descriptor: &PlaceDescriptor) -> Result<String, Error> {
        if let AddressRoot::Value(value) = descriptor.root {
            if let Some(holder) = self.leases.handle_leaf(value) {
                return self.lent_handle_leaf_read(holder, descriptor);
            }
        }
        let function = self.function;
        let reject = |message: &str| fail(function, message);
        let AddressRoot::Value(value) = descriptor.root else {
            return Err(reject("handle load has no evaluated root"));
        };
        let handle_ty = crate::typed_ir::resolve_type(
            &self.function.graph.values[value.0].ty,
            &self.planning.declarations.aliases,
        )
        .map_err(|message| fail(self.function, message))?;
        let (mut ty, pinned) = match &handle_ty {
            Type::Reference { mutable, target } if !mutable || self.leases.get(value).is_some() || self.values.contains_key(&value) => {
                (target.as_ref().clone(), false)
            }
            Type::PinnedReference { mutable, target }
                if !mutable || self.leases.get(value).is_some() || self.values.contains_key(&value) =>
            {
                (target.as_ref().clone(), true)
            }
            _ => {
                return Err(reject(
                    "address loads require a shared handle, certified exclusive window, or materialized reference cell",
                ))
            }
        };
        let Some((AddressProjection::Dereference, projections)) =
            descriptor.projections.split_first()
        else {
            return Err(reject("handle load has no checked dereference boundary"));
        };
        if !self.types.can_repeat(&descriptor.ty) {
            return Err(reject(
                "handle loads require Copy leaves; linear leaves need lending storage",
            ));
        }
        // Preserve incoming loan provenance. Shared handles use immediate
        // reborrows; exclusive windows and materialized reborrows read their
        // owning cell in place, without moving or duplicating the handle.
        let exclusive = matches!(
            handle_ty,
            Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. }
        );
        let (mut steps, mut reference) = if exclusive {
            // Keep the exclusive handle in its owner. Naming a loaded
            // #ref-mut would be an owned move, not this nonmoving read.
            let reference = if self.leases.get(value).is_some()
                || self
                    .values
                    .get(&value)
                    .is_some_and(|slot| self.slots[*slot].raw)
            {
                self.value(value, false)
            } else {
                let slot = &self.slots[self.values[&value]];
                format!(
                    "(#deref (#pin-get-payload-mut {} {} 0))",
                    Self::slot_ref(slot, true),
                    slot.full
                )
            };
            (Vec::new(), reference)
        } else {
            let name = self.fresh("shared-handle");
            (
                vec![format!(
                    "(#let {name} {} {})",
                    crate::type_source(&handle_ty),
                    self.value(value, false)
                )],
                name,
            )
        };
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
            if exclusive {
                // This is still one variable-rooted owning-cell recipe, not
                // a moved intermediate aggregate or a stored derived ref.
                // The checked Copy leaf getter reads through the handle.
                reference = format!("(#get {reference} {field})");
                if ty == Type::Unit && index + 1 != projections.len() {
                    return Err(reject("cannot project through a unit field"));
                }
                continue;
            }
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
            } else if exclusive && !projections.is_empty() {
                reference
            } else {
                format!("(#deref {reference})")
            },
        ))
    }

    fn lent_handle_leaf_read(
        &mut self,
        holder: PlaceId,
        leaf: &PlaceDescriptor,
    ) -> Result<String, Error> {
        let holder = &self.function.graph.places[holder.0];
        let AddressRoot::Value(parent) = holder.root else {
            unreachable!("certified evaluated holder")
        };
        let input_ty = self.function.graph.values[parent.0].ty.clone();
        let input = self.fresh("field-lend-input");
        let helper = self.fresh("field-lend-read");
        let mut expression = input.clone();
        let mut ty = crate::typed_ir::resolve_type(&input_ty, &self.planning.declarations.aliases)
            .map_err(|message| fail(self.function, message))?;
        for descriptor in [holder, leaf] {
            for step in &descriptor.projections {
                match step {
                    AddressProjection::Dereference => {
                        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) =
                            ty
                        else {
                            return Err(fail(
                                self.function,
                                "certified field read lost its reference boundary",
                            ));
                        };
                        ty = *target;
                        // Field getters already project through a reference.
                        // Only a whole referent needs an explicit dereference.
                        if descriptor.projections.len() == 1 {
                            expression = format!("(#deref {expression})");
                        }
                    }
                    AddressProjection::Field(field) => {
                        let declaration = self.planning.declarations.field(*field);
                        if self.planning.declarations.field_id(&ty, &declaration.name)
                            != Some(*field)
                        {
                            return Err(fail(
                                self.function,
                                "certified field read lost its checked field identity",
                            ));
                        }
                        ty = declaration.ty.clone();
                        expression = format!("(#get {expression} {})", declaration.name);
                    }
                    AddressProjection::Tuple(index) => {
                        let Type::Tuple(fields) = ty else {
                            return Err(fail(
                                self.function,
                                "certified field read lost its tuple type",
                            ));
                        };
                        ty = fields.get(*index).cloned().ok_or_else(|| {
                            fail(
                                self.function,
                                "certified field read tuple index is out of bounds",
                            )
                        })?;
                        expression = format!("(#get {expression} {index})");
                    }
                    _ => {
                        return Err(fail(
                            self.function,
                            "certified field read acquired an effectful projection",
                        ))
                    }
                }
                ty = crate::typed_ir::resolve_type(&ty, &self.planning.declarations.aliases)
                    .map_err(|message| fail(self.function, message))?;
            }
        }
        if ty
            != crate::typed_ir::resolve_type(&leaf.ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?
        {
            return Err(fail(
                self.function,
                "certified field read disagrees with its leaf type",
            ));
        }
        self.projections.push(format!(
            "(#fn {helper} (: {input} {}) {} (#return {expression}))",
            crate::type_source(&input_ty),
            crate::type_source(&leaf.ty)
        ));
        let exclusive = matches!(
            crate::typed_ir::resolve_type(&input_ty, &self.planning.declarations.aliases),
            Ok(Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. })
        );
        let parent = if exclusive
            && self.leases.get(parent).is_none()
            && self
                .values
                .get(&parent)
                .is_some_and(|slot| !self.slots[*slot].raw)
        {
            format!(
                "(#deref {})",
                self.payload_ref(&self.slots[self.values[&parent]], true)
            )
        } else {
            self.value(parent, false)
        };
        Ok(format!("(#call {helper} (: {input} {parent}))"))
    }

    fn reborrow_from_handle(
        &mut self,
        dst: ValueId,
        place: PlaceId,
        mutable: bool,
        pinned: bool,
    ) -> Result<String, Error> {
        let slot = *self.values.get(&dst).ok_or_else(|| {
            fail(
                self.function,
                "borrow result has no physical reference cell",
            )
        })?;
        self.reborrow_to_slot(slot, place, mutable, pinned)
    }

    fn aggregate_borrow(
        &mut self,
        id: PlaceId,
        mutable: bool,
        pinned: bool,
    ) -> Result<String, Error> {
        let descriptor = &self.function.graph.places[id.0];
        let AddressRoot::Local(binding) = descriptor.root else {
            return Err(fail(self.function, "field borrow lost its owning binding"));
        };
        crate::generator::async_owner::validate_mutability(&self.function.graph, binding, mutable)
            .map_err(|message| fail(self.function, message))?;
        let (mut place, target) = self.owned_projection_address(id, mutable)?;
        // An exact leaf cell supplies a pinned payload reference. A deeper
        // field/tuple/index suffix is a place, not the value of that place.
        if !self.is_word_place(id)
            && self.aggregate_exact_field(descriptor).is_none()
            && !descriptor.projections.is_empty()
        {
            place = format!("(#pin-borrow{} {place})", if mutable { "-mut" } else { "" });
        }
        if pinned {
            return Ok(place);
        }
        let input = self.fresh("field-borrow-input");
        let helper = self.fresh("field-borrow");
        let input_ty = Type::PinnedReference {
            mutable,
            target: Box::new(target.clone()),
        };
        let output_ty = Type::Reference {
            mutable,
            target: Box::new(target),
        };
        self.projections.push(format!("(#fn {helper} (: {input} {}) {} (#return (#unsafe (#ptr-borrow{} {input} (#ref-ptr {input})))))",
            crate::type_source(&input_ty), crate::type_source(&output_ty), if mutable { "-mut" } else { "" }));
        Ok(format!("(#call {helper} (: {input} {place}))"))
    }

    fn owned_array_borrow(&mut self, id: PlaceId, mutable: bool) -> Result<String, Error> {
        let descriptor = &self.function.graph.places[id.0];
        let AddressRoot::Local(binding) = descriptor.root else {
            return Err(fail(self.function, "array borrow lost its checked owner"));
        };
        crate::generator::async_owner::validate_mutability(&self.function.graph, binding, mutable)
            .map_err(|message| fail(self.function, message))?;
        // Use the checked index snapshot (or a proved in-bounds literal),
        // never re-evaluate the source index. The poll owns stationary storage
        // while executing; this ordinary reference does not pin the source.
        let (place, target) = self.owned_projection_address(id, mutable)?;
        let input = Type::PinnedReference {
            mutable,
            target: Box::new(target.clone()),
        };
        let output = Type::Reference {
            mutable,
            target: Box::new(target),
        };
        let name = self.fresh("owner-project-array");
        let argument = self.fresh("owner-project-array-input");
        let suffix = if mutable { "-mut" } else { "" };
        self.projections.push(format!(
            "(#fn {name} (: {argument} {}) {} (#return (#unsafe (#ptr-borrow{suffix} {argument} (#ref-ptr {argument})))))",
            crate::type_source(&input),
            crate::type_source(&output),
        ));
        let input = if self.is_word_place(id) {
            place
        } else {
            format!("(#pin-borrow{suffix} {place})")
        };
        Ok(format!("(#call {name} (: {argument} {input}))"))
    }

    fn immediate_reference(&mut self, value: ValueId) -> Result<String, Error> {
        let borrow = self
            .immediate
            .get(value)
            .expect("certified immediate borrow");
        if let Some(operation) = borrow.slice.clone() {
            let mut inputs = HashMap::new();
            for operand in operation
                .operands
                .iter()
                .filter(|operand| operand.position != [1])
            {
                inputs.insert(
                    operand.value,
                    crate::parse(&self.value(operand.value, true))
                        .map_err(|error| fail(self.function, error.to_string()))?
                        .remove(0)
                        .expr,
                );
            }
            return self.slice_borrow(&operation, &inputs);
        }
        let descriptor = &self.function.graph.places[borrow.place.0];
        if self.is_word_place(borrow.place) || self.aggregate_field(descriptor).is_some() {
            return self.aggregate_borrow(borrow.place, borrow.mutable, false);
        }
        if matches!(descriptor.root, AddressRoot::Local(binding) if !self.active_preview_aliases.contains(&binding) && self.aggregates.contains_key(&binding) && self.slots[self.bindings[&binding]].words.is_none())
        {
            return Err(fail(
                self.function,
                "whole aggregate borrowing requires contiguous owning storage",
            ));
        }
        if self.owned_indices.contains_key(&borrow.place)
            || self.static_owned_projection(descriptor)
        {
            return self.owned_array_borrow(borrow.place, borrow.mutable);
        }
        // The certificate limits this borrow to one synchronous operation:
        // the frame cannot move while that call is executing. No reference
        // cell or pending-edge pointer is created for this argument.
        let owner = crate::generator::async_owner::Borrow::new(
            &self.function.graph,
            descriptor,
            &self.planning.declarations,
            borrow.mutable,
            false,
            true,
        )
        .map_err(|message| fail(self.function, message))?;
        if owner.output
            != crate::typed_ir::resolve_type(
                &self.function.graph.values[value.0].ty,
                &self.planning.declarations.aliases,
            )
            .map_err(|message| fail(self.function, message))?
        {
            return Err(fail(
                self.function,
                "immediate owner borrow disagrees with its checked result type",
            ));
        }
        let slot = &self.slots[*self
            .bindings
            .get(&owner.binding)
            .ok_or_else(|| fail(self.function, "immediate borrow has no owner cell"))?];
        let input = self.payload_ref(slot, borrow.mutable);
        let name = self.fresh("immediate-owner-project");
        let argument = self.fresh("immediate-owner-input");
        let input = if self.pinned
            || borrow.mutable
            || self.active_preview_aliases.contains(&owner.binding)
        {
            self.projections.push(owner.declaration(&name, &argument));
            input
        } else {
            self.projections.push(
                owner.declaration_from_unpinned_slot(&name, &argument, &slot.name, &slot.full),
            );
            format!(
                "(#borrow{} (#get task {}))",
                if borrow.mutable { "-mut" } else { "" },
                slot.field
            )
        };
        Ok(format!("(#call {name} (: {argument} {input}))"))
    }

    fn reborrow_to_slot(
        &mut self,
        dst: usize,
        place: PlaceId,
        mutable: bool,
        pinned: bool,
    ) -> Result<String, Error> {
        let descriptor = &self.function.graph.places[place.0];
        if let AddressRoot::Global(global) = descriptor.root {
            let mut target = self
                .planning
                .declarations
                .declaration_name(crate::typed_ir::DeclarationId::Global(global))
                .to_owned();
            for projection in &descriptor.projections {
                target = match projection {
                    AddressProjection::Field(field) => format!(
                        "(#get {target} {})",
                        self.planning.declarations.field(*field).name
                    ),
                    AddressProjection::Tuple(index) => format!("(#get {target} {index})"),
                    _ => {
                        return Err(fail(
                            self.function,
                            "global borrows require checked field or tuple projections",
                        ))
                    }
                };
            }
            // Static storage is stationary. Original-source checking already
            // requires unsafe access and validates the actual global loan;
            // keep that identity rather than inventing a frame-local anchor.
            let value = format!(
                "(#unsafe (#{}borrow{} {target}))",
                if pinned { "pin-" } else { "" },
                if mutable { "-mut" } else { "" }
            );
            return Ok(self.put(dst, &value));
        }
        if matches!(descriptor.root, AddressRoot::Local(_)) {
            if pinned && !self.pinned {
                return Err(fail(
                    self.function,
                    "pinning a local requires a pinned async frame",
                ));
            }
            if self.aggregate_field(descriptor).is_some() {
                let value = self.aggregate_borrow(place, mutable, pinned)?;
                return Ok(self.put(dst, &value));
            }
            if matches!(descriptor.root, AddressRoot::Local(binding) if !self.active_preview_aliases.contains(&binding) && self.aggregates.contains_key(&binding) && self.slots[self.bindings[&binding]].words.is_none())
            {
                return Err(fail(
                    self.function,
                    "whole aggregate borrowing requires contiguous owning storage",
                ));
            }
            if self.owned_indices.contains_key(&place) || self.static_owned_projection(descriptor) {
                let expected = Type::Reference {
                    mutable,
                    target: Box::new(descriptor.ty.clone()),
                };
                if expected
                    != crate::typed_ir::resolve_type(
                        &self.slots[dst].ty,
                        &self.planning.declarations.aliases,
                    )
                    .map_err(|message| fail(self.function, message))?
                {
                    return Err(fail(
                        self.function,
                        "array borrow disagrees with its checked type",
                    ));
                }
                let value = self.owned_array_borrow(place, mutable)?;
                return Ok(self.put(dst, &value));
            }
            // A movable poll is stationary while executing. Its internal
            // handles were certified Empty on every Pending boundary in new;
            // this does not make a source pin movable or grant borrow access.
            let owner = crate::generator::async_owner::Borrow::new(
                &self.function.graph,
                descriptor,
                &self.planning.declarations,
                mutable,
                pinned,
                self.pinned || !pinned,
            )
            .map_err(|message| fail(self.function, message))?;
            let slot = self.bindings.get(&owner.binding).ok_or_else(|| {
                fail(
                    self.function,
                    "stable owner borrow has no physical binding cell",
                )
            })?;
            let slot = &self.slots[*slot];
            let input = self.payload_ref(slot, mutable);
            let name = self.fresh("owner-project");
            let argument = self.fresh("owner-project-input");
            self.projections.push(owner.declaration(&name, &argument));
            if owner.output
                != crate::typed_ir::resolve_type(
                    &self.slots[dst].ty,
                    &self.planning.declarations.aliases,
                )
                .map_err(|message| fail(self.function, message))?
            {
                return Err(fail(
                    self.function,
                    "stable owner borrow disagrees with its checked result type",
                ));
            }
            return Ok(self.put(dst, &format!("(#call {name} (: {argument} {input}))")));
        }
        let project = crate::generator::async_projection::Reborrow::new(
            &self.function.graph,
            descriptor,
            &self.planning.declarations,
            mutable,
            pinned,
        )
        .map_err(|message| fail(self.function, message))?;
        if project.output
            != crate::typed_ir::resolve_type(
                &self.slots[dst].ty,
                &self.planning.declarations.aliases,
            )
            .map_err(|message| fail(self.function, message))?
        {
            return Err(fail(
                self.function,
                "borrow result disagrees with its checked reference type",
            ));
        }
        let name = self.fresh("project");
        let argument = self.fresh("project-input");
        self.projections.push(project.declaration(&name, &argument));
        let handle = self.nonmoving_handle(project.root, &project.input)?;
        Ok(self.put(dst, &format!("(#call {name} (: {argument} {handle}))")))
    }

    fn nonmoving_handle(&self, root: ValueId, ty: &Type) -> Result<String, Error> {
        if self
            .values
            .get(&root)
            .is_some_and(|index| self.slots[*index].raw)
            || self
                .leases
                .get(root)
                .is_some_and(|lease| self.slots[self.bindings[&lease.binding]].raw)
        {
            return Ok(self.value(root, false));
        }
        Ok(
            if matches!(
                crate::typed_ir::resolve_type(ty, &self.planning.declarations.aliases)
                    .map_err(|message| fail(self.function, message))?,
                Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. }
            ) {
                let slot = self.values.get(&root).ok_or_else(|| {
                    fail(
                        self.function,
                        "projected reborrow has no evaluated exclusive handle cell",
                    )
                })?;
                let slot = &self.slots[*slot];
                format!(
                    "(#deref (#pin-get-payload-mut {} {} 0))",
                    Self::slot_ref(slot, true),
                    slot.full
                )
            } else {
                self.value(root, false)
            },
        )
    }

    fn write_through_handle(
        &mut self,
        descriptor: &PlaceDescriptor,
        value: ValueId,
    ) -> Result<String, Error> {
        let write = crate::generator::async_projection::Write::new(
            &self.function.graph,
            descriptor,
            &self.planning.declarations,
            self.types,
        )
        .map_err(|message| fail(self.function, message))?;
        let name = self.fresh("write");
        let argument = self.fresh("write-input");
        let parameter = self.fresh("write-value");
        self.projections
            .push(write.declaration(&name, &argument, &parameter));
        let handle = self.nonmoving_handle(write.projection.root, &write.projection.input)?;
        Ok(format!(
            "(#call {name} (: {argument} {handle} : {parameter} {}))",
            self.value(value, true)
        ))
    }

    fn initial_occupancy(&self) -> Vec<bool> {
        let mut initialized = vec![false; self.slots.len()];
        for (&binding, &slot) in &self.bindings {
            if binding.0 < self.function.graph.parameter_count {
                if let Some(aggregate) = self.aggregates.get(&binding) {
                    for cell in aggregate.cells() {
                        initialized[cell] = true;
                    }
                } else {
                    initialized[slot] = true;
                }
            }
        }
        for &slot in self.external_captures.values() {
            initialized[slot] = true;
        }
        initialized
    }

    /// Render the actual cell-writing helpers once per reachable source block.
    /// Restore emission scratch even on failure. Immutable checked plans are
    /// reused; tracing must not rerun their analyses or publish helper names.
    fn physical_occupancy(&mut self) -> Result<Vec<OccupancyTrace>, Error> {
        let _timing = crate::timing::detail("generator.async.physical_occupancy");
        let reserved = self.reserved.borrow().clone();
        let next = self.next.get();
        let projections = self.projections.clone();
        let snapshots = self.cell_snapshots.clone();
        let arrays = self.array_anchors.clone();
        let slices = self.slice_anchors.clone();
        let state = self.current_state;
        let trace = self.occupancy_trace.borrow_mut().take();
        let current = self.physical_current.borrow_mut().take();
        let aliases = self.active_preview_aliases.clone();
        let result = self.trace_physical_occupancy();
        *self.reserved.borrow_mut() = reserved;
        self.next.set(next);
        self.projections = projections;
        self.cell_snapshots = snapshots;
        self.array_anchors = arrays;
        self.slice_anchors = slices;
        self.current_state = state;
        *self.occupancy_trace.borrow_mut() = trace;
        *self.physical_current.borrow_mut() = current;
        self.active_preview_aliases = aliases;
        result
    }

    fn trace_physical_occupancy(&mut self) -> Result<Vec<OccupancyTrace>, Error> {
        let graph = &self.function.graph;
        let probe = &mut *self;
        let mut traces = (0..graph.blocks.len())
            .map(|_| OccupancyTrace::default())
            .collect::<Vec<_>>();
        let mut reachable = vec![false; graph.blocks.len()];
        let mut pending = vec![graph.entry];
        while let Some(block) = pending.pop() {
            if std::mem::replace(&mut reachable[block.0], true) {
                continue;
            }
            pending.extend(graph.successors(block));
            probe.current_state = block.0;
            probe.active_preview_aliases = probe.preview_aliases.entry[block.0].clone();
            *probe.occupancy_trace.borrow_mut() = Some(OccupancyTrace::default());
            probe.clear_addresses(&probe.address_retirement.as_ref().unwrap().entry[block.0]);
            let retired = probe
                .retirement
                .as_ref()
                .map_or_else(Vec::new, |plan| plan.entry[block.0].clone());
            probe.clear_values(&retired);
            for (index, action) in graph.blocks[block.0].actions.iter().enumerate() {
                probe.action(action)?;
                probe.clear_addresses(
                    probe
                        .address_retirement
                        .as_ref()
                        .unwrap()
                        .after
                        .get(&(block.0, index))
                        .map_or(&[], Vec::as_slice),
                );
                let retired = probe
                    .retirement
                    .as_ref()
                    .map_or_else(Vec::new, |plan| plan.after_action[block.0][index].clone());
                probe.clear_values(&retired);
            }
            probe.terminal(block, &graph.blocks[block.0].terminator)?;
            let trace = probe.occupancy_trace.borrow_mut().take().unwrap();
            if trace.edges.len() != graph.successors(block).len() {
                return Err(fail(
                    probe.function,
                    "physical async trace lost a successor edge",
                ));
            }
            traces[block.0] = trace;
        }
        Ok(traces)
    }

    /// Specialize source and physical initialization histories and verify projected access
    /// in each history. Reconstructing an owner requires every field; restoring
    /// one field does not require unrelated fields to be Full. This is not yet
    /// a proof of permissions to access physical cells. Source
    /// ownership and loan validation remain mandatory.
    fn check_owned_cells(
        &mut self,
    ) -> Result<crate::generator::async_initialization::Specialization, Error> {
        let physical = self.physical_occupancy()?;
        let graph = &self.function.graph;
        let mut field_slots = self
            .aggregates
            .values()
            .flat_map(Aggregate::cells)
            .collect::<Vec<_>>();
        field_slots.sort_unstable();
        let fields = field_slots
            .iter()
            .enumerate()
            .map(|(index, slot)| (*slot, graph.bindings.len() + index))
            .collect::<HashMap<_, _>>();
        let set_binding = |full: &mut Vec<bool>, binding: BindingId, initialized: bool| {
            full[binding.0] = initialized;
            if let Some(aggregate) = self.aggregates.get(&binding) {
                for index in aggregate.cells() {
                    full[fields[&index]] = initialized;
                }
            }
        };
        let mut initial = (0..graph.bindings.len())
            .map(|index| index < graph.parameter_count)
            .collect::<Vec<_>>();
        initial.resize(graph.bindings.len() + field_slots.len(), false);
        for index in 0..graph.parameter_count {
            set_binding(&mut initial, BindingId(index), true);
        }
        let physical_start = initial.len();
        initial.extend(self.initial_occupancy());
        let transfer = |located: &crate::generator::async_exec::LocatedAction,
                        full: &mut Vec<bool>| {
            match &located.action {
                Action::Bind { binding, .. } => set_binding(full, *binding, true),
                Action::Preview(pattern) | Action::Commit(pattern) => {
                    for binding in &pattern.bindings {
                        set_binding(full, *binding, true);
                    }
                }
                Action::ScopeEnter(bindings) | Action::ScopeExit(bindings) => {
                    for binding in bindings {
                        set_binding(full, *binding, false);
                    }
                }
                Action::EndPreview(pattern) => {
                    for binding in &pattern.bindings {
                        set_binding(full, *binding, false);
                    }
                }
                Action::Release { place, .. }
                    if self.types.can_repeat(&graph.places[place.0].ty)
                        && !self.types.contains_reference(&graph.places[place.0].ty) => {}
                Action::Store { place, .. }
                | Action::Release { place, .. }
                | Action::Load { place, .. } => {
                    let descriptor = &graph.places[place.0];
                    if let AddressRoot::Local(binding) = descriptor.root {
                        if descriptor.projections.is_empty() {
                            match &located.action {
                                Action::Store { .. } => set_binding(full, binding, true),
                                Action::Release { .. } => set_binding(full, binding, false),
                                Action::Load {
                                    kind: LoadKind::Read,
                                    ..
                                } if !self.types.can_repeat(&graph.bindings[binding.0].ty) => {
                                    let lending = located
                                        .source
                                        .and_then(|source| self.lending.as_ref()?.access(source));
                                    // Lending keeps the owner Full. Nonmoving
                                    // access still requires a certified window
                                    // or a materialized reborrow at emission.
                                    if !matches!(
                                        lending,
                                        Some(crate::generator::async_lend::Access::Lend(_))
                                    ) {
                                        set_binding(full, binding, false);
                                    }
                                }
                                _ => {}
                            }
                        } else {
                            let initialized = match &located.action {
                                Action::Store { .. } => Some(true),
                                Action::Release { .. } => Some(false),
                                Action::Load {
                                    kind: LoadKind::Read,
                                    ..
                                } if !self.types.can_repeat(&descriptor.ty)
                                    && !matches!(
                                        located.source.and_then(|source| self
                                            .lending
                                            .as_ref()?
                                            .access(source)),
                                        Some(crate::generator::async_lend::Access::Lend(_))
                                    ) =>
                                {
                                    Some(false)
                                }
                                _ => None,
                            };
                            if let Some(initialized) = initialized {
                                if let Some(field) = self.aggregate_exact_field(descriptor) {
                                    full[fields[&field.slot]] = initialized;
                                } else if let Some((aggregate, path)) =
                                    self.aggregate_subtree(descriptor)
                                {
                                    for slot in aggregate
                                        .fields
                                        .iter()
                                        .filter(|field| field.path.starts_with(&path))
                                        .map(|field| field.slot)
                                        .chain(
                                            aggregate
                                                .shells
                                                .iter()
                                                .filter(|shell| shell.path.starts_with(&path))
                                                .map(|shell| shell.slot),
                                        )
                                    {
                                        full[fields[&slot]] = initialized;
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        };
        let successors = (0..graph.blocks.len())
            .map(|block| {
                graph
                    .successors(BlockId(block))
                    .into_iter()
                    .map(|next| next.0)
                    .collect()
            })
            .collect::<Vec<_>>();
        let initialization =
            crate::generator::async_initialization::Specialization::solve_with_edges(
                graph.entry.0,
                &successors,
                initial,
                16_384,
                |block, full| {
                    for located in &graph.blocks[block].actions {
                        transfer(located, full);
                    }
                    for &(cell, initialized) in &physical[block].writes {
                        full[physical_start + cell] = initialized;
                    }
                },
                |block, edge, full| {
                    for &(cell, initialized) in &physical[block].edges[&edge] {
                        full[physical_start + cell] = initialized;
                    }
                },
            )
            .map_err(|message| fail(self.function, message))?;
        for state in &initialization.states {
            let mut full = state.before.clone();
            for located in &graph.blocks[state.block].actions {
                let descriptor = match &located.action {
                    Action::Place { descriptor, .. } => Some(descriptor),
                    Action::Load { place, .. }
                    | Action::Store { place, .. }
                    | Action::Release { place, .. }
                    | Action::Borrow { place, .. } => Some(&graph.places[place.0]),
                    _ => None,
                };
                if let Some(
                    descriptor @ PlaceDescriptor {
                        root: AddressRoot::Local(binding),
                        projections,
                        ..
                    },
                ) = descriptor
                {
                    if (!projections.is_empty() || matches!(located.action, Action::Borrow { .. }))
                        && !full[binding.0]
                    {
                        return Err(Error {
                            message: "projected access requires a definitely Full owning cell"
                                .into(),
                            span: located.span.unwrap_or(self.function.source.function.span),
                        });
                    }
                    let reads = matches!(
                        located.action,
                        Action::Load { .. } | Action::Release { .. } | Action::Borrow { .. }
                    );
                    let projection = !projections.is_empty()
                        && (!matches!(located.action, Action::Place { .. } | Action::Store { .. })
                            || self
                                .aggregate_field(descriptor)
                                .is_some_and(|field| projections.len() > field.path.len()));
                    let initialized = if let Some(field) = self.aggregate_field(descriptor) {
                        (!reads && !projection) || full[fields[&field.slot]]
                    } else if reads {
                        self.aggregates.get(binding).is_none_or(|aggregate| {
                            let path = self
                                .aggregate_subtree(descriptor)
                                .map(|(_, path)| path)
                                .unwrap_or_default();
                            aggregate
                                .fields
                                .iter()
                                .filter(|field| field.path.starts_with(&path))
                                .map(|field| field.slot)
                                .chain(
                                    aggregate
                                        .shells
                                        .iter()
                                        .filter(|shell| shell.path.starts_with(&path))
                                        .map(|shell| shell.slot),
                                )
                                .all(|slot| full[fields[&slot]])
                        })
                    } else {
                        true
                    };
                    if !initialized {
                        return Err(Error {
                            message: "projected access or reconstruction requires initialized field storage".into(),
                            span: located.span.unwrap_or(self.function.source.function.span),
                        });
                    }
                }
                transfer(located, &mut full);
            }
        }
        Ok(initialization)
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

    fn computed_owned_projection(&self, descriptor: &PlaceDescriptor) -> bool {
        let AddressRoot::Value(value) = descriptor.root else {
            return false;
        };
        !descriptor.projections.is_empty()
            && descriptor.projections.iter().all(|step| {
                matches!(
                    step,
                    AddressProjection::Field(_)
                        | AddressProjection::Tuple(_)
                        | AddressProjection::Index(_)
                )
            })
            && matches!(
                crate::typed_ir::resolve_type(
                    &self.function.graph.values[value.0].ty,
                    &self.planning.declarations.aliases,
                ),
                Ok(Type::Named(_) | Type::Tuple(_) | Type::Array(_, _))
            )
            && self
                .values
                .get(&value)
                .is_some_and(|slot| !self.slots[*slot].raw)
    }

    fn clone_computed_projection(
        &mut self,
        dst: ValueId,
        place: PlaceId,
        descriptor: &PlaceDescriptor,
    ) -> Result<String, Error> {
        let AddressRoot::Value(value) = descriptor.root else {
            return Err(fail(self.function, "computed clone lost its owning root"));
        };
        let mut ty = crate::typed_ir::resolve_type(
            &self.function.graph.values[value.0].ty,
            &self.planning.declarations.aliases,
        )
        .map_err(|message| fail(self.function, message))?;
        let owner_ty = crate::type_source(&ty);
        let argument = self.fresh("clone-owner-input");
        let helper = self.fresh("clone-owner-projection");
        let mut projected = format!("(#deref {argument})");
        let mut signature = vec![format!("({argument} (#pin-ref {owner_ty}))")];
        let mut indices = Vec::new();
        for (position, step) in descriptor.projections.iter().enumerate() {
            if let AddressProjection::Index(index) = step {
                let Type::Array(element, _) = ty else {
                    return Err(fail(
                        self.function,
                        "computed clone lost its checked array type",
                    ));
                };
                let parameter = self.fresh("clone-index");
                signature.push(format!("({parameter} #usize)"));
                let saved = self
                    .owned_indices
                    .get(&place)
                    .and_then(|indices| indices.iter().find(|saved| saved.projection == position));
                let value = if let Some(saved) = saved {
                    self.read(saved.slot, false)
                } else {
                    format!(
                        "{}usize",
                        self.literal_index(*index).ok_or_else(|| {
                            fail(
                                self.function,
                                "computed clone lost its checked index snapshot",
                            )
                        })?
                    )
                };
                indices.push(format!("({parameter} {value})"));
                projected = format!("(#index {projected} {parameter})");
                ty = crate::typed_ir::resolve_type(&element, &self.planning.declarations.aliases)
                    .map_err(|message| fail(self.function, message))?;
                continue;
            }
            let field = match step {
                AddressProjection::Field(id) => {
                    let declaration = self.planning.declarations.field(*id);
                    if self.planning.declarations.field_id(&ty, &declaration.name) != Some(*id) {
                        return Err(fail(
                            self.function,
                            "computed clone lost its checked field identity",
                        ));
                    }
                    ty = declaration.ty.clone();
                    declaration.name.clone()
                }
                AddressProjection::Tuple(index) => {
                    let Type::Tuple(fields) = ty else {
                        return Err(fail(
                            self.function,
                            "computed clone lost its checked tuple type",
                        ));
                    };
                    ty = fields.get(*index).cloned().ok_or_else(|| {
                        fail(self.function, "computed clone tuple index is out of bounds")
                    })?;
                    index.to_string()
                }
                _ => {
                    return Err(fail(
                        self.function,
                        "computed clone needs a fixed owning projection",
                    ))
                }
            };
            ty = crate::typed_ir::resolve_type(&ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?;
            projected = format!("(#get {projected} {field})");
        }
        let expected =
            crate::typed_ir::resolve_type(&descriptor.ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?;
        if ty != expected {
            return Err(fail(
                self.function,
                "computed clone disagrees with its checked leaf type",
            ));
        }
        let ty = crate::type_source(&ty);
        self.projections.push(format!(
            "(#fn {helper} ({}) {ty}\n  (#return (#clone {projected})))",
            signature.join(" ")
        ));
        let slot = &self.slots[self.values[&value]];
        let reference = self.payload_ref(slot, false);
        let retire = if !self.types.can_repeat(&slot.ty)
            && !self
                .physical_uses
                .retained_after_projected_clone(value, place, dst)
        {
            format!("(#forget {})", self.value(value, true))
        } else {
            String::new()
        };
        let cloned = self.fresh("cloned-projection");
        let mut arguments = vec![format!("({argument} {reference})")];
        arguments.extend(indices);
        Ok(self.put_value(
            dst,
            &format!(
                "(#block (#let {cloned} {ty} (#call {helper} ({})))\n  {retire}\n  {cloned})",
                arguments.join(" ")
            ),
        ))
    }

    fn action(
        &mut self,
        located: &crate::generator::async_exec::LocatedAction,
    ) -> Result<String, Error> {
        let graph = &self.function.graph;
        let error = |message: &str| Error {
            message: message.into(),
            span: located.span.unwrap_or(self.function.source.function.span),
        };
        match &located.action {
            Action::Load { dst, .. } if self.immediate.elides_load(*dst) => Ok(String::new()),
            Action::Compute { dst, operation } => {
                if self.immediate.get(*dst).is_some() {
                    // Materialize the certified slice only at its synchronous
                    // consumer. It has no physical frame cell to initialize.
                    return Ok(String::new());
                }
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
                    if self.immediate.get(id).is_some() {
                        let reference = self.immediate_reference(id)?;
                        inputs.insert(
                            id,
                            crate::parse(&reference)
                                .map_err(|_| error("immediate borrow expression did not parse"))?
                                .remove(0)
                                .expr,
                        );
                        continue;
                    }
                    let transfer = match self.leases.get(id) {
                        Some(lease) => {
                            assert_eq!(
                                lease.consumer,
                                crate::generator::async_lease::Consumer::Call,
                                "a leaf read lease cannot be a call operand"
                            );
                            false
                        }
                        None => true,
                    };
                    inputs.insert(
                        id,
                        crate::parse(&self.value(id, transfer))
                            .map_err(|_| error("stored value expression did not parse"))?
                            .remove(0)
                            .expr,
                    );
                }
                if let Compute::Checked(operation) = operation {
                    if operation.head == "borrow-slice" {
                        let text = self.slice_borrow(operation, &inputs)?;
                        return Ok(self.put_value(*dst, &text));
                    }
                    if matches!(operation.head.as_str(), "slice-mut-range" | "slice-mut-len") {
                        // The builtin reborrows an exclusive handle place,
                        // not a computed temporary. Name the already evaluated
                        // snapshot in an ordinary function parameter so its
                        // return-loan contract preserves the actual referent.
                        let helper = self.fresh("slice-range");
                        let argument = self.fresh("slice-range-input");
                        let start = self.fresh("slice-range-start");
                        let end = self.fresh("slice-range-end");
                        let base = operation
                            .operands
                            .iter()
                            .find(|operand| operand.position == [1])
                            .ok_or_else(|| error("slice operation lost its checked holder"))?
                            .value;
                        let slot = &self.slots[*self.values.get(&base).ok_or_else(|| {
                            error("slice operation requires a retained checked holder")
                        })?];
                        let holder = format!(
                            "(#pin-get-payload-mut {} {} 0)",
                            Self::slot_ref(slot, true),
                            slot.full
                        );
                        let ty = crate::type_source(&slot.ty);
                        if operation.head == "slice-mut-len" {
                            self.projections.push(format!("(#fn {helper} (: {argument} (#pin-ref-mut {ty})) #usize (#return (#slice-mut-len (#deref {argument}))))"));
                            return Ok(self.put_value(
                                *dst,
                                &format!("(#call {helper} (: {argument} {holder}))"),
                            ));
                        }
                        self.projections.push(format!("(#fn {helper} (: {argument} (#pin-ref-mut {ty}) : {start} #usize : {end} #usize) {ty} (#return (#slice-mut-range (#deref {argument}) {start} {end})))"));
                        let operand = |position| -> Result<String, Error> {
                            let value = operation
                                .operands
                                .iter()
                                .find(|operand| operand.position == [position])
                                .ok_or_else(|| error("slice range lost a checked operand"))?
                                .value;
                            crate::expression_source(&inputs[&value])
                                .map_err(|_| error("slice range operand did not serialize"))
                        };
                        let text = format!(
                            "(#call {helper} (: {argument} {holder} : {start} {} : {end} {}))",
                            operand(2)?,
                            operand(3)?
                        );
                        return Ok(self.put_value(*dst, &text));
                    }
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
            Action::Place { dst, descriptor } => {
                if self.owned_indices.contains_key(dst) {
                    return self.select_owned_indices(*dst, descriptor);
                }
                if self.addresses.contains_key(dst) {
                    return self.select_address(*dst, descriptor);
                }
                let static_owned = self.static_owned_projection(descriptor);
                let simple_owned = static_owned
                    || (matches!(descriptor.root, AddressRoot::Local(_))
                        && descriptor.projections.iter().all(|projection| {
                            matches!(
                                projection,
                                AddressProjection::Field(_) | AddressProjection::Tuple(_)
                            )
                        }));
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
                let computed_value = (matches!(descriptor.root, AddressRoot::Value(_))
                    && descriptor.projections.is_empty())
                    || self.computed_owned_projection(descriptor);
                let global_value = matches!(descriptor.root, AddressRoot::Global(_))
                    && descriptor.projections.iter().all(|projection| {
                        matches!(
                            projection,
                            AddressProjection::Field(_) | AddressProjection::Tuple(_)
                        )
                    });
                if (!simple_owned && !simple_handle && !computed_value && !global_value)
                    || (!descriptor.checks().is_empty() && !static_owned)
                {
                    return Err(error(
                        "projected addresses need checked storage and immediate place checks",
                    ));
                }
                Ok(String::new())
            }
            Action::Load { dst, .. } if self.leases.handle_leaf(*dst).is_some() => {
                Ok(String::new())
            }
            Action::Load { dst, place, kind } => {
                let descriptor = &graph.places[place.0];
                if let AddressRoot::Global(global) = descriptor.root {
                    if !descriptor.projections.is_empty() || !self.types.can_repeat(&descriptor.ty)
                    {
                        return Err(error("global loads require a whole Copy value"));
                    }
                    let mut read = self
                        .planning
                        .declarations
                        .declaration_name(crate::typed_ir::DeclarationId::Global(global))
                        .to_owned();
                    if *kind == LoadKind::Clone {
                        read = self.clone_read(&descriptor.ty, &read);
                    }
                    if located.unsafe_context {
                        read = format!("(#unsafe {read})");
                    }
                    return Ok(self.put_value(*dst, &read));
                }
                if let AddressRoot::Value(value) = descriptor.root {
                    if *kind == LoadKind::Clone && self.computed_owned_projection(descriptor) {
                        return self.clone_computed_projection(*dst, *place, descriptor);
                    }
                    if descriptor.projections.is_empty() {
                        if !self.types.can_repeat(&descriptor.ty) {
                            if *kind == LoadKind::Clone {
                                let used_elsewhere =
                                    self.physical_uses.retained_after_clone(value, *place, *dst);
                                let index = *self.values.get(&value).ok_or_else(|| {
                                    error("computed clone source has no owning cell")
                                })?;
                                let slot = &self.slots[index];
                                if slot.raw {
                                    return Err(error(
                                        "computed clone requires typed owning storage",
                                    ));
                                }
                                let reference = self.payload_ref(slot, false);
                                let helper = self.fresh("clone-computed");
                                let argument = self.fresh("clone-input");
                                let ty = crate::type_source(&descriptor.ty);
                                // Clone from the existing stationary cell.
                                // Reference-bearing clones retain their checked
                                // origins through the typed helper. Preserve a
                                // reused original; consume only sole-use inputs
                                // so a loop can refill their cells.
                                self.projections.push(format!(
                                    "(#fn {helper} (: {argument} (#pin-ref {ty})) {ty}\n  (#return (#clone (#deref {argument}))))"
                                ));
                                let cloned = self.fresh("cloned-temporary");
                                let retire = if used_elsewhere {
                                    String::new()
                                } else {
                                    format!("(#forget {})", self.value(value, true))
                                };
                                let read = format!("(#block (#let {cloned} {ty}\n  (#call {helper} (: {argument} {reference})))\n  {retire}\n  {cloned})");
                                return Ok(self.put_value(*dst, &read));
                            }
                            return Err(error(
                                "computed owning value loads require explicit lending storage",
                            ));
                        }
                        let read = self.value(value, false);
                        let read = if *kind == LoadKind::Clone {
                            self.clone_read(&descriptor.ty, &read)
                        } else {
                            read
                        };
                        return Ok(self.put_value(*dst, &read));
                    }
                }
                if self.addresses.contains_key(place) {
                    if !self.types.can_repeat(&descriptor.ty)
                        || self.types.contains_reference(&descriptor.ty)
                    {
                        return Err(error("selected loads require Copy reference-free leaves"));
                    }
                    let read = format!("(#deref {})", self.selected_reference(*place));
                    let read = if *kind == LoadKind::Clone {
                        self.clone_read(&descriptor.ty, &read)
                    } else {
                        read
                    };
                    return Ok(self.put_value(*dst, &read));
                }
                if matches!(descriptor.root, AddressRoot::Value(_)) {
                    let read = self.handle_leaf_read(descriptor)?;
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
                    if let Some((aggregate, path)) = self.aggregate_subtree(descriptor) {
                        if *kind == LoadKind::Clone {
                            let read = self.clone_aggregate(binding, &path)?;
                            return Ok(self.put_value(*dst, &read));
                        }
                        if matches!(
                            located
                                .source
                                .and_then(|source| self.lending.as_ref()?.access(source)),
                            Some(crate::generator::async_lend::Access::Lend(_))
                        ) {
                            return Err(error(
                                "whole aggregate lending requires contiguous owning storage",
                            ));
                        }
                        let read = self.read_aggregate(
                            aggregate,
                            &path,
                            !self.types.can_repeat(&descriptor.ty),
                        );
                        return Ok(self.put_value(*dst, &read));
                    }
                    if self.leases.get(*dst).is_some() {
                        self.owned_projection_address(*place, true)?;
                        return Ok(String::new());
                    }
                    if self.leases.projected_snapshot(*dst) == Some(*place) {
                        // Lend the stored handle at its original evaluation
                        // point. The child value cell holds this actual checked
                        // reborrow through later effects and Pending edges.
                        let mut read = self.owned_projection_address(*place, true)?.0;
                        if self.is_word_place(*place) {
                            read = format!("(#deref {read})");
                        }
                        let slot = &self.slots[self.values[dst]];
                        let reborrow =
                            format!("(#call {} (: {} {read}))", slot.lend, slot.lend_argument);
                        return Ok(self.put_value(*dst, &reborrow));
                    }
                    {
                        if let Some(field) = self.aggregate_exact_field(descriptor) {
                            let index = field.slot;
                            let read = match kind {
                                LoadKind::Read => self.read(index, !self.slots[index].copy),
                                LoadKind::Clone => {
                                    let slot = &self.slots[index];
                                    let ty = crate::type_source(&slot.ty);
                                    let input = self.fresh("aggregate-clone-input");
                                    let helper = self.fresh("aggregate-clone");
                                    let reference = self.payload_ref(slot, false);
                                    self.projections.push(format!("(#fn {helper} (: {input} (#pin-ref {ty})) {ty} (#return (#clone (#deref {input}))))"));
                                    format!("(#call {helper} (: {input} {reference}))")
                                }
                            };
                            return Ok(self.put_value(*dst, &read));
                        }
                    }
                    let read = self.owned_projection_read(*place)?;
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
                if self.aggregates.contains_key(&binding)
                    && !self.active_preview_aliases.contains(&binding)
                {
                    if *kind == LoadKind::Clone {
                        let read = self.clone_aggregate(binding, &[])?;
                        return Ok(self.put_value(*dst, &read));
                    }
                    let transfer = !self.types.can_repeat(&graph.bindings[binding.0].ty);
                    return Ok(self.put_value(*dst, &self.read_binding(binding, transfer)));
                }
                if self.slots[*slot].raw {
                    if self.leases.get(*dst).is_some() {
                        return Ok(String::new());
                    }
                    let transfer = located
                        .source
                        .and_then(|source| self.lending.as_ref()?.access(source))
                        .is_some_and(|access| {
                            matches!(access, crate::generator::async_lend::Access::Move(_))
                        });
                    return Ok(self.put_value(*dst, &self.read(*slot, transfer)));
                }
                if *kind == LoadKind::Read
                    && !self.slots[*slot].copy
                    && self.types.contains_reference(&self.slots[*slot].ty)
                {
                    let access = located.source.and_then(|source| {
                        self.lending.as_ref().and_then(|plan| plan.access(source))
                    });
                    match access {
                        Some(crate::generator::async_lend::Access::Move(place))
                            if place
                                == &crate::typed_place::Place::root(
                                    crate::typed_body::PlaceRoot::Local(binding),
                                ) => {}
                        Some(crate::generator::async_lend::Access::Lend(_)) => {
                            if self
                                .leases
                                .get(*dst)
                                .is_some_and(|lease| lease.binding == binding)
                            {
                                return Ok(String::new());
                            }
                            if self.leases.snapshot(*dst) == Some(binding) {
                                let slot = &self.slots[*slot];
                                let holder = format!(
                                    "(#pin-get-payload-mut {} {} 0)",
                                    Self::slot_ref(slot, true),
                                    slot.full
                                );
                                let input = if matches!(
                                    crate::typed_ir::resolve_type(
                                        &slot.ty,
                                        &self.planning.declarations.aliases
                                    ),
                                    Ok(Type::MutableSlice(_))
                                ) {
                                    holder
                                } else {
                                    format!("(#deref {holder})")
                                };
                                let reborrow = format!(
                                    "(#call {} (: {} {input}))",
                                    slot.lend, slot.lend_argument,
                                );
                                return Ok(self.put_value(*dst, &reborrow));
                            }
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
                    LoadKind::Clone => {
                        // Keep the original owner in its stationary cell.
                        // A typed shared projection lets ordinary clone-hook
                        // checking retain pointee origins in both owners.
                        let slot = &self.slots[*slot];
                        let reference = self.payload_ref(slot, false);
                        let ty = crate::type_source(&slot.ty);
                        let helper = self.fresh("clone-owner");
                        let argument = self.fresh("clone-owner-input");
                        self.projections.push(format!(
                            "(#fn {helper} (: {argument} (#pin-ref {ty})) {ty}\n  (#return (#clone (#deref {argument}))))"
                        ));
                        format!("(#call {helper} (: {argument} {reference}))")
                    }
                };
                Ok(self.put_value(*dst, &read))
            }
            Action::Bind { binding, value, .. } => {
                let mut guards = self
                    .addresses
                    .iter()
                    .filter_map(|(place, index)| {
                        if graph.places[place.0].root == AddressRoot::Local(*binding) {
                            let slot = &self.slots[*index];
                            Some((
                                place.0,
                                format!(
                                    "(#assert (#variant-is {} {}))",
                                    Self::slot_ref(slot, false),
                                    slot.empty
                                ),
                            ))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                guards.sort_by_key(|(place, _)| *place);
                let store = self.put_binding(*binding, &self.value(*value, true));
                Ok(format!(
                    "{}\n{store}",
                    guards
                        .into_iter()
                        .map(|(_, guard)| guard)
                        .collect::<Vec<_>>()
                        .join("\n")
                ))
            }
            Action::Store { place, value } => {
                let descriptor = &graph.places[place.0];
                if self.addresses.contains_key(place) {
                    if !self.types.can_repeat(&descriptor.ty)
                        || self.types.contains_reference(&descriptor.ty)
                    {
                        return Err(error("selected writes require Copy reference-free leaves"));
                    }
                    let reference = self.selected_reference(*place);
                    let value = self.value(*value, true);
                    if self.is_word_place(*place) {
                        let incoming = self.fresh("selected-word-value");
                        let target = self.fresh("selected-word-target");
                        let words = self.fresh("selected-word-slice");
                        let ty = crate::type_source(&descriptor.ty);
                        return Ok(format!(
                            "(#block (#let {incoming} {ty} {value})
                          (#let {target} (#pin-ref-mut {ty}) {reference})
                          (#let {words} (#slice-mut #u64)
                            (#unsafe (#word-view (#slice-mut #u64) {target})))
                          (#unsafe (#word-write {ty} {words} {incoming})))"
                        ));
                    }
                    return Ok(
                        if matches!(
                            self.slots[self.addresses[place]].ty,
                            Type::PinnedReference { .. }
                        ) {
                            format!("(#unsafe (#pin-write {reference} {value}))")
                        } else {
                            format!("(#deref-set {reference} {value})")
                        },
                    );
                }
                if matches!(descriptor.root, AddressRoot::Value(_)) {
                    return self
                        .write_through_handle(descriptor, *value)
                        .map_err(|failure| Error {
                            message: failure.message,
                            span: located.span.unwrap_or(self.function.source.function.span),
                        });
                }
                let AddressRoot::Local(binding) = descriptor.root else {
                    return Err(error(
                        "nonlocal stores need their checked address representation",
                    ));
                };
                if !descriptor.projections.is_empty() {
                    if let Some((aggregate, path)) = self.aggregate_subtree(descriptor) {
                        return Ok(self.put_aggregate(aggregate, &path, &self.value(*value, true)));
                    }
                    if let Some(field) = self.aggregate_exact_field(descriptor) {
                        return Ok(self.put(field.slot, &self.value(*value, true)));
                    }
                    if let Some((slice, ty)) = self.word_owned_slice(*place, true)? {
                        let value = self.value(*value, true);
                        if ty == Type::Unit {
                            return Ok(value);
                        }
                        let incoming = self.fresh("projected-word-value");
                        let ty = crate::type_source(&ty);
                        return Ok(format!(
                            "(#block (#let {incoming} {ty} {value})
                            (#unsafe (#word-write {ty} {slice} {incoming})))"
                        ));
                    }
                    let (target, ty) = self.owned_projection_place(*place, true)?;
                    let value = self.value(*value, true);
                    return Ok(if ty == Type::Unit {
                        value
                    } else {
                        // Only Copy, reference-free leaves reach this point.
                        // No owner or borrowed handle is moved or captured.
                        let reference = if self.is_word_place(*place) {
                            target
                        } else {
                            format!("(#pin-borrow-mut {target})")
                        };
                        format!("(#unsafe (#pin-write {reference} {value}))")
                    });
                }
                Ok(self.put_binding(binding, &self.value(*value, true)))
            }
            Action::Release { place, kind } => {
                let descriptor = &graph.places[place.0];
                let AddressRoot::Local(binding) = descriptor.root else {
                    return Err(error(
                        "nonlocal releases need their checked address representation",
                    ));
                };
                if self.types.can_repeat(&descriptor.ty)
                    && !self.types.contains_reference(&descriptor.ty)
                {
                    // Ordinary release of reference-free Copy data discards
                    // a copy, not the source place. Still perform the read:
                    // projected/indexed access retains its evaluation/checks.
                    let value = if descriptor.projections.is_empty() {
                        self.read_binding(binding, false)
                    } else if let Some((aggregate, path)) = self.aggregate_subtree(descriptor) {
                        self.read_aggregate(aggregate, &path, false)
                    } else if let Some(field) = self.aggregate_exact_field(descriptor) {
                        self.read(field.slot, false)
                    } else {
                        if self.is_word_place(*place) {
                            self.owned_projection_read(*place)?
                        } else {
                            self.owned_projection_place(*place, false)?.0
                        }
                    };
                    return Ok(format!(
                        "(#{} {value})",
                        if *kind == ReleaseKind::Drop {
                            "drop"
                        } else {
                            "forget"
                        }
                    ));
                }
                if !descriptor.projections.is_empty() {
                    if let Some((aggregate, path)) = self.aggregate_subtree(descriptor) {
                        return Ok(format!(
                            "(#{} {})",
                            if *kind == ReleaseKind::Drop {
                                "drop"
                            } else {
                                "forget"
                            },
                            self.read_aggregate(aggregate, &path, true)
                        ));
                    }
                    {
                        if let Some(field) = self.aggregate_exact_field(descriptor) {
                            let slot = &self.slots[field.slot];
                            if slot.copy && self.types.contains_reference(&slot.ty) {
                                self.occupancy_write(field.slot, false);
                                if slot.words.is_some() {
                                    return Ok(String::new());
                                }
                                return Ok(format!(
                                    "(#call {} (: slot {}))",
                                    slot.clear,
                                    Self::slot_ref(slot, true)
                                ));
                            }
                            return Ok(format!(
                                "(#{} {})",
                                if *kind == ReleaseKind::Drop {
                                    "drop"
                                } else {
                                    "forget"
                                },
                                self.read(field.slot, true)
                            ));
                        }
                    }
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
                if *kind == ReleaseKind::Forget {
                    if let Some(&index) = self.bindings.get(&binding) {
                        if let Some(region) = &self.slots[index].words {
                            // A checked explicit whole-owner discard has no
                            // payload read. Retire its retained loans directly;
                            // projected releases keep their leaf-aware path.
                            self.occupancy_write(index, false);
                            return Ok(self.forget_word_region(region));
                        }
                    }
                }
                let value = self.read_binding(binding, true);
                Ok(format!(
                    "(#{} {value})",
                    match kind {
                        ReleaseKind::Drop => "drop",
                        ReleaseKind::Forget => "forget",
                    }
                ))
            }
            Action::ScopeEnter(_) => Ok(String::new()),
            Action::ScopeExit(bindings) => self.clear_scope(bindings),
            Action::Borrow { dst: Some(dst), .. } if self.immediate.get(*dst).is_some() => {
                Ok(String::new())
            }
            Action::Borrow {
                dst: Some(dst),
                place,
                mutable,
                pinned,
                scope: None,
            } if !self.addresses.contains_key(place) => self
                .reborrow_from_handle(*dst, *place, *mutable, *pinned)
                .map_err(|failure| Error {
                    message: failure.message,
                    span: located.span.unwrap_or(self.function.source.function.span),
                }),
            Action::Borrow {
                dst: Some(dst),
                place,
                mutable,
                pinned,
                scope: None,
            } if self.addresses.contains_key(place) => {
                let expected = if *pinned {
                    Type::PinnedReference {
                        mutable: *mutable,
                        target: Box::new(graph.places[place.0].ty.clone()),
                    }
                } else {
                    Type::Reference {
                        mutable: *mutable,
                        target: Box::new(graph.places[place.0].ty.clone()),
                    }
                };
                let address = self.addresses[place];
                if self.slots[address].ty != expected {
                    // A pinned frame's checked array selection is retained as
                    // a pinned address. The source requested an ordinary loan,
                    // not a pin: preserve that exact capability while anchoring
                    // the emitted loan to the selected storage. Never upgrade
                    // ordinary storage to pinned or change exclusivity here.
                    if matches!((&self.slots[address].ty, &expected),
                        (Type::PinnedReference { mutable: actual, target: from },
                         Type::Reference { mutable: requested, target: to })
                        if actual == requested && from == to)
                    {
                        let helper = self.fresh("selected-source-borrow");
                        let input = self.fresh("selected-source-input");
                        self.projections.push(format!(
                            "(#fn {helper} (: {input} {}) {} (#return (#unsafe (#ptr-borrow{} {input} (#ref-ptr {input})))))",
                            crate::type_source(&self.slots[address].ty), crate::type_source(&expected),
                            if *mutable { "-mut" } else { "" },
                        ));
                        let read = self.read(address, true);
                        return Ok(
                            self.put_value(*dst, &format!("(#call {helper} (: {input} {read}))"))
                        );
                    }
                    return Err(error(
                        "selected borrow cannot change its checked pinning or exclusivity",
                    ));
                }
                let read = self.read(self.addresses[place], true);
                Ok(self.put_value(*dst, &read))
            }
            Action::Borrow {
                dst: None,
                scope: Some(scope),
                place,
                mutable,
                pinned,
            } => {
                let slot = self.scopes[scope];
                if self.addresses.contains_key(place) {
                    let address = self.addresses[place];
                    if self.slots[address].ty != self.slots[slot].ty {
                        return Err(error(
                            "scoped selection cannot change checked reference capabilities",
                        ));
                    }
                    Ok(self.put(slot, &self.read(address, true)))
                } else {
                    self.reborrow_to_slot(slot, *place, *mutable, *pinned)
                        .map_err(|failure| Error {
                            message: failure.message,
                            span: located.span.unwrap_or(self.function.source.function.span),
                        })
                }
            }
            Action::EndBorrow { scope } => Ok(self.clear_handle_slots(&[self.scopes[scope]])),
            Action::Borrow { .. } => Err(error(
                "borrow/address tokens must retain their checked lifetime and ownership mode",
            )),
            Action::Preview(pattern) => self.pattern_bind(pattern, false),
            Action::Commit(pattern) => {
                for binding in &pattern.bindings {
                    self.active_preview_aliases.remove(binding);
                }
                self.pattern_bind(pattern, true)
            }
            Action::EndPreview(pattern) => {
                let result = pattern
                    .bindings
                    .iter()
                    .map(|binding| self.clear_binding(*binding))
                    .collect::<Vec<_>>()
                    .join("\n");
                for binding in &pattern.bindings {
                    self.active_preview_aliases.remove(binding);
                }
                Ok(result)
            }
        }
    }

    fn slice_borrow(
        &mut self,
        operation: &crate::generator::async_exec::Operation,
        inputs: &HashMap<ValueId, Expr>,
    ) -> Result<String, Error> {
        let error = |message| Error {
            message,
            span: self.body.nodes[operation.source.0]
                .span
                .unwrap_or(self.function.source.function.span),
        };
        let operand = operation
            .operands
            .iter()
            .find(|operand| operand.position == [1])
            .ok_or_else(|| error("slice borrow has no checked storage operand".into()))?;
        let place = self
            .function
            .graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match action.action {
                Action::Load { dst, place, .. } if dst == operand.value => Some(place),
                _ => None,
            })
            .ok_or_else(|| error("slice borrowing requires checked array storage".into()))?;
        let descriptor = &self.function.graph.places[place.0];
        if self.types.requires_move(&descriptor.ty) {
            return Err(error(
                "non-Copy array slice borrowing needs a nonmoving storage lease".into(),
            ));
        }
        if self.pinned
            || !matches!(descriptor.root, AddressRoot::Local(_))
            || !descriptor.projections.iter().all(|projection| {
                matches!(
                    projection,
                    AddressProjection::Field(_) | AddressProjection::Tuple(_)
                )
            })
        {
            return Err(error(
                "slice borrowing needs an ordinary static local storage projection".into(),
            ));
        }
        let owner = crate::generator::async_owner::Borrow::new(
            &self.function.graph,
            descriptor,
            &self.planning.declarations,
            false,
            false,
            true,
        )
        .map_err(error)?;
        let reference = if self.is_word_place(place) {
            self.aggregate_borrow(place, false, false)?
        } else {
            let slot = &self.slots[self.bindings[&owner.binding]];
            let helper = self.fresh("immediate-owner-project-slice");
            let argument = self.fresh("slice-owner-input");
            self.projections.push(
                owner.declaration_from_unpinned_slot(&helper, &argument, &slot.name, &slot.full),
            );
            format!(
                "(#call {helper} (: {argument} (#borrow (#get task {}))))",
                slot.field
            )
        };
        let slice = format!("(#slice-of {reference})");
        if operation.operands.len() == 1 {
            return Ok(slice);
        }
        let bound = |position| -> Result<String, Error> {
            let operand = operation
                .operands
                .iter()
                .find(|operand| operand.position == [position])
                .ok_or_else(|| error("slice borrow has an incomplete checked bound".into()))?;
            crate::expression_source(&inputs[&operand.value]).map_err(error)
        };
        Ok(format!(
            "(#slice-range {slice} {} {})",
            bound(2)?,
            bound(3)?
        ))
    }

    fn edge(
        &mut self,
        block: BlockId,
        index: usize,
        edge: &Edge,
        ready: Option<&str>,
    ) -> Result<String, Error> {
        let fork = self.occupancy_fork();
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
            stores.push((*parameter, name));
        }
        let retired = self.retire_edge(block, index);
        let stores = stores
            .into_iter()
            .map(|(parameter, name)| self.put_value(parameter, &name))
            .collect::<Vec<_>>();
        self.occupancy_edge(index, fork);
        Ok(format!(
            "{}\n{}\n{}\n{}\n(#continue)",
            stages.join("\n"),
            retired,
            stores.join("\n"),
            self.set_pc(self.successor_pc(index)?)
        ))
    }

    fn set_pc(&self, pc: u32) -> String {
        format!(
            "(#{}set-field task pc {pc}u32)",
            if self.pinned { "pin-" } else { "" }
        )
    }

    fn successor_pc(&self, edge: usize) -> Result<u32, Error> {
        // Trace-only rendering has no specialized dispatcher yet. These PCs
        // are discarded; ordinary production emission still requires a plan.
        if self.initialization.is_none() && self.occupancy_trace.borrow().is_some() {
            let target = self.function.graph.successors(BlockId(self.current_state))[edge];
            return u32::try_from(target.0)
                .map_err(|_| fail(self.function, "async state exceeds #u32 range"));
        }
        let target = self
            .initialization
            .as_ref()
            .and_then(|plan| plan.states.get(self.current_state))
            .and_then(|state| state.successors.get(edge))
            .ok_or_else(|| fail(self.function, "missing specialized async successor"))?;
        u32::try_from(*target).map_err(|_| fail(self.function, "async state exceeds #u32 range"))
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
                pending: _,
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
                let edge = self.edge(block, 0, ready, Some(&result))?;
                let fork = self.occupancy_fork();
                let store = self.put_value(*child, &next);
                let retired = self.retire_edge(block, 1);
                let bindings = self.retirement.as_ref().map_or_else(Vec::new, |plan| {
                    plan.pending_bindings[block.0]
                        .iter()
                        .filter_map(|binding| self.bindings.get(binding).copied())
                        .collect::<Vec<_>>()
                });
                let retired_bindings = self.clear_handle_slots(&bindings);
                let empty = self.expose_empty_reference_cells(block, false);
                self.occupancy_edge(1, fork);
                // A movable graph frame has no retained self-loans. Internal
                // field pinning is retired by explicit unsafe extraction;
                // forgetting a temporary pin must not authorize a safe move.
                let pending_task = if self.pinned {
                    "task"
                } else {
                    "(#unsafe (#pin-read (#pin-borrow-mut task)))"
                };
                Ok(format!("(#let {polled} {} {call})\n\
                  (#match {polled}\n\
                    (#case ({} {next}) (#block {store} {retired} {retired_bindings} {empty} {} (#return ({} {pending_task})) (#unreachable)))\n\
                    (#case ({} {result}) (#block {edge} (#unreachable))))", crate::type_source(poll_type), protocol.pending, self.set_pc(self.successor_pc(1)?), self.pending, protocol.ready))
            }
            Terminator::Return(value) => {
                let value = value.map_or_else(|| "()".into(), |value| self.value(value, true));
                let name = self.fresh("result");
                let empty = self.expose_empty_reference_cells(block, true);
                let finish = self.finish.clone();
                let complete = if self.pinned {
                    let refs = self.reference_slots();
                    let clear = self.clear_handle_slots(&refs);
                    let owners = self
                        .slots
                        .iter()
                        .filter(|slot| slot.linear && slot.words.is_none())
                        .map(|slot| {
                            format!(
                                "(#assert (#variant-is {} {}))",
                                Self::slot_ref(slot, false),
                                slot.empty
                            )
                        })
                        .collect::<Vec<_>>()
                        .join("\n");
                    format!("{clear}\n{owners}\n{}", self.set_pc(u32::MAX))
                } else {
                    format!(
                        "(#call {finish} (: task (#unsafe (#pin-read (#pin-borrow-mut task)))))"
                    )
                };
                Ok(format!(
                    "(#let {name} {} {value})\n{empty}\n{complete}\n(#return ({} {name}))",
                    crate::type_source(&self.result),
                    self.ready
                ))
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
                    let reference = self.payload_ref(slot, false);
                    let reference = crate::parse(&reference)
                        .map_err(|error| fail(self.function, error.to_string()))?
                        .remove(0)
                        .expr;
                    let source = crate::parse(&source)
                        .map_err(|error| fail(self.function, error.to_string()))?
                        .remove(0)
                        .expr;
                    let prefix = self.fresh("pattern-inspect");
                    let test = crate::generator::async_pattern::test(
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

    fn reference_slots(&self) -> Vec<usize> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(index, slot)| {
                (!slot.linear && self.types.contains_reference(&slot.ty)).then_some(index)
            })
            .collect()
    }

    fn cleanup_occupied(&self) -> &HashSet<usize> {
        // The graph, transfer plans, and slot mapping are fixed after new.
        // Private cancellation and public cleanup need the same owner-inclusive
        // result; the reference-only Pending plan cannot substitute for it.
        self.cleanup_occupied_cache
            .get_or_init(|| self.compute_cleanup_occupied())
    }

    fn cancellation_states(&self) -> Vec<usize> {
        let plan = self
            .initialization
            .as_ref()
            .expect("async cancellation requires a dispatcher plan");
        let mut states = vec![0];
        states.extend(plan.states.iter().filter_map(|state| {
            matches!(
                self.function.graph.blocks[state.block].terminator,
                Terminator::Await { .. }
            )
            .then(|| state.successors[1])
        }));
        states.sort_unstable();
        states.dedup();
        states
    }

    fn compute_cleanup_occupied(&self) -> HashSet<usize> {
        let _timing = crate::timing::detail("generator.async.cancellation_cells");
        if let Some(plan) = &self.initialization {
            // Cancellation is possible at construction and after Pending,
            // not at arbitrary internal dispatcher instructions. Use the
            // actual cell effects, including retirement and partial moves.
            let physical_start = plan.states[0].before.len() - self.slots.len();
            let mut occupied = HashSet::new();
            for state in self.cancellation_states() {
                for (cell, slot) in self.slots.iter().enumerate() {
                    if plan.states[state].before[physical_start + cell]
                        && (slot.linear || self.types.contains_reference(&slot.ty))
                    {
                        occupied.insert(cell);
                    }
                }
            }
            return occupied;
        }
        // Keep the former union solver only as an independent test oracle.
        // Production cleanup must use the plan that determines the emitted PC.
        #[cfg(not(test))]
        panic!("async cleanup requires specialized physical initialization");
        #[cfg(test)]
        self.legacy_cleanup_occupied()
    }

    #[cfg(test)]
    fn legacy_cleanup_occupied(&self) -> HashSet<usize> {
        use crate::generator::async_cells::Cell;
        crate::generator::async_cells::Plan::cancellation(
            &self.function.graph,
            self.types,
            self.retirement.as_ref(),
            self.lending.as_ref(),
        )
        .iter()
        .flat_map(|plan| &plan.cancel_live)
        .filter_map(|cell| match cell {
            Cell::Binding(binding) => Some(self.aggregates.get(binding).map_or_else(
                || {
                    self.bindings
                        .get(binding)
                        .copied()
                        .into_iter()
                        .collect::<Vec<_>>()
                },
                |aggregate| aggregate.cells().collect(),
            )),
            Cell::Value(value) => self.values.get(value).map(|slot| vec![*slot]),
            Cell::Scope(scope) => self.scopes.get(scope).map(|slot| vec![*slot]),
        })
        .flatten()
        .collect()
    }

    fn cleanup_names(&self, occupied: &HashSet<usize>) -> Result<HashMap<usize, String>, Error> {
        fn visit<'b>(node: &'b crate::SpannedExpr, output: &mut Vec<&'b crate::SpannedExpr>) {
            output.push(node);
            for child in &node.children {
                visit(child, output);
            }
        }
        let mut expressions = Vec::new();
        for statement in self.function.source.function.children.iter().skip(4) {
            visit(statement, &mut expressions);
        }
        let mut used = HashSet::new();
        let mut names = HashMap::new();
        for (index, _) in self
            .slots
            .iter()
            .enumerate()
            .filter(|(index, slot)| slot.linear && occupied.contains(index))
        {
            let aggregate_field = self.aggregates.iter().find_map(|(binding, aggregate)| {
                aggregate
                    .fields
                    .iter()
                    .find(|field| field.slot == index)
                    .map(|field| {
                        format!(
                            "{}.{}",
                            self.function.graph.bindings[binding.0].name, field.name
                        )
                    })
                    .or_else(|| {
                        aggregate
                            .shells
                            .iter()
                            .find(|shell| shell.slot == index)
                            .map(|shell| {
                                format!(
                                    "{}.{}",
                                    self.function.graph.bindings[binding.0].name, shell.name
                                )
                            })
                    })
            });
            let name = if let Some(field) = aggregate_field {
                field
            } else if let Some((binding, _)) =
                self.bindings.iter().find(|(_, actual)| **actual == index)
            {
                self.function.graph.bindings[binding.0].name.clone()
            } else if let Some((value, _)) =
                self.values.iter().find(|(_, actual)| **actual == index)
            {
                if let Some(site) = self
                    .function
                    .graph
                    .blocks
                    .iter()
                    .find_map(|block| match block.terminator {
                        Terminator::Await { site, child, .. } if child == *value => Some(site),
                        _ => None,
                    })
                {
                    format!("await-{site}")
                } else {
                    let span = self.function.graph.values[value.0].span.ok_or_else(|| {
                        fail(
                            self.function,
                            "owned cancellation temporary has no source identity",
                        )
                    })?;
                    let ordinal = expressions.iter().position(|expression| expression.span == span).ok_or_else(|| fail(self.function, "owned cancellation temporary has no original source-expression identity"))?;
                    format!("source-expression-{ordinal}")
                }
            } else {
                return Err(fail(
                    self.function,
                    "owned cancellation address has no source identity",
                ));
            };
            let mut field = name.clone();
            let mut occurrence = 1;
            while !used.insert(field.clone()) {
                occurrence += 1;
                field = format!("{name}.{occurrence}");
            }
            names.insert(index, field);
        }
        Ok(names)
    }

    fn cancellation_handlers(&self) -> Result<HashMap<String, String>, Error> {
        let Some(Expr::List(config)) = &self.function.cancel else {
            if self.function.cancel.is_some() {
                return Err(fail(self.function, "invalid graph cleanup configuration"));
            }
            return Ok(HashMap::new());
        };
        let [Expr::Symbol(_), Expr::List(entries)] = config.as_slice() else {
            return Err(fail(
                self.function,
                "graph cleanup requires (function ((source-slot handler) ...))",
            ));
        };
        let mut handlers = HashMap::new();
        for entry in entries {
            let Expr::List(entry) = entry else {
                return Err(fail(self.function, "invalid graph cleanup handler"));
            };
            let [Expr::Symbol(slot), Expr::Symbol(handler)] = entry.as_slice() else {
                return Err(fail(
                    self.function,
                    "graph cleanup handler requires (source-slot handler)",
                ));
            };
            if handlers.insert(slot.clone(), handler.clone()).is_some() {
                return Err(fail(
                    self.function,
                    format!("duplicate graph cleanup slot '{slot}'"),
                ));
            }
        }
        Ok(handlers)
    }

    fn stationary_child(&self, slot: &Slot) -> bool {
        let ty = crate::typed_ir::resolve_type(&slot.ty, &self.planning.declarations.aliases)
            .unwrap_or_else(|_| slot.ty.clone());
        self.planning.interfaces.functions.values().any(|interface|
            interface.provenance == crate::generator::async_interfaces::Provenance::AsyncPoll
                && matches!(interface.declaration.parameters.first().map(|parameter| &parameter.ty),
                    Some(Type::PinnedReference { target, .. }) if target.as_ref() == &ty))
    }

    fn cancels_in_place(&self, slot: &Slot) -> bool {
        !slot.dependencies.is_empty() || (self.pinned && self.stationary_child(slot))
    }

    /// Cancel dependent values before extracting any referent. Cleanup and
    /// configured destruction share this sequence and cannot export a dangling child.
    fn in_place_cleanup(&self) -> Result<String, Error> {
        let occupied = self.cleanup_occupied();
        let names = self.cleanup_names(occupied)?;
        let handlers = self.cancellation_handlers()?;
        let mut dependent = self
            .slots
            .iter()
            .enumerate()
            .filter(|(index, slot)| {
                slot.linear && self.cancels_in_place(slot) && occupied.contains(index)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let mut order = Vec::new();
        while !dependent.is_empty() {
            let next = dependent.iter().position(|candidate| {
                !dependent.iter().any(|other| {
                    other != candidate
                        && self.slots[*other]
                            .dependencies
                            .iter()
                            .any(|binding| self.bindings.get(binding) == Some(candidate))
                })
            });
            let Some(next) = next else {
                return Err(fail(self.function, "cyclic async cancellation dependency"));
            };
            order.push(dependent.remove(next));
        }
        // A Copy reference-bearing binding can itself be a child's referent
        // (for example a borrowed slice descriptor). It is non-owning, but
        // its storage must remain intact until dependent children are gone.
        let lenders = order
            .iter()
            .flat_map(|index| &self.slots[*index].dependencies)
            .filter_map(|binding| self.bindings.get(binding).copied())
            .collect::<HashSet<_>>();
        let (retained, disposable): (Vec<_>, Vec<_>) = self
            .reference_slots()
            .into_iter()
            .partition(|index| lenders.contains(index));
        let mut output = vec![self.clear_handle_slots(&disposable)];
        let mut emptied = order.clone();
        emptied.extend(self.reference_slots());
        emptied.sort_unstable();
        emptied.dedup();
        let mut contracts = HashMap::new();
        for &index in &order {
            let slot = &self.slots[index];
            let name = &names[&index];
            let handler = handlers.get(name).ok_or_else(|| fail(self.function, format!("async source slot '{name}' retaining a frame-local borrow requires an in-place cancellation handler")))?;
            let declaration = self.planning.interfaces.function(handler).ok_or_else(|| {
                fail(
                    self.function,
                    format!("unknown graph cleanup handler '{handler}'"),
                )
            })?;
            let aliases = &self.planning.declarations.aliases;
            let expected = crate::typed_ir::resolve_type(&slot.ty, aliases)
                .map_err(|message| fail(self.function, message))?;
            let parameter = declaration
                .parameters
                .first()
                .and_then(|parameter| crate::typed_ir::resolve_type(&parameter.ty, aliases).ok());
            let pinned = matches!(&parameter, Some(Type::PinnedReference { mutable: true, target }) if target.as_ref() == &expected);
            let stationary_child = self.stationary_child(slot);
            if stationary_child && !pinned {
                return Err(fail(self.function, format!("pinned child in source slot '{name}' requires an in-place handler taking a pinned mutable reference")));
            }
            if declaration.unsafe_call
                || declaration.parameters.len() != 1
                || declaration.return_type != Type::Unit
                || (!pinned && parameter.as_ref() != Some(&expected))
            {
                return Err(fail(self.function, format!("dependent cleanup handler '{handler}' must safely consume {} or cancel its pinned mutable reference and return ()", crate::type_source(&slot.ty))));
            }
            contracts.insert(index, (handler, &declaration.parameters[0].name, pinned));
        }
        if !order.is_empty() {
            let plan = self.initialization.as_ref().unwrap();
            let physical_start = plan.states[0].before.len() - self.slots.len();
            let mut cases = Vec::new();
            for state in self.cancellation_states() {
                let mut operations = Vec::new();
                for &index in &order {
                    if !plan.states[state].before[physical_start + index] {
                        continue;
                    }
                    let slot = &self.slots[index];
                    let (handler, parameter, pinned) = contracts[&index];
                    let reference = Self::slot_ref(slot, true);
                    let operation = if pinned {
                        if slot.words.is_some() {
                            if self.word_cleanup_available(handler) {
                                // A generated destroyer needs only occupied
                                // payloads, not a typed view of discarded captures.
                                operations.push(format!(
                                    "(#unsafe (#call {handler}-words (: {parameter} {})))",
                                    self.word_slice(slot.words.as_ref().unwrap(), true)
                                ));
                                operations
                                    .push(self.forget_word_region(slot.words.as_ref().unwrap()));
                                continue;
                            }
                            operations.push(format!(
                                "(#call {handler} (: {parameter} {}))",
                                self.payload_ref(slot, true)
                            ));
                            operations.push(self.forget_word_region(slot.words.as_ref().unwrap()));
                            continue;
                        }
                        // The externally visible PC proves this child Full.
                        // This typed projection preserves stack/heap layout;
                        // pinning alone is not initialization permission.
                        format!("(#call {handler} (: {parameter} (#unsafe (#pin-get-payload-unchecked-mut {reference} {} 0))))\n(#unsafe (#forget (#pin-read {reference})))\n(#unsafe (#pin-write {reference} ({})))", slot.full, slot.empty)
                    } else {
                        let payload = self.fresh("dependent-child");
                        // Consume a movable child without relocating its
                        // stationary lender; never move a pinned child.
                        format!(
                            "(#let {payload} {} {})\n(#call {handler} (: {parameter} {payload}))",
                            crate::type_source(&slot.ty),
                            self.read(index, true)
                        )
                    };
                    operations.push(operation);
                }
                cases.push(format!(
                    "(#case {state}u32 (#block {} ()))",
                    operations.join("\n")
                ));
            }
            // Ready and previously cancelled frames have no live children.
            cases.push(format!("(#case {}u32 ())", u32::MAX));
            cases.push("(#case _ (#unreachable))".into());
            output.push(format!("(#match (#get task pc) {})", cases.join("\n")));
        }
        // Publish child retirement before touching the retained lenders.
        // Opaque handler calls can otherwise erase the input tag facts used
        // by ordinary stored-internal-loan checking at that access boundary.
        output.extend(order.iter().map(|index| {
            let slot = &self.slots[*index];
            if let Some(region) = &slot.words {
                return self.forget_word_region(region);
            }
            format!(
                "(#assert (#variant-is {} {}))",
                Self::slot_ref(slot, false),
                slot.empty
            )
        }));
        output.push(self.clear_handle_slots(&retained));
        // Later cleanup calls can invalidate earlier stored-variant facts.
        // Independently check and publish the complete cleared state before
        // any field extraction or returned cleanup aggregate is assembled.
        output.extend(
            emptied
                .into_iter()
                .filter(|index| self.slots[*index].words.is_none())
                .map(|index| {
                    let slot = &self.slots[index];
                    format!(
                        "(#assert (#variant-is {} {}))",
                        Self::slot_ref(slot, false),
                        slot.empty
                    )
                }),
        );
        Ok(output.join("\n"))
    }

    /// Export cancellation obligations by source declaration/await identity.
    /// Private cell numbers and the dispatcher PC are never part of this ABI.
    fn cleanup_interface(&self, receiver: &str) -> Result<String, Error> {
        let occupied = self.cleanup_occupied();
        let names = self.cleanup_names(occupied)?;
        let cleanup = format!("{}::Cleanup", self.frame);
        let mut fields = Vec::new();
        let mut definitions = Vec::new();
        let mut transfers = Vec::new();
        let mut captures = Vec::new();
        let mut public = Vec::new();
        for (index, slot) in self
            .slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.linear)
        {
            if !occupied.contains(&index) {
                if slot.words.is_some() {
                    continue;
                }
                // A solver fact is made visible to independent ordinary checking.
                transfers.push(format!(
                    "(#assert (#variant-is (#borrow (#get state {})) {}))",
                    slot.field, slot.empty
                ));
                continue;
            }
            let field = names[&index].clone();
            let cell = format!("{cleanup}::{field}");
            let empty = format!("{cell}::Empty");
            let full = format!("{cell}::Full");
            for name in [&cell, &empty, &full] {
                if !self.reserved.borrow_mut().insert(name.clone()) {
                    return Err(fail(self.function, format!("async generated cleanup name '{name}' conflicts with an existing declaration")));
                }
            }
            definitions.push(format!(
                "(#enum {cell} (#linear) (({empty}) ({full} {})))",
                crate::type_source(&slot.ty)
            ));
            fields.push(format!("({field} {cell})"));
            let local = self.fresh("cleanup-slot");
            let payload = self.fresh("cleanup-payload");
            if self.pinned && self.cancels_in_place(slot) {
                // This owner was destroyed at its stationary address. Its
                // stale words must never be exported as another live owner.
                let guard = if slot.words.is_none() {
                    format!(
                        "(#assert (#variant-is (#borrow (#get state {})) {}))",
                        slot.field, slot.empty
                    )
                } else {
                    String::new()
                };
                transfers.push(format!("{guard}\n(#let {local} {cell} ({empty}))"));
            } else if let Some(region) = &slot.words {
                let plan = self.initialization.as_ref().unwrap();
                let physical_start = plan.states[0].before.len() - self.slots.len();
                let slice = if self.pinned {
                    self.word_slice(region, true)
                } else {
                    format!(
                        "(#borrow-slice-mut (#get state {}) {}usize {}usize)",
                        region.field,
                        region.start,
                        region.start + region.length
                    )
                };
                let mut cases = self
                    .cancellation_states()
                    .into_iter()
                    .map(|state| {
                        let value = if plan.states[state].before[physical_start + index] {
                            slot.constant.as_ref().map_or_else(
                                || {
                                    format!(
                                        "({full} (#unsafe (#word-take {} {slice})))",
                                        crate::type_source(&slot.ty)
                                    )
                                },
                                |value| format!("({full} {value})"),
                            )
                        } else {
                            format!("({empty})")
                        };
                        format!("(#case {state}u32 {value})")
                    })
                    .collect::<Vec<_>>();
                cases.push(format!("(#case {}u32 ({empty}))", u32::MAX));
                cases.push("(#case _ (#unreachable))".into());
                transfers.push(format!(
                    "(#let {local} {cell} (#match (#get state pc) {}))",
                    cases.join(" ")
                ));
            } else {
                transfers.push(format!("(#let {local} {cell} (#match (#get state {}) (#case {} ({empty})) (#case ({} {payload}) ({full} {payload}))))", slot.field, slot.empty, slot.full));
            }
            captures.push(format!("({field} {local})"));
            public.push((
                field,
                empty,
                full,
                slot.ty.clone(),
                self.cancels_in_place(slot),
            ));
        }
        let state_type = if self.pinned {
            let name = self.fresh("cleanup-state-type");
            let fields = self
                .slots
                .iter()
                .filter(|slot| slot.words.is_none() && slot.linear)
                .map(|slot| format!("({} {})", slot.field, slot.name))
                .collect::<Vec<_>>()
                .join(" ");
            definitions.push(format!("(#struct {name} (#linear) ((pc #u32) {fields}))"));
            name
        } else {
            self.frame.clone()
        };
        let extraction = if self.pinned {
            // Keep loan clearing and extraction in this ordinary function.
            // A separate raw-state exporter loses entry/clearing correlation
            // in nested caller contracts for conditional internal references.
            let clear = self.in_place_cleanup()?;
            let pc = self.fresh("cleanup-pc");
            let mut takes = vec![format!("(#let {pc} #u32 (#get task pc))")];
            let mut captures = vec![format!("(pc {pc})")];
            for slot in self
                .slots
                .iter()
                .filter(|slot| slot.words.is_none() && slot.linear)
            {
                let value = self.fresh("cleanup-extracted");
                takes.push(format!(
                    "(#let {value} {} (#unsafe (#pin-read {})))\n(#unsafe (#pin-write {} ({})))",
                    slot.name,
                    Self::slot_ref(slot, true),
                    Self::slot_ref(slot, true),
                    slot.empty
                ));
                captures.push(format!("({} {value})", slot.field));
            }
            format!(
                "{clear}\n{}\n{}\n(#let state {state_type} (#struct-literal {state_type} ({})))",
                takes.join("\n"),
                self.set_pc(u32::MAX),
                captures.join(" ")
            )
        } else {
            format!("(#let-mut state {} task)", self.frame)
        };
        let mut source = format!(
            "{}\n(#struct {cleanup} (#linear) ({}))\n\
            (#fn {}::cleanup (: task {receiver}) {cleanup}\n\
              {extraction}\n{}\n\
              (#forget state) (#return (#struct-literal {cleanup} ({}))))",
            definitions.join("\n"),
            fields.join(" "),
            self.poll,
            transfers.join("\n"),
            captures.join(" ")
        );
        if let Some(config) = &self.function.cancel {
            let Expr::List(config) = config else {
                return Err(fail(self.function, "invalid graph cleanup configuration"));
            };
            let [Expr::Symbol(dispatch), Expr::List(_)] = config.as_slice() else {
                return Err(fail(
                    self.function,
                    "graph cleanup requires (function ((source-slot handler) ...))",
                ));
            };
            let mut handlers = self.cancellation_handlers()?;
            let mut calls = Vec::new();
            for (field, empty, full, ty, dependent) in &public {
                let handler = handlers.remove(field).ok_or_else(|| {
                    fail(
                        self.function,
                        format!("missing graph cleanup handler for source slot '{field}'"),
                    )
                })?;
                if *dependent {
                    // Dependent payloads were destroyed while their referents
                    // remained in the pinned parent; public cells must be Empty.
                    calls.push(format!(
                        "(#assert (#variant-is (#borrow (#get task {field})) {empty}))"
                    ));
                    continue;
                }
                let declaration = self.planning.interfaces.function(&handler).ok_or_else(|| {
                    fail(
                        self.function,
                        format!("unknown graph cleanup handler '{handler}'"),
                    )
                })?;
                let aliases = &self.planning.declarations.aliases;
                if declaration.unsafe_call
                    || declaration.parameters.len() != 1
                    || declaration.return_type != Type::Unit
                    || crate::typed_ir::resolve_type(&declaration.parameters[0].ty, aliases).ok()
                        != crate::typed_ir::resolve_type(ty, aliases).ok()
                {
                    return Err(fail(self.function, format!("graph cleanup handler '{handler}' must safely consume one {} and return ()", crate::type_source(ty))));
                }
                let payload = self.fresh("cleanup-owned");
                calls.push(format!("(#match (#get task {field}) (#case {empty} ()) (#case ({full} {payload}) (#call {handler} (: {} {payload}))))", declaration.parameters[0].name));
            }
            if let Some(slot) = handlers.keys().min() {
                return Err(fail(
                    self.function,
                    format!("unknown graph cleanup source slot '{slot}'"),
                ));
            }
            source.push_str(&format!(
                "\n(#fn {dispatch} (: task {cleanup}) () {} (#forget task) (#return ()))",
                calls.join("\n")
            ));
            if self.pinned {
                // Preserve the clearing-before-owner-access sequence in this
                // entry point too. An aggregate call summary does not encode
                // that ordering, whereas ordinary statements do.
                let destruction = calls.join("\n").replace("(#get task ", "(#get cleanup ");
                source.push_str(&format!("\n(#fn {}::destroy (: task {receiver}) ()\n{extraction}\n{}\n(#forget state)\n(#let cleanup {cleanup} (#struct-literal {cleanup} ({})))\n{destruction}\n(#forget cleanup)\n(#return ()))", self.poll, transfers.join("\n"), captures.join(" ")));
            }
        }
        Ok(source)
    }

    /// The word-only entry is useful when captures are only retired, not
    /// restored as reference-bearing handler arguments. Such arguments keep
    /// the existing typed cancellation protocol and its contents contracts.
    fn word_cleanup_available(&self, handler: &str) -> bool {
        fn visit(emitter: &Emitter<'_>, handler: &str, active: &mut HashSet<String>) -> bool {
            let Some(interface) = emitter.planning.interfaces.functions.get(handler) else {
                return false;
            };
            if interface.provenance != crate::generator::async_interfaces::Provenance::GraphDestroy
            {
                let Some(parameter) = interface.declaration.parameters.first() else {
                    return false;
                };
                let ty = crate::typed_ir::resolve_type(
                    &parameter.ty,
                    &emitter.planning.declarations.aliases,
                )
                .unwrap_or_else(|_| parameter.ty.clone());
                let target = match &ty {
                    Type::PinnedReference { target, .. } => target.as_ref(),
                    _ => &ty,
                };
                return !emitter.types.contains_reference(target);
            }
            if !active.insert(handler.into()) {
                return false;
            }
            let result = handler.strip_suffix("::destroy")
                .and_then(|poll| emitter.planning.functions.iter().find(|function|
                    function.source.generated_poll.as_deref() == Some(poll)))
                .and_then(|function| function.cancel.as_ref())
                .is_some_and(|config| match config {
                    Expr::List(parts) => parts.get(1).is_some_and(|entries| match entries {
                        Expr::List(entries) => entries.iter().all(|entry| matches!(entry, Expr::List(pair)
                            if pair.get(1).is_some_and(|handler| matches!(handler, Expr::Symbol(handler) if visit(emitter, handler, active))))),
                        _ => false,
                    }),
                    _ => false,
                });
            active.remove(handler);
            result
        }
        self.planning
            .interfaces
            .functions
            .get(handler)
            .is_some_and(|interface| {
                interface.provenance == crate::generator::async_interfaces::Provenance::GraphDestroy
            })
            && visit(self, handler, &mut HashSet::new())
    }

    /// Cancel a word-backed child without materializing discarded references.
    /// The unsafe entry requires the stationary frame's exact physical layout
    /// and a valid dispatcher state. Source occupancy/ownership checking and
    /// ordinary checking of every typed handler input remain mandatory.
    fn word_cleanup(&self, source: &str) -> Result<String, Error> {
        if !self.pinned || !self.word_cleanup_available(&format!("{}::destroy", self.poll)) {
            return Ok(String::new());
        }
        use super::async_word_cleanup::Layout;
        let layout = Layout::new(source, &self.frame, &self.planning.declarations)
            .map_err(|message| fail(self.function, message))?;
        let occupied = self.cleanup_occupied();
        let names = self.cleanup_names(occupied)?;
        let handlers = self.cancellation_handlers()?;
        let plan = self.initialization.as_ref().unwrap();
        let physical_start = plan.states[0].before.len() - self.slots.len();
        let region = |slot: &Slot, payload: bool| {
            if let Some(words) = &slot.words {
                let (base, _) = layout.fields[&words.field];
                (base + words.start, words.length)
            } else {
                let (base, width) = layout.fields[&slot.field];
                if payload {
                    (base + 1, width - 1)
                } else {
                    (base, width)
                }
            }
        };
        let retire = |slot: &Slot| {
            let (start, length) = region(slot, false);
            format!(
                "(#unsafe (#word-forget (#array #u64 {length}) {}))",
                Layout::slice(start, length)
            )
        };
        let mut cases = Vec::new();
        for state in self.cancellation_states() {
            let live = |index: usize| plan.states[state].before[physical_start + index];
            let mut dependent = self
                .slots
                .iter()
                .enumerate()
                .filter(|(index, slot)| {
                    slot.linear
                        && occupied.contains(index)
                        && live(*index)
                        && self.cancels_in_place(slot)
                })
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            let mut order = Vec::new();
            while !dependent.is_empty() {
                let next = dependent
                    .iter()
                    .position(|candidate| {
                        !dependent.iter().any(|other| {
                            other != candidate
                                && self.slots[*other]
                                    .dependencies
                                    .iter()
                                    .any(|binding| self.bindings.get(binding) == Some(candidate))
                        })
                    })
                    .ok_or_else(|| fail(self.function, "cyclic async cancellation dependency"))?;
                order.push(dependent.remove(next));
            }
            let lenders = order
                .iter()
                .flat_map(|index| &self.slots[*index].dependencies)
                .filter_map(|binding| self.bindings.get(binding).copied())
                .collect::<HashSet<_>>();
            let references = self.reference_slots();
            let retained = references
                .iter()
                .copied()
                .filter(|index| lenders.contains(index))
                .collect::<Vec<_>>();
            let mut operations = references
                .into_iter()
                .filter(|index| !lenders.contains(index))
                .map(|index| retire(&self.slots[index]))
                .collect::<Vec<_>>();
            let dependents = order.iter().copied().collect::<HashSet<_>>();
            order.extend(
                self.slots
                    .iter()
                    .enumerate()
                    .filter(|(index, slot)| {
                        slot.linear
                            && occupied.contains(index)
                            && live(*index)
                            && !dependents.contains(index)
                    })
                    .map(|(index, _)| index),
            );
            let mut retired_lenders = false;
            for index in order {
                let slot = &self.slots[index];
                if !dependents.contains(&index) && !retired_lenders {
                    // All dependent children have completed cancellation. The
                    // remaining non-owning lender handles may now be retired.
                    operations.extend(retained.iter().map(|index| retire(&self.slots[*index])));
                    retired_lenders = true;
                }
                let handler = &handlers[&names[&index]];
                let declaration = self.planning.interfaces.function(handler).unwrap();
                let parameter = &declaration.parameters[0].name;
                let pinned = matches!(declaration.parameters[0].ty, Type::PinnedReference { .. });
                let (start, length) = region(slot, true);
                let slice = Layout::slice(start, length);
                if pinned && self.word_cleanup_available(handler) {
                    operations.push(format!(
                        "(#unsafe (#call {handler}-words (: {parameter} {slice})))"
                    ));
                } else if pinned {
                    operations.push(format!("(#call {handler} (: {parameter} (#unsafe (#word-view (#pin-ref-mut {}) {slice}))))", crate::type_source(&slot.ty)));
                } else {
                    operations.push(format!(
                        "(#call {handler} (: {parameter} (#unsafe (#word-take {} {slice}))))",
                        crate::type_source(&slot.ty)
                    ));
                }
                operations.push(retire(slot));
            }
            cases.push(format!(
                "(#case {state}u32 (#block {} ()))",
                operations.join("\n")
            ));
        }
        cases.push(format!("(#case {}u32 ())", u32::MAX));
        cases.push("(#case _ (#unreachable))".into());
        Ok(format!("; Caller proves exact stationary layout and initialized dispatcher state.\n; Only occupied handler payloads are read; discarded captures are retired.\n(#unsafe-fn {}-destroy-words (: task (#slice-mut #u64)) ()\n(#assert (#usize.== (#slice-mut-len task) {}usize))\n(#match (#unsafe (#word-read #u32 {})) {})\n(#unsafe (#word-forget (#array #u64 {}) {}))\n(#unsafe (#word-write #u32 {} {}u32))\n(#forget task) (#return ()))",
            self.poll, layout.words, Layout::slice(0, 1), cases.join("\n"), layout.words, Layout::slice(0, layout.words), Layout::slice(0, 1), u32::MAX))
    }

    /// The public names describe source parameters; private cell identities
    /// appear only inside these independently checked ordinary functions.
    fn parameter_access(&self) -> Result<String, Error> {
        let start = self
            .planning
            .interfaces
            .function(&self.function.model.source_name)
            .ok_or_else(|| fail(self.function, "async start interface disappeared"))?;
        let mut definitions = Vec::new();
        for (requested, name) in &self.function.source.frame_access {
            let (index, parameter) = start
                .parameters
                .iter()
                .enumerate()
                .find(|(_, parameter)| parameter.name == *requested)
                .ok_or_else(|| {
                    fail(
                        self.function,
                        format!("unknown async access parameter '{requested}'"),
                    )
                })?;
            let slot_index = self.bindings.get(&BindingId(index)).copied();
            if !self.pinned
                || !self.types.can_repeat(&parameter.ty)
                || self.types.contains_reference(&parameter.ty)
            {
                return Err(fail(
                    self.function,
                    "async parameter access requires reference-free Copy data in a pinned frame",
                ));
            }
            let mut guards = vec!["(#assert (#u32.== (#get task pc) 4294967295u32))".to_owned()];
            for (other_index, other) in self.slots.iter().enumerate() {
                if Some(other_index) != slot_index
                    && other.words.is_none()
                    && (other.linear || self.types.contains_reference(&other.ty))
                {
                    guards.push(format!(
                        "(#assert (#variant-is {} {}))",
                        Self::slot_ref(other, false),
                        other.empty
                    ));
                }
            }
            let guards = guards.join("\n");
            let ty = crate::type_source(&parameter.ty);
            if crate::typed_ir::resolve_type(&parameter.ty, &self.planning.declarations.aliases)
                .map_err(|message| fail(self.function, message))?
                == Type::Unit
            {
                definitions.push(format!(
                    "(#fn {name}-replace (: task (#pin-ref-mut {}) : value {ty}) ()
                    {guards} (#forget value) (#return ()))
                    (#fn {name}-read (: task (#pin-ref {})) {ty} {guards} (#return ()))",
                    self.frame, self.frame
                ));
                continue;
            }
            let slot = &self.slots[slot_index.ok_or_else(|| {
                fail(self.function, "async access parameter has no physical cell")
            })?];
            if slot.raw {
                return Err(fail(
                    self.function,
                    "async access parameter unexpectedly uses reference storage",
                ));
            }
            if let Some(region) = &slot.words {
                definitions.push(format!(
                    "(#fn {name}-replace (: task (#pin-ref-mut {}) : value {ty}) ()
                  {guards} (#unsafe (#word-write {ty} {} value)) (#return ()))
                  (#fn {name}-read (: task (#pin-ref {})) {ty}
                  {guards} (#return (#unsafe (#word-read {ty} {}))))",
                    self.frame,
                    self.word_slice(region, true),
                    self.frame,
                    self.word_slice(region, false)
                ));
                continue;
            }
            let previous = self.fresh("previous-parameter-cell");
            let occupied = self.fresh("previous-parameter-value");
            let target = Self::slot_ref(slot, true);
            definitions.push(format!(
                "(#fn {name}-replace (: task (#pin-ref-mut {}) : value {ty}) ()
                {guards}
                (#let {previous} {} (#unsafe (#pin-read {target})))
                (#match {previous} (#case {} ()) (#case ({} {occupied}) (#forget {occupied})))
                (#unsafe (#pin-write {target} ({} value)))
                (#return ()))
                (#fn {name}-read (: task (#pin-ref {})) {ty}
                {guards}
                (#return (#deref (#pin-get-payload {} {} 0))))",
                self.frame,
                slot.name,
                slot.empty,
                slot.full,
                slot.full,
                self.frame,
                Self::slot_ref(slot, false),
                slot.full
            ));
        }
        Ok(definitions.join("\n"))
    }

    fn emit(mut self) -> Result<Generated, Error> {
        self.initialization = Some(self.check_owned_cells()?);
        let graph: &Graph = &self.function.graph;
        let mut cases = Vec::new();
        let count = self.initialization.as_ref().unwrap().states.len();
        for state in 0..count {
            self.current_state = state;
            let before = &self.initialization.as_ref().unwrap().states[state].before;
            *self.physical_current.borrow_mut() =
                Some(before[before.len() - self.slots.len()..].to_vec());
            let index = self.initialization.as_ref().unwrap().states[state].block;
            self.active_preview_aliases = self.preview_aliases.entry[index].clone();
            let block = &graph.blocks[index];
            let mut actions = Vec::new();
            actions.push(
                self.clear_addresses(&self.address_retirement.as_ref().unwrap().entry[index]),
            );
            let retired = self
                .retirement
                .as_ref()
                .map_or_else(Vec::new, |plan| plan.entry[index].clone());
            actions.push(self.clear_values(&retired));
            for (action_index, action) in block.actions.iter().enumerate() {
                let owner = match action.action {
                    Action::Bind { binding, .. } => Some(binding),
                    Action::Borrow { place, .. }
                    | Action::Load { place, .. }
                    | Action::Store { place, .. }
                    | Action::Release { place, .. } => match graph.places[place.0].root {
                        AddressRoot::Local(binding) => Some(binding),
                        _ => None,
                    },
                    _ => None,
                };
                let storage_owner = |binding: BindingId| {
                    !matches!(
                        graph.bindings[binding.0].ty,
                        Type::Reference { .. }
                            | Type::PinnedReference { .. }
                            | Type::PinOwned(_)
                            | Type::PinShared(_)
                    ) && self.bindings.contains_key(&binding)
                };
                let touches_owner = owner.is_some_and(storage_owner)
                    || matches!(&action.action, Action::ScopeExit(bindings)
                        if bindings.iter().copied().any(storage_owner));
                // Publish checked state facts immediately before owner access.
                // Earlier facts may have been invalidated by an unsafe call.
                if let Some(plan) = self
                    .reference_cells
                    .as_ref()
                    .filter(|_| self.pinned && touches_owner)
                {
                    for cell in plan
                        .action_empty
                        .get(&(BlockId(index), action_index))
                        .into_iter()
                        .flatten()
                    {
                        let slot = match cell {
                            crate::generator::async_cells::Cell::Binding(binding) => {
                                self.bindings.get(binding)
                            }
                            crate::generator::async_cells::Cell::Value(value) => {
                                self.values.get(value)
                            }
                            crate::generator::async_cells::Cell::Scope(scope) => {
                                self.scopes.get(scope)
                            }
                        };
                        if let Some(slot) = slot {
                            let slot = &self.slots[*slot];
                            if slot.words.is_some() {
                                continue;
                            }
                            actions.push(format!(
                                "(#assert (#variant-is {} {}))",
                                Self::slot_ref(slot, false),
                                slot.empty
                            ));
                        }
                    }
                }
                actions.push(self.action(action)?);
                actions.push(
                    self.clear_addresses(
                        self.address_retirement
                            .as_ref()
                            .unwrap()
                            .after
                            .get(&(index, action_index))
                            .map_or(&[], Vec::as_slice),
                    ),
                );
                let retired = self.retirement.as_ref().map_or_else(Vec::new, |plan| {
                    plan.after_action[index][action_index].clone()
                });
                actions.push(self.clear_values(&retired));
            }
            let terminal = self.terminal(BlockId(index), &block.terminator)?;
            cases.push(format!(
                "(#case {state}u32 (#block {} {terminal} (#unreachable)))",
                actions.join("\n")
            ));
        }
        *self.physical_current.borrow_mut() = None;
        let fields = self.frame_fields();
        let start_parameters = &self
            .planning
            .interfaces
            .function(&self.function.model.source_name)
            .unwrap()
            .parameters;
        let mut initial = Vec::new();
        let mut factory_captures = Vec::new();
        let mut captured_cells = HashMap::new();
        let mut captured_pointers = HashMap::new();
        let mut external_parameters = self.external_captures.keys().copied().collect::<Vec<_>>();
        external_parameters.sort_by_key(|binding| binding.0);
        for binding in external_parameters {
            let parameter = start_parameters.get(binding.0).ok_or_else(|| {
                fail(
                    self.function,
                    "poll-only context references cannot be retained in a selected async anchor",
                )
            })?;
            let (Type::Reference { mutable, .. } | Type::PinnedReference { mutable, .. }) =
                crate::typed_ir::resolve_type(&parameter.ty, &self.planning.declarations.aliases)
                    .map_err(|message| fail(self.function, message))?
            else {
                unreachable!()
            };
            let capture_index = self.external_captures[&binding];
            let capture = &self.slots[capture_index];
            let cell = self.fresh("external-capture");
            let pointer = self.fresh("external-pointer");
            let suffix = if mutable { "-mut" } else { "" };
            let source_slot = &self.slots[self.bindings[&binding]];
            factory_captures.push(format!(
                "(#let-mut {cell} {} ({} {}))
              (#let {pointer} {} (#ref-ptr
                (#get-payload (#borrow{suffix} {cell}) {} 0)))",
                capture.name,
                capture.full,
                parameter.name,
                crate::type_source(&source_slot.storage),
                capture.full
            ));
            captured_cells.insert(capture_index, cell);
            captured_pointers.insert(binding, pointer);
        }
        let mut initial_parts = HashMap::new();
        let mut aggregate_parameters = self
            .aggregates
            .iter()
            .filter(|(binding, _)| binding.0 < start_parameters.len())
            .collect::<Vec<_>>();
        aggregate_parameters.sort_by_key(|(binding, _)| binding.0);
        for (binding, aggregate) in aggregate_parameters {
            let parameter = &start_parameters[binding.0];
            let mut names = HashMap::new();
            let pattern = self.aggregate_pattern(aggregate, &[], &mut names);
            factory_captures.push(format!(
                "(#let {pattern} {} {})",
                crate::type_source(&parameter.ty),
                parameter.name
            ));
            for (slot, name) in names {
                initial_parts.insert(slot, name);
            }
            for shell in &aggregate.shells {
                initial_parts.insert(shell.slot, format!("({})", shell.alive));
            }
        }
        for (index, slot) in self.slots.iter().enumerate() {
            if slot.words.is_some() {
                continue;
            }
            let parameter = self.bindings.iter().find_map(|(binding, actual)| {
                (*actual == index
                    && binding.0 < start_parameters.len()
                    && !self.aggregates.contains_key(binding))
                .then(|| &start_parameters[binding.0])
            });
            let value = if let Some(part) = initial_parts.get(&index) {
                format!("({} {part})", slot.full)
            } else if let Some(cell) = captured_cells.get(&index) {
                cell.clone()
            } else {
                parameter.map_or_else(
                    || format!("({})", slot.empty),
                    |parameter| {
                        let value = self
                            .bindings
                            .iter()
                            .find_map(|(binding, actual)| {
                                (*actual == index)
                                    .then(|| captured_pointers.get(binding))
                                    .flatten()
                            })
                            .map_or(parameter.name.as_str(), String::as_str);
                        format!("({} {value})", slot.full)
                    },
                )
            };
            initial.push(format!("({} {})", slot.field, value));
        }
        for region in self.word_buffers() {
            let buffer = self.fresh("initial-words");
            factory_captures.push(format!(
                "(#let-mut {buffer} (#array #u64 {}) (#array-repeat 0u64))",
                region.capacity
            ));
            for (index, slot) in self.slots.iter().enumerate() {
                let parameter = self.bindings.iter().find_map(|(binding, actual)| {
                    (*actual == index
                        && binding.0 < start_parameters.len()
                        && !self.aggregates.contains_key(binding))
                    .then(|| &start_parameters[binding.0].name)
                });
                let Some(part) = initial_parts.get(&index).or(parameter) else {
                    continue;
                };
                let Some(word) = &slot.words else {
                    continue;
                };
                if word.field != region.field {
                    continue;
                }
                if slot.constant.is_some() {
                    factory_captures.push(format!("(#forget {part})"));
                    continue;
                }
                let physical = if slot.raw {
                    self.bindings
                        .iter()
                        .find_map(|(binding, actual)| {
                            (*actual == index)
                                .then(|| captured_pointers.get(binding))
                                .flatten()
                        })
                        .cloned()
                        .unwrap_or_else(|| format!("(#ref-ptr {part})"))
                } else {
                    part.clone()
                };
                factory_captures.push(format!("(#unsafe (#word-write {} (#borrow-slice-mut {buffer} {}usize {}usize) {physical}))",
                    crate::type_source(&slot.storage), word.start, word.start + word.length));
            }
            initial.push(format!("({} {buffer})", region.field));
            initial.push(format!(
                "({} (#array-of (#array {} 0)))",
                region.marker,
                crate::type_source(&region.owner)
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
            .filter(|slot| slot.words.is_none())
            .map(|slot| {
                format!(
                    "(#call {} (: slot (#get task {})))",
                    slot.finish, slot.field
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let pinned_type = Type::PinnedReference {
            mutable: true,
            target: Box::new(Type::Named(self.frame.clone())),
        };
        let receiver = if self.pinned {
            crate::type_source(&pinned_type)
        } else {
            self.frame.clone()
        };
        let source = format!(
            "{}\n\
          (#struct {} (#linear) ((pc #u32) {fields}))\n(#opaque {})\n\
          (#enum {} () (({} {}) ({} {})))\n\
          (#fn {} ({signature}) {}\n\
            {}\n\
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
            receiver,
            self.ready,
            crate::type_source(&self.result),
            self.function.model.source_name,
            self.frame,
            factory_captures.join("\n"),
            self.frame,
            0,
            initial.join(" "),
            self.finish,
            self.frame,
            self.poll,
            receiver,
            crate::type_source(&self.function.source.waker),
            self.poll_type,
            cases.join("\n")
        );
        let projections = self.projections.join("\n");
        let cleanup = self.cleanup_interface(&receiver)?;
        let word_cleanup = self.word_cleanup(&format!("{source}\n{cleanup}"))?;
        let access = self.parameter_access()?;
        let source = crate::generator::format_generated_source(&format!(
            "{source}\n{cleanup}\n{word_cleanup}\n{projections}\n{access}"
        ))
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
        .map(|function| generate_function(planning, function))
        .collect()
}

pub(crate) fn generate_function(
    planning: &Planning,
    function: &Function,
) -> Result<Generated, Error> {
    #[cfg(test)]
    EMISSION_COUNT.with(|count| count.set(count.get() + 1));
    Emitter::new(planning, function)?.emit()
}

#[cfg(test)]
thread_local! {
    pub(crate) static EMISSION_COUNT: Cell<usize> = const { Cell::new(0) };
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
            // Protocol bundles have already been expanded in the prepared
            // program, but must remain in the standalone inspectable artifact.
            if matches!(&source.expr, Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#syntax"))
            {
                continue;
            }
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
    let sources = planning
        .functions
        .iter()
        .map(|function| function.source.clone())
        .collect::<Vec<_>>();
    crate::generator::async_source::attach_validation(&mut program, &sources);
    Ok(program)
}

#[cfg(test)]
#[path = "../../tests/regressions/selected_address_snapshots.rs"]
mod selected_address_snapshots;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_guard_aliases_never_initialize_preview_owner_cells() {
        let function = "(#fn work (: source (#ref #u64)) #u64
          (#let holder Holder (Holding (#struct-literal View (: value source))))
          (#return (#match holder
            (#case (Holding view)
              (#when (#u64.==
                (#await Child ChildPending ChildReady child-poll (Start 0u64))
                (#deref (#get (#borrow view) value))))
              (#block (#forget view) 42u64))
            (#case (Holding other) (#block (#forget other) 42u64)))))";
        let planning = prepare_generator(
            "#async-fn-pinned",
            function,
            "(#struct View (#linear) (: value (#ref #u64)))
             (#enum Holder (#linear) ((Holding View))) ",
        );
        let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let binding = *emitter.preview_aliases.patterns.keys().next().unwrap();
        let slot = emitter.bindings[&binding];
        let traces = emitter.physical_occupancy().unwrap();
        let graph = &planning.functions[0].graph;
        let preview = graph
            .blocks
            .iter()
            .position(|block| {
                block.actions.iter().any(|action| {
                    matches!(&action.action, Action::Preview(pattern)
                if pattern.bindings.contains(&binding))
                })
            })
            .unwrap();
        assert!(!traces[preview].writes.contains(&(slot, true)));
        let commit = graph
            .blocks
            .iter()
            .position(|block| {
                block.actions.iter().any(|action| {
                    matches!(&action.action, Action::Commit(pattern)
                if pattern.bindings.contains(&binding))
                })
            })
            .unwrap();
        assert!(traces[commit].writes.contains(&(slot, true)));
        assert!(emitter.active_preview_aliases.is_empty());
        // A preview is a stationary alias, not an initialized local owner.
        // Recover its address through the original enum payload even when
        // its eventual committed owner has a word-backed storage slot.
        let mut anchor_emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        anchor_emitter.active_preview_aliases.insert(binding);
        let anchor = anchor_emitter.anchor_project(
            &crate::typed_place::Place::root(crate::typed_body::PlaceRoot::Local(binding)),
            0,
            false,
            &HashMap::new(),
        );
        assert!(anchor.contains("Holding"), "{anchor}");
        if let Some(region) = &emitter.slots[slot].words {
            assert!(!anchor.contains(&region.field), "{anchor}");
        }
        let actual = emitter.emit().unwrap();
        let expected = Emitter::new(&planning, &planning.functions[0])
            .unwrap()
            .emit()
            .unwrap();
        assert_eq!(actual.source, expected.source);
        crate::CheckedProgram::validate_with_span(&program(&planning, &[actual]).unwrap()).unwrap();
    }
    use std::{
        fs,
        process::Command,
        sync::atomic::{AtomicUsize, Ordering},
        time::{Duration, Instant},
    };

    const CONTEXT: &str = "
      (#enum Child (#linear) ((Start #u64) (Resume #u64)))
      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Start value) (ChildPending (Resume value)))
          (#case (Resume value) (ChildReady value)))))";

    fn prepare(body: &str, main: &str) -> Planning {
        prepare_function(&format!("(#fn work ((seed #u64)) #u64 {body})"), main)
    }

    fn prepare_function(function: &str, main: &str) -> Planning {
        prepare_generator("#async-fn", function, main)
    }

    fn prepare_generator(generator: &str, function: &str, main: &str) -> Planning {
        prepare_generator_result(generator, function, main).unwrap()
    }

    fn prepare_generator_result(
        generator: &str,
        function: &str,
        main: &str,
    ) -> Result<Planning, crate::source_error::SourceError> {
        let fn_name = function
            .split("(#fn ")
            .nth(1)
            .and_then(|tail| tail.split_whitespace().next())
            .expect("async test function has a name");
        let source = format!(
            "{CONTEXT}
          (@{generator} (: protocol {fn_name}-await : waker #u64
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
        crate::generator::async_prepare::prepare(&syntax)
    }

    #[test]
    fn scope_cleanup_uses_borrow_dependencies_instead_of_input_order() {
        let planning = prepare_generator(
            "#async-fn-pinned",
            "(#fn work (: seed #u64) #u64
          (#let owner #u64 seed)
          (#let view (#ref #u64) (#borrow owner))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#return (#u64.+.wrap (#deref view) extra)))",
            "",
        );
        let function = &planning.functions[0];
        let mut emitter = Emitter::new(&planning, function).unwrap();
        let binding = |name| {
            BindingId(
                function
                    .graph
                    .bindings
                    .iter()
                    .position(|binding| binding.name == name)
                    .unwrap(),
            )
        };
        let owner = binding("owner");
        let view = binding("view");
        let owner_slot = emitter.bindings[&owner];
        let view_slot = emitter.bindings[&view];
        for bindings in [[owner, view], [view, owner]] {
            *emitter.occupancy_trace.borrow_mut() = Some(OccupancyTrace::default());
            let output = emitter.clear_scope(&bindings).unwrap();
            assert!(
                output.trim().is_empty(),
                "word cells retire through state facts"
            );
            let trace = emitter.occupancy_trace.borrow_mut().take().unwrap();
            assert!(
                trace
                    .writes
                    .iter()
                    .position(|(slot, _)| *slot == view_slot)
                    .unwrap()
                    < trace
                        .writes
                        .iter()
                        .position(|(slot, _)| *slot == owner_slot)
                        .unwrap()
            );
        }
        emitter.slots[owner_slot].dependencies.push(view);
        assert!(emitter
            .clear_scope(&[view, owner])
            .err()
            .unwrap()
            .message
            .contains("cyclic async scope-exit dependency"));
    }

    #[test]
    fn selected_external_parameter_has_a_lifetime_bearing_capture() {
        let planning = prepare_generator(
            "#async-fn-pinned",
            "(#fn work (: external (#ref #u64) : choose #bool) #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#if choose (#borrow owner) external))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#let answer #u64 (#u64.+.wrap (#deref view) extra))
          (#drop view) (#return answer))",
            "",
        );
        let function = &planning.functions[0];
        let body = &planning.declarations.bodies[&function.model.body_name];
        let plan = crate::generator::async_self_borrow::Plan::new(
            &function.graph,
            body,
            &planning.declarations.flows[&function.model.body_name],
            &planning.declarations,
            true,
        )
        .unwrap();
        assert_eq!(
            plan.external_parameters.len(),
            1,
            "anchors: {:?}; bindings: {:?}",
            plan.bindings,
            body.bindings
        );
    }

    fn runtime(body: &str, main: &str, expected: i32) -> Vec<Generated> {
        let planning = prepare(body, main);
        runtime_planned(planning, expected)
    }

    #[test]
    fn dispatcher_specializes_different_initialization_histories_and_resumes_both() {
        let function = "(#fn work (: seed #u64 : choose #bool) #u64
          (#let owner #u64 seed)
          (#let view (#ref #u64) (#borrow owner))
          (#if choose (#forget view) ())
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#return (#u64.+.wrap owner extra)))";
        for choose in ["true", "false"] {
            let main = format!(
                "(#fn main () #u64
              (#let waker #u64 0u64)
              (#let-mut task Work-frame (#call work (: seed 42u64 : choose {choose})))
              (#let first Work-poll-result (#call work-poll
                (: task (#pin-borrow-mut task) : waker (#borrow waker))))
              (#let-else (work-pending next) Work-poll-result first (#unreachable))
              (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                (#case (work-ready value) value)
                (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
              (#forget task) (#return answer))"
            );
            let planning = prepare_generator("#async-fn-pinned", function, &main);
            let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
            let specialized = emitter.check_owned_cells().unwrap();
            let view = planning.functions[0]
                .graph
                .bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap();
            assert!(specialized.states.iter().any(|left| {
                specialized.states.iter().any(|right| {
                    left.block == right.block && left.before[view] != right.before[view]
                })
            }));
            let generated = runtime_planned(planning, 42);
            assert!(!generated[0].source.contains("initialization-bits"));
        }
    }

    #[test]
    fn primitive_bindings_use_exact_word_layouts_without_tag_helpers() {
        let function = "(#fn work (: seed #u64) #u64
          (#let small #i8 -1i8) (#let wide #u128 340282366920938463463374607431768211455u128)
          (#let floating #f64 1.5f64) (#let flag #bool true)
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#return (#u64.+.wrap seed extra)))";
        let planning = prepare_generator("#async-fn-pinned", function, "");
        let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let definitions = emitter.slot_definitions();
        let fields = emitter.frame_fields();
        let mut saved_words = 0;
        for (binding, index) in &emitter.bindings {
            let slot = &emitter.slots[*index];
            let region = slot
                .words
                .as_ref()
                .expect("all bindings in this fixture are primitive");
            let expected = if planning.functions[0].graph.bindings[binding.0].ty == Type::U128 {
                2
            } else {
                1
            };
            assert_eq!(region.capacity, expected);
            assert!(fields.contains(&format!("({} (#array #u64 {expected}))", region.field)));
            assert!(!definitions.contains(&format!("(#enum {} (#linear) ", slot.name)));
            assert!(!definitions.contains(&format!("(#fn {} ", slot.put)));
            // The old cell used one discriminator plus the same value words.
            saved_words += 1;
        }
        assert_eq!(saved_words, 6);
        let temporary_slots = emitter
            .values
            .values()
            .filter(|index| {
                let slot = &emitter.slots[**index];
                matches!(
                    slot.ty,
                    Type::U64 | Type::I8 | Type::U128 | Type::F64 | Type::Bool
                )
            })
            .collect::<Vec<_>>();
        assert!(!temporary_slots.is_empty());
        for index in temporary_slots {
            let slot = &emitter.slots[*index];
            assert!(
                slot.words.is_some(),
                "primitive temporary {} is still tagged",
                slot.field
            );
            assert!(!definitions.contains(&format!("(#enum {} (#linear) ", slot.name)));
        }
    }

    #[test]
    fn pinned_enum_payload_handles_use_word_owners_and_select_active_anchors() {
        let function = "(#fn work (: choose #bool) #u64
          (#let-mut owner Choice (#if choose (Left 40u64) (Right 40u64)))
          (#let view (#pin-ref-mut #u64) (#if choose
            (#pin-get-payload-mut (#pin-borrow-mut owner) Left 0)
            (#pin-get-payload-mut (#pin-borrow-mut owner) Right 0)))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#unsafe (#pin-write view (#u64.+.wrap (#deref view) extra)))
          (#let answer #u64 (#deref view))
          (#drop view) (#forget owner) (#return answer))";
        for choose in ["true", "false"] {
            let main = format!(
                "(#enum Choice (#linear) ((Left #u64) (Right #u64)))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut task Work-frame (#call work (: choose {choose})))
                (#let first Work-poll-result (#call work-poll
                  (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready result) result)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget task) (#return answer))"
            );
            let planning = prepare_generator("#async-fn-pinned", function, &main);
            let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
            for (index, binding) in planning.functions[0].graph.bindings.iter().enumerate() {
                if binding.name == "owner" {
                    assert!(emitter.slots[emitter.bindings[&BindingId(index)]]
                        .words
                        .is_some());
                } else if binding.name == "view" {
                    assert!(emitter.slots[emitter.bindings[&BindingId(index)]].raw);
                }
            }
            runtime_planned(planning, 42);
            let inactive = function.replace(
                "(#if choose (Left 40u64) (Right 40u64))",
                "(#if choose (Right 40u64) (Left 40u64))",
            );
            let planning = prepare_generator("#async-fn-pinned", &inactive, &main);
            let generated = generate(&planning).unwrap();
            runtime_generated_outcome(planning, generated, NativeOutcome::Signal(4));
        }
    }

    #[test]
    fn pinned_enum_array_anchors_ignore_inactive_prototype_variants() {
        let function = "(#fn work (: choose #bool) #u64
          (#let-mut owner (#array Choice 2) (#array-of (#array Choice 2)
            (Left (#array-of (#array #u64 2) 0u64 40u64))
            (Right (#array-of (#array #u64 2) 0u64 40u64))))
          (#let-mut outer #usize (#if choose 0usize 1usize))
          (#let-mut inner #usize 1usize)
          (#let view (#pin-ref-mut #u64) (#if choose
            (#pin-borrow-mut (#index (#pin-get-payload-mut (#pin-borrow-mut (#index owner outer)) Left 0) inner))
            (#pin-borrow-mut (#index (#pin-get-payload-mut (#pin-borrow-mut (#index owner outer)) Right 0) inner))))
          (#set outer 0usize) (#set inner 0usize)
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#unsafe (#pin-write view (#u64.+.wrap (#deref view) extra)))
          (#let answer #u64 (#deref view)) (#drop view) (#forget owner) (#return answer))";
        for choose in ["true", "false"] {
            let main = format!(
                "(#enum Choice (#linear) ((Left (#array #u64 2)) (Right (#array #u64 2))))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut task Work-frame (#call work (: choose {choose})))
                (#let first Work-poll-result (#call work-poll
                  (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready result) result)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget task) (#return answer))"
            );
            runtime_planned(prepare_generator("#async-fn-pinned", function, &main), 42);
            let heap = main.replace(
                "(#let-mut task Work-frame (#call work (: choose",
                "(#let pointer (#ptr-mut Work-frame) (#unsafe (#linux-syscall (#ptr-mut Work-frame) 9usize
                  (0usize (#size-of Work-frame) 3usize 34usize -1i64 0usize))))
                 (#let initial Work-frame (#call work (: choose",
            ).replace(
                "(#let first Work-poll-result",
                "(#let-mut task (#pin-own Work-frame) (#unsafe (#pin-own-of pointer initial)))
                 (#let first Work-poll-result",
            ).replace("(#pin-borrow-mut task)", "(#pin-own-borrow-mut task)")
             .replace("(#forget task) (#return answer)",
                    "(#forget next)
                 (#let allocation (#ptr-mut Work-frame) (#unsafe (#pin-release task)))
                 (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (allocation (#size-of Work-frame)))) 0i64))
                 (#return answer)");
            runtime_planned(prepare_generator("#async-fn-pinned", function, &heap), 42);
        }
    }

    #[test]
    fn owned_reference_transfers_take_contiguous_storage_without_a_tag_match() {
        let planning = prepare_generator(
            "#async-fn-pinned",
            "(#fn work (: source (#ref #u64)) #u64
              (#let holder Holder (#struct-literal Holder (: view source)))
              (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#let answer #u64 (#deref (#get holder view)))
              (#forget holder) (#return (#u64.+.wrap answer extra)))",
            "(#struct Holder (#linear) (: view (#ref #u64)))
             (#fn main () #u64 (#return 0u64))",
        );
        let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let binding = planning.functions[0]
            .graph
            .bindings
            .iter()
            .position(|binding| binding.name == "holder")
            .unwrap();
        let index = emitter.bindings[&BindingId(binding)];
        assert!(!emitter.slots[index].raw);
        assert!(emitter.slots[index].words.is_some());
        *emitter.physical_current.borrow_mut() = Some(vec![true; emitter.slots.len()]);
        let transfer = emitter.read(index, true);
        assert!(!transfer.contains("#match"), "{transfer}");
        assert!(transfer.contains("#word-take"), "{transfer}");
        assert!(!transfer.contains("#pin-write"), "{transfer}");
        assert!(!emitter.physical_current.borrow().as_ref().unwrap()[index]);
        let generated = generate(&planning).unwrap();
        crate::CheckedProgram::validate_with_span(&program(&planning, &generated).unwrap())
            .unwrap();
    }

    #[test]
    fn reference_free_aggregate_bindings_and_temporaries_have_no_occupancy_tags() {
        let planning = prepare(
            "(#let child Child (Start seed))
             (#let amount #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
             (#forget child) (#return (#u64.+.wrap seed amount))",
            "(#fn main () #u64 (#return 0u64))",
        );
        let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let definitions = emitter.slot_definitions();
        let mut aggregates = 0;
        for index in emitter.values.values().chain(emitter.bindings.values()) {
            let slot = &emitter.slots[*index];
            let ty =
                crate::typed_ir::resolve_type(&slot.ty, &planning.declarations.aliases).unwrap();
            if slot.raw
                || matches!(ty, Type::Unit | Type::Never)
                || emitter.types.contains_reference(&ty)
            {
                continue;
            }
            let region = slot
                .words
                .as_ref()
                .expect("reference-free binding or temporary must be untagged");
            assert_eq!(
                region.capacity,
                crate::codegen::storage_word_count(
                    &ty,
                    &planning.declarations.structs,
                    &planning.declarations.enums,
                )
                .unwrap()
            );
            assert!(!definitions.contains(&format!("(#enum {} (#linear) ", slot.name)));
            assert!(!definitions.contains(&format!("(#unsafe-fn {} ", slot.take)));
            if matches!(ty, Type::Named(_) | Type::Array(_, _) | Type::Tuple(_)) {
                aggregates += 1;
            }
        }
        assert!(aggregates > 0, "fixture must cover a whole aggregate value");
        let generated = generate(&planning).unwrap();
        crate::CheckedProgram::validate_with_span(&program(&planning, &generated).unwrap())
            .unwrap();
    }

    #[test]
    fn contiguous_clone_snapshot_does_not_consume_original_cells() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut owner Owner (#struct-literal Owner (: kept seed : item (#struct-literal Token (: value 1u64)))))
          (#let moved Token (#get owner item)) (#forget moved)
          (#set-field owner item (#struct-literal Token (: value 2u64)))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#forget owner) (#return seed))";
        let main = "(#struct Token (#linear) (: value #u64))
          (#struct Owner () (: kept #u64 : item Token))";
        let planning = prepare_generator("#async-fn-pinned", function, main);
        let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let owner = planning.functions[0]
            .graph
            .bindings
            .iter()
            .position(|binding| binding.name == "owner")
            .unwrap();
        let aggregate = &emitter.aggregates[&BindingId(owner)];
        assert!(aggregate
            .fields
            .iter()
            .any(|field| emitter.slots[field.slot].linear));
        assert!(aggregate
            .fields
            .iter()
            .all(|field| emitter.slots[field.slot].words.is_some()));
        *emitter.occupancy_trace.borrow_mut() = Some(OccupancyTrace::default());
        emitter.clone_aggregate(BindingId(owner), &[]).unwrap();
        let trace = emitter.occupancy_trace.borrow_mut().take().unwrap();
        assert!(
            trace.writes.is_empty(),
            "snapshot changed original occupancy: {:?}",
            trace.writes
        );
    }

    #[test]
    fn erased_thin_handles_keep_pointer_words_and_checked_anchors() {
        let planning = prepare_generator(
            "#async-fn-pinned",
            "(#fn work (: seed #u64) #u64
              (#let owner #u64 seed)
              (#let view (#ref #u64) (#borrow owner))
              (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#deref view) extra)))",
            "",
        );
        let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let definitions = emitter.slot_definitions();
        let mut handles = 0;
        for (index, slot) in emitter
            .slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.raw)
        {
            handles += 1;
            let words = slot.words.as_ref().expect("erased handles need no tag");
            assert_eq!(words.capacity, 1);
            assert_eq!(words.owner, slot.storage);
            assert!(matches!(words.owner, Type::RawPointer { .. }));
            assert!(slot.anchor.is_some());
            assert!(!definitions.contains(&format!("(#enum {} (#linear) ", slot.name)));
            assert!(!definitions.contains(&format!("(#unsafe-fn {} ", slot.take)));
            let read = emitter.read(index, false);
            assert!(read.contains("#word-read (#ptr"));
            assert!(!read.contains(&slot.peek));
        }
        assert!(handles > 0);
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        crate::CheckedProgram::validate_with_span(&program).unwrap();
        for property in [crate::ThreadProperty::Send, crate::ThreadProperty::Sync] {
            assert!(!crate::type_has_thread_property(
                &program,
                &Type::Named(generated[0].frame.clone()),
                property
            )
            .unwrap());
        }
    }

    #[test]
    fn contiguous_erasure_preserves_structural_thread_properties() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut owner Owner (#struct-literal Owner (: kept seed
            : pointer (#ptr-null (#ptr #u64)) : item (#struct-literal Token (: value 1u64)))))
          (#let kept (#ref #u64) (#borrow (#get owner kept)))
          (#let moved Token (#get owner item)) (#forget moved)
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#set-field owner item (#struct-literal Token (: value extra)))
          (#let answer #u64 (#deref kept)) (#forget kept) (#forget owner) (#return answer))";
        let main = "(#struct Token (#linear) (: value #u64))
          (#struct Owner () (: kept #u64 : pointer (#ptr #u64) : item Token))";
        let planning = prepare_generator("#async-fn-pinned", function, main);
        let generated = generate(&planning).unwrap();
        assert!(generated[0].source.contains("(#array Owner 0)"));
        let program = program(&planning, &generated).unwrap();
        crate::CheckedProgram::validate_with_span(&program).unwrap();
        for property in [crate::ThreadProperty::Send, crate::ThreadProperty::Sync] {
            assert!(!crate::type_has_thread_property(
                &program,
                &Type::Named(generated[0].frame.clone()),
                property
            )
            .unwrap());
        }
    }

    #[test]
    fn specialized_physical_occupancy_matches_native_pending_cell_tags() {
        let function = "(#fn work (: seed #u64 : external (#ref #u64)) #u64
          (#let-mut owner Owner (#struct-literal Owner (: kept seed : item (#struct-literal Token (: value 1u64)))))
          (#let kept (#ref #u64) (#borrow (#get owner kept)))
          (#let moved Token (#get owner item)) (#forget moved)
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let last #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#set-field owner item (#struct-literal Token (: value last)))
          (#let answer #u64 (#u64.+.wrap (#deref kept) extra))
          (#assert (#u64.== (#deref external) 0u64))
          (#forget kept) (#forget owner) (#return answer))";
        let main = "(#struct Token (#linear) (: value #u64))
          (#struct Owner () (: kept #u64 : item Token))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 40u64 : external (#borrow waker))))
            (#let-else (work-pending first) Work-poll-result (#call work-poll
              (: task (#pin-borrow-mut task) : waker (#borrow waker))) (#unreachable))
            (#let-else (work-pending second) Work-poll-result (#call work-poll
              (: task first : waker (#borrow waker))) (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task second : waker (#borrow waker)))
              (#case (work-ready value) value)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget first) (#forget second) (#forget task) (#return answer))";
        let planning = prepare_generator("#async-fn-pinned", function, main);
        let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let expected = Emitter::new(&planning, &planning.functions[0])
            .unwrap()
            .emit()
            .unwrap()
            .source;
        let specialization = emitter.check_owned_cells().unwrap();
        // Tracing is repeatable and must not consume gensyms, retain probe
        // helpers or alter the subsequent ordinary generated source.
        assert_eq!(expected, emitter.emit().unwrap().source);
        let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let physical_start = specialization.states[0].before.len() - emitter.slots.len();
        assert_eq!(
            &specialization.states[0].before[physical_start..],
            emitter.initial_occupancy()
        );
        let child = planning.functions[0]
            .graph
            .blocks
            .iter()
            .find_map(|block| match block.terminator {
                Terminator::Await { child, .. } => Some(child),
                _ => None,
            })
            .unwrap();
        let child_slot = emitter.values[&child];
        let await_state = specialization.states.iter().find(|state|
            matches!(planning.functions[0].graph.blocks[state.block].terminator, Terminator::Await { child: value, .. } if value == child)).unwrap();
        assert!(!await_state.after[physical_start + child_slot]);
        assert!(
            !specialization.states[await_state.successors[0]].before[physical_start + child_slot]
        );
        assert!(
            specialization.states[await_state.successors[1]].before[physical_start + child_slot]
        );
        let pending_states = specialization
            .states
            .iter()
            .filter(|state| {
                matches!(
                    planning.functions[0].graph.blocks[state.block].terminator,
                    Terminator::Await { .. }
                )
            })
            .map(|state| state.successors[1])
            .collect::<HashSet<_>>();
        let cases = specialization
            .states
            .iter()
            .enumerate()
            .filter(|(pc, _)| pending_states.contains(pc))
            .map(|(pc, state)| {
                let checks = emitter
                    .slots
                    .iter()
                    .enumerate()
                    .filter(|(_, slot)| slot.words.is_none())
                    .chain(
                        emitter
                            .slots
                            .iter()
                            .enumerate()
                            .filter(|(_, slot)| slot.words.is_some()),
                    )
                    .map(|(cell, slot)| {
                        if slot.words.is_some() {
                            // There is no runtime initialization tag for a
                            // word region. Native address/value parity is
                            // checked by async_contiguous_storage instead.
                            return String::new();
                        }
                        format!(
                            "(#assert (#variant-is {} {}))",
                            Emitter::slot_ref(slot, false),
                            if state.before[physical_start + cell] {
                                &slot.full
                            } else {
                                &slot.empty
                            },
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("(#case {pc}u32 (#block {checks} ()))")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let oracle = format!("(#match (#get task pc) {cases} (#case _ (#unreachable)))");
        let mut generated = generate(&planning).unwrap();
        let pending = "(#return (work-pending task))";
        assert!(generated[0].source.contains(pending));
        let uninstrumented = generated[0].source.clone();
        let instrumented = uninstrumented.replace(pending, &format!("{oracle} {pending}"));
        generated[0].source = crate::generator::format_generated_source(&instrumented).unwrap();
        let seed = emitter
            .slots
            .iter()
            .find(|slot| {
                slot.words.is_none()
                    && oracle.contains(&format!(
                        "(#assert (#variant-is {} {}))",
                        Emitter::slot_ref(slot, false),
                        slot.full
                    ))
            })
            .expect("a pending owner or retained reference still has a typed cell");
        let correct = format!(
            "(#assert (#variant-is {} {}))",
            Emitter::slot_ref(seed, false),
            seed.full
        );
        let incorrect = format!(
            "(#assert (#variant-is {} {}))",
            Emitter::slot_ref(seed, false),
            seed.empty
        );
        assert!(oracle.contains(&correct));
        let bad_oracle = oracle.replace(&correct, &incorrect);
        let bad = Generated {
            frame: generated[0].frame.clone(),
            origin: generated[0].origin,
            source: crate::generator::format_generated_source(
                &uninstrumented.replace(pending, &format!("{bad_oracle} {pending}")),
            )
            .unwrap(),
        };
        runtime_generated(planning, generated, 42);
        // Prove that the native oracle is reached, not just type-checked.
        runtime_generated_outcome(
            prepare_generator("#async-fn-pinned", function, main),
            vec![bad],
            NativeOutcome::Signal(4),
        );
    }

    #[test]
    fn primitive_values_skip_cell_tags_and_preserve_stack_and_heap_layouts() {
        let function = "(#fn work (: seed #u64) #u64
          (#let pair Pair (#struct-literal Pair (: left seed : right 0u64)))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#return (#u64.+.wrap (#u64.+.wrap (#get pair left) (#get pair right)) extra)))";
        for heap in [false, true] {
            let construct = "(#call work (: seed 40u64))";
            let setup = if heap {
                format!(
                    "(#let initial Work-frame {construct})
                  (#let pointer (#ptr-mut Work-frame) (#unsafe (#linux-syscall (#ptr-mut Work-frame)
                  9usize (0usize (#size-of Work-frame) 3usize 34usize -1i64 0usize))))
                  (#let-mut task (#pin-own Work-frame) (#unsafe (#pin-own-of pointer initial)))"
                )
            } else {
                format!("(#let-mut task Work-frame {construct})")
            };
            let borrow = if heap {
                "pin-own-borrow-mut"
            } else {
                "pin-borrow-mut"
            };
            let finish = if heap {
                "(#let raw (#ptr-mut Work-frame) (#unsafe (#pin-release task)))
                 (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (raw (#size-of Work-frame)))) 0i64))"
            } else {
                "(#forget task)"
            };
            let main = format!(
                "(#struct Pair () (: left #u64 : right #u64))
              (#fn main () #u64
                (#let waker #u64 0u64) {setup}
                (#let-else (work-pending next) Work-poll-result (#call work-poll
                  (: task (#{borrow} task) : waker (#borrow waker))) (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready value) value)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget next) {finish} (#return answer))"
            );
            let planning = prepare_generator("#async-fn-pinned", function, &main);
            let emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
            let definitions = emitter.slot_definitions();
            let mut copies = 0;
            let mut owners = 0;
            for slot in &emitter.slots {
                if slot.raw
                    || emitter.types.contains_reference(&slot.storage)
                    || matches!(slot.ty, Type::Unit | Type::Never)
                {
                    continue;
                }
                if slot.words.is_some() {
                    if slot.linear {
                        owners += 1;
                    } else {
                        copies += 1;
                    }
                    assert!(!definitions.contains(&format!("(#enum {} (#linear) ", slot.name)));
                    assert!(!definitions.contains(&format!("(#unsafe-fn {} ", slot.take)));
                } else {
                    panic!(
                        "reference-free concrete binding or value remains tagged: {}",
                        slot.field
                    );
                }
            }
            assert!(copies > 0 && owners > 0);
            runtime_planned(planning, 42);
        }
    }

    #[test]
    fn plain_copy_release_preserves_initialized_source_storage_across_pending() {
        let function = "(#fn work (: seed #u64) #u64
          (#let owner #u64 seed) (#forget owner)
          (#let view (#ref #u64) (#borrow owner))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#return (#u64.+.wrap (#deref view) extra)))";
        let main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 42u64)))
          (#let-else (work-pending next) Work-poll-result (#call work-poll
            (: task (#pin-borrow-mut task) : waker (#borrow waker))) (#unreachable))
          (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let projected = function.replace(
            "(#let owner #u64 seed) (#forget owner)",
            "(#let pair Pair (#struct-literal Pair (: left seed : right 0u64)))
             (#forget (#get pair left)) (#let owner #u64 (#get pair left)) (#forget pair)",
        );
        let projected_main = format!("(#struct Pair () (: left #u64 : right #u64))\n{main}");
        let planning = prepare_generator("#async-fn-pinned", &projected, &projected_main);
        assert!(Emitter::new(&planning, &planning.functions[0])
            .unwrap()
            .aggregates
            .is_empty());
        runtime_planned(planning, 42);
    }

    #[test]
    fn nested_exclusive_pattern_storage_survives_loop_and_consecutive_polls() {
        let source = include_str!("../../examples/async_destructure.lim")
            .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref-mut #u64))")
            .replace("(#as right #u64)", "(#deref right)")
            .replace(
                "(#let waker #u64",
                "(#let-mut owner #u64 11u64) (#let waker #u64",
            )
            .replace("9u16 11u16", "9u16 (#borrow-mut owner)");
        let loop_syntax = crate::prepare_program_syntax(
            &source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        runtime_planned(
            crate::generator::async_prepare::prepare(&loop_syntax).unwrap(),
            42,
        );
        let source = format!(
            "{}
          (#fn main () #u64
            (#let-mut owner #u64 11u64)
            (#let waker #u64 0u64)
            (#let frame Work-task (#call work (: values
              (#struct-literal Values (: a 22u64 : z
                (#tuple (#tuple #u16 (#ref-mut #u64)) 9u16 (#borrow-mut owner)))))))
            (#let-else (work-pending first) Work-poll-result
              (#call work-poll (: task frame : waker (#borrow waker))) (#unreachable))
            (#let-else (work-pending second) Work-poll-result
              (#call work-poll (: task first : waker (#borrow waker))) (#unreachable))
            (#let-else (work-ready value) Work-poll-result
              (#call work-poll (: task second : waker (#borrow waker))) (#unreachable))
            (#return value))",
            source.split_once("(#fn main").unwrap().0
        );
        let syntax = crate::prepare_program_syntax(
            &source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        runtime_planned(
            crate::generator::async_prepare::prepare(&syntax).unwrap(),
            42,
        );
        let cancelled = format!(
            "{} (#forget first) (#set owner 42u64) (#return owner))",
            source
                .split_once("(#let-else (work-pending second)")
                .unwrap()
                .0,
        );
        let syntax = crate::prepare_program_syntax(
            &cancelled,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        runtime_planned(
            crate::generator::async_prepare::prepare(&syntax).unwrap(),
            42,
        );
        let invalid = source.replace(
            "(#let-else (work-ready value)",
            "(#set owner 99u64) (#let-else (work-ready value)",
        );
        let syntax = crate::prepare_program_syntax(
            &invalid,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        let planning = crate::generator::async_prepare::prepare(&syntax).unwrap();
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("a Pending exclusive frame retains its external loan");
        assert_eq!(code, crate::DiagnosticCode::Borrow, "{message}");
        let span = span.expect("retained exclusive loan keeps the assignment span");
        assert_eq!(&invalid[span.start..span.end], "#set", "{message}");
        assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    }

    fn runtime_planned(planning: Planning, expected: i32) -> Vec<Generated> {
        let generated = generate(&planning).unwrap();
        runtime_generated(planning, generated, expected)
    }

    fn runtime_generated(
        planning: Planning,
        generated: Vec<Generated>,
        expected: i32,
    ) -> Vec<Generated> {
        runtime_generated_outcome(planning, generated, NativeOutcome::Exit(expected))
    }

    enum NativeOutcome {
        Exit(i32),
        Signal(i32),
    }

    fn runtime_generated_outcome(
        planning: Planning,
        generated: Vec<Generated>,
        expected: NativeOutcome,
    ) -> Vec<Generated> {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
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
        let launch_deadline = Instant::now() + Duration::from_secs(5);
        let mut child = loop {
            match Command::new(&binary).spawn() {
                Ok(child) => break child,
                Err(error)
                    if error.kind() == std::io::ErrorKind::ExecutableFileBusy
                        && Instant::now() < launch_deadline =>
                {
                    std::thread::sleep(Duration::from_millis(1));
                }
                Err(error) => panic!("cannot launch {}: {error}", binary.display()),
            }
        };
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
        match expected {
            NativeOutcome::Exit(expected) => assert_eq!(
                status.code(),
                Some(expected),
                "{status:?}\n{}",
                generated[0].source
            ),
            NativeOutcome::Signal(expected) => {
                use std::os::unix::process::ExitStatusExt;
                assert_eq!(status.signal(), Some(expected), "{status:?}");
            }
        }
        generated
    }

    const RUN: &str = "
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-task (#call work (: seed 40u64)))
        (#loop
          (#match (#call work-poll (: task task : waker (#borrow waker)))
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready value) (#block (#return value) (#unreachable)))))
        (#return (#unreachable)))";

    #[test]
    fn computed_projected_clone_preserves_reference_origins() {
        let function = "(#fn work (: owner (#ref #u64)) #u64
          (#let duplicate Holder (#clone (#get (#call make-envelope (: reference owner)) item)))
          (#let delta #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#let result #u64 (#deref (#get duplicate reference)))
          (#forget duplicate) (#return result))";
        let main = "(#struct Holder (#linear) (: reference (#ref #u64)))
          (#struct Envelope () (: item Holder))
          (#fn make-envelope (: reference (#ref #u64)) Envelope
            (#return (#struct-literal Envelope
              (: item (#struct-literal Holder (: reference reference))))))
          (#fn main () #u64
            (#let owner #u64 42u64) (#let waker #u64 0u64)
            (#let first Work-poll-result (#call work-poll
              (: task (#call work (: owner (#borrow owner))) : waker (#borrow waker))))
            (#let-else (work-pending pending) Work-poll-result first (#unreachable))
            (#let second Work-poll-result (#call work-poll
              (: task pending : waker (#borrow waker))))
            (#return (#match second
              (#case (work-ready result) result)
              (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
        let generated = runtime_planned(prepare_function(function, main), 42);
        let standalone =
            crate::parse_program(&format!("{CONTEXT}\n{}\n{main}", generated[0].source)).unwrap();
        crate::CheckedProgram::validate(&standalone).unwrap();
        let tuple_function = function.replace(
            "(#get (#call make-envelope (: reference owner)) item)",
            "(#get (#call make-tuple (: reference owner)) 0)",
        );
        assert_ne!(tuple_function, function);
        let tuple_main = format!(
            "{main}\n(#fn make-tuple (: reference (#ref #u64)) (#tuple Holder #u64)
          (#return (#tuple (#tuple Holder #u64)
            (#struct-literal Holder (: reference reference)) 0u64)))"
        );
        runtime_planned(prepare_function(&tuple_function, &tuple_main), 42);
        let hooked_main = main
            .replace(
                "(#struct Holder (#linear) (: reference (#ref #u64)))",
                "(#struct Holder (#linear) (: reference (#ref #u64) : offset #u64))",
            )
            .replace(
                "(#struct-literal Holder (: reference reference))",
                "(#struct-literal Holder (: reference reference : offset 0u64))",
            );
        let hooked_main = format!(
            "{hooked_main}\n(#fn Holder-clone (: source Holder) Holder
          (#let reference (#ref #u64) (#get source reference))
          (#let offset #u64 (#u64.+.wrap (#get source offset) 1u64))
          (#forget source)
          (#return (#struct-literal Holder (: reference reference : offset offset))))"
        );
        let hooked_function = function.replace(
            "(#let result #u64 (#deref (#get duplicate reference)))",
            "(#let result #u64 (#u64.+.wrap (#deref (#get duplicate reference)) (#get duplicate offset)))",
        );
        assert_ne!(hooked_function, function);
        runtime_planned(prepare_function(&hooked_function, &hooked_main), 43);

        let reused_function = function
            .replace(
                "(#let delta #u64",
                "(#let original Envelope (#call make-envelope (: reference owner)))\n          (#let delta #u64",
            )
            .replace(
                "(#let result #u64 (#deref (#get duplicate reference)))",
                "(#let result #u64 (#u64.+.wrap (#deref (#get duplicate reference)) (#deref (#get (#get original item) reference))))\n          (#forget original)",
            );
        let mut reused = prepare_function(&reused_function, main);
        let callee = reused.declarations.function_id("make-envelope").unwrap();
        let body_name = reused.functions[0].model.body_name.clone();
        let graph = &mut reused.functions[0].graph;
        let calls = graph
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(block, body)| {
                body.actions
                    .iter()
                    .enumerate()
                    .filter_map(move |(action, located)| match &located.action {
                        Action::Compute {
                            dst,
                            operation: Compute::Checked(operation),
                        } if operation.callee == Some(callee) => Some((block, action, *dst)),
                        _ => None,
                    })
            })
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 2);
        let (block, action, dst) = calls[1];
        // Both constructors in this fixture are pure and identical. Model
        // reuse explicitly, not general elimination of arbitrary user calls.
        graph.blocks[block].actions[action].action = Action::Compute {
            dst,
            operation: Compute::Identity(calls[0].2),
        };
        graph.validate().unwrap();
        graph
            .validate_against(&reused.declarations.bodies[&body_name])
            .unwrap();
        runtime_planned(reused, 84);
    }

    #[test]
    fn reused_computed_reference_owner_remains_available_after_cloning() {
        let function = "(#fn work (: owner (#ref #u64)) #u64
          (#let duplicate Holder (#clone (#call make-holder (: reference owner))))
          (#let original Holder (#call make-holder (: reference owner)))
          (#let delta #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#let result #u64 (#u64.+.wrap (#deref (#get duplicate reference))
            (#u64.+.wrap (#deref (#get original reference)) delta)))
          (#forget duplicate) (#forget original) (#return result))";
        let main = "(#struct Holder (#linear) (: reference (#ref #u64)))
          (#fn make-holder (: reference (#ref #u64)) Holder
            (#return (#struct-literal Holder (: reference reference))))
          (#fn main () #u64
            (#let-mut owner #u64 21u64) (#let waker #u64 0u64)
            (#let first Work-poll-result (#call work-poll
              (: task (#call work (: owner (#borrow owner))) : waker (#borrow waker))))
            (#let-else (work-pending pending) Work-poll-result first (#unreachable))
            (#let second Work-poll-result (#call work-poll
              (: task pending : waker (#borrow waker))))
            (#return (#match second
              (#case (work-ready result) result)
              (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
        fn reuse_constructor(planning: &mut Planning) {
            // Model reuse of the first pure constructor's computed value.
            // This fixture has no allocation, IO or observable clone hook;
            // do not apply this transformation to arbitrary user calls.
            let callee = planning.declarations.function_id("make-holder").unwrap();
            let body_name = planning.functions[0].model.body_name.clone();
            let graph = &mut planning.functions[0].graph;
            let calls = graph
                .blocks
                .iter()
                .enumerate()
                .flat_map(|(block, body)| {
                    body.actions
                        .iter()
                        .enumerate()
                        .filter_map(move |(action, located)| match &located.action {
                            Action::Compute {
                                dst,
                                operation: Compute::Checked(operation),
                            } if operation.callee == Some(callee) => Some((block, action, *dst)),
                            _ => None,
                        })
                })
                .collect::<Vec<_>>();
            assert_eq!(calls.len(), 2);
            let original = calls[0].2;
            assert!(graph
                .blocks
                .iter()
                .flat_map(|block| &block.actions)
                .any(|located| {
                    matches!(located.action, Action::Load { place, kind: LoadKind::Clone, .. }
                    if graph.places[place.0].root == AddressRoot::Value(original))
                }));
            let (block, action, dst) = calls[1];
            graph.blocks[block].actions[action].action = Action::Compute {
                dst,
                operation: Compute::Identity(original),
            };
            graph.validate().unwrap();
            graph
                .validate_against(&planning.declarations.bodies[&body_name])
                .unwrap();
        }
        let mut planning = prepare_function(function, main);
        reuse_constructor(&mut planning);
        let generated = runtime_planned(planning, 42);
        assert_eq!(
            generated[0]
                .source
                .split_whitespace()
                .filter(|token| *token == "make-holder")
                .count(),
            1
        );
        let standalone =
            crate::parse_program(&format!("{CONTEXT}\n{}\n{main}", generated[0].source)).unwrap();
        let checked = crate::CheckedProgram::validate(&standalone)
            .expect("reused computed owners check without async witnesses");
        crate::codegen::generate_checked_executable_assembly(
            &checked,
            crate::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();

        let invalid = main.replace(
            "(#let second Work-poll-result",
            "(#set owner 99u64) (#let second Work-poll-result",
        );
        let mut planning = prepare_function(function, &invalid);
        reuse_constructor(&mut planning);
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("both owners retain their caller loan");
        assert_eq!(code, crate::DiagnosticCode::Borrow, "{message}");
        let span = span.expect("caller mutation has an original span");
        let source = &program.source_files[span.source_id as usize].source;
        let write = source.find("(#set owner 99u64)").unwrap();
        assert!(
            span.start >= write && span.end <= write + "(#set owner 99u64)".len(),
            "{span:?}: {source}"
        );
    }

    #[test]
    fn cleanup_is_uniform_and_does_not_reserve_a_private_state_api() {
        for kind in ["#async-fn", "#async-fn-pinned"] {
            let planning = prepare_generator(
                kind,
                "(#fn work (: seed #u64) #u64
                  (#return (#await Child ChildPending ChildReady child-poll (Start seed))))",
                "(#struct Work-frame-state () (: value #u64))",
            );
            let generated = generate(&planning).unwrap();
            let output = &generated[0];
            assert!(output.source.contains("(#fn work-poll-cleanup "));
            assert!(output
                .source
                .contains(&format!("(#struct {}-cleanup (#linear) ", output.frame)));
            assert!(!output.source.contains("work-poll-cancel"));
            assert!(!output.source.contains("Work-frame-state"));
            crate::CheckedProgram::validate(&program(&planning, &generated).unwrap()).unwrap();
        }
    }

    #[test]
    fn cleanup_and_destroy_reuse_specialized_occupancy_with_legacy_oracle() {
        let planning = prepare_generator(
            "#async-fn-pinned",
            "(#fn work (: seed #u64) #u64
              (#let owner Child (Start seed))
              (#let amount #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#forget owner) (#return (#u64.+.wrap seed amount)))",
            "",
        );
        let function = &planning.functions[0];
        let mut emitter = Emitter::new(&planning, function).unwrap();
        let owner = BindingId(
            function
                .graph
                .bindings
                .iter()
                .position(|binding| binding.name == "owner")
                .unwrap(),
        );
        assert!(!emitter.reference_cells.as_ref().is_some_and(|plan| plan
            .cancel_live
            .contains(&crate::generator::async_cells::Cell::Binding(owner))));
        let before = crate::generator::async_cells::CANCELLATION_SOLVES.with(|count| count.get());
        assert!(emitter.cleanup_occupied_cache.get().is_none());
        assert!(emitter
            .cleanup_occupied()
            .contains(&emitter.bindings[&owner]));
        assert!(std::ptr::eq(
            emitter.cleanup_occupied(),
            emitter.cleanup_occupied()
        ));
        assert_eq!(
            crate::generator::async_cells::CANCELLATION_SOLVES.with(|count| count.get()),
            before + 1
        );
        emitter.add_slot("test-extra".into(), Type::U64);
        assert!(emitter.cleanup_occupied_cache.get().is_none());
        emitter.cleanup_occupied();
        assert_eq!(
            crate::generator::async_cells::CANCELLATION_SOLVES.with(|count| count.get()),
            before + 2
        );
        // Extra test storage is not part of the graph; use a fresh emitter to
        // exercise all actual cleanup/destroy emission call paths.
        let before = crate::generator::async_cells::CANCELLATION_SOLVES.with(|count| count.get());
        let generated = Emitter::new(&planning, function).unwrap().emit().unwrap();
        assert_eq!(
            crate::generator::async_cells::CANCELLATION_SOLVES.with(|count| count.get()),
            before
        );
        crate::CheckedProgram::validate(&program(&planning, &[generated]).unwrap()).unwrap();
    }

    #[test]
    #[ignore = "manual cancellation-analysis microbenchmark"]
    fn benchmark_async_cancellation_occupancy() {
        let mut body = String::new();
        for index in 0..16 {
            body.push_str(&format!("(#let owner-{index} Child (Start seed))\n"));
            body.push_str(&format!("(#let value-{index} #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))\n"));
        }
        for index in 0..16 {
            body.push_str(&format!("(#forget owner-{index})\n"));
        }
        body.push_str("(#return seed)");
        let planning = prepare_generator(
            "#async-fn-pinned",
            &format!("(#fn work (: seed #u64) #u64 {body})"),
            "",
        );
        let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        let expected = emitter.compute_cleanup_occupied();
        assert!(!expected.is_empty());
        let mut uncached = Vec::new();
        let mut cached = Vec::new();
        for _ in 0..11 {
            let started = Instant::now();
            for _ in 0..20 {
                for _ in 0..3 {
                    assert_eq!(
                        std::hint::black_box(emitter.compute_cleanup_occupied()),
                        expected
                    );
                }
            }
            uncached.push(started.elapsed().as_nanos());
            let started = Instant::now();
            for _ in 0..20 {
                emitter.cleanup_occupied_cache.take();
                for _ in 0..3 {
                    assert_eq!(std::hint::black_box(emitter.cleanup_occupied()), &expected);
                }
            }
            cached.push(started.elapsed().as_nanos());
        }
        uncached.sort_unstable();
        cached.sort_unstable();
        eprintln!("cancellation occupancy, 20 emitters x 3 queries: uncached median={} us cached median={} us reduction={:.1}%",
            uncached[5] / 1000, cached[5] / 1000, 100.0 * (1.0 - cached[5] as f64 / uncached[5] as f64));
    }

    #[test]
    fn owning_cell_initializers_check_empty_before_extracting_pinned_storage() {
        let planning = prepare(
            "(#let child Child (Start seed)) (#forget child) (#return seed)",
            "(#struct RefOwner (#linear) (: view (#ref-mut #u64)))
             (#fn main () #u64 (#return 0u64))",
        );
        let mut emitter = Emitter::new(&planning, &planning.functions[0]).unwrap();
        // Exercise typed-cell helpers separately from word-backed production
        // owners. Reference-bearing storage still uses this guarded fallback.
        let owner_index = emitter.add_slot("test-typed-owner".into(), Type::Named("Child".into()));
        let owner = &emitter.slots[owner_index];
        let put_name = owner.put.clone();
        let empty = owner.empty.clone();
        let source = emitter.slot_definitions();
        let function = source.split(&format!("(#fn {put_name} ")).nth(1).unwrap();
        let guard = function
            .find(&format!("(#assert (#variant-is slot {empty}))"))
            .unwrap();
        assert!(guard < function.find("(#pin-read slot)").unwrap());

        // The inline path stages an owned reference-containing value first,
        // but must guard its destination before the destructive read as well.
        let slot = emitter.add_slot("test-owner".into(), Type::Named("RefOwner".into()));
        let inline = emitter.put(slot, "incoming-reference");
        let guard = inline.find("(#assert (#variant-is ").unwrap();
        assert!(inline.find("incoming-reference").unwrap() < guard);
        assert!(guard < inline.find("(#pin-read ").unwrap());

        // Exercise the remaining typed-cell fallback independently of the
        // production primitive word-storage selection.
        let copy_index = emitter.add_slot("test-copy".into(), Type::U64);
        let copy = &emitter.slots[copy_index];
        let source = emitter.slot_definitions();
        let function = source.split(&format!("(#fn {} ", copy.put)).nth(1).unwrap();
        let function = function.split("(#fn ").next().unwrap();
        assert!(
            !function.contains("(#assert (#variant-is"),
            "Copy assignments remain overwritable"
        );
    }

    #[test]
    fn owning_cell_initializers_trap_on_full_and_accept_empty() {
        for occupied in [false, true] {
            let body = "(#let child Child (Start seed)) (#forget child) (#return seed)";
            let initial = prepare(body, "(#fn main () #u64 (#return 0u64))");
            let mut emitter = Emitter::new(&initial, &initial.functions[0]).unwrap();
            let before = emitter.slot_definitions();
            let index = emitter.add_slot("test-typed-owner".into(), Type::Named("Child".into()));
            let definitions = emitter.slot_definitions();
            let definitions = definitions.strip_prefix(&before).unwrap();
            let slot = &emitter.slots[index];
            let constructor = if occupied {
                format!("({} (Start 1u64))", slot.full)
            } else {
                format!("({})", slot.empty)
            };
            let main = format!("(#fn main () #u64
              (#let-mut cell {name} {constructor})
              (#call {put} (: slot (#pin-borrow-mut cell) : value (Start 42u64)))
              (#let value Child (#unsafe (#call {take} (: slot (#pin-borrow-mut cell)))))
              (#forget cell)
              (#return (#match value (#case (Start answer) answer) (#case (Resume answer) answer))))",
              name=slot.name, put=slot.put, take=slot.take);
            let planning = prepare(body, &main);
            let mut generated = generate(&planning).unwrap();
            generated[0].source = crate::generator::format_generated_source(&format!(
                "{}\n{definitions}",
                generated[0].source
            ))
            .unwrap();
            runtime_generated_outcome(
                planning,
                generated,
                if occupied {
                    NativeOutcome::Signal(4)
                } else {
                    NativeOutcome::Exit(42)
                },
            );
        }
    }

    #[test]
    fn dispatcher_executes_nested_branches_and_loops_across_pending() {
        let generated = runtime(
            "
          (#let-mut total #u64 seed)
          (#for (#let-mut index #u64 0u64) (#u64.< index 2u64) (#set index (#u64.+.wrap index 1u64))
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
          (#let result #u64 (#await Child ChildPending ChildReady child-poll resource))
          (#return (#u64.+.wrap result 2u64))";
        runtime(body, RUN, 42);
        let error = prepare_generator_result(
            "#async-fn",
            "(#fn work (: seed #u64) #u64
          (#let resource Child (Start seed))
          (#let result #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
          (#return result))",
            RUN,
        )
        .err()
        .unwrap();
        assert_eq!(error.code, DiagnosticCode::Linear);
        let span = error.span.unwrap();
        assert_eq!(span.source_id, 0);
        assert_eq!(
            &error.source_text.unwrap()[span.start..span.end],
            "resource"
        );
    }

    #[test]
    fn value_break_and_outer_transfer_paths_reach_selected_continuations() {
        runtime(
            "
          (#let result #u64 (#label outer (#loop
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Start seed)))
            (#loop (#break-to outer (#u64.+.wrap result 2u64))))))
          (#return result)",
            RUN,
            42,
        );
    }

    #[test]
    fn pending_retries_polling_without_repeating_child_construction() {
        let main = "
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let first Work-poll-result (#call work-poll (: task (#call work (: seed 40u64)) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready value) value)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";
        runtime("(#return (#u64.+.wrap seed (#await Child ChildPending ChildReady child-poll (Start 2u64))))", main, 42);
    }

    #[test]
    fn guarded_copy_patterns_keep_scrutinees_across_rejected_awaits() {
        runtime(
            "
          (#return (#match (#tuple (#tuple #u64) seed)
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
          (#let pair (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) seed 2u64))
          (#let (#tuple first second) (#tuple #u64 #u64) pair)
          (#return (#if-let (#tuple value) (#tuple (#tuple #u64) first)
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
            "(#struct Leaf (#linear) ((number #u64) (enabled #bool)))
          (#struct Container (#linear) ((leaf Leaf) (items (#array #u64 2))))
          (#enum Owned (#linear) ((Packed Container) Absent))
          {RUN}"
        );
        runtime(
            "(#let owned Owned (Packed (#struct-literal Container
              (: leaf (#struct-literal Leaf (: number seed : enabled true))
               : items (#array-of (#array #u64 2) 1u64 2u64)))))
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
            "(#let tuple (#tuple Child #u64)
              (#tuple (#tuple Child #u64) (Start seed) 2u64))
          (#let (#tuple child bias) (#tuple Child #u64) tuple)
          (#return (#if-let (Start value) child
            (#u64.+.wrap bias (#await Child ChildPending ChildReady child-poll (Start value)))
            0u64))",
            RUN,
            42,
        );
    }

    #[test]
    fn rejected_linear_tests_retain_owners_and_short_circuit_payload_access() {
        let main = format!("(#type OwnedTuple (#tuple Child #u64)) {RUN}");
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
            "(#type Pair (#tuple #u64 #u64))
          (#struct Inner (#linear) ((padding #u64) (empty ()) (pair Pair)))
          (#struct Owner (#linear) ((padding #u64) (inner Inner)))
          {RUN}"
        );
        runtime(
            "(#let owner Owner (#struct-literal Owner
              (: padding 99u64 : inner (#struct-literal Inner
                (: padding 88u64 : empty () : pair (#tuple Pair seed 1u64))))))
          (#let empty () (#get (#get owner inner) empty))
          (#let first #u64 (#get (#get (#get owner inner) pair) 0))
          (#let second #u64 (#get (#get (#get owner inner) pair) 1))
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
            "(#type Pair (#array #u64 2))
          (#fn sum ((items Pair)) #u64
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
                if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#let" || head == "#let-mut")
                {
                    for child in items.iter().skip(3) {
                        constructor_heads(child, heads);
                    }
                    return;
                }
                if let [Expr::Symbol(head), Expr::List(ty), ..] = items.as_slice() {
                    if matches!(ty.first(), Some(Expr::Symbol(name)) if name == "#array") {
                        heads.push(head.clone());
                    }
                }
                let start = if matches!(items.first(), Some(Expr::Symbol(head))
                    if matches!(head.as_str(), "#array-of" | "#word-read" | "#word-write" | "#word-view"))
                {
                    2
                } else {
                    0
                };
                for child in items.iter().skip(start) {
                    constructor_heads(child, heads);
                }
            }
        }
        let mut heads = Vec::new();
        for expression in crate::parse(&generated[0].source).unwrap() {
            if let Expr::List(items) = &expression.expr {
                if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#fn" || head == "#unsafe-fn")
                {
                    for body in items.iter().skip(4) {
                        constructor_heads(body, &mut heads);
                    }
                }
            }
        }
        assert!(heads.iter().any(|head| head == "#array-of"));
        assert!(!heads.iter().any(|head| head == "#array"));
    }

    #[test]
    fn incoming_shared_handles_are_read_without_losing_their_loans() {
        for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
            let main = format!(
                "(#fn main () #u64
                (#let waker #u64 0u64) (#let value #u64 40u64)
                (#let view ({ty} #u64) ({borrow} value))
                (#let task Work-task (#call work (: value view)))
                (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#assert (#u64.== (#deref view) 40u64))
                (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready result) result)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))"
            );
            runtime_planned(
                prepare_function(
                    &format!(
                        "(#fn work ((value ({ty} #u64))) #u64
                        (#let loaded #u64 (#deref value))
                        (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
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
        let main = "(#fn main () #u64
          (#let waker #u64 0u64) (#let value #u64 20u64)
          (#let task Work-task (#call work (: value (#borrow value))))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready result) result)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";
        let generated = runtime_planned(
            prepare_function(
                "(#fn work (: value (#ref #u64)) #u64
              (#let alias (#ref #u64) value)
              (#let first #u64 (#deref value)) (#drop value)
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#u64.+.wrap first (#deref alias)) child)))",
                main,
            ),
            42,
        );
        assert!(generated[0].source.contains("retired-cell"));
    }

    #[test]
    fn selected_shared_handles_survive_branch_transfers_and_loop_retries() {
        let main = "(#fn main () #u64
          (#let waker #u64 0u64) (#let left #u64 20u64) (#let right #u64 99u64)
          (#let-mut task Work-task (#call work (: choose true : left (#borrow left) : right (#borrow right))))
          (#loop
            (#let result Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#match result
              (#case (work-pending next) (#block (#set task next) ()))
              (#case (work-ready answer) (#block (#return answer) ()))))
          (#return (#unreachable)))";
        runtime_planned(
            prepare_function(
                "(#fn work (: choose #bool : left (#ref #u64) : right (#ref #u64)) #u64
              (#let selected (#ref #u64) (#if choose left right))
              (#drop left) (#drop right)
              (#let-mut count #u64 0u64) (#let-mut sum #u64 0u64)
              (#while (#u64.< count 2u64)
                (#let before #u64 (#deref selected))
                (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
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
            "(#enum ReferenceStep () ((ReferenceStart (#ref #u64)) (ReferenceResume (#ref #u64))))
          (#enum ReferencePoll () ((ReferencePending ReferenceStep) (ReferenceReady (#ref #u64))))
          (#fn reference-poll (: task ReferenceStep : waker (#ref #u64)) ReferencePoll
            (#return (#match task
              (#case (ReferenceStart value) (ReferencePending (ReferenceResume value)))
              (#case (ReferenceResume value) (ReferenceReady value)))))";
        let function = "(#fn work (: value (#ref #u64)) #u64
          (#let before #u64 (#deref value))
          (#let step ReferenceStep (ReferenceStart value)) (#drop value)
          (#let after (#ref #u64)
            (#await ReferenceStep ReferencePending ReferenceReady reference-poll
              (#block (#let sending ReferenceStep step) (#drop step) sending)))
          (#return (#u64.+.wrap (#u64.+.wrap before (#deref after)) 2u64)))";
        let main = format!(
            "{extra}
          (#fn main () #u64
            (#let waker #u64 0u64) (#let value #u64 20u64)
            (#let task Work-task (#call work (: value (#borrow value))))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready result) result)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))"
        );
        let planning = prepare_function(function, &main);
        for checked in &planning.functions {
            let plan = crate::generator::async_retire::Plan::new(
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
                        "the restored Copy child is not retired before work-pending"
                    );
                }
            }
        }
        runtime_planned(planning, 42);

        // The source handle and its named child copy have both been released.
        // Only the actual suspended child keeps the referent borrowed now.
        let bad_main = format!(
            "{extra}
          (#fn main () #u64
            (#let waker #u64 0u64) (#let-mut value #u64 20u64)
            (#let task Work-task (#call work (: value (#borrow value))))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
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
        let extra = "(#enum ExclusiveChild (#linear) ((ExclusiveStart (#ref-mut #u64)) (ExclusiveResume (#ref-mut #u64))))

          (#enum ExclusivePoll () ((ExclusivePending ExclusiveChild) (ExclusiveReady #u64)))
          (#fn exclusive-poll (: task ExclusiveChild : waker (#ref #u64)) ExclusivePoll
            (#return (#match task
              (#case (ExclusiveStart view) (#block
                (#deref-set view (#u64.+.wrap (#deref view) 1u64))
                (ExclusivePending (ExclusiveResume view))))
              (#case (ExclusiveResume view) (#block
                (#deref-set view (#u64.+.wrap (#deref view) 1u64))
                (ExclusiveReady (#deref view)))))))";
        let function = "(#fn work (: view (#ref-mut #u64)) #u64
          (#let child ExclusiveChild (ExclusiveStart view))
          (#return (#await ExclusiveChild ExclusivePending ExclusiveReady exclusive-poll child)))";
        let main = format!(
            "{extra}
              (#fn main () #u64
                (#let waker #u64 0u64) (#let-mut value #u64 40u64)
                (#let task Work-task (#call work (: view (#borrow-mut value))))
                (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready answer) answer)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#assert (#u64.== value 42u64)) (#return answer))"
        );
        runtime_planned(prepare_function(function, &main), 42);
        let bad_main = main.replace(
            "(#let-else (work-pending next)",
            "(#set value 0u64) (#let-else (work-pending next)",
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
    fn exclusive_call_operands_retain_their_evaluated_handle_across_effects_and_awaits() {
        for amount in [
            "(#call later ())",
            "(#await Child ChildPending ChildReady child-poll (Start 2u64))",
        ] {
            let planning = prepare_generator("#async-fn-pinned",
                &format!(
                    "(#fn work (: view (#ref-mut #u64)) #u64
              (#let before #u64 (#deref view))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap before (#call read-view (: view view : amount {amount})))))"
                ),
                "(#fn read-view (: view (#ref-mut #u64) : amount #u64) #u64 (#return (#u64.+.wrap (#deref view) amount)))
              (#fn later () #u64 (#return 0u64))
              (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 20u64)
                (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
                (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
                (#let-mut answer #u64 0u64)
                (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
                  (#case (work-pending next) (#block (#set running next) ()))
                  (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
                (#drop running) (#forget task)
                (#return answer))",
            );
            runtime_planned(planning, if amount.contains("#await") { 42 } else { 40 });
        }
    }

    #[test]
    fn exclusive_returned_children_survive_pending_with_parent_permissions() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let function = format!(
                "(#fn work (: view ({ty} #u64)) #u64
                  (#let returned ({ty} #u64) (#call echo (: view view)))
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#deref returned) child)))"
            );
            let main = format!(
                "(#fn echo (: view ({ty} #u64)) ({ty} #u64) (#return view))
                  (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
                    (#let-mut task Work-frame (#call work (: view ({borrow} value))))
                    (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                      (#case (work-ready answer) answer)
                      (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                    (#forget task) (#set value 99u64) (#return answer))"
            );
            runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
            let bad = main.replace(
                "(#let-else (work-pending next)",
                "(#set value 99u64) (#let-else (work-pending next)",
            );
            let planning = prepare_generator("#async-fn-pinned", &function, &bad);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .unwrap();
            assert_eq!(error.1, DiagnosticCode::Borrow);
            let span = error.2.unwrap();
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                "#set"
            );
            let bad_function = function.replace(
                "(#let child #u64",
                "(#let invalid #u64 (#deref view)) (#let child #u64",
            );
            let planning = prepare_generator("#async-fn-pinned", &bad_function, &main);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .unwrap();
            assert_eq!(error.1, DiagnosticCode::Borrow);
            let span = error.2.unwrap();
            assert!((span.source_id as usize) < planning.program.source_files.len());
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                "#deref"
            );
        }
    }

    #[test]
    fn aggregate_returned_children_keep_evaluated_parents_across_later_awaits() {
        let function = "(#fn work (: view (#ref-mut #u64)) #u64
          (#let returned Holder (#call capture (: view view : amount
            (#await Child ChildPending ChildReady child-poll (Start 1u64)))))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
          (#let answer #u64 (#u64.+.wrap (#deref (#get returned view)) child))
          (#forget returned) (#drop view) (#return answer))";
        let main = "(#struct Holder (#linear) (: view (#ref-mut #u64)))
          (#fn capture (: view (#ref-mut #u64) : amount #u64) Holder
            (#deref-set view (#u64.+.wrap (#deref view) amount))
            (#return (#struct-literal Holder (: view view))))
          (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
            (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
            (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
            (#let-mut retries #u64 0u64) (#let-mut answer #u64 0u64)
            (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
              (#case (work-pending next) (#block (#set running next)
                (#set retries (#u64.+.wrap retries 1u64)) ()))
              (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
            (#drop running) (#forget task) (#set value 99u64)
            (#assert (#u64.== retries 2u64)) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let invalid = function.replace(
            "(#let child #u64",
            "(#deref-set view 99u64) (#let child #u64",
        );
        let planning = prepare_generator("#async-fn-pinned", &invalid, main);
        let generated = generate(&planning).unwrap();
        let proposed = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&proposed)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
        let span = error.2.unwrap();
        assert!((span.source_id as usize) < planning.program.source_files.len());
        assert_eq!(
            &proposed.source_files[span.source_id as usize].source[span.start..span.end],
            "#deref-set",
        );
        let first = "(#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))";
        let second =
            "(#let second Work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
          (#let-else (work-pending last) Work-poll-result second (#unreachable))";
        for (polls, handle, expected) in [
            (String::new(), "(#pin-borrow-mut task)", 40),
            (first.to_owned(), "next", 40),
            (format!("{first}\n{second}"), "last", 41),
        ] {
            let main = format!(
                "(#struct Holder (#linear) (: view (#ref-mut #u64)))
                  (#fn capture (: view (#ref-mut #u64) : amount #u64) Holder
                    (#deref-set view (#u64.+.wrap (#deref view) amount))
                    (#return (#struct-literal Holder (: view view))))
                  (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
                    (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
                    {polls}
                    (#let state Work-frame-cleanup (#call work-poll-cleanup (: task {handle})))
                    (#forget state) (#forget task)
                    (#assert (#u64.== value {expected}u64)) (#set value 99u64)
                    (#return 42u64))"
            );
            // A missing reference in an Empty input slot is not a fabricated
            // output loan. Transfer occupied linear holders to explicit user
            // cleanup, and allow the referent again only after that cleanup.
            runtime_planned(prepare_generator("#async-fn-pinned", function, &main), 42);
            if expected == 41 {
                let cleanup = "(#fn echo-state (: state Work-frame-cleanup) Work-frame-cleanup
                    (#return state))";
                let conflicting = format!("{cleanup}\n{}", main.replace(
                    "(#forget state) (#forget task)",
                    "(#set value 99u64) (#let observed Work-frame-cleanup (#call echo-state (: state state))) (#forget observed) (#forget task)",
                ));
                let planning = prepare_generator("#async-fn-pinned", function, &conflicting);
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                let error = crate::CheckedProgram::validate_with_span(&proposed)
                    .err()
                    .unwrap();
                assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
                let span = error.2.unwrap();
                assert!(
                    proposed.source_files[span.source_id as usize].source[span.start..span.end]
                        == *"#set",
                    "{} at {}",
                    error.0,
                    &proposed.source_files[span.source_id as usize].source[span.start..span.end]
                );
            }
        }
    }

    #[test]
    fn projected_exclusive_arguments_snapshot_before_later_suspension() {
        let declarations = "(#struct Holder (#linear) (: view (#ref-mut #u64)))
          (#fn capture (: view (#ref-mut #u64)) Holder
            (#return (#struct-literal Holder (: view view))))
          (#fn capture-tuple (: view (#ref-mut #u64)) (#tuple (#ref-mut #u64) #u64)
            (#return (#tuple view 0u64)))
          (#fn read (: view (#ref-mut #u64) : amount #u64) #u64
            (#return (#u64.+.wrap (#deref view) amount)))
          (#fn echo (: view (#ref-mut #u64) : amount #u64) (#ref-mut #u64)
            (#deref-set view (#u64.+.wrap (#deref view) amount)) (#return view))";
        let main = "(#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
            (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
            (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
            (#let-mut retries #u64 0u64) (#let-mut answer #u64 0u64)
            (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
              (#case (work-pending next) (#block (#set running next)
                (#set retries (#u64.+.wrap retries 1u64)) ()))
              (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
            (#drop running) (#forget task) (#set value 99u64)
            (#assert (#u64.== retries 1u64)) (#return answer))";
        for (ty, constructor, projected) in [
            (
                "Holder",
                "(#call capture (: view view))",
                "(#get owner view)",
            ),
            (
                "(#tuple (#ref-mut #u64) #u64)",
                "(#call capture-tuple (: view view))",
                "(#get owner 0)",
            ),
        ] {
            for (body, retries) in [
                (
                    format!(
                        "(#let answer #u64 (#call read (: view {projected} : amount
                    (#await Child ChildPending ChildReady child-poll (Start 2u64)))))"
                    ),
                    1,
                ),
                (
                    format!(
                        "(#let child (#ref-mut #u64) (#call echo (: view {projected} : amount
                    (#await Child ChildPending ChildReady child-poll (Start 2u64)))))
                    (#let later #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
                    (#let answer #u64 (#u64.+.wrap (#deref child) later)) (#drop child)"
                    ),
                    2,
                ),
            ] {
                let function = format!(
                    "(#fn work (: view (#ref-mut #u64)) #u64
                    (#let owner {ty} {constructor}) {body}
                    (#forget owner) (#drop view) (#return answer))"
                );
                let planning = prepare_generator(
                    "#async-fn-pinned",
                    &function,
                    &format!(
                        "{declarations}\n{}",
                        main.replace(
                            "(#u64.== retries 1u64)",
                            &format!("(#u64.== retries {retries}u64)")
                        )
                    ),
                );
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                if let Err((message, code, span, _)) =
                    crate::CheckedProgram::validate_with_span(&proposed)
                {
                    let span = span.unwrap();
                    panic!(
                        "{function}\n{code:?}: {message} at {}",
                        &proposed.source_files[span.source_id as usize].source
                            [span.start..span.end]
                    );
                }
                runtime_generated(planning, generated, 42);
                let invalid = function.replace(
                    "(#let answer #u64",
                    "(#deref-set view 99u64) (#let answer #u64",
                );
                let planning = prepare_generator(
                    "#async-fn-pinned",
                    &invalid,
                    &format!("{declarations}\n{main}"),
                );
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                let error = crate::CheckedProgram::validate_with_span(&proposed)
                    .err()
                    .unwrap();
                assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
                let span = error.2.unwrap();
                assert_eq!(
                    &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                    "#deref-set"
                );
            }
        }
    }

    #[test]
    fn retained_arguments_use_the_snapshot_not_the_replaced_parent() {
        let function = "(#fn work ((#mut view (#ref-mut #u64)) (other (#ref-mut #u64))) #u64
            (#let answer #u64 (#call read-view (: view view : amount
              (#block (#set view other)
                (#await Child ChildPending ChildReady child-poll (Start 2u64))))))
            (#assert (#u64.== (#deref view) 100u64)) (#return answer))";
        let main = "(#fn read-view (: view (#ref-mut #u64) : amount #u64) #u64
              (#return (#u64.+.wrap (#deref view) amount)))
            (#fn main () #u64 (#let waker #u64 0u64) (#let-mut first #u64 40u64) (#let-mut other #u64 100u64)
              (#let-mut task Work-frame (#call work (: view (#borrow-mut first) : other (#borrow-mut other))))
              (#let initial Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
              (#let-else (work-pending next) Work-poll-result initial (#unreachable))
              (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                (#case (work-ready answer) answer)
                (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
              (#forget task) (#set first 99u64) (#set other 99u64) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
    }

    #[test]
    fn computed_exclusive_results_retire_after_their_actual_leaf_read() {
        let function = "(#fn work (: view (#ref-mut #u64)) #u64
            (#let before #u64 (#deref (#call echo (: view view)))) (#drop view)
            (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
            (#return (#u64.+.wrap before child)))";
        let main = "(#fn echo (: view (#ref-mut #u64)) (#ref-mut #u64) (#return view))
            (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
              (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
              (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
              (#let-else (work-pending next) Work-poll-result first (#unreachable))
              (#set value 99u64)
              (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                (#case (work-ready answer) answer)
                (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
              (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
    }

    #[test]
    fn pinned_cancellation_transfers_only_initialized_children_to_explicit_cleanup() {
        for phase in ["initial", "pending", "ready"] {
            let planning = prepare_generator(
                "#async-fn-pinned",
                "(#fn work (: view (#ref-mut #u64)) #u64
                  (#let returned (#ref-mut #u64) (#call echo (: view view)))
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#deref returned) child)))",
                "(#fn echo (: view (#ref-mut #u64)) (#ref-mut #u64) (#return view))",
            );
            // Inspect the proposed storage declarations, rather than assuming
            // a private fresh-name numbering scheme in the cleanup function.
            let mut generated = generate(&planning).unwrap();
            let parsed = program(&planning, &generated).unwrap();
            let slot_type = parsed
                .items
                .iter()
                .find_map(|item| match item {
                    Item::Struct { name, fields, .. } if name == "Work-frame-cleanup" => fields
                        .iter()
                        .find(|field| field.name == "await-0")
                        .map(|field| field.ty.clone()),
                    _ => None,
                })
                .unwrap();
            let Type::Named(slot_name) = slot_type else {
                panic!("child has no storage enum")
            };
            let variants = parsed
                .items
                .iter()
                .find_map(|item| match item {
                    Item::Enum { name, variants, .. } if name == &slot_name => Some(variants),
                    _ => None,
                })
                .unwrap();
            let empty = &variants
                .iter()
                .find(|variant| variant.fields.is_empty())
                .unwrap()
                .name;
            let full = &variants
                .iter()
                .find(|variant| variant.fields == [Type::Named("Child".into())])
                .unwrap()
                .name;
            let polls = match phase {
                "initial" => String::new(),
                "pending" => "(#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable)) (#drop next)".into(),
                "ready" => "(#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                      (#case (work-ready answer) answer)
                      (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                    (#assert (#u64.== answer 42u64))".into(),
                _ => unreachable!(),
            };
            let expected_count = if phase == "pending" { 1 } else { 0 };
            let extra = format!(
                "
                (#fn cancel-child (: task Child : count (#ref-mut #u64)) ()
                  (#match task
                    (#case (Start value) (#assert false))
                    (#case (Resume value) (#assert (#u64.== value 2u64))))
                  (#deref-set count (#u64.+.wrap (#deref count) 1u64)) (#return ()))
                (#fn destroy-state (: state Work-frame-cleanup : count (#ref-mut #u64)) ()
                  (#match (#get state await-0)
                    (#case {empty} ())
                    (#case ({full} child) (#call cancel-child (: task child : count count))))
                  (#forget state) (#return ()))
                (#fn main () #u64
                  (#let waker #u64 0u64) (#let-mut value #u64 40u64) (#let-mut count #u64 0u64)
                  (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
                  {polls}
                  (#let state Work-frame-cleanup (#call work-poll-cleanup (: task (#pin-borrow-mut task))))
                  (#call destroy-state (: state state : count (#borrow-mut count)))
                  (#set value 99u64)
                  (#let again Work-frame-cleanup (#call work-poll-cleanup (: task (#pin-borrow-mut task))))
                  (#assert (#u32.== (#get task pc) 4294967295u32))
                  (#call destroy-state (: state again : count (#borrow-mut count)))
                  (#assert (#u64.== count {expected_count}u64))
                  (#forget task) (#return 42u64))"
            );
            generated[0].source = crate::generator::format_generated_source(&format!(
                "{}\n{extra}",
                generated[0].source
            ))
            .unwrap();
            runtime_generated(planning, generated, 42);
        }
    }

    #[test]
    fn retained_child_lending_is_recreated_only_on_actual_loop_iterations() {
        let function = "(#fn work (: view (#ref-mut #u64)) #u64
          (#let-mut total #u64 0u64)
          (#while (#u64.< total 42u64)
            (#let returned (#ref-mut #u64) (#call echo (: view view)))
            (#let amount #u64 (#if (#u64.== total 0u64)
              (#await Child ChildPending ChildReady child-poll (Start 20u64))
              (#await Child ChildPending ChildReady child-poll (Start 22u64))))
            (#assert (#u64.== (#deref returned) 40u64))
            (#set total (#u64.+.wrap total amount)))
          (#return total))";
        let main = "(#fn echo (: view (#ref-mut #u64)) (#ref-mut #u64) (#return view))
          (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
            (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
            (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
            (#let-mut answer #u64 0u64) (#let-mut retries #u64 0u64)
            (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
              (#case (work-pending next) (#block (#set running next)
                (#set retries (#u64.+.wrap retries 1u64)) ()))
              (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
            (#drop running) (#forget task) (#set value 99u64)
            (#assert (#u64.== retries 2u64)) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
    }

    #[test]
    fn returned_shared_reference_holders_retain_their_actual_pointees_across_pending() {
        let function = "(#fn work (: view (#ref-mut Source)) #u64
          (#let holder Holder (#call echo (: view view)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#return (#call read-holder (: holder holder : amount child))))";
        let main = "(#struct Source () (: amount #u64)) (#struct Holder () (: view (#ref #u64)))
          (#fn echo (: view (#ref-mut Source)) Holder
            (#return (#struct-literal Holder (: view (#borrow (#get view amount))))))
          (#fn read-holder (: holder Holder : amount #u64) #u64
            (#return (#u64.+.wrap (#deref (#get holder view)) amount)))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut value Source (#struct-literal Source (: amount 40u64)))
            (#let-mut task Work-frame (#call work (: view (#borrow-mut value))))
            (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready answer) answer)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget task) (#set value (#struct-literal Source (: amount 99u64))) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let bad = main.replace(
            "(#let-else (work-pending next)",
            "(#set value (#struct-literal Source (: amount 99u64))) (#let-else (work-pending next)",
        );
        let planning = prepare_generator("#async-fn-pinned", function, &bad);
        let generated = generate(&planning).unwrap();
        let proposed = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&proposed)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Borrow);
        let span = error.2.unwrap();
        assert_eq!(
            &proposed.source_files[span.source_id as usize].source[span.start..span.end],
            "#set"
        );
    }

    #[test]
    fn ready_transfers_exclusive_results_without_retaining_the_empty_frame() {
        for (ty, borrow, write) in [
            ("#ref-mut", "#borrow-mut", "(#deref-set result 42u64)"),
            (
                "#pin-ref-mut",
                "#pin-borrow-mut",
                "(#unsafe (#pin-write result 42u64))",
            ),
        ] {
            let function = format!(
                "(#fn work (: view ({ty} #u64)) ({ty} #u64)
              (#let returned ({ty} #u64) (#call echo (: view view)))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return returned))"
            );
            let main = format!("(#fn echo (: view ({ty} #u64)) ({ty} #u64) (#return view))
              (#fn main () #u64 (#let waker #u64 0u64) (#let-mut value #u64 40u64)
                (#let-mut task Work-frame (#call work (: view ({borrow} value))))
                (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let result ({ty} #u64) (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready result) result)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget task) {write} (#drop result) (#return value))");
            runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
            let bad = main.replace(
                &format!("(#forget task) {write}"),
                &format!("(#forget task) (#set value 99u64) {write}"),
            );
            let planning = prepare_generator("#async-fn-pinned", &function, &bad);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .unwrap();
            assert_eq!(error.1, DiagnosticCode::Borrow);
            let span = error.2.unwrap();
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                "#set"
            );
        }
    }

    #[test]
    fn cleanup_handlers_are_required_by_source_identity() {
        let source = format!(
            "{CONTEXT}
          (@#async-fn-pinned (: protocol work-await : waker #u64
            : cancel (work-cancel ((unknown-slot cancel-start)))
            : function (#fn work (: seed #u64) #u64
              (#return (#await Child ChildPending ChildReady child-poll (Start seed))))))"
        );
        let syntax = crate::prepare_program_syntax(
            &source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        let planning = crate::generator::async_prepare::prepare(&syntax).unwrap();
        let error = generate(&planning).err().unwrap();
        assert_eq!(
            error.message,
            "missing graph cleanup handler for source slot 'await-0'"
        );
        let original = &planning.program.source_files[error.span.source_id as usize].source;
        assert!(original[error.span.start..error.span.end].starts_with("(#fn work"));
    }

    #[test]
    fn whole_owner_borrows_reject_a_consumed_source_owner() {
        let function = "(#fn work (: seed #u64) #u64
          (#let owner Source (#struct-literal Source (: amount seed)))
          (#forget owner)
          (#let view (#pin-ref Source) (#pin-borrow owner))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#drop view) (#return child))";
        let error = prepare_generator_result(
            "#async-fn-pinned",
            function,
            "(#struct Source (#linear) (: amount #u64)) ",
        )
        .err()
        .expect("a consumed owner cannot supply a borrow");
        assert_eq!(error.code, DiagnosticCode::Linear);
        let span = error.span.unwrap();
        let source = error.source_text.unwrap();
        assert_eq!(&source[span.start..span.end], "(#pin-borrow owner)");
    }

    #[test]
    fn zero_sized_local_owner_borrows_have_a_real_stable_cell() {
        let function = "(#fn work (: seed #u64) #u64
          (#let owner Empty (#struct-literal Empty ()))
          (#let view (#pin-ref Empty) (#pin-borrow owner))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#drop view) (#forget owner) (#return (#u64.+.wrap seed child)))";
        let main = "(#struct Empty (#linear) ())
          (#fn main () #u64 (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 40u64)))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready answer) answer)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
    }

    #[test]
    fn disjoint_mutable_owner_fields_stay_stationary_through_repeated_pending() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut owner Source (#struct-literal Source (: left seed : right 2u64)))
          (#let left (#pin-ref-mut #u64) (#pin-borrow-mut (#get owner left)))
          (#let right (#pin-ref #u64) (#pin-borrow (#get owner right)))
          (#for (#let-mut index #u64 0u64) (#u64.< index 2u64) (#set index (#u64.+.wrap index 1u64))
            (#unsafe (#pin-write left (#u64.+.wrap (#deref left) 1u64)))
            (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64))))
          (#let answer #u64 (#u64.+.wrap (#deref left) (#deref right)))
          (#drop left) (#drop right) (#forget owner) (#return answer))";
        let main = "(#struct Source (#linear) (: left #u64 : right #u64))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 38u64)))
            (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
            (#let-mut retries #u64 0u64) (#let-mut answer #u64 0u64)
            (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
              (#case (work-pending next) (#block (#set running next) (#set retries (#u64.+.wrap retries 1u64)) ()))
              (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
            (#drop running) (#forget task) (#assert (#u64.== retries 2u64)) (#return answer))";
        // Recycled parent handles retain the identity of each internal child
        // loan through the caller loop. The overlapping-borrow negative below
        // remains checked independently of the generated representation.
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);

        // Distinct consumed continuation handles already retain those loans.
        // The source async loop itself is unchanged and suspends twice.
        let main = "(#struct Source (#linear) (: left #u64 : right #u64))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 38u64)))
            (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let second Work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
            (#let-else (work-pending last) Work-poll-result second (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task last : waker (#borrow waker)))
              (#case (work-ready answer) answer)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let invalid = function.replace(
            "(#pin-borrow (#get owner right))",
            "(#pin-borrow (#get owner left))",
        );
        let planning = prepare_generator("#async-fn-pinned", &invalid, main);
        let generated = generate(&planning).unwrap();
        let proposed = program(&planning, &generated).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&proposed)
            .err()
            .unwrap();
        assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
        let span = error.2.unwrap();
        assert!((span.source_id as usize) < planning.program.source_files.len());
        assert_eq!(
            &proposed.source_files[span.source_id as usize].source[span.start..span.end],
            "#pin-borrow"
        );
    }

    #[test]
    fn pinned_owner_cancellation_ends_internal_loans_before_transferring_owners() {
        let function = "(#fn work (: seed #u64) #u64
          (#let offset #u64 (#await Child ChildPending ChildReady child-poll (Start 5u64)))
          (#let-mut owner Source (#struct-literal Source (: amount (#u64.+.wrap seed offset))))
          (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get owner amount)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let observed #u64 (#deref view)) (#drop view) (#forget owner)
          (#return (#u64.+.wrap observed child)))";
        let first =
            "(#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))";
        let second =
            "(#let second Work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
          (#let-else (work-pending last) Work-poll-result second (#unreachable))";
        for (phase, polls, receiver, owners, children, child_value) in [
            ("initial", String::new(), "(#pin-borrow-mut task)", 0, 0, 0),
            ("before-owner", first.into(), "next", 0, 1, 5),
            ("after-owner", format!("{first}\n{second}"), "last", 1, 1, 2),
            (
                "ready",
                format!(
                    "{first}\n{second}
                  (#let answer #u64 (#match (#call work-poll (: task last : waker (#borrow waker)))
                    (#case (work-ready answer) answer)
                    (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                  (#assert (#u64.== answer 42u64))"
                ),
                "(#pin-borrow-mut task)",
                0,
                0,
                0,
            ),
        ] {
            let planning = prepare_generator(
                "#async-fn-pinned",
                function,
                "(#struct Source (#linear) (: amount #u64)) ",
            );
            let mut generated = generate(&planning).unwrap();
            let parsed = program(&planning, &generated).unwrap();
            let fields = parsed
                .items
                .iter()
                .find_map(|item| match item {
                    Item::Struct { name, fields, .. } if name == "Work-frame-cleanup" => {
                        Some(fields)
                    }
                    _ => None,
                })
                .unwrap();
            let mut cleanup = Vec::new();
            let mut owner_cells = 0;
            for field in fields {
                let Type::Named(slot) = &field.ty else {
                    continue;
                };
                let variants = parsed
                    .items
                    .iter()
                    .find_map(|item| match item {
                        Item::Enum { name, variants, .. } if name == slot => Some(variants),
                        _ => None,
                    })
                    .unwrap();
                let Some(full) = variants.iter().find(|variant| {
                    variant.fields == [Type::Named("Source".into())]
                        || variant.fields == [Type::Named("Child".into())]
                }) else {
                    continue;
                };
                let empty = &variants
                    .iter()
                    .find(|variant| variant.fields.is_empty())
                    .unwrap()
                    .name;
                let destroy = if full.fields == [Type::Named("Source".into())] {
                    owner_cells += 1;
                    "(#assert (#u64.== (#get value amount) 40u64)) (#forget value)
                     (#deref-set owners (#u64.+.wrap (#deref owners) 1u64))"
                        .to_string()
                } else {
                    format!(
                        "(#match value
                      (#case (Start amount) (#assert false))
                      (#case (Resume amount) (#assert (#u64.== amount {child_value}u64))))
                      (#deref-set children (#u64.+.wrap (#deref children) 1u64))"
                    )
                };
                cleanup.push(format!(
                    "(#match (#get state {})
                  (#case {empty} ()) (#case ({} value) (#block {destroy} ())))",
                    field.name, full.name
                ));
            }
            assert!(
                owner_cells > 0,
                "{phase}: no actual owner storage inspected"
            );
            let extra = format!("(#fn destroy-state
                (: state Work-frame-cleanup : owners (#ref-mut #u64) : children (#ref-mut #u64)) ()
                {} (#forget state) (#return ()))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut owners #u64 0u64) (#let-mut children #u64 0u64)
                (#let-mut task Work-frame (#call work (: seed 35u64)))
                {polls}
                (#let state Work-frame-cleanup (#call work-poll-cleanup (: task {receiver})))
                (#call destroy-state (: state state : owners (#borrow-mut owners) : children (#borrow-mut children)))
                (#let again Work-frame-cleanup (#call work-poll-cleanup (: task (#pin-borrow-mut task))))
                (#assert (#u32.== (#get task pc) 4294967295u32))
                (#call destroy-state (: state again : owners (#borrow-mut owners) : children (#borrow-mut children)))
                (#assert (#u64.== owners {owners}u64))
                (#assert (#u64.== children {children}u64))
                (#forget task) (#return 42u64))", cleanup.join("\n"));
            generated[0].source = crate::generator::format_generated_source(&format!(
                "{}\n{extra}",
                generated[0].source,
            ))
            .unwrap();
            runtime_generated(planning, generated, 42);
        }
    }

    #[test]
    fn branch_and_loop_local_pinned_owners_initialize_at_their_execution_points() {
        for selected in [false, true] {
            let function = format!(
                "(#fn work (: selected #bool : count (#ptr-mut #u64)) #u64
                  (#let offset #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
                  (#let-mut total #u64 0u64)
                  (#if selected
                    (#block
                      (#for (#let-mut index #u64 0u64) (#u64.< index 2u64)
                        (#set index (#u64.+.wrap index 1u64))
                        (#let owner Source (#call make-owner (: seed (#u64.+.wrap 19u64 offset) : count count)))
                        (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
                        (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
                        (#set total (#u64.+.wrap total (#u64.+.wrap (#deref view) child)))
                        (#drop view) (#forget owner)) ())
                    (#block (#set total 42u64) ()))
                  (#return total))"
            );
            let main = format!(
                "(#struct Source (#linear) (: amount #u64))
                  (#fn make-owner (: seed #u64 : count (#ptr-mut #u64)) Source
                    (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
                    (#return (#struct-literal Source (: amount seed))))
                  (#fn main () #u64
                    (#let waker #u64 0u64) (#let-mut count #u64 0u64)
                    (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
                      ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
                    (#let-mut task Work-frame (#call work (: selected {selected} : count pointer)))
                    (#assert (#u64.== count 0u64))
                    (#let-mut running (#pin-ref-mut Work-frame) (#pin-borrow-mut task))
                    (#let-mut retries #u64 0u64) (#let-mut answer #u64 0u64)
                    (#loop (#match (#call work-poll (: task running : waker (#borrow waker)))
                      (#case (work-pending next) (#block (#set running next)
                        (#set retries (#u64.+.wrap retries 1u64))
                        (#assert (#u64.== count (#u64.-.wrap retries 1u64))) ()))
                      (#case (work-ready result) (#block (#set answer result) (#break) (#unreachable)))))
                    (#drop running) (#forget task)
                    (#assert (#u64.== count {owners}u64))
                    (#assert (#u64.== retries {polls}u64)) (#return answer))",
                owners = if selected { 2 } else { 0 },
                polls = if selected { 3 } else { 1 },
            );
            runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
        }
    }

    #[test]
    fn local_owner_initialization_after_await_is_lazy_and_runs_exactly_once() {
        let function = "(#fn work (: seed #u64 : count (#ptr-mut #u64)) #u64
          (#let offset #u64 (#await Child ChildPending ChildReady child-poll (Start 5u64)))
          (#let owner Source (#call make-owner (: seed (#u64.+.wrap seed offset) : count count)))
          (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let observed #u64 (#deref view)) (#drop view) (#forget owner)
          (#return (#u64.+.wrap observed child)))";
        let main = "(#struct Source (#linear) (: padding #u64 : amount #u64))
          (#fn make-owner (: seed #u64 : count (#ptr-mut #u64)) Source
            (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
            (#return (#struct-literal Source (: padding 99u64 : amount seed))))
          (#fn main () #u64 (#let waker #u64 0u64) (#let-mut count #u64 0u64)
            (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let-mut task Work-frame (#call work (: seed 35u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#assert (#u64.== count 0u64))
            (#let second Work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
            (#let-else (work-pending last) Work-poll-result second (#unreachable))
            (#assert (#u64.== count 1u64))
            (#let answer #u64 (#match (#call work-poll (: task last : waker (#borrow waker)))
              (#case (work-ready answer) answer)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget task) (#assert (#u64.== count 1u64)) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
    }

    #[test]
    fn delayed_pinned_owners_cancel_only_after_initialization() {
        let function = "(#fn work (: created (#ref Counter) : destroyed (#ref Counter)) #u64
          (#let offset #u64 (#await Child ChildPending ChildReady child-poll (Start 5u64)))
          (#let owner Source (#call make-owner (: amount (#u64.+.wrap 35u64 offset) : count created)))
          (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let observed #u64 (#deref view)) (#drop view)
          (#call destroy-owner (: owner owner : count destroyed))
          (#return (#u64.+.wrap observed child)))";
        let declarations = "(#struct Counter (#linear) (: storage (#atomic #u64)))
          (#fn read-counter (: count (#ref Counter)) #u64
            (#return (#atomic-load (#borrow (#get count storage)) #memory-relaxed)))
          (#fn bump-counter (: count (#ref Counter)) ()
            (#atomic-store (#borrow (#get count storage))
              (#u64.+.wrap (#call read-counter (: count count)) 1u64) #memory-relaxed)
            (#return ()))
          (#struct Source (#linear) (: amount #u64))
          (#fn make-owner (: amount #u64 : count (#ref Counter)) Source
            (#call bump-counter (: count count))
            (#return (#struct-literal Source (: amount amount))))
          (#fn destroy-owner (: owner Source : count (#ref Counter)) ()
            (#assert (#u64.== (#get owner amount) 40u64))
            (#call bump-counter (: count count))
            (#forget owner) (#return ()))";
        let cleanup = "(#fn cancel-state (: state Work-frame-cleanup : count (#ref Counter)) ()
            (#match (#get state owner)
              (#case Work-frame-cleanup-owner-empty ())
              (#case (Work-frame-cleanup-owner-full owner)
                (#call destroy-owner (: owner owner : count count))))
            (#forget state) (#return ()))";
        let first = "(#let first Work-poll-result
            (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))";
        let second = "(#let second Work-poll-result
            (#call work-poll (: task next : waker (#borrow waker))))
            (#let-else (work-pending last) Work-poll-result second (#unreachable))";
        let ready = "(#let answer #u64 (#match
            (#call work-poll (: task last : waker (#borrow waker)))
              (#case (work-ready result) result)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#assert (#u64.== answer 42u64))";
        for (polls, handle, constructed, prior_destroyed) in [
            (String::new(), "(#pin-borrow-mut task)", 0, 0),
            (first.to_owned(), "next", 0, 0),
            (format!("{first}\n{second}"), "last", 1, 0),
            (
                format!("{first}\n{second}\n{ready}"),
                "(#pin-borrow-mut task)",
                1,
                1,
            ),
        ] {
            let main = format!("{declarations}\n{cleanup}
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let created Counter (#struct-literal Counter (: storage (#atomic-init #u64 0u64))))
                (#let destroyed Counter (#struct-literal Counter (: storage (#atomic-init #u64 0u64))))
                (#let-mut task Work-frame (#call work (: created (#borrow created) : destroyed (#borrow destroyed))))
                (#assert (#u64.== (#call read-counter (: count (#borrow created))) 0u64)) {polls}
                (#assert (#u64.== (#call read-counter (: count (#borrow created))) {constructed}u64))
                (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {prior_destroyed}u64))
                (#let state Work-frame-cleanup (#call work-poll-cleanup (: task {handle})))
                (#call cancel-state (: state state : count (#borrow destroyed)))
                (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {constructed}u64))
                (#let again Work-frame-cleanup (#call work-poll-cleanup (: task (#pin-borrow-mut task))))
                (#call cancel-state (: state again : count (#borrow destroyed)))
                (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {constructed}u64))
                (#forget task) (#forget created) (#forget destroyed) (#return 42u64))");
            let planning = prepare_generator("#async-fn-pinned", function, &main);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            if let Err((message, code, span, _)) =
                crate::CheckedProgram::validate_with_span(&proposed)
            {
                let span = span.unwrap();
                let source = &proposed.source_files[span.source_id as usize].source;
                panic!(
                    "{code:?}: {message}\n{}\n{}",
                    source[..span.start]
                        .lines()
                        .rev()
                        .find(|line| line.starts_with("(#fn "))
                        .unwrap_or("no function"),
                    source
                        .lines()
                        .skip(span.line.saturating_sub(4))
                        .take(8)
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
            runtime_generated(planning, generated, 42);
        }
    }

    #[test]
    fn internal_scalar_reference_inside_holder_survives_repeated_poll() {
        let function = "(#fn work (: seed #u64) #u64
          (#let owner Source (#struct-literal Source (: amount (#borrow seed))))
          (#let view (#pin-ref (#ref #u64)) (#pin-borrow (#get owner amount)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let observed #u64 (#deref (#deref view)))
          (#drop view) (#forget owner)
          (#return (#u64.+.wrap observed child)))";
        let main = "(#struct Source () (: amount (#ref #u64)))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 40u64)))
            (#let first Work-poll-result (#call work-poll
              (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready result) result)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget task) (#return answer))";
        let generated = runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        assert!(generated[0].source.contains("exact-word-anchor"));
    }

    #[test]
    fn pinned_local_owner_borrows_are_initialized_during_poll_and_stay_stationary() {
        let function = "(#fn work (: seed #u64) #u64
          (#let owner Source (#struct-literal Source (: amount seed)))
          (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
          (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#let observed #u64 (#deref view)) (#drop view) (#forget owner)
          (#return (#u64.+.wrap observed child)))";
        let main = "(#struct Source (#linear) (: amount #u64))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 40u64)))
            (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready answer) answer)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        // A live continuation still protects the frame. After retiring the
        // continuation, permanent pinning prohibits moving the frame, but
        // explicit forget may end its lifetime in place: erased self-pointers
        // are no longer externally accessible and need not keep a fake loan.
        for (action, retire, offending) in [
            ("(#forget task)", "", "#forget"),
            (
                "(#let moved Work-frame task) (#forget moved)",
                "(#drop next)",
                "task",
            ),
        ] {
            let bad = format!("(#struct Source (#linear) (: amount #u64))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut task Work-frame (#call work (: seed 40u64)))
                (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable)) {retire}
                {action} {} (#return 0u64))", if retire.is_empty() { "(#drop next)" } else { "" });
            let planning = prepare_generator("#async-fn-pinned", function, &bad);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .expect("a stored internal reference must protect its stationary frame");
            assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
            let span = error.2.unwrap();
            assert_eq!(span.source_id, 0);
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                offending
            );
        }
    }

    #[test]
    fn external_reference_field_writes_keep_the_evaluated_destination_across_await() {
        for (parent, borrow, destination) in [
            (
                "#ref-mut",
                "#borrow-mut",
                "(#deref-set (#borrow-mut (#get view amount))",
            ),
            (
                "#pin-ref-mut",
                "#pin-borrow-mut",
                "(#pin-set-field view amount",
            ),
        ] {
            let function = format!(
                "(#fn work (: view ({parent} Source)) #u64
              {destination} (#await Child ChildPending ChildReady child-poll (Start 40u64)))
              (#return (#u64.+.wrap (#get view amount) 2u64)))"
            );
            let main = format!("(#struct Source (#linear) (: padding #u64 : amount #u64))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut owner Source (#struct-literal Source (: padding 99u64 : amount 10u64)))
                (#let-mut task Work-frame (#call work (: view ({borrow} owner))))
                (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready answer) answer)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget task) (#assert (#u64.== (#get owner amount) 40u64))
                (#assert (#u64.== (#get owner padding) 99u64)) (#forget owner) (#return answer))");
            runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
            let bad = main.replace(
                "(#let-else (work-pending next)",
                "(#set-field owner amount 99u64) (#let-else (work-pending next)",
            );
            let planning = prepare_generator("#async-fn-pinned", &function, &bad);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .unwrap();
            assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
            let span = error.2.unwrap();
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                "#set-field"
            );
        }
    }

    #[test]
    fn fresh_external_field_reborrows_release_on_explicit_cancellation() {
        for (parent, borrow, project) in [
            ("#ref", "#borrow", "#borrow"),
            ("#ref-mut", "#borrow-mut", "#borrow-mut"),
            ("#pin-ref", "#pin-borrow", "#pin-borrow"),
            ("#pin-ref-mut", "#pin-borrow-mut", "#pin-borrow-mut"),
        ] {
            let function = format!(
                "(#fn work (: view ({parent} Source)) #u64
              (#let selected ({parent} #u64) ({project} (#get view amount)))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#deref selected) child)))"
            );
            let main = format!(
                "(#struct Source (#linear) (: amount #u64))
              (#fn main () #u64 (#let waker #u64 0u64)
              (#let-mut owner Source (#struct-literal Source (: amount 40u64)))
              (#let-mut task Work-frame (#call work (: view ({borrow} owner))))
              (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
              (#let-else (work-pending next) Work-poll-result first (#unreachable)) (#drop next)
              (#let state Work-frame-cleanup (#call work-poll-cleanup (: task (#pin-borrow-mut task))))
              (#forget state) (#forget task) (#set-field owner amount 42u64)
              (#let answer #u64 (#get owner amount)) (#forget owner) (#return answer))"
            );
            runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
            let bad = main.replace(
                "(#drop next)",
                "(#set-field owner amount 99u64) (#drop next)",
            );
            let planning = prepare_generator("#async-fn-pinned", &function, &bad);
            let generated = generate(&planning).unwrap();
            let proposed = program(&planning, &generated).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&proposed)
                .err()
                .unwrap();
            assert_eq!(error.1, DiagnosticCode::Borrow, "{}", error.0);
            let span = error.2.unwrap();
            assert_eq!(
                &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                "#set-field"
            );
        }
    }

    #[test]
    fn fresh_external_field_reborrows_survive_suspension() {
        for nested in [false, true] {
            for (parent, child, initial, project, write) in [
                ("#ref", "#ref", "#borrow", "#borrow", ""),
                (
                    "#ref-mut",
                    "#ref-mut",
                    "#borrow-mut",
                    "#borrow-mut",
                    "(#deref-set selected 40u64)",
                ),
                ("#pin-ref", "#pin-ref", "#pin-borrow", "#pin-borrow", ""),
                (
                    "#pin-ref-mut",
                    "#pin-ref-mut",
                    "#pin-borrow-mut",
                    "#pin-borrow-mut",
                    "(#unsafe (#pin-write selected 40u64))",
                ),
            ] {
                let leaf = if nested {
                    "(#get (#get view amount) 1)"
                } else {
                    "(#get view amount)"
                };
                let field_type = if nested { "(#tuple #u64 #u64)" } else { "#u64" };
                let amount = if write.is_empty() { 40 } else { 10 };
                let field_value = if nested {
                    format!("(#tuple (#tuple #u64 #u64) 77u64 {amount}u64)")
                } else {
                    format!("{amount}u64")
                };
                let owner_leaf = if nested {
                    "(#get (#get owner amount) 1)"
                } else {
                    "(#get owner amount)"
                };
                let function = format!(
                    "(#fn work (: view ({parent} Source)) #u64
              (#let selected ({child} #u64) ({project} {leaf}))
              (#let step #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              {write} (#return (#u64.+.wrap (#deref selected) step)))"
                );
                let main = format!("(#struct Source (#linear) (: padding #u64 : amount {field_type}))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut owner Source (#struct-literal Source (: padding 99u64 : amount {field_value})))
                (#let-mut task Work-frame (#call work (: view ({initial} owner))))
                (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready answer) answer)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#forget task) (#assert (#u64.== {owner_leaf} 40u64)) (#forget owner) (#return answer))");
                runtime_planned(prepare_generator("#async-fn-pinned", &function, &main), 42);
                let bad = main
                    .replace(
                        "(#let-else (work-pending next)",
                        "(#forget owner) (#let-else (work-pending next)",
                    )
                    .replace(
                        &format!("(#assert (#u64.== {owner_leaf} 40u64)) (#forget owner)"),
                        "",
                    );
                let planning = prepare_generator("#async-fn-pinned", &function, &bad);
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                let error = crate::CheckedProgram::validate_with_span(&proposed)
                    .err()
                    .unwrap();
                assert_eq!(error.1, DiagnosticCode::Borrow);
                let span = error.2.unwrap();
                assert_eq!(
                    &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                    "#forget"
                );
                let invalid = function.replace("(#let step", "(#drop view) (#let step");
                let planning = prepare_generator("#async-fn-pinned", &invalid, &main);
                let generated = generate(&planning).unwrap();
                let proposed = program(&planning, &generated).unwrap();
                let error = crate::CheckedProgram::validate_with_span(&proposed)
                    .err()
                    .unwrap();
                assert_eq!(error.1, DiagnosticCode::Borrow);
                let span = error.2.unwrap();
                assert!((span.source_id as usize) < planning.program.source_files.len());
                assert_eq!(
                    &proposed.source_files[span.source_id as usize].source[span.start..span.end],
                    "#drop"
                );
            }
        }
    }

    #[test]
    fn exclusive_immediate_calls_keep_the_parent_handle_across_pending() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let write = if ty == "#pin-ref-mut" {
                "(#unsafe (#pin-write view (#u64.+.wrap (#deref view) amount)))"
            } else {
                "(#deref-set view (#u64.+.wrap (#deref view) amount))"
            };
            let function = format!(
                "(#fn work (: view ({ty} #u64) : count (#ptr-mut #u64)) #u64
                  (#let first #u64 (#call adjust (: view view : amount 10u64 : count count)))
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#let second #u64 (#call adjust (: view view : amount 20u64 : count count)))
                  (#return (#u64.+.wrap second child)))"
            );
            let main = format!(
                "(#fn adjust (: count (#ptr-mut #u64) : amount #u64 : view ({ty} #u64)) #u64
                  (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64))) {write}
                  (#return (#deref view)))
                  (#fn main () #u64
                    (#let waker #u64 0u64) (#let-mut value #u64 10u64)
                    (#let-mut count #u64 0u64)
                    (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
                      ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
                    (#let task Work-task (#call work (: view ({borrow} value) : count pointer)))
                    (#assert (#u64.== count 0u64))
                    (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#assert (#u64.== count 1u64))
                    (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                      (#case (work-ready answer) answer)
                      (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                    (#assert (#u64.== count 2u64))
                    (#assert (#u64.== value 40u64)) (#set value 99u64) (#return answer))"
            );
            // Named argument spelling is deliberately reversed: checked
            // declaration order evaluates amount before lending view.
            runtime_planned(prepare_function(&function, &main), 42);
            let bad = main.replace(
                "(#let-else (work-pending next)",
                "(#set value 99u64) (#let-else (work-pending next)",
            );
            let planning = prepare_function(&function, &bad);
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
    }

    #[test]
    fn immediate_call_results_do_not_retain_released_reference_inputs() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let write = if ty == "#pin-ref-mut" {
                "(#unsafe (#pin-write view (#u64.+.wrap (#deref view) 1u64)))"
            } else {
                "(#deref-set view (#u64.+.wrap (#deref view) 1u64))"
            };
            let function = format!(
                "(#fn work (: view ({ty} #u64)) #u64
                  (#call increment (: view view))
                  (#let owned Owned (#call capture (: view view))) (#drop view)
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#let answer #u64 (#u64.+.wrap (#get owned value) child))
                  (#forget owned) (#return answer))"
            );
            let main = format!(
                "(#struct Owned (#linear) (: value #u64))
                  (#fn increment (: view ({ty} #u64)) ()
                    {write} (#return ()))
                  (#fn capture (: view ({ty} #u64)) Owned
                    (#return (#struct-literal Owned (: value (#deref view)))))
                  (#fn main () #u64
                    (#let waker #u64 0u64) (#let-mut value #u64 39u64)
                    (#let task Work-task (#call work (: view ({borrow} value))))
                    (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#assert (#u64.== value 40u64)) (#set value 99u64)
                    (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
                      (#case (work-ready answer) answer)
                      (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))"
            );
            runtime_planned(prepare_function(&function, &main), 42);
        }
    }

    #[test]
    fn exclusive_in_place_reads_do_not_move_handles_across_pending() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let function = format!(
                "(#fn work (: view ({ty} #u64)) #u64
                  (#let before #u64 (#deref view))
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#u64.+.wrap before (#deref view)) child)))"
            );
            let main = format!(
                "(#fn main () #u64
                  (#let waker #u64 0u64) (#let-mut value #u64 20u64)
                  (#let task Work-task (#call work (: view ({borrow} value))))
                  (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                  (#let-else (work-pending next) Work-poll-result first (#unreachable))
                  (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                    (#case (work-ready answer) answer)
                    (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                  (#set value 99u64) (#return answer))"
            );
            runtime_planned(prepare_function(&function, &main), 42);
            let bad = main.replace(
                "(#let-else (work-pending next)",
                "(#set value 99u64) (#let-else (work-pending next)",
            );
            let planning = prepare_function(&function, &bad);
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
    }

    #[test]
    fn exclusive_field_reads_follow_checked_owners_through_loop_suspension() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let function = format!(
                "(#fn work (: view ({ty} Holder)) #u64
                  (#let-mut total #u64 0u64)
                  (#for (#let-mut count #u64 0u64) (#u64.< count 2u64) (#set count (#u64.+.wrap count 1u64))
                    (#set total (#u64.+.wrap total (#get view amount)))
                    (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 1u64)))
                    (#set total (#u64.+.wrap total child)))
                  (#return total))"
            );
            let main = format!(
                "(#struct Holder (#linear) (: amount #u64))
                  (#fn main () #u64
                    (#let waker #u64 0u64)
                    (#let-mut owner Holder (#struct-literal Holder (: amount 20u64)))
                    (#let-mut task Work-task (#call work (: view ({borrow} owner))))
                    (#loop
                      (#match (#call work-poll (: task task : waker (#borrow waker)))
                        (#case (work-pending next) (#block (#set task next) ()))
                        (#case (work-ready answer) (#block (#forget owner) (#return answer) (#unreachable)))))
                    (#return (#unreachable)))"
            );
            runtime_planned(prepare_function(&function, &main), 42);
        }
    }

    #[test]
    fn exclusive_nested_and_tuple_reads_do_not_move_borrowed_aggregates() {
        for (ty, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            for (declarations, target, construct, projection) in [
                (
                    "(#struct Inner (#linear) (: amount #u64))
                   (#struct Holder (#linear) (: inner Inner)) ",
                    "Holder",
                    "(#struct-literal Holder (: inner (#struct-literal Inner (: amount 40u64))))",
                    "(#get (#get view inner) amount)",
                ),
                (
                    "",
                    "(#tuple #u64 #u64)",
                    "(#tuple (#tuple #u64 #u64) 100u64 40u64)",
                    "(#get view 1)",
                ),
            ] {
                let function = format!(
                    "(#fn work (: view ({ty} {target})) #u64
                      (#let before #u64 {projection})
                      (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                      (#return (#u64.+.wrap before child)))"
                );
                let main = format!(
                    "{declarations}
                      (#fn main () #u64
                        (#let waker #u64 0u64) (#let-mut owner {target} {construct})
                        (#let first Work-poll-result (#call work-poll (: task (#call work (: view ({borrow} owner))) : waker (#borrow waker))))
                        (#let-else (work-pending next) Work-poll-result first (#unreachable))
                        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                          (#case (work-ready answer) answer)
                          (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                        (#forget owner) (#return answer))"
                );
                runtime_planned(prepare_function(&function, &main), 42);
            }
        }
    }

    #[test]
    fn in_place_lending_keeps_original_consumption_errors_at_the_source_use() {
        let error = prepare_generator_result(
            "#async-fn",
            "(#fn work (: view (#ref-mut #u64)) #u64
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#drop view) (#return (#deref view)))",
            "(#fn main () #u64 (#return 0u64))",
        )
        .err()
        .unwrap();
        assert_eq!(error.code, DiagnosticCode::Linear);
        let span = error.span.unwrap();
        let source = error.source_text.unwrap();
        // The ordinary checker reports the original dereference, not a
        // generated slot extraction or a whole synthesized work-poll function.
        assert_eq!(&source[span.start..span.end], "(#deref view)");
        assert_eq!(span.source_id, 0);
    }

    #[test]
    fn shared_reference_fields_survive_outer_handle_release() {
        for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
            let extra = "(#struct Holder () (: padding #u64 : view (#ref #u64)))";
            let function = format!(
                "(#fn work (: holder ({ty} Holder)) #u64
                  (#let loaded (#ref #u64) (#get holder view)) (#drop holder)
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#return (#u64.+.wrap (#deref loaded) child)))"
            );
            let main = format!(
                "{extra}
                  (#fn main () #u64
                    (#let waker #u64 0u64) (#let value #u64 40u64)
                    (#let holder Holder (#struct-literal Holder (: padding 99u64 : view (#borrow value))))
                    (#let task Work-task (#call work (: holder ({borrow} holder))))
                    (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#let result #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                      (#case (work-ready result) result)
                      (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                    (#forget holder) (#return result))"
            );
            runtime_planned(prepare_function(&function, &main), 42);

            let bad_main = format!(
                "{extra}
                  (#fn main () #u64
                    (#let waker #u64 0u64) (#let-mut value #u64 40u64)
                    (#let holder Holder (#struct-literal Holder (: padding 99u64 : view (#borrow value))))
                    (#let task Work-task (#call work (: holder ({borrow} holder))))
                    (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                    (#let-else (work-pending next) Work-poll-result first (#unreachable))
                    (#set value 99u64) (#forget next) (#return 0u64))"
            );
            // Only the copied leaf remains live after the outer handle was
            // dropped. Empty-cell witnesses now expose that distinction to
            // the ordinary checker: releasing the container is valid, but
            // mutating the copied reference's pointee remains forbidden.
            let release_main = main
                .replace(
                    "(#let-else (work-pending next) Work-poll-result first (#unreachable))",
                    "(#let-else (work-pending next) Work-poll-result first (#unreachable)) (#forget holder)",
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
        let main = "(#struct Stored () (: view (#ref #u64)))
          (#struct Holder (#linear) (: padding #u64 : stored Stored))
          (#fn read-stored (: value Stored) #u64 (#return (#deref (#get value view))))
          (#fn main () #u64
            (#let waker #u64 0u64) (#let value #u64 40u64)
            (#let holder Holder (#struct-literal Holder (: padding 99u64
              : stored (#struct-literal Stored (: view (#borrow value))))))
            (#let task Work-task (#call work (: holder (#borrow holder))))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let result #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready result) result)
              (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
            (#forget holder) (#return result))";
        runtime_planned(
            prepare_function(
                "(#fn work (: holder (#ref Holder)) #u64
                  (#let loaded Stored (#get holder stored)) (#drop holder)
                  (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
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
                "(#type Pair (#tuple #u64 #u64))
                (#struct Inner (#linear) ((padding #u64) (pair Pair)))
                (#struct Owner (#linear) ((padding #u64) (inner Inner)))
                (#fn main () #u64
                  (#let waker #u64 0u64)
                  (#let owner Owner (#struct-literal Owner (: padding 77u64
                    : inner (#struct-literal Inner (: padding 88u64
                      : pair (#tuple (#tuple #u64 #u64) 40u64 99u64))))))
                  (#let view ({ty} Owner) ({borrow} owner))
                  (#let task Work-task (#call work (: view view)))
                  (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                  (#let-else (work-pending next) Work-poll-result first (#unreachable))
                  (#assert (#u64.== (#get view padding) 77u64))
                  (#let result #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                    (#case (work-ready result) result)
                    (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                  (#drop view) (#forget owner) (#return result))"
            );
            runtime_planned(
                prepare_function(
                    &format!(
                        "(#fn work ((view ({ty} Owner))) #u64
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
            "(#fn work ((view (#ref #u64))) #u64
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#deref view) child)))",
            "(#fn main () #u64
              (#let waker #u64 0u64) (#let-mut value #u64 40u64)
              (#let task Work-task (#call work (: view (#borrow value))))
              (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
              (#let-else (work-pending next) Work-poll-result first (#unreachable))
              (#set value 99u64)
              (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
                (#case (work-ready result) result)
                (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))",
        );
        let generated = generate(&planning).unwrap();
        let program = program(&planning, &generated).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("work-pending still retains a reference to value");
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
            "(#fn work ((view (#ref #u64))) #u64
              (#return (#u64.+.wrap (#deref view)
                (#await Child ChildPending ChildReady child-poll (Start 2u64)))))",
            "(#fn escape () Work-task
              (#let value #u64 40u64)
              (#return (#call work (: view (#borrow value)))))
              (#fn main () #u64 (#return 42u64))",
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
            "(#fn work ((view (#ref Owner)) (count (#ptr-mut #u64))) #u64
              (#return (#u64.+.wrap
                (#get (#unsafe (#call select (: view view : count count))) value)
                (#await Child ChildPending ChildReady child-poll (Start 2u64)))))",
            "(#struct Owner (#linear) ((padding #u64) (value #u64)))
              (#unsafe-fn select ((view (#ref Owner)) (count (#ptr-mut #u64))) (#ref Owner)
                (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
                (#return view))
              (#fn main () #u64
                (#let waker #u64 0u64) (#let-mut count #u64 0u64)
                (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
                  ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
                (#let owner Owner (#struct-literal Owner (: padding 77u64 : value 40u64)))
                (#let task Work-task (#call work (: view (#borrow owner) : count pointer)))
                (#assert (#u64.== count 0u64))
                (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
                (#let-else (work-pending next) Work-poll-result first (#unreachable))
                (#assert (#u64.== count 1u64))
                (#let result #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready result) result)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                (#assert (#u64.== count 1u64))
                (#forget owner) (#return result))",
        );
        runtime_planned(planning, 42);
    }

    #[test]
    fn copy_projected_operands_survive_pending_without_moving_the_owner() {
        let main = format!("(#struct Owner (#linear) ((value #u64)))  {RUN}");
        runtime(
            "(#let owner Owner (#struct-literal Owner (: value seed)))
          (#let result #u64 (#u64.+.wrap (#get owner value)
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
            format!("(#struct Owner (#linear) ((padding #u64) (empty ()) (value #u64)))  {RUN}");
        let generated = runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : empty () : value 0u64)))
          (#set-field owner value (#await Child ChildPending ChildReady child-poll (Start seed)))
          (#assert (#u64.== (#get owner padding) 77u64))
          (#let-mut pair (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) (#get owner value) 0u64))
          (#set-field pair 1 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#set-field owner empty (#block (#assert true) ()))
          (#let result #u64 (#u64.+.wrap (#get pair 0) (#get pair 1)))
          (#forget owner) (#return result)",
            &main,
            42,
        );
        assert!(generated[0].source.contains("#pin-borrow-mut"));
    }

    #[test]
    fn projected_write_rhs_is_evaluated_once_before_pending_retries() {
        let main = "(#struct Owner (#linear) ((padding #u64) (value #u64)))
          (#fn counted ((count (#ptr-mut #u64))) Child
            (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
            (#return (Start 2u64)))
          (#fn main () #u64
            (#let waker #u64 0u64) (#let-mut count #u64 0u64)
            (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Work-task (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#assert (#u64.== count 1u64))
            (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready value) (#block (#assert (#u64.== count 1u64)) value))
              (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed #u64) (count (#ptr-mut #u64))) #u64
            (#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : value seed)))
            (#set-field owner value (#u64.+.wrap (#get owner value)
              (#await Child ChildPending ChildReady child-poll (#call counted (: count count)))))
            (#assert (#u64.== (#get owner padding) 77u64))
            (#let result #u64 (#get owner value)) (#forget owner) (#return result))",
            main,
        );
        runtime_planned(planning, 42);
    }

    #[test]
    fn physical_projection_gate_rejects_a_missing_checked_owner_initialization() {
        // Source validation succeeds first. Corrupt only the executable graph
        // to verify the independent representation guard still fails closed.
        let mut planning = prepare(
            "(#let-mut owner Owner (#struct-literal Owner (: value seed)))
             (#let result #u64 (#get owner value))
             (#forget owner) (#return result)",
            &format!("(#struct Owner (#linear) ((value #u64)))  {RUN}"),
        );
        let function = &mut planning.functions[0];
        let body = &planning.declarations.bodies[&function.model.body_name];
        let owner = crate::typed_body::BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "owner")
                .unwrap(),
        );
        let mut removed = 0;
        for block in &mut function.graph.blocks {
            block.actions.retain(|located| {
                let keep =
                    !matches!(located.action, Action::Bind { binding, .. } if binding == owner);
                removed += usize::from(!keep);
                keep
            });
        }
        assert_eq!(removed, 1);
        let error = generate(&planning)
            .err()
            .expect("an uninitialized physical cell cannot supply a projection");
        assert!(
            error.message.contains("definitely Full"),
            "{}",
            error.message
        );
        let source = &planning.program.source_files[error.span.source_id as usize].source;
        assert!(source[error.span.start..error.span.end].contains("owner"));
    }

    #[test]
    fn field_storage_rejects_reconstruction_when_restoration_is_removed() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut owner Pair (#struct-literal Pair
            (: left (#struct-literal Resource (: value seed))
             : right (#struct-literal Resource (: value 2u64)))))
          (#let moved Resource (#get owner left))
          (#let delta #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#forget moved)
          (#set-field owner left (#struct-literal Resource (: value delta)))
          (#let duplicate Pair (#clone owner)) (#forget duplicate)
          (#forget owner) (#return seed))";
        let declarations = format!(
            "(#struct Resource (#linear) (: value #u64))
          (#struct Pair () (: left Resource : right Resource)) {RUN}"
        );
        for function in [
            function.to_owned(),
            function.replace(
                "(#let duplicate Pair (#clone owner)) (#forget duplicate)",
                "",
            ),
        ] {
            let mut planning = prepare_function(&function, &declarations);
            assert!(generate(&planning).is_ok());
            let graph = &mut planning.functions[0].graph;
            let mut removed = 0;
            for block in &mut graph.blocks {
                block.actions.retain(|located| {
                    let remove = matches!(located.action, Action::Store { place, .. }
                    if matches!(graph.places[place.0].root, AddressRoot::Local(_))
                        && !graph.places[place.0].projections.is_empty());
                    removed += usize::from(remove);
                    !remove
                });
            }
            assert_eq!(removed, 1);
            let error = generate(&planning)
                .err()
                .expect("a missing leaf cannot be reconstructed");
            assert!(
                error.message.contains("initialized field storage"),
                "{}",
                error.message
            );
            let source = &planning.program.source_files[error.span.source_id as usize].source;
            assert!(source[error.span.start..error.span.end].contains("owner"));
        }
    }

    #[test]
    fn nested_field_storage_rejects_missing_subtree_restoration() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut owner Outer (#struct-literal Outer (: inner
            (#struct-literal Pair
              (: left (#struct-literal Resource (: value seed))
               : right (#struct-literal Resource (: value 2u64)))))))
          (#let moved Resource (#get (#get owner inner) left))
          (#let delta #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#forget moved)
          (#let sibling Resource (#get (#get owner inner) right))
          (#set-field owner inner (#struct-literal Pair
            (: left (#struct-literal Resource (: value delta)) : right sibling)))
          (#let duplicate Pair (#clone (#get owner inner))) (#forget duplicate)
          (#forget owner) (#return seed))";
        let declarations = format!(
            "(#struct Resource (#linear) (: value #u64))
             (#struct Pair () (: left Resource : right Resource))
             (#struct Outer () (: inner Pair)) {RUN}"
        );
        for function in [
            function.to_owned(),
            function.replace(
                "(#let duplicate Pair (#clone (#get owner inner))) (#forget duplicate)",
                "",
            ),
        ] {
            let mut planning = prepare_function(&function, &declarations);
            assert!(generate(&planning).is_ok());
            let graph = &mut planning.functions[0].graph;
            let mut removed = 0;
            for block in &mut graph.blocks {
                block.actions.retain(|located| {
                    let remove = matches!(located.action, Action::Store { place, .. }
                    if matches!(graph.places[place.0].root, AddressRoot::Local(_))
                        && !graph.places[place.0].projections.is_empty());
                    removed += usize::from(remove);
                    !remove
                });
            }
            assert_eq!(removed, 1);
            let error = generate(&planning)
                .err()
                .expect("an incomplete subtree cannot be reconstructed");
            assert!(
                error.message.contains("initialized field storage"),
                "{}",
                error.message
            );
            let source = &planning.program.source_files[error.span.source_id as usize].source;
            assert!(source[error.span.start..error.span.end].contains("owner"));
        }
    }

    #[test]
    fn selected_decomposed_field_requires_its_own_restoration() {
        let function = "(#fn work (: seed #u64) #u64
          (#let-mut pair Pair (#struct-literal Pair
            (: left (#struct-literal Resource (: value seed))
             : right (#struct-literal Holder
               (: data (#array-of (#array #u64 2) seed 22u64))))))
          (#let moved Holder (#get pair right))
          (#let delta #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#forget moved)
          (#set-field pair right (#struct-literal Holder
            (: data (#array-of (#array #u64 2) delta 22u64))))
          (#let view (#ref #u64) (#borrow (#index (#get (#get pair right) data) 1usize)))
          (#let result #u64 (#deref view))
          (#drop view) (#forget pair) (#return result))";
        let declarations = format!(
            "(#struct Resource (#linear) (: value #u64))
             (#struct Holder (#linear) (: data (#array #u64 2)))
             (#struct Pair () (: left Resource : right Holder)) {RUN}"
        );
        let mut planning = prepare_function(function, &declarations);
        assert!(generate(&planning).is_ok());
        let graph = &mut planning.functions[0].graph;
        let mut removed = 0;
        for block in &mut graph.blocks {
            block.actions.retain(|located| {
                let remove = matches!(located.action, Action::Store { place, .. }
                    if matches!(graph.places[place.0].root, AddressRoot::Local(_))
                        && !graph.places[place.0].projections.is_empty());
                removed += usize::from(remove);
                !remove
            });
        }
        assert_eq!(removed, 1);
        let error = generate(&planning)
            .err()
            .expect("a selected address cannot use an unrestored field cell");
        assert!(
            error.message.contains("initialized field storage"),
            "{error:?}"
        );
        let source = &planning.program.source_files[error.span.source_id as usize].source;
        assert!(source[error.span.start..error.span.end].contains("pair"));
    }

    #[test]
    fn projected_access_rejects_consumed_source_owners_before_storage() {
        // Original ownership rejects invalid projections before any physical
        // representation can obscure the consumed source owner's identity.
        for body in [
            "(#forget owner) (#set-field owner value 42u64)",
            "(#if (#u64.== seed 0u64) (#forget owner) ())
              (#set-field owner value 42u64)",
            "(#while (#u64.== seed 0u64) (#forget owner))
              (#set-field owner value 42u64)",
            "(#set-field owner value (#block (#forget owner)
              (#await Child ChildPending ChildReady child-poll (Start 42u64))))",
        ] {
            let error = prepare_generator_result(
                "#async-fn",
                &format!(
                    "(#fn work (: seed #u64) #u64
                    (#let-mut owner Owner (#struct-literal Owner (: value seed)))
                    {body} (#forget owner) (#return 42u64))"
                ),
                &format!("(#struct Owner (#linear) ((value #u64)))  {RUN}"),
            )
            .err()
            .expect("a consumed owner cannot supply a projection");
            assert_eq!(error.code, DiagnosticCode::Linear);
            assert!(error.message.contains("owner"), "{error:?}");
            let span = error.span.unwrap();
            assert!(error.source_text.unwrap()[span.start..span.end].contains("owner"));
        }

        // A genuine whole-cell reconstruction remains supported.
        runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: value 0u64)))
          (#forget owner)
          (#set owner (#struct-literal Owner (: value seed)))
          (#set-field owner value (#u64.+.wrap (#get owner value)
            (#await Child ChildPending ChildReady child-poll (Start 2u64))))
          (#let result #u64 (#get owner value)) (#forget owner) (#return result)",
            &format!("(#struct Owner (#linear) ((value #u64)))  {RUN}"),
            42,
        );
    }

    #[test]
    fn projected_copy_writes_preserve_full_cells_around_loop_backedges() {
        runtime(
            "(#let-mut owner Owner (#struct-literal Owner (: padding 77u64 : value seed)))
          (#for (#let-mut index #u64 0u64) (#u64.< index 2u64)
            (#set index (#u64.+.wrap index 1u64))
            (#set-field owner value (#u64.+.wrap (#get owner value)
              (#await Child ChildPending ChildReady child-poll (Start 1u64)))))
          (#assert (#u64.== (#get owner padding) 77u64))
          (#let result #u64 (#get owner value)) (#forget owner) (#return result)",
            &format!("(#struct Owner (#linear) ((padding #u64) (value #u64)))  {RUN}"),
            42,
        );
    }

    #[test]
    fn copy_clone_hooks_run_once_for_projected_and_plain_loads() {
        let main = "(#struct Value () ((number #u64) (count (#ptr-mut #u64))))
          (#fn Value-clone ((value Value)) Value
            (#unsafe (#ptr-write (#get value count)
              (#u64.+.wrap (#ptr-read (#get value count)) 1u64)))
            (#return value))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut count #u64 0u64)
            (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Work-task (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#assert (#u64.== count 2u64))
            (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready value) (#block
                (#assert (#u64.== count 2u64)) value))
              (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed #u64) (count (#ptr-mut #u64))) #u64
            (#let owner (#tuple Value #u64) (#tuple (#tuple Value #u64)
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
    fn selected_array_address_survives_rhs_pending_and_is_checked_eagerly() {
        let function = "(#fn work ((seed #u64)) #u64
          (#let-mut items (#array #u64 2) (#array-of (#array #u64 2) 7u64 0u64))
          (#let-mut index #usize 1usize)
          (#set-index items index (#block (#set index 0usize)
            (#await Child ChildPending ChildReady child-poll (Start seed))))
          (#let result #u64 (#index items 1usize))
          (#assert (#u64.== (#index items 0usize) 7u64))
          (#forget items) (#return result))";
        let main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#let result #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready answer) answer)
            (#case (work-pending pending) (#block (#forget pending) (#unreachable)))))
          (#forget task) (#return result))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let movable_main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready answer) answer)
            (#case (work-pending pending) (#block (#forget pending) (#unreachable))))))";
        runtime_planned(prepare_generator("#async-fn", function, movable_main), 42);
        // An invalid selection must trap before polling the RHS child. If
        // delayed until Store, this program would instead return 99 on Pending.
        let invalid = function.replace("1usize", "2usize");
        let main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#let state Work-frame-cleanup (#call work-poll-cleanup (: task next)))
          (#forget state) (#forget task) (#return 99u64))";
        let planning = prepare_generator("#async-fn-pinned", &invalid, main);
        let generated = generate(&planning).unwrap();
        runtime_generated_outcome(planning, generated, NativeOutcome::Signal(4));
        let movable_main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#forget first) (#return 99u64))";
        let planning = prepare_generator("#async-fn", &invalid, movable_main);
        let generated = generate(&planning).unwrap();
        runtime_generated_outcome(planning, generated, NativeOutcome::Signal(4));
    }

    #[test]
    fn nested_selection_checks_its_parent_before_awaiting_a_child_index() {
        let function = "(#fn work (: seed #u64) #u64
          (#let items (#array (#array #u64 2) 2)
            (#array-of (#array (#array #u64 2) 2)
              (#array-of (#array #u64 2) 0u64 7u64)
              (#array-of (#array #u64 2) 0u64 seed)))
          (#let-mut outer #usize 1usize)
          (#let result #u64 (#index (#index items outer)
            (#block (#set outer 0usize)
              (#as (#await Child ChildPending ChildReady child-poll (Start 1u64)) #usize))))
          (#forget items) (#return result))";
        let main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
            (#case (work-ready result) result)
            (#case (work-pending pending) (#block (#forget pending) (#unreachable)))))
          (#forget task) (#return answer))";
        runtime_planned(prepare_generator("#async-fn-pinned", function, main), 42);
        let invalid = function.replace("outer #usize 1usize", "outer #usize 2usize");
        let main = "(#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work (: seed 42u64)))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending next) Work-poll-result first (#unreachable))
          (#let state Work-frame-cleanup (#call work-poll-cleanup (: task next)))
          (#forget state) (#forget task) (#return 99u64))";
        let planning = prepare_generator("#async-fn-pinned", &invalid, main);
        let generated = generate(&planning).unwrap();
        runtime_generated_outcome(planning, generated, NativeOutcome::Signal(4));
    }

    #[test]
    fn selected_payload_and_nested_array_addresses_keep_their_checked_owners() {
        let main = "(#enum Choice () ((Good #u64) (Bad #u64)))
          (#struct Owner () (: values (#array #u64 2)))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut task Work-frame (#call work (: seed 42u64)))
            (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready result) result)
              (#case (work-pending pending) (#block (#forget pending) (#unreachable)))))
            (#forget task) (#return answer))";
        for body in [
            "(#let-mut owner Choice (Good 0u64))
              (#set-payload owner Good 0 (#await Child ChildPending ChildReady child-poll (Start seed)))
              (#let answer #u64 (#get-payload owner Good 0)) (#forget owner) (#return answer)",
            "(#let owner Owner (#struct-literal Owner (: values (#array-of (#array #u64 2) 0u64 seed))))
              (#let amount #u64 (#index (#get owner values) 1usize))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#forget owner) (#return (#u64.+.wrap amount child))",
            "(#let-mut owner (#array #u64 2) (#array-of (#array #u64 2) 0u64 seed))
              (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#index owner 1usize)))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#let answer #u64 (#deref view)) (#drop view) (#forget owner)
              (#return (#u64.+.wrap answer child))",
        ] {
            let function = format!("(#fn work (: seed #u64) #u64 {body})");
            runtime_planned(prepare_generator("#async-fn-pinned", &function, main), 42);
        }
    }

    #[test]
    fn movable_array_selection_can_await_its_index() {
        let planning = prepare(
            "(#let items (#array #u64 1) (#array-of (#array #u64 1) seed))
          (#return (#index items (#as
            (#await Child ChildPending ChildReady child-poll (Start 0u64)) #usize)))",
            RUN,
        );
        runtime_planned(planning, 40);
    }

    #[test]
    fn movable_dynamic_selections_are_frozen_again_on_each_loop_iteration() {
        runtime(
            "(#let-mut index #usize 1usize)
              (#let-mut items (#array #u64 2) (#array-of (#array #u64 2) 0u64 0u64))
              (#for (#let-mut iteration #u64 0u64) (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
                (#set-index items index (#block (#set index (#usize.-.wrap 1usize index))
                  (#await Child ChildPending ChildReady child-poll (Start 21u64)))))
              (#return (#u64.+.wrap (#index items 0usize) (#index items 1usize)))",
            RUN,
            42,
        );
    }

    #[test]
    fn movable_polls_keep_explicitly_retired_local_handles_within_the_poll() {
        let main = format!(
            "(#struct Counter () (: value #u64))
          (#fn touch (: target (#ref-mut #u64)) ()
            (#deref-set target (#u64.+.wrap (#deref target) 1u64)) (#return ()))
          {RUN}"
        );
        for body in [
            "(#let-mut total #u64 seed)
              (#let view (#ref-mut #u64) (#borrow-mut total))
              (#call touch (: target view)) (#call touch (: target view))
              (#forget view)
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#return (#u64.+.wrap total child))",
            "(#let-mut counter Counter (#struct-literal Counter (: value seed)))
              (#let container (#ref-mut Counter) (#borrow-mut counter))
              (#call touch (: target (#borrow-mut (#get container value))))
              (#call touch (: target (#borrow-mut (#get container value))))
              (#forget container)
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#let answer #u64 (#get counter value)) (#forget counter)
              (#return (#u64.+.wrap answer child))",
            "(#let total #u64 seed)
              (#let view (#ref #u64) (#borrow total))
              (#let answer #u64 (#deref view)) (#forget view)
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap answer child))",
            "(#let total #u64 seed)
              (#let answer #u64 (#borrow total (#u64.+.wrap total 2u64)))
              (#let child #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
              (#return (#u64.+.wrap answer child))",
        ] {
            runtime(body, &main, 42);
        }
    }

    #[test]
    fn movable_local_references_require_complete_physical_boundary_proofs() {
        let body = "(#let owner #u64 seed)
          (#let view (#ref #u64) (#borrow owner))
          (#let answer #u64 (#deref view)) (#forget view)
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
          (#return (#u64.+.wrap answer extra))";
        let planning = prepare(body, RUN);
        let function = &planning.functions[0];
        let mut emitter = Emitter::new(&planning, function).unwrap();
        let view = BindingId(
            function
                .graph
                .bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let slot = &emitter.slots[emitter.bindings[&view]];
        assert!(!slot.raw, "poll-local loans must retain their capability");
        assert!(slot.anchor.is_some(), "movement still needs anchor facts");
        emitter.reference_cells = None;
        assert!(emitter
            .validate_movable_reference_boundaries()
            .unwrap_err()
            .message
            .contains("physical suspension-cell facts"));
        let mut emitter = Emitter::new(&planning, function).unwrap();
        emitter
            .reference_cells
            .as_mut()
            .unwrap()
            .pending_empty
            .clear();
        assert!(emitter
            .validate_movable_reference_boundaries()
            .unwrap_err()
            .message
            .contains("every reachable Pending boundary"));

        // A selected address is an implementation detail, not permission to
        // move a frame containing a live local loan. Require the same physical
        // Empty proof even when the original capability is pointer-backed.
        let selected = prepare(
            "(#let left #u64 seed) (#let right #u64 50u64)
              (#let view (#ref #u64)
                (#if (#u64.== seed 40u64) (#borrow left) (#borrow right)))
              (#let answer #u64 (#deref view)) (#forget view)
              (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap answer extra))",
            RUN,
        );
        let function = &selected.functions[0];
        let mut emitter = Emitter::new(&selected, function).unwrap();
        let view = BindingId(
            function
                .graph
                .bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let slot = &emitter.slots[emitter.bindings[&view]];
        assert!(
            slot.raw,
            "multi-target handles must preserve the selected address"
        );
        assert!(
            slot.anchor.is_some(),
            "selection still needs referent facts"
        );
        emitter.validate_movable_reference_boundaries().unwrap();
        emitter
            .reference_cells
            .as_mut()
            .unwrap()
            .pending_empty
            .clear();
        assert!(emitter
            .validate_movable_reference_boundaries()
            .unwrap_err()
            .message
            .contains("every reachable Pending boundary"));

        for body in [
            "(#let owner #u64 seed)
              (#let view (#ref #u64) (#borrow owner))
              (#let alias (#ref #u64) view) (#forget view)
              (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#let answer #u64 (#deref alias)) (#forget alias)
              (#return (#u64.+.wrap answer extra))",
            "(#let owner #u64 seed)
              (#let view (#ref #u64) (#borrow owner))
              (#if (#u64.== seed 40u64) (#forget view)
                (#block
                  (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
                  (#assert (#u64.== (#deref view) seed)) (#forget view) ()))
              (#return seed)",
            "(#let owner #u64 seed)
              (#let holder Holder (#struct-literal Holder (: view (#borrow owner))))
              (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#let answer #u64 (#deref (#get holder view))) (#forget holder)
              (#return (#u64.+.wrap answer extra))",
        ] {
            let planning = prepare(
                body,
                &format!("(#struct Holder () (: view (#ref #u64))) {RUN}"),
            );
            let error = generate(&planning)
                .err()
                .expect("a retained local loan cannot move with the frame");
            assert_eq!(
                error.message,
                "local references surviving suspension require a pinned async frame"
            );
            assert_ne!(error.span, planning.functions[0].source.function.span);
        }
    }

    #[test]
    fn movable_index_metadata_does_not_authorize_user_self_references() {
        let planning = prepare(
            "(#let items (#array #u64 2) (#array-of (#array #u64 2) seed 0u64))
              (#let index #usize 0usize)
              (#let view (#ref #u64) (#borrow (#index items index)))
              (#let answer #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#return (#u64.+.wrap (#deref view) answer))",
            RUN,
        );
        let error = generate(&planning)
            .err()
            .expect("movable self-reference must be rejected");
        assert!(
            error.message.contains("pinned") || error.message.contains("stable"),
            "{}",
            error.message
        );
    }

    #[test]
    fn unsupported_storage_modes_fail_before_proposing_unsafe_code() {
        let planning = prepare(
            "
          (#let owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) seed 2u64))
          (#let view (#ref #u64) (#borrow (#get owner 0)))
          (#return (#u64.+.wrap (#deref view)
            (#await Child ChildPending ChildReady child-poll (Start 2u64))))",
            RUN,
        );
        let error = generate(&planning).err().unwrap();
        assert_eq!(
            error.message,
            "local references surviving suspension require a pinned async frame"
        );
        let source = &planning.program.source_files[error.span.source_id as usize].source;
        assert_eq!(
            &source[error.span.start..error.span.end],
            "(#borrow (#get owner 0))"
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
        let generated = generate(&planning).unwrap();
        let ordinary = program(&planning, &generated).unwrap();
        crate::CheckedProgram::validate_with_span(&ordinary).unwrap();
    }

    #[test]
    fn user_panic_call_survives_await_and_ordinary_code_generation() {
        runtime(
            "(#return (#call panic (: value
              (#await Child ChildPending ChildReady child-poll (Start seed)))))",
            "(#fn panic ((value #u64)) #u64 (#return value))
             (#fn main () #u64
               (#let waker #u64 0u64)
               (#let task Work-task (#call work (: seed 42u64)))
               (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
               (#let-else (work-pending next) Work-poll-result first (#unreachable))
               (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
                 (#case (work-ready answer) answer)
                 (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))",
            42,
        );
    }

    #[test]
    fn constructors_run_on_execution_not_creation_or_pending_retry() {
        let main = "
          (#unsafe-fn make-child ((seed #u64) (count (#ptr-mut #u64))) Child
            (#unsafe (#ptr-write count (#u64.+.wrap (#ptr-read count) 1u64)))
            (#return (Start seed)))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut count #u64 0u64)
            (#let pointer (#ptr-mut #u64) (#unsafe (#asm (#ptr-mut #u64)
              ((rdi (#borrow-mut count))) \"and rdi, -2\\nmov rax, rdi\")))
            (#let task Work-task (#call work (: seed 40u64 : count pointer)))
            (#assert (#u64.== count 0u64))
            (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#let-else (work-pending next) Work-poll-result first (#unreachable))
            (#assert (#u64.== count 1u64))
            (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
              (#case (work-ready value) (#block
                (#assert (#u64.== count 1u64)) value))
              (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";
        let planning = prepare_function(
            "(#fn work ((seed #u64) (count (#ptr-mut #u64))) #u64
          (#return (#u64.+.wrap seed (#await Child ChildPending ChildReady child-poll
            (#unsafe (#call make-child (: seed 2u64 : count count)))))))",
            main,
        );
        runtime_planned(planning, 42);
    }
}
