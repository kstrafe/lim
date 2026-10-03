//! Actual caller relationships for references stored inside a borrowed owner.
//!
//! A parameter's pointer-slot name is not its physical referent. Preserve the
//! storage slot and the owner-relative pointee separately before attempting a
//! context-sensitive callee check. This plan grants no borrow permission and
//! does not replace ordinary checking or initialization/retirement contracts.
//! This remains staged: caller loans and callee entry states must stay
//! correlated before conditional poll functions can use these entry seeds.
#![allow(dead_code)]

use crate::typed_body::{BindingId, Body, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId, LoanOrigin};
use crate::typed_ir::{resolve_type, Declarations, FunctionId};
use crate::typed_place::{Place, Segment};
use crate::Type;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Alias {
    pub parameter: BindingId,
    /// Position of the child pointer in the incoming parameter value.
    pub storage: Vec<Segment>,
    /// Incoming pointer whose actual pointee owns the child's target.
    pub owner_input: Vec<Segment>,
    /// Physical projection from that owner's pointee, not from the child slot.
    pub projection: Vec<Segment>,
    pub mutable: bool,
    pub pinned: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Plan {
    pub callee: FunctionId,
    pub aliases: Vec<Alias>,
}

/// One immutable-declaration analysis run, never a persistent compiler cache.
#[derive(Default)]
struct Cache {
    baseline: HashMap<FunctionId, std::rc::Rc<FlowLoanOrigins>>,
    checked: HashSet<Plan>,
}

pub(crate) fn check_calls(
    body: &Body,
    flow: &FlowGraph,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &std::cell::OnceCell<FlowLoanOrigins>,
) -> Result<(), crate::typed_borrow::BorrowConflict> {
    let mut checked = Cache::default();
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Evaluate(value) = node.action else {
            continue;
        };
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[value.0].kind
        else {
            continue;
        };
        let name = declarations
            .function_name(*callee)
            .expect("resolved function identity");
        if declarations.bodies.get(name).is_some_and(|target| {
            target
                .parameter_referent_loan_slots
                .iter()
                .all(Vec::is_empty)
        }) {
            continue;
        }
        let origins = cache.get_or_init(|| flow.loan_origins(body));
        let event = FlowNodeId(index);
        let plan =
            Plan::for_call(body, flow, event, value, origins, declarations).map_err(|message| {
                crate::typed_borrow::BorrowConflict {
                    message,
                    span: node.span,
                    labels: vec![],
                }
            })?;
        if let Err((parameter, mut error)) =
            plan.check_owner_writes_inner(declarations, types, &mut Vec::new(), &mut checked)
        {
            if let Some(span) = error.span {
                error.labels.push((
                    span,
                    "callee accesses the internally borrowed owner here".into(),
                ));
            }
            error.span = children
                .get(parameter.0 + 1)
                .and_then(|argument| body.nodes[argument.0].span)
                .or(node.span);
            return Err(error);
        }
    }
    Ok(())
}

fn static_path(path: &[Segment]) -> bool {
    path.iter().all(|segment| {
        matches!(
            segment,
            Segment::Field(_) | Segment::Tuple(_) | Segment::Payload(_, _) | Segment::Index(_)
        )
    })
}

fn same_pointer_root(parent: &LoanOrigin, child: &LoanOrigin) -> bool {
    parent.place.root == child.place.root
        && (!matches!(parent.place.root, PlaceRoot::Parameter(_))
            || parent.parameter_storage == child.parameter_storage)
}

/// Validate source identities rather than reinterpreting a name as a field.
fn project(mut ty: Type, path: &[Segment], declarations: &Declarations) -> Result<Type, String> {
    for segment in path {
        ty = resolve_type(&ty, &declarations.aliases)?;
        ty = match (segment, ty) {
            (
                Segment::Dereference,
                Type::Reference { target, .. } | Type::PinnedReference { target, .. },
            ) => *target,
            (Segment::Field(id), Type::Named(owner)) => {
                let field = declarations
                    .structs
                    .get(&owner)
                    .and_then(|fields| fields.get(id.index))
                    .ok_or("incoming self-loan lost its checked field")?;
                if declarations.field_id(&Type::Named(owner), &field.name) != Some(*id) {
                    return Err("incoming self-loan lost its field identity".into());
                }
                field.ty.clone()
            }
            (Segment::Tuple(index), Type::Tuple(elements)) => elements
                .get(*index)
                .cloned()
                .ok_or("incoming self-loan tuple index is out of bounds")?,
            (Segment::Payload(id, index), Type::Named(owner)) => {
                let variant = declarations
                    .enums
                    .get(&owner)
                    .and_then(|variants| variants.get(id.index))
                    .ok_or("incoming self-loan lost its checked variant")?;
                if declarations.variant_id(&Type::Named(owner), &variant.name) != Some(*id) {
                    return Err("incoming self-loan lost its variant identity".into());
                }
                variant
                    .fields
                    .get(*index)
                    .cloned()
                    .ok_or("incoming self-loan payload index is out of bounds")?
            }
            (Segment::Index(index), Type::Array(element, length)) if *index < length as u128 => {
                *element
            }
            _ => return Err("incoming self-loan needs a checked static storage path".into()),
        };
    }
    resolve_type(&ty, &declarations.aliases)
}

impl Alias {
    pub fn validate(
        &self,
        parameter_type: &Type,
        declarations: &Declarations,
    ) -> Result<(), String> {
        let mut prefix = self.owner_input.clone();
        prefix.push(Segment::Dereference);
        if !static_path(&self.owner_input)
            || !self.storage.starts_with(&prefix)
            || !static_path(&self.storage[prefix.len()..])
        {
            return Err("incoming self-loan storage is not inside its owner pointee".into());
        }
        let owner = project(parameter_type.clone(), &self.owner_input, declarations)?;
        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) = owner else {
            return Err("incoming self-loan owner is not a reference slot".into());
        };
        let child = project(parameter_type.clone(), &self.storage, declarations)?;
        let (target_type, mutable, pinned) = match child {
            Type::Reference { target, mutable } => (*target, mutable, false),
            Type::PinnedReference { target, mutable } => (*target, mutable, true),
            _ => return Err("incoming self-loan storage is not a reference slot".into()),
        };
        if (self.mutable && !mutable) || pinned != self.pinned {
            return Err("incoming self-loan changed its reference capability".into());
        }
        if !static_path(&self.projection) {
            return Err("incoming self-loan needs its selected address snapshot".into());
        }
        let leaf = project(*target, &self.projection, declarations)?;
        if leaf != target_type {
            return Err("incoming self-loan disagrees with its checked pointee type".into());
        }
        Ok(())
    }
}

impl Plan {
    pub fn for_call(
        body: &Body,
        flow: &FlowGraph,
        event: FlowNodeId,
        value: NodeId,
        origins: &FlowLoanOrigins,
        declarations: &Declarations,
    ) -> Result<Self, String> {
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[value.0].kind
        else {
            return Err("incoming self-loans require an actual resolved call".into());
        };
        declarations
            .function_name(*callee)
            .ok_or("incoming self-loan callee identity disappeared")?;
        let target = &declarations.function(*callee).signature;
        if children.len() != target.parameters.len() + 1 {
            return Err("incoming self-loan call argument identities changed".into());
        }
        let mut aliases = Vec::new();
        for (parameter, argument) in children.iter().skip(1).enumerate() {
            let ty = &target.parameters[parameter];
            for parent in origins.value_before(body, flow, event, *argument) {
                if parent.lifetime_only
                    || !static_path(&parent.storage)
                    || !static_path(&parent.place.segments)
                {
                    continue;
                }
                let pointer = project(ty.clone(), &parent.storage, declarations)?;
                if !matches!(
                    pointer,
                    Type::Reference { .. } | Type::PinnedReference { .. }
                ) {
                    continue;
                }
                for child in origins.pointee_before(body, event, &parent) {
                    if child.lifetime_only
                        || !same_pointer_root(&parent, &child)
                        || !child.place.segments.starts_with(&parent.place.segments)
                        || !static_path(&child.storage)
                    {
                        continue;
                    }
                    let mut storage = parent.storage.clone();
                    storage.push(Segment::Dereference);
                    storage.extend_from_slice(&child.storage);
                    let alias = Alias {
                        parameter: BindingId(parameter),
                        storage,
                        owner_input: parent.storage.clone(),
                        projection: child.place.segments[parent.place.segments.len()..].to_vec(),
                        mutable: child.mutable,
                        pinned: child.pinned,
                    };
                    alias.validate(ty, declarations)?;
                    if !aliases.contains(&alias) {
                        aliases.push(alias);
                    }
                }
            }
        }
        Ok(Self {
            callee: *callee,
            aliases,
        })
    }

    /// This is an additional rejection check, NOT a proof granting a parent
    /// reborrow. In particular it does not waive existing direct/call checks.
    /// Callee entry seeds are may-aliases; definite replacement may retire them,
    /// but a branch-only clear must not erase a retained child.
    #[cfg(test)]
    pub fn check_owner_writes(
        &self,
        declarations: &Declarations,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), crate::typed_borrow::BorrowConflict> {
        self.check_owner_writes_inner(declarations, types, &mut Vec::new(), &mut Cache::default())
            .map_err(|(_, error)| error)
    }

    fn check_owner_writes_inner(
        &self,
        declarations: &Declarations,
        types: &crate::linearcheck::LinearTypes,
        stack: &mut Vec<FunctionId>,
        cache: &mut Cache,
    ) -> Result<(), (BindingId, crate::typed_borrow::BorrowConflict)> {
        use crate::typed_borrow::BorrowConflict;
        if self.aliases.is_empty() || cache.checked.contains(self) {
            return Ok(());
        }
        let name = declarations
            .function_name(self.callee)
            .expect("checked callee identity");
        let Some(body) = declarations.bodies.get(name) else {
            return Err((
                self.aliases[0].parameter,
                BorrowConflict {
                    message:
                        "cannot inspect callee access to an owner containing internal references"
                            .into(),
                    span: None,
                    labels: vec![],
                },
            ));
        };
        if stack.contains(&self.callee) {
            return Err((
                self.aliases[0].parameter,
                BorrowConflict {
                    message: "recursive internal-loan checking is not permitted".into(),
                    span: None,
                    labels: vec![],
                },
            ));
        }
        stack.push(self.callee);
        let flow = &declarations.flows[name];
        let origins = flow.loan_origins_with_entry_aliases(body, &self.aliases);
        let baseline = cache
            .baseline
            .entry(self.callee)
            .or_insert_with(|| std::rc::Rc::new(flow.loan_origins(body)))
            .clone();
        let consumptions = flow.consumptions(body, types);
        let live = flow.liveness(body);
        for (index, node) in flow.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            let live_bindings = live
                .before(event)
                .into_iter()
                .filter(|binding| {
                    binding.0 >= body.parameter_count
                        && !consumptions.definitely_consumed_before(
                            event,
                            &Place::root(PlaceRoot::Local(*binding)),
                        )
                })
                .collect::<Vec<_>>();
            // Baseline pointer-slot identity identifies accesses through the
            // owner, as opposed to legitimate writes through its child handle.
            // The specialized solver supplies the child's actual lifetime.
            let mut writes = baseline
                .stores_before(body, flow, event)
                .into_iter()
                .map(|store| store.destination)
                .collect::<Vec<_>>();
            match &node.action {
                FlowAction::Read {
                    place,
                    place_base: false,
                    ..
                } if consumptions.consumes_at(event, place) => {
                    if let PlaceRoot::Local(binding) = place.root {
                        writes.extend(baseline.projected_origins(event, binding, &place.segments));
                    }
                }
                FlowAction::Release { place, .. } => {
                    if let PlaceRoot::Local(binding) = place.root {
                        writes.extend(baseline.projected_origins(event, binding, &place.segments));
                    }
                }
                FlowAction::Evaluate(value) if body.consuming_pin_reads.contains(value) => {
                    if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                        writes.extend(baseline.value_before(body, flow, event, children[1]));
                    }
                }
                _ => {}
            }
            for (family, alias) in self.aliases.iter().enumerate() {
                if !origins.entry_alias_retained_before(event, family, alias, &live_bindings) {
                    continue;
                }
                let held = Place {
                    root: PlaceRoot::Parameter(alias.parameter),
                    segments: alias.projection.clone(),
                };
                if writes.iter().any(|write| {
                    write.place.root == held.root
                        && write.parameter_storage.as_deref() == Some(alias.owner_input.as_slice())
                        && write.place.overlaps(&held)
                }) {
                    return Err((alias.parameter, BorrowConflict {
                        message: format!("cannot mutate or consume an owner while its stored internal reference is retained in '{name}'"),
                        span: node.span, labels: vec![],
                    }));
                }
            }
            if let FlowAction::Evaluate(value) = node.action {
                if matches!(
                    body.nodes[value.0].kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                ) {
                    let nested = Self::for_call(body, flow, event, value, &origins, declarations)
                        .map_err(|message| {
                        (
                            self.aliases[0].parameter,
                            BorrowConflict {
                                message,
                                span: node.span,
                                labels: vec![],
                            },
                        )
                    })?;
                    if let Err((parameter, error)) =
                        nested.check_owner_writes_inner(declarations, types, stack, cache)
                    {
                        let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                            unreachable!()
                        };
                        let parameter = origins
                            .value_before(body, flow, event, children[parameter.0 + 1])
                            .into_iter()
                            .find_map(|origin| match origin.place.root {
                                PlaceRoot::Parameter(parameter)
                                    if self
                                        .aliases
                                        .iter()
                                        .any(|alias| alias.parameter == parameter) =>
                                {
                                    Some(parameter)
                                }
                                _ => None,
                            })
                            .unwrap_or(self.aliases[0].parameter);
                        return Err((parameter, error));
                    }
                }
            }
        }
        stack.pop();
        cache.checked.insert(self.clone());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_flow::FlowAction;

    const SOURCE: &str = "
      (#struct Link (: value u64 : state u32 : view (#pin-ref u64)))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref u64) (#pin-borrow (#get target value)))
        (#pin-set-field target view view) (#return target))
      (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#pin-set-field target state 2u32) (#return target))
      (#fn driver (: outside (#pin-ref u64)) u64
        (#let-mut link Link (#struct-literal Link (: value 42u64 : state 0u32 : view outside)))
        (#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let installed (#pin-ref-mut Link) (#call install (: target running)))
        (#set running installed)
        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))
        (#set running updated)
        (#pin-set-field running view outside)
        (#drop running) (#forget link) (#return 0u64))";

    fn fixture(source: &str) -> Declarations {
        let program = crate::parse_program(source).unwrap();
        let mut declarations = crate::typecheck::resolve_program_for_analysis(&program, false)
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        declarations.staged_parameter_contents_summaries();
        declarations
    }

    fn call_plan(declarations: &Declarations, caller: &str, callee: &str) -> Plan {
        let body = &declarations.bodies[caller];
        let flow = &declarations.flows[caller];
        let origins = flow.loan_origins(body);
        let id = declarations.function_id(callee).unwrap();
        let (event, value) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, event)| match event.action {
                FlowAction::Evaluate(value)
                    if matches!(body.nodes[value.0].kind,
                    NodeKind::Form { callee: Some(found), .. } if found == id) =>
                {
                    Some((FlowNodeId(index), value))
                }
                _ => None,
            })
            .unwrap();
        Plan::for_call(body, flow, event, value, &origins, declarations).unwrap()
    }

    #[test]
    fn actual_stored_self_loan_has_separate_storage_and_referent_paths() {
        let declarations = fixture(SOURCE);
        let plan = call_plan(&declarations, "driver", "tick");
        let view = declarations
            .field_id(&Type::Named("Link".into()), "view")
            .unwrap();
        let value = declarations
            .field_id(&Type::Named("Link".into()), "value")
            .unwrap();
        assert_eq!(plan.callee, declarations.function_id("tick").unwrap());
        assert_eq!(
            plan.aliases,
            vec![Alias {
                parameter: BindingId(0),
                storage: vec![Segment::Dereference, Segment::Field(view)],
                owner_input: vec![],
                projection: vec![Segment::Field(value)],
                mutable: false,
                pinned: true,
            }]
        );
        assert!(call_plan(&declarations, "driver", "install")
            .aliases
            .is_empty());
    }

    #[test]
    fn external_pointees_and_cleared_self_loans_are_not_owner_aliases() {
        for source in [
            SOURCE.replace("(#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)", ""),
            SOURCE.replace("(#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
                "(#pin-set-field running view outside) (#let updated (#pin-ref-mut Link) (#call tick (: target running)))"),
        ] {
            let declarations = fixture(&source);
            assert!(call_plan(&declarations, "driver", "tick").aliases.is_empty());
        }
    }

    #[test]
    fn symbolic_nested_pointer_slots_do_not_imply_physical_self_aliases() {
        let source = "(#struct Link (: value u64 : view (#pin-ref u64)))
          (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link) (#return target))
          (#fn driver (: input (#pin-ref-mut Link)) (#pin-ref-mut Link)
            (#return (#call tick (: target input))))";
        let declarations = fixture(source);
        assert!(call_plan(&declarations, "driver", "tick")
            .aliases
            .is_empty());
    }

    #[test]
    fn malformed_storage_capabilities_and_pointee_types_fail_closed() {
        let declarations = fixture(SOURCE);
        let plan = call_plan(&declarations, "driver", "tick");
        let alias = plan.aliases.first().unwrap();
        let ty = &declarations.bodies["tick"].bindings[0].ty;
        for kind in 0..6 {
            let mut bad = alias.clone();
            match kind {
                0 => {
                    if let Segment::Field(field) = &mut bad.storage[1] {
                        field.index = usize::MAX;
                    }
                }
                1 => bad.projection = vec![Segment::DynamicIndex],
                2 => bad.mutable = true,
                3 => bad.pinned = false,
                5 => {
                    bad.storage.clear();
                    bad.projection.clear();
                }
                _ => {
                    bad.projection = vec![Segment::Field(
                        declarations
                            .field_id(&Type::Named("Link".into()), "state")
                            .unwrap(),
                    )]
                }
            }
            assert!(bad.validate(ty, &declarations).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn disjoint_owner_writes_and_writes_through_the_child_are_not_rejected() {
        for operation in [
            "(#pin-set-field target state 2u32)",
            "(#let observed u64 (#deref (#get target view))) (#forget observed)",
        ] {
            let source = SOURCE.replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            plan.check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
                .unwrap();
        }
    }

    #[test]
    fn destructive_owner_writes_are_checked_using_actual_incoming_aliases() {
        let source = SOURCE.replace(
            "(#pin-set-field target state 2u32)",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        let error = plan
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &source[span.start..span.end],
            "(#pin-set-field target value 99u64)"
        );
        // An external child pointer does not borrow the owner's value field.
        let external = source.replace("(#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)", "");
        let declarations = fixture(&external);
        call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
    }

    #[test]
    fn definite_clear_retires_entry_alias_but_conditional_clear_does_not() {
        for conditional in [false, true] {
            let clear = if conditional {
                "(#if (#u32.== (#get target state) 0u32) (#pin-set-field target view outside) ())"
            } else {
                "(#pin-set-field target view outside)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
                )
                .replace(
                    "(#pin-set-field target state 2u32)",
                    &format!("{clear} (#pin-set-field target value 99u64)"),
                );
            let declarations = fixture(&source);
            let result = call_plan(&declarations, "driver", "tick")
                .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(result.is_err(), conditional, "{result:?}\n{source}");
        }
    }

    #[test]
    fn staged_check_locates_destructive_calls_with_temporary_parent_origins() {
        let source = SOURCE.replace(
            "(#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))\n        (#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)\n        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))\n        (#set running updated)\n        (#pin-set-field running view outside)\n        (#drop running)",
            "(#let running (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))\n        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))\n        (#pin-set-field updated view outside) (#drop updated)",
        );
        let program = crate::parse_program(&source).unwrap();
        crate::CheckedProgram::validate(&program)
            .unwrap_or_else(|error| panic!("{error}\n{source}"));
        let invalid = source.replace(
            "(#pin-set-field target state 2u32)",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&invalid);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let error = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_err();
        assert!(
            error.message.contains("stored internal reference"),
            "{}",
            error.message
        );
        let span = error.span.unwrap();
        assert_eq!(&invalid[span.start..span.end], "running");
        assert!(error.labels.iter().any(
            |(span, _)| &invalid[span.start..span.end] == "(#pin-set-field target value 99u64)"
        ));
    }

    #[test]
    fn aliases_are_substituted_into_nested_callee_checks() {
        let source = format!("{SOURCE}").replace(
            "(#pin-set-field target state 2u32) (#return target)",
            "(#return (#call smash (: owner target)))",
        ) + "\n(#fn smash (: owner (#pin-ref-mut Link)) (#pin-ref-mut Link)
          (#pin-set-field owner value 99u64) (#return owner))";
        let declarations = fixture(&source);
        let result = call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default());
        let error = result.unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &source[span.start..span.end],
            "(#call smash (: owner target))"
        );
    }

    #[test]
    fn nested_tuple_projection_is_physical_not_child_pointer_storage() {
        let source = SOURCE
            .replace(": value u64", ": value (#tuple u64 u64)")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow (#get (#get target value) 1))",
            )
            .replace(
                ": value 42u64",
                ": value (#tuple (#tuple u64 u64) 1u64 42u64)",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 1);
        assert_eq!(plan.aliases[0].projection.last(), Some(&Segment::Tuple(1)));
        plan.check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
        let invalid = source.replace("(#pin-set-field target state 2u32)",
            "(#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64)))");
        let declarations = fixture(&invalid);
        assert!(call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .is_err());
    }

    #[test]
    fn retained_exclusive_child_permits_its_own_write_not_an_owner_write() {
        let source = SOURCE
            .replace("#pin-ref u64", "#pin-ref-mut u64")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow-mut (#get target value))",
            )
            .replace(
                "(#pin-set-field target view view)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view))",
            )
            .replace(
                "(#pin-set-field running view outside)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get running view)) outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#unsafe (#pin-write (#get target view) 9u64))",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 1);
        assert!(plan.aliases[0].mutable);
        plan.check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
        let invalid = source.replace(
            "(#unsafe (#pin-write (#get target view) 9u64))",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&invalid);
        assert!(call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .is_err());
    }

    #[test]
    fn clearing_the_field_does_not_retire_a_live_local_child_copy() {
        for read_after_write in [false, true] {
            let operation = if read_after_write {
                "(#let saved (#pin-ref u64) (#get target view))
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)
                 (#let observed u64 (#deref saved)) (#forget observed)"
            } else {
                "(#let saved (#pin-ref u64) (#get target view))
                 (#let observed u64 (#deref saved)) (#forget observed)
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
                )
                .replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let result = call_plan(&declarations, "driver", "tick")
                .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(result.is_err(), read_after_write, "{result:?}\n{source}");
        }
    }

    #[test]
    fn fresh_same_address_borrows_do_not_resurrect_retired_entry_loans() {
        for keep_copy in [false, true] {
            let save = if keep_copy {
                "(#let saved (#pin-ref u64) (#get target view))"
            } else {
                ""
            };
            let use_copy = if keep_copy {
                "(#let observed u64 (#deref saved)) (#forget observed)"
            } else {
                ""
            };
            let operation = format!(
                "{save}
              (#pin-set-field target view outside)
              (#let fresh (#pin-ref u64) (#pin-borrow (#get target value)))
              (#pin-set-field target view fresh)
              (#pin-set-field target state 2u32) {use_copy}"
            );
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
                )
                .replace("(#pin-set-field target state 2u32)", &operation);
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            let body = &declarations.bodies["tick"];
            let flow = &declarations.flows["tick"];
            let origins = flow.loan_origins_with_entry_aliases(body, &plan.aliases);
            let state_field = declarations
                .field_id(&Type::Named("Link".into()), "state")
                .unwrap();
            let event = flow.nodes.iter().enumerate().find_map(|(index, node)| {
                let value = match node.action {
                    FlowAction::Evaluate(value) | FlowAction::Write { value, .. } => value,
                    _ => return None,
                };
                let NodeKind::Form { head, children, callee: None, .. } = &body.nodes[value.0].kind else { return None; };
                (head == "pin-set-field" && matches!(body.nodes[children[2].0].kind,
                    NodeKind::Declaration(crate::typed_ir::DeclarationId::Field(field)) if field == state_field))
                    .then_some(FlowNodeId(index))
            }).unwrap();
            let live = flow
                .liveness(body)
                .before(event)
                .into_iter()
                .filter(|binding| binding.0 >= body.parameter_count)
                .collect::<Vec<_>>();
            assert_eq!(
                origins.entry_alias_retained_before(event, 0, &plan.aliases[0], &live),
                keep_copy
            );
            let actual =
                origins.pointee_before(body, event, &origins.before(event, BindingId(0))[0]);
            assert!(actual.iter().any(|origin| origin.place.root == PlaceRoot::Parameter(BindingId(0))
                && origin.place.segments == plan.aliases[0].projection && origin.entry_loan.is_none()),
                "the fresh same-address child exists independently of the incoming family: {actual:?}");
            assert!(!actual.iter().any(|origin| origin.entry_loan == Some(0)),
                "replacing the child field retires that stored copy, even when a separate local copy remains");
        }
    }

    #[test]
    fn projected_child_reborrows_retain_the_incoming_family() {
        let source = SOURCE
            .replace(": value u64", ": value (#tuple u64 u64)")
            .replace(
                ": value 42u64",
                ": value (#tuple (#tuple u64 u64) 40u64 2u64)",
            )
            .replace("#pin-ref u64", "#pin-ref (#tuple u64 u64)")
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref (#tuple u64 u64)))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref u64) (#pin-borrow (#get (#get target view) 1)))
                 (#pin-set-field target view outside)
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64)))
                 (#let observed u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64))");
    }

    #[test]
    fn separate_incoming_families_at_one_address_retire_independently() {
        let source = SOURCE
            .replace(
                ": view (#pin-ref u64)))",
                ": view (#pin-ref u64) : second (#pin-ref u64)))",
            )
            .replace(": view outside", ": view outside : second outside")
            .replace(
                "(#pin-set-field target view view)",
                "(#pin-set-field target view view) (#pin-set-field target second view)",
            )
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#pin-set-field target view outside) (#pin-set-field target state 2u32)",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 2);
        assert_eq!(plan.aliases[0].projection, plan.aliases[1].projection);
        let body = &declarations.bodies["tick"];
        let flow = &declarations.flows["tick"];
        let origins = flow.loan_origins_with_entry_aliases(body, &plan.aliases);
        let field = |name| {
            declarations
                .field_id(&Type::Named("Link".into()), name)
                .unwrap()
        };
        let event = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Write { place, .. }
                    if place.segments.last() == Some(&Segment::Field(field("state"))) =>
                {
                    Some(FlowNodeId(index))
                }
                _ => None,
            })
            .unwrap();
        for (family, alias) in plan.aliases.iter().enumerate() {
            assert_eq!(
                origins.entry_alias_retained_before(event, family, alias, &[]),
                alias.storage.last() == Some(&Segment::Field(field("second")))
            );
        }
    }

    #[test]
    fn projected_borrows_keep_the_receiver_evaluated_before_index_effects() {
        let source = SOURCE
            .replace(": value u64", ": value (#array u64 2)")
            .replace(
                ": value 42u64",
                ": value (#array-of (#array u64 2) 40u64 42u64)",
            )
            .replace("#pin-ref u64", "#pin-ref (#array u64 2)")
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref (#array u64 2)))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref u64) (#pin-borrow (#index (#get target view)
                   (#block (#pin-set-field target view outside) 1usize))))
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value))
                   (#array-of (#array u64 2) 99u64 100u64)))
                 (#let observed u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_writes(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end],
            "(#pin-write (#pin-borrow-mut (#get target value))\n                   (#array-of (#array u64 2) 99u64 100u64))");
    }

    #[test]
    fn run_local_cache_keeps_distinct_alias_contexts_separate() {
        let source = SOURCE
            .replace(": state u32", ": state u64")
            .replace(": state 0u32", ": state 0u64")
            .replace("state 2u32", "state 2u64");
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        let types = crate::linearcheck::LinearTypes::default();
        let mut cache = Cache::default();
        for _ in 0..2 {
            plan.check_owner_writes_inner(&declarations, &types, &mut Vec::new(), &mut cache)
                .unwrap();
        }
        assert_eq!(cache.checked.len(), 1);
        assert_eq!(cache.baseline.len(), 1);
        let mut other = plan.clone();
        other.aliases[0].projection = vec![Segment::Field(
            declarations
                .field_id(&Type::Named("Link".into()), "state")
                .unwrap(),
        )];
        other.aliases[0]
            .validate(&declarations.bodies["tick"].bindings[0].ty, &declarations)
            .unwrap();
        assert!(other
            .check_owner_writes_inner(&declarations, &types, &mut Vec::new(), &mut cache)
            .is_err());
        assert!(!cache.checked.contains(&other));
        // A different set of declarations never inherits a checked context.
        assert!(Cache::default().checked.is_empty());
    }

    #[test]
    fn reordered_arguments_locate_the_owner_actually_accessed_by_the_callee() {
        let source = SOURCE.replace("(#fn tick (: target (#pin-ref-mut Link))",
            "(#fn tick (: first (#pin-ref-mut Link) : target (#pin-ref-mut Link))")
            .replace("(#pin-set-field target state 2u32)", "(#pin-set-field target value 99u64)")
            .replace("(#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
                "(#let-mut another Link (#struct-literal Link (: value 7u64 : state 0u32 : view outside)))
                 (#let second (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut another))))
                 (#let updated (#pin-ref-mut Link) (#call tick (: target second : first running)))");
        let declarations = fixture(&source);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let error = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "second");
    }
}
