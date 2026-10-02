//! Staged worker-contract coordinates for opaque task captures.
//!
//! This is identity substitution, not a spawn/join call contract. In particular,
//! worker normal-return facts must not become spawn completion guarantees or
//! apply to a failed join which still owns a running retry handle.

use crate::typed_body::{BindingId, PlaceRoot};
use crate::typed_flow::{
    ReferentExitEffect, ReferentFunctionEffects, ReferentRead, ReferentVariantExit,
};
use crate::typed_ir::{AggregateId, FunctionId};
use crate::typed_place::{Place, Segment};
use std::collections::HashMap;

/// Rebase an input selector onto a task capture, without changing its position
/// in the value being stored. Those output slots are not task fields.
pub(crate) fn capture_loan_summary(
    owner: AggregateId,
    parameters: usize,
    loan: &crate::typed_body::ParameterLoanSummary,
) -> Option<crate::typed_body::ParameterLoanSummary> {
    let mut captured = loan.clone();
    if loan.global.is_none() {
        if loan.parameter >= parameters {
            return None;
        }
        captured.parameter = 0;
        captured
            .input_storage
            .insert(0, Segment::ThreadCapture(owner, loan.parameter));
        for index in captured.storage_inputs.iter_mut().flatten() {
            if *index >= loan.input_storage.len() {
                return None;
            }
            *index += 1;
        }
    }
    Some(captured)
}

pub(crate) fn capture_store_summaries(
    owner: AggregateId,
    parameters: usize,
    stores: &[crate::typed_body::ParameterStoreSummary],
) -> Option<Vec<crate::typed_body::ParameterStoreSummary>> {
    stores
        .iter()
        .map(|store| {
            Some(crate::typed_body::ParameterStoreSummary {
                destination: capture_loan_summary(owner, parameters, &store.destination)?,
                sources: store
                    .sources
                    .iter()
                    .map(|source| capture_loan_summary(owner, parameters, source))
                    .collect::<Option<Vec<_>>>()?,
                definitely_written: store.definitely_written,
            })
        })
        .collect()
}

pub(crate) struct CapturedWorkerContract {
    pub worker: FunctionId,
    pub facts: ReferentFunctionEffects,
}

/// A running or retryable worker has not established its normal-return facts.
/// In particular this type intentionally has no restoration guarantees.
pub(crate) struct PendingWorkerEffects {
    pub effects: Vec<ReferentExitEffect>,
    pub unresolved: Vec<crate::typed_flow::FlowNodeId>,
    pub unresolved_reads: Vec<crate::typed_flow::FlowNodeId>,
}

impl CapturedWorkerContract {
    pub fn pending_effects(&self) -> PendingWorkerEffects {
        pending_effects(&self.facts)
    }
}

fn pending_effects(facts: &ReferentFunctionEffects) -> PendingWorkerEffects {
    let mut effects = Vec::<ReferentExitEffect>::new();
    // Exit effects miss transient consumption followed by restoration.
    // Keep both sources, retaining their exact storage identities/spans.
    let accesses = facts
        .consuming_accesses
        .iter()
        .map(|access| ReferentExitEffect {
            place: access.place.clone(),
            input_storage: access.input_storage.clone(),
            referent_projection: access.referent_projection.clone(),
            definitely_consumed: false,
            consumption_spans: vec![access.span],
        });
    for mut incoming in facts.effects.iter().cloned().chain(accesses) {
        if matches!(incoming.place.root, PlaceRoot::Local(_)) {
            continue;
        }
        incoming.definitely_consumed = false;
        if let Some(existing) = effects.iter_mut().find(|effect| {
            effect.place == incoming.place
                && effect.input_storage == incoming.input_storage
                && effect.referent_projection == incoming.referent_projection
        }) {
            for span in incoming.consumption_spans {
                if !existing.consumption_spans.contains(&span) {
                    existing.consumption_spans.push(span);
                }
            }
        } else {
            effects.push(incoming);
        }
    }
    PendingWorkerEffects {
        effects,
        unresolved: facts.unresolved.clone(),
        unresolved_reads: facts.unresolved_reads.clone(),
    }
}

/// Compiler operations return independently of worker completion: spawn can
/// fail, and join can return a retry handle. Only join-success selects final
/// worker state. Precondition coordinates stay those of spawn's worker args.
pub(crate) fn operation_summaries(
    worker: FunctionId,
    owner: AggregateId,
    body: &crate::typed_body::Body,
    facts: &ReferentFunctionEffects,
    infer_entry_contracts: bool,
    spawn_ok: crate::typed_ir::VariantId,
    spawn_error: crate::typed_ir::VariantId,
    join_ok: crate::typed_ir::VariantId,
    join_error: crate::typed_ir::VariantId,
) -> Option<(ReferentFunctionEffects, ReferentFunctionEffects)> {
    let captured = capture_worker_contract(worker, owner, body.parameter_count, facts)?;
    let pending = pending_effects(facts);
    let pending_capture = captured.pending_effects();
    let required = facts
        .consumed_entry
        .iter()
        .map(|place| {
            let (input_storage, referent_projection) =
                crate::typed_flow::split_referent_effect_place(body, place);
            ReferentExitEffect {
                place: place.clone(),
                input_storage,
                referent_projection,
                definitely_consumed: true,
                consumption_spans: Vec::new(),
            }
        })
        .collect::<Vec<_>>();
    let captures = Captures {
        owner,
        parameters: body.parameter_count,
    };
    let required_capture = captures.effects(&required)?;
    let restored = facts
        .restored_from_consumed_entry
        .iter()
        .map(|place| {
            let (input_storage, referent_projection) =
                crate::typed_flow::split_referent_effect_place(body, place);
            ReferentExitEffect {
                place: place.clone(),
                input_storage,
                referent_projection,
                definitely_consumed: true,
                consumption_spans: Vec::new(),
            }
        })
        .collect::<Vec<_>>();
    let restored_capture = captures.effects(&restored)?;
    let empty = || ReferentFunctionEffects {
        has_normal_return: true,
        effects: Vec::new(),
        unresolved: Vec::new(),
        reads: Vec::new(),
        unresolved_reads: Vec::new(),
        entry_reads: Vec::new(),
        consuming_accesses: Vec::new(),
        restored_from_consumed_entry: Vec::new(),
        consumed_entry: Vec::new(),
        effects_from_consumed_entry: Vec::new(),
        variant_exits: HashMap::new(),
    };
    let mut spawn = empty();
    spawn.effects = pending.effects.clone();
    spawn.unresolved = pending.unresolved.clone();
    spawn.unresolved_reads = pending.unresolved_reads.clone();
    spawn.entry_reads = facts
        .entry_reads
        .iter()
        .filter(|read| !matches!(read.place.root, PlaceRoot::Local(_)))
        .cloned()
        .collect();
    spawn.reads = spawn.entry_reads.clone();
    spawn.consumed_entry = facts.consumed_entry.clone();
    spawn.effects_from_consumed_entry = pending.effects.clone();
    spawn
        .effects_from_consumed_entry
        .extend(required.iter().cloned());
    spawn.variant_exits.insert(
        spawn_ok,
        ReferentVariantExit {
            restored: Vec::new(),
            has_normal_return: true,
            effects: pending.effects,
            effects_from_consumed_entry: infer_entry_contracts
                .then(|| spawn.effects_from_consumed_entry.clone()),
            consumed_entry: required.clone(),
            unresolved: pending.unresolved,
        },
    );
    spawn.variant_exits.insert(
        spawn_error,
        ReferentVariantExit {
            restored: Vec::new(),
            has_normal_return: true,
            effects: Vec::new(),
            effects_from_consumed_entry: infer_entry_contracts.then_some(required),
            consumed_entry: Vec::new(),
            unresolved: Vec::new(),
        },
    );
    // Do not install unconditional completed-worker restoration or reads in
    // join: its error result still owns a potentially running worker.
    let mut join = empty();
    join.effects = pending_capture.effects.clone();
    join.unresolved = pending_capture.unresolved.clone();
    join.unresolved_reads = pending_capture.unresolved_reads;
    join.variant_exits.insert(
        join_ok,
        ReferentVariantExit {
            restored: restored_capture,
            has_normal_return: captured.facts.has_normal_return,
            effects: captured.facts.effects,
            effects_from_consumed_entry: infer_entry_contracts
                .then_some(captured.facts.effects_from_consumed_entry),
            consumed_entry: required_capture,
            unresolved: captured.facts.unresolved,
        },
    );
    join.variant_exits.insert(
        join_error,
        ReferentVariantExit {
            restored: Vec::new(),
            has_normal_return: true,
            effects: pending_capture.effects,
            effects_from_consumed_entry: None,
            consumed_entry: Vec::new(),
            unresolved: pending_capture.unresolved,
        },
    );
    Some((spawn, join))
}

struct Captures {
    owner: AggregateId,
    parameters: usize,
}

impl Captures {
    fn place(&self, place: &Place) -> Option<Place> {
        match place.root {
            PlaceRoot::Parameter(binding) if binding.0 < self.parameters => {
                let mut segments = vec![Segment::ThreadCapture(self.owner, binding.0)];
                segments.extend(place.segments.iter().cloned());
                Some(Place {
                    root: PlaceRoot::Parameter(BindingId(0)),
                    segments,
                })
            }
            PlaceRoot::Global(_) => Some(place.clone()),
            _ => None,
        }
    }

    fn slot(&self, place: &Place, slot: &Option<Vec<Segment>>) -> Option<Vec<Segment>> {
        match place.root {
            PlaceRoot::Parameter(binding) => slot.as_ref().map(|slot| {
                let mut captured = vec![Segment::ThreadCapture(self.owner, binding.0)];
                captured.extend(slot.iter().cloned());
                captured
            }),
            _ => slot.clone(),
        }
    }

    fn effects(&self, effects: &[ReferentExitEffect]) -> Option<Vec<ReferentExitEffect>> {
        effects
            .iter()
            .filter(|effect| !matches!(effect.place.root, PlaceRoot::Local(_)))
            .map(|effect| {
                Some(ReferentExitEffect {
                    place: self.place(&effect.place)?,
                    input_storage: self.slot(&effect.place, &effect.input_storage),
                    referent_projection: effect.referent_projection.clone(),
                    definitely_consumed: effect.definitely_consumed,
                    consumption_spans: effect.consumption_spans.clone(),
                })
            })
            .collect()
    }

    fn reads(&self, reads: &[ReferentRead]) -> Option<Vec<ReferentRead>> {
        reads
            .iter()
            .filter(|read| !matches!(read.place.root, PlaceRoot::Local(_)))
            .map(|read| {
                Some(ReferentRead {
                    place: self.place(&read.place)?,
                    input_storage: self.slot(&read.place, &read.input_storage),
                    referent_projection: read.referent_projection.clone(),
                    event: read.event,
                    span: read.span,
                })
            })
            .collect()
    }

    fn places(&self, places: &[Place]) -> Option<Vec<Place>> {
        places.iter().map(|place| self.place(place)).collect()
    }
}

pub(crate) fn capture_worker_contract(
    worker: FunctionId,
    owner: AggregateId,
    parameters: usize,
    facts: &ReferentFunctionEffects,
) -> Option<CapturedWorkerContract> {
    let captures = Captures { owner, parameters };
    let variant_exits = facts
        .variant_exits
        .iter()
        .map(|(variant, exit)| {
            Some((
                *variant,
                ReferentVariantExit {
                    restored: captures.effects(&exit.restored)?,
                    has_normal_return: exit.has_normal_return,
                    effects: captures.effects(&exit.effects)?,
                    effects_from_consumed_entry: match &exit.effects_from_consumed_entry {
                        Some(effects) => Some(captures.effects(effects)?),
                        None => None,
                    },
                    consumed_entry: captures.effects(&exit.consumed_entry)?,
                    unresolved: exit.unresolved.clone(),
                },
            ))
        })
        .collect::<Option<HashMap<_, _>>>()?;
    Some(CapturedWorkerContract {
        worker,
        facts: ReferentFunctionEffects {
            has_normal_return: facts.has_normal_return,
            effects: captures.effects(&facts.effects)?,
            effects_from_consumed_entry: captures.effects(&facts.effects_from_consumed_entry)?,
            reads: captures.reads(&facts.reads)?,
            entry_reads: captures.reads(&facts.entry_reads)?,
            consuming_accesses: captures.reads(&facts.consuming_accesses)?,
            consumed_entry: captures.places(&facts.consumed_entry)?,
            restored_from_consumed_entry: captures.places(&facts.restored_from_consumed_entry)?,
            unresolved: facts.unresolved.clone(),
            unresolved_reads: facts.unresolved_reads.clone(),
            variant_exits,
        },
    })
}
