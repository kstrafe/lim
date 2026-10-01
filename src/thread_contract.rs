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
        let mut effects = Vec::<ReferentExitEffect>::new();
        // Exit effects miss transient consumption followed by restoration.
        // Keep both sources, retaining their exact storage identities/spans.
        let accesses = self
            .facts
            .consuming_accesses
            .iter()
            .map(|access| ReferentExitEffect {
                place: access.place.clone(),
                input_storage: access.input_storage.clone(),
                referent_projection: access.referent_projection.clone(),
                definitely_consumed: false,
                consumption_spans: vec![access.span],
            });
        for mut incoming in self.facts.effects.iter().cloned().chain(accesses) {
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
            unresolved: self.facts.unresolved.clone(),
            unresolved_reads: self.facts.unresolved_reads.clone(),
        }
    }
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
