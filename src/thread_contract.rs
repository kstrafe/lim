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
