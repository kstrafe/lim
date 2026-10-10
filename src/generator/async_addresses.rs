//! Liveness of selected addresses, separate from value/owner retirement.
//! An address is formed once by Place, not reconstructed by a later consumer.
use super::async_exec::{Action, Graph, PlaceId};
use std::collections::{HashMap, HashSet};

pub(crate) struct Plan {
    pub after: HashMap<(usize, usize), Vec<PlaceId>>,
    pub entry: Vec<Vec<PlaceId>>,
}

impl Plan {
    pub fn new(graph: &Graph, snapshots: &HashSet<PlaceId>) -> Self {
        if snapshots.is_empty() {
            return Self {
                after: HashMap::new(),
                entry: vec![Vec::new(); graph.blocks.len()],
            };
        }
        let mut predecessors = vec![Vec::new(); graph.blocks.len()];
        for block in 0..graph.blocks.len() {
            for successor in graph.successors(super::async_exec::BlockId(block)) {
                predecessors[successor.0].push(block);
            }
        }
        let mut incoming = vec![HashSet::new(); graph.blocks.len()];
        let mut outgoing = incoming.clone();
        loop {
            let mut changed = false;
            for block in (0..graph.blocks.len()).rev() {
                let mut live = HashSet::new();
                for successor in graph.successors(super::async_exec::BlockId(block)) {
                    live.extend(incoming[successor.0].iter().copied());
                }
                outgoing[block] = live.clone();
                for action in graph.blocks[block].actions.iter().rev() {
                    Self::transfer(&action.action, &mut live, snapshots);
                }
                if incoming[block] != live {
                    incoming[block] = live;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let dead = |before: &HashSet<PlaceId>, live: &HashSet<PlaceId>| {
            let mut dead = before.difference(live).copied().collect::<Vec<_>>();
            dead.sort_by_key(|place| place.0);
            dead
        };
        let mut after = HashMap::new();
        for (block, body) in graph.blocks.iter().enumerate() {
            let mut live = outgoing[block].clone();
            for (index, action) in body.actions.iter().enumerate().rev() {
                let after_live = live.clone();
                Self::transfer(&action.action, &mut live, snapshots);
                let mut held = live.clone();
                if let Action::Place { dst, .. } = action.action {
                    if snapshots.contains(&dst) {
                        held.insert(dst);
                    }
                }
                let retired = dead(&held, &after_live);
                if !retired.is_empty() {
                    after.insert((block, index), retired);
                }
            }
        }
        let mut entry = Vec::new();
        for block in 0..graph.blocks.len() {
            let mut before = HashSet::new();
            for &predecessor in &predecessors[block] {
                before.extend(outgoing[predecessor].iter().copied());
            }
            entry.push(dead(&before, &incoming[block]));
        }
        Self { after, entry }
    }

    fn transfer(action: &Action, live: &mut HashSet<PlaceId>, snapshots: &HashSet<PlaceId>) {
        match action {
            Action::Place { dst, descriptor } => {
                live.remove(dst);
                if snapshots.contains(dst) {
                    if let Some(parent) = descriptor
                        .parent
                        .filter(|parent| snapshots.contains(parent))
                    {
                        live.insert(parent);
                    }
                }
            }
            Action::Load { place, .. }
            | Action::Store { place, .. }
            | Action::Borrow { place, .. }
            | Action::Release { place, .. } => {
                if snapshots.contains(place) {
                    live.insert(*place);
                }
            }
            _ => {}
        }
    }
}
