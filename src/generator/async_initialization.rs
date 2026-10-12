//! Compile-time initialization facts, independent of frame cell representation.
//!
//! These facts do not prove aliasing, lifetimes, pinning or physical layout.
//! Conditional facts require state specialization before unchecked access;
//! they must never be silently interpreted as initialized storage.

use std::collections::HashMap;

/// One dispatcher state with an exact initialization history. Two histories
/// at the same source block are intentionally not joined. The dispatcher PC
/// can therefore identify initialized fields without an additional bitset.
#[derive(Debug)]
pub(crate) struct SpecializedState {
    pub(crate) block: usize,
    pub(crate) before: Vec<bool>,
    pub(crate) after: Vec<bool>,
    /// In the source graph's successor order (including Pending retries).
    pub(crate) successors: Vec<usize>,
}

#[derive(Debug)]
pub(crate) struct Specialization {
    /// Deterministic breadth-first order; state zero is the constructor entry.
    pub(crate) states: Vec<SpecializedState>,
}

impl Specialization {
    pub(crate) fn solve(
        entry: usize,
        successors: &[Vec<usize>],
        initial: Vec<bool>,
        limit: usize,
        transfer: impl Fn(usize, &mut Vec<bool>),
    ) -> Result<Self, String> {
        if entry >= successors.len()
            || successors
                .iter()
                .flatten()
                .any(|next| *next >= successors.len())
        {
            return Err("invalid async initialization graph".into());
        }
        if limit == 0 {
            return Err("async initialization specialization has no state budget".into());
        }
        let mut identities = HashMap::new();
        identities.insert((entry, initial.clone()), 0);
        let mut states = vec![SpecializedState {
            block: entry,
            before: initial,
            after: Vec::new(),
            successors: Vec::new(),
        }];
        let mut cursor = 0;
        while cursor < states.len() {
            let block = states[cursor].block;
            let mut after = states[cursor].before.clone();
            transfer(block, &mut after);
            if after.len() != states[cursor].before.len() {
                return Err("async initialization transfer changed the storage domain".into());
            }
            let mut next_states = Vec::new();
            for &next in &successors[block] {
                let key = (next, after.clone());
                let id = if let Some(&id) = identities.get(&key) {
                    id
                } else {
                    if states.len() == limit {
                        return Err(format!(
                            "async initialization specialization exceeds {limit} states"
                        ));
                    }
                    let id = states.len();
                    identities.insert(key, id);
                    states.push(SpecializedState {
                        block: next,
                        before: after.clone(),
                        after: Vec::new(),
                        successors: Vec::new(),
                    });
                    id
                };
                next_states.push(id);
            }
            states[cursor].after = after;
            states[cursor].successors = next_states;
            cursor += 1;
        }
        Ok(Self { states })
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fact {
    Empty,
    Full,
    Conditional,
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct State {
    must: Vec<bool>,
    may: Vec<bool>,
}

#[cfg(test)]
impl State {
    pub(crate) fn definitely_initialized(&self) -> &[bool] {
        &self.must
    }

    pub(crate) fn fact(&self, index: usize) -> Fact {
        match (self.must[index], self.may[index]) {
            (true, true) => Fact::Full,
            (false, false) => Fact::Empty,
            (false, true) => Fact::Conditional,
            (true, false) => unreachable!("must initialization implies may initialization"),
        }
    }
}

#[cfg(test)]
pub(crate) struct Analysis {
    pub(crate) before: Vec<Option<State>>,
    pub(crate) after: Vec<Option<State>>,
}

#[cfg(test)]
impl Analysis {
    /// Transfers assign initialization facts, never inspect data or emit code.
    /// The same transfer runs independently on the must and may domains.
    pub(crate) fn solve(
        entry: usize,
        successors: &[Vec<usize>],
        initial: Vec<bool>,
        transfer: impl Fn(usize, &mut Vec<bool>),
    ) -> Self {
        let count = successors.len();
        let mut reachable = vec![false; count];
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if std::mem::replace(&mut reachable[block], true) {
                continue;
            }
            pending.extend(&successors[block]);
        }
        let mut predecessors = vec![Vec::new(); count];
        for (block, next) in successors.iter().enumerate() {
            if reachable[block] {
                for &next in next {
                    predecessors[next].push(block);
                }
            }
        }
        let top = State {
            must: vec![true; initial.len()],
            may: vec![false; initial.len()],
        };
        let mut before = reachable
            .iter()
            .map(|live| live.then(|| top.clone()))
            .collect::<Vec<_>>();
        let mut after = before.clone();
        loop {
            let mut changed = false;
            for block in 0..count {
                if !reachable[block] {
                    continue;
                }
                let mut incoming = if block == entry {
                    State {
                        must: initial.clone(),
                        may: initial.clone(),
                    }
                } else {
                    top.clone()
                };
                for &previous in &predecessors[block] {
                    let previous = after[previous].as_ref().unwrap();
                    for (held, other) in incoming.must.iter_mut().zip(&previous.must) {
                        *held &= other;
                    }
                    for (held, other) in incoming.may.iter_mut().zip(&previous.may) {
                        *held |= other;
                    }
                }
                let mut outgoing = incoming.clone();
                transfer(block, &mut outgoing.must);
                transfer(block, &mut outgoing.may);
                changed |= before[block].as_ref() != Some(&incoming)
                    || after[block].as_ref() != Some(&outgoing);
                before[block] = Some(incoming);
                after[block] = Some(outgoing);
            }
            if !changed {
                break;
            }
        }
        Self { before, after }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn specialization_preserves_correlated_fields_and_exact_successors() {
        let graph = [vec![1, 2], vec![3], vec![3], vec![4], vec![4]];
        let plan =
            Specialization::solve(
                0,
                &graph,
                vec![false, false],
                16,
                |block, fields| match block {
                    1 => fields[0] = true,
                    2 => fields[1] = true,
                    _ => {}
                },
            )
            .unwrap();
        let joined = plan
            .states
            .iter()
            .filter(|state| state.block == 3)
            .map(|state| state.before.clone())
            .collect::<Vec<_>>();
        assert_eq!(joined, vec![vec![true, false], vec![false, true]]);
        assert_eq!(plan.states.len(), 7);
        for state in &plan.states {
            for (&original, &specialized) in graph[state.block].iter().zip(&state.successors) {
                assert_eq!(plan.states[specialized].block, original);
                assert_eq!(plan.states[specialized].before, state.after);
            }
        }
        let repeat =
            Specialization::solve(
                0,
                &graph,
                vec![false, false],
                16,
                |block, fields| match block {
                    1 => fields[0] = true,
                    2 => fields[1] = true,
                    _ => {}
                },
            )
            .unwrap();
        for (left, right) in plan.states.iter().zip(&repeat.states) {
            assert_eq!(left.block, right.block);
            assert_eq!(left.before, right.before);
            assert_eq!(left.successors, right.successors);
        }
    }

    #[test]
    fn specialization_handles_loop_entry_and_excludes_unreachable_states() {
        let plan = Specialization::solve(
            0,
            &[vec![1], vec![1, 2], vec![], vec![1]],
            vec![false],
            8,
            |block, fields| {
                if block == 1 {
                    fields[0] = true;
                }
            },
        )
        .unwrap();
        assert_eq!(plan.states.len(), 4);
        assert!(plan.states.iter().all(|state| state.block != 3));
        assert_eq!(
            plan.states
                .iter()
                .filter(|state| state.block == 1)
                .map(|state| state.before[0])
                .collect::<Vec<_>>(),
            vec![false, true]
        );
        assert!(plan
            .states
            .iter()
            .filter(|state| state.block == 2)
            .all(|state| state.before == [true]));
    }

    #[test]
    fn specialization_reports_limits_and_invalid_domains_without_fallback() {
        assert!(
            Specialization::solve(0, &[vec![1], vec![]], vec![false], 1, |_, _| {})
                .err()
                .unwrap()
                .contains("exceeds 1 states")
        );
        assert!(Specialization::solve(0, &[vec![2]], vec![], 8, |_, _| {}).is_err());
        assert!(
            Specialization::solve(0, &[vec![]], vec![false], 8, |_, fields| fields.push(true))
                .err()
                .unwrap()
                .contains("storage domain")
        );
    }

    #[test]
    fn definite_facts_match_the_previous_solver_on_cyclic_graphs() {
        for mask in 0..256usize {
            let mut successors = vec![vec![1], vec![2], vec![3], vec![]];
            for bit in 0..8 {
                if mask & (1 << bit) != 0 {
                    successors[bit / 2].push((bit + 2) % 4);
                }
            }
            let initial = vec![mask & 1 != 0, mask & 2 != 0];
            let transfer = |block: usize, state: &mut Vec<bool>| {
                if block == 1 {
                    state[0] = false;
                }
                if block == 2 {
                    state[1] = true;
                }
            };
            let actual = Analysis::solve(0, &successors, initial.clone(), transfer);
            let exact =
                Specialization::solve(0, &successors, initial.clone(), 32, transfer).unwrap();
            for block in 0..4 {
                let mut must = vec![true; 2];
                let mut may = vec![false; 2];
                for state in exact.states.iter().filter(|state| state.block == block) {
                    for index in 0..2 {
                        must[index] &= state.before[index];
                        may[index] |= state.before[index];
                    }
                }
                assert_eq!(
                    must,
                    actual.before[block].as_ref().unwrap().must,
                    "specialized must parity, graph {mask}, block {block}"
                );
                assert_eq!(
                    may,
                    actual.before[block].as_ref().unwrap().may,
                    "specialized may parity, graph {mask}, block {block}"
                );
            }
            let mut predecessors = vec![Vec::new(); 4];
            for (block, next) in successors.iter().enumerate() {
                for &next in next {
                    predecessors[next].push(block);
                }
            }
            let mut before = vec![vec![true; 2]; 4];
            let mut after = before.clone();
            loop {
                let mut changed = false;
                for block in 0..4 {
                    let mut incoming = if block == 0 {
                        initial.clone()
                    } else {
                        vec![true; 2]
                    };
                    for &previous in &predecessors[block] {
                        for (held, other) in incoming.iter_mut().zip(&after[previous]) {
                            *held &= other;
                        }
                    }
                    let mut outgoing = incoming.clone();
                    transfer(block, &mut outgoing);
                    changed |= before[block] != incoming || after[block] != outgoing;
                    before[block] = incoming;
                    after[block] = outgoing;
                }
                if !changed {
                    break;
                }
            }
            for block in 0..4 {
                assert_eq!(
                    actual.before[block]
                        .as_ref()
                        .unwrap()
                        .definitely_initialized(),
                    before[block],
                    "mask {mask}, block {block}"
                );
                assert_eq!(
                    actual.after[block]
                        .as_ref()
                        .unwrap()
                        .definitely_initialized(),
                    after[block],
                    "mask {mask}, block {block}"
                );
            }
        }
    }

    #[test]
    fn partial_moves_and_restoration_preserve_sibling_facts() {
        let facts = Analysis::solve(
            0,
            &[vec![1], vec![2], vec![]],
            vec![true, true],
            |block, state| {
                if block == 0 {
                    state[1] = false;
                }
                if block == 1 {
                    state[1] = true;
                }
            },
        );
        let suspended = facts.before[1].as_ref().unwrap();
        assert_eq!(suspended.fact(0), Fact::Full);
        assert_eq!(suspended.fact(1), Fact::Empty);
        assert_eq!(facts.before[2].as_ref().unwrap().fact(1), Fact::Full);
    }

    #[test]
    fn divergent_initialization_is_conditional_not_full() {
        let facts = Analysis::solve(
            0,
            &[vec![1, 2], vec![3], vec![3], vec![], vec![3]],
            vec![false],
            |block, state| {
                if block == 1 || block == 4 {
                    state[0] = true;
                }
            },
        );
        assert_eq!(facts.before[3].as_ref().unwrap().fact(0), Fact::Conditional);
        assert_eq!(facts.before[4], None);
        assert_eq!(facts.after[4], None);
    }

    #[test]
    fn loop_backedges_do_not_invent_definite_initialization() {
        let facts = Analysis::solve(
            0,
            &[vec![1], vec![1, 2], vec![]],
            vec![false],
            |block, state| {
                if block == 1 {
                    state[0] = true;
                }
            },
        );
        assert_eq!(facts.before[1].as_ref().unwrap().fact(0), Fact::Conditional);
        assert_eq!(facts.after[1].as_ref().unwrap().fact(0), Fact::Full);
        assert_eq!(facts.before[2].as_ref().unwrap().fact(0), Fact::Full);
    }
}
