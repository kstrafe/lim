//! Compile-time initialization facts, independent of frame cell representation.
//!
//! These facts do not prove aliasing, lifetimes, pinning or physical layout.
//! Conditional facts require state specialization before unchecked access;
//! they must never be silently interpreted as initialized storage.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fact {
    Empty,
    Full,
    Conditional,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct State {
    must: Vec<bool>,
    may: Vec<bool>,
}

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

pub(crate) struct Analysis {
    pub(crate) before: Vec<Option<State>>,
    pub(crate) after: Vec<Option<State>>,
}

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
