use std::collections::{BTreeSet, HashMap};

pub(super) const MAX_DECLARATIONS: usize = 4096;

pub(super) struct Metadata {
    pub name: String,
    pub dependencies: BTreeSet<String>,
    pub members: Option<Vec<String>>,
}

pub(super) struct Schedule {
    groups: Vec<Vec<usize>>,
    dependents: Vec<Vec<usize>>,
    remaining: Vec<usize>,
    ready: BTreeSet<(usize, usize)>,
    done: Vec<bool>,
    completed: usize,
}

impl Schedule {
    pub(super) fn new(
        metadata: Vec<Metadata>,
        builtin: impl Fn(&str) -> bool,
    ) -> Result<Self, (usize, String)> {
        let count = metadata.len();
        if count > MAX_DECLARATIONS {
            return Err((MAX_DECLARATIONS, "kernel declaration limit exceeded".into()));
        }

        let mut by_name = HashMap::with_capacity(count);
        for (index, item) in metadata.iter().enumerate() {
            if by_name.insert(item.name.as_str(), index).is_some() {
                return Err((
                    index,
                    format!("duplicate kernel declaration '{}'", item.name),
                ));
            }
        }

        for (index, item) in metadata.iter().enumerate() {
            for dependency in &item.dependencies {
                if !by_name.contains_key(dependency.as_str()) && !builtin(dependency) {
                    return Err((index, format!("unknown kernel declaration '{dependency}'")));
                }
            }
        }

        let mut grouped = vec![false; count];
        let mut groups = Vec::<Vec<usize>>::with_capacity(count);
        for (index, item) in metadata.iter().enumerate() {
            if grouped[index] {
                continue;
            }
            let Some(members) = &item.members else {
                continue;
            };
            if members.is_empty() || members.len() > 16 {
                return Err((
                    index,
                    "mutual group membership must be identical on every inductive member".into(),
                ));
            }
            let mut seen = BTreeSet::new();
            if !members.iter().all(|member| seen.insert(member.as_str()))
                || !seen.contains(item.name.as_str())
            {
                return Err((
                    index,
                    "mutual group membership must be identical on every inductive member".into(),
                ));
            }
            let mut group = Vec::with_capacity(members.len());
            for member in members {
                let Some(&member_index) = by_name.get(member.as_str()) else {
                    return Err((index, format!("unknown mutual group family '{member}'")));
                };
                let other = &metadata[member_index];
                if other.members.as_ref() != Some(members) {
                    return Err((
                        index,
                        "mutual group membership must be identical on every inductive member"
                            .into(),
                    ));
                }
                if grouped[member_index] {
                    return Err((
                        index,
                        "mutual group membership must be identical on every inductive member"
                            .into(),
                    ));
                }
                group.push(member_index);
            }
            for &member_index in &group {
                grouped[member_index] = true;
            }
            groups.push(group);
        }
        for index in 0..count {
            if !grouped[index] {
                groups.push(vec![index]);
            }
        }

        // Keep groups in source priority order, while retaining explicit member order.
        groups.sort_by_key(|group| group.iter().copied().min().unwrap_or(usize::MAX));
        let mut group_of = vec![usize::MAX; count];
        let mut source_priority = Vec::with_capacity(groups.len());
        for (group_index, group) in groups.iter().enumerate() {
            source_priority.push(group.iter().copied().min().unwrap_or(usize::MAX));
            for &member in group {
                group_of[member] = group_index;
            }
        }

        let mut edge_sets = vec![BTreeSet::<usize>::new(); groups.len()];
        for (source, item) in metadata.iter().enumerate() {
            let from = group_of[source];
            for dependency in &item.dependencies {
                let Some(&target) = by_name.get(dependency.as_str()) else {
                    continue;
                };
                let to = group_of[target];
                if from == to {
                    if groups[from].len() > 1 || metadata[source].members.is_some() {
                        // Only edges internal to a validated explicit inductive group
                        // (including a singleton inductive family) are omitted.
                        continue;
                    }
                }
                edge_sets[from].insert(to);
            }
        }
        let mut dependents = vec![Vec::new(); groups.len()];
        let mut remaining = vec![0usize; groups.len()];
        for (dependent, prerequisites) in edge_sets.into_iter().enumerate() {
            remaining[dependent] = prerequisites.len();
            for prerequisite in prerequisites {
                dependents[prerequisite].push(dependent);
            }
        }
        let mut ready = BTreeSet::new();
        for index in 0..groups.len() {
            if remaining[index] == 0 {
                ready.insert((source_priority[index], index));
            }
        }

        // Drop all names and string dependency keys before returning.
        drop(by_name);
        drop(metadata);
        Ok(Self {
            groups,
            dependents,
            remaining,
            ready,
            done: vec![false; source_priority.len()],
            completed: 0,
        })
    }

    pub(super) fn next(&mut self) -> Result<Option<Vec<usize>>, (usize, String)> {
        let Some(&(priority, group_index)) = self.ready.iter().next() else {
            if self.completed == self.groups.len() {
                return Ok(None);
            }
            let source = self
                .done
                .iter()
                .enumerate()
                .filter_map(|(group_index, done)| {
                    (!done).then_some(
                        self.groups[group_index]
                            .iter()
                            .copied()
                            .min()
                            .unwrap_or(usize::MAX),
                    )
                })
                .min()
                .unwrap_or(0);
            return Err((
                source,
                "cyclic kernel declaration dependencies are forbidden; use structural induction"
                    .into(),
            ));
        };
        self.ready.remove(&(priority, group_index));
        if self.done[group_index] {
            return Err((
                priority,
                "kernel declaration schedule state is inconsistent".into(),
            ));
        }
        self.done[group_index] = true;
        self.completed += 1;
        for &dependent in &self.dependents[group_index] {
            self.remaining[dependent] -= 1;
            if self.remaining[dependent] == 0 {
                let source = self.groups[dependent]
                    .iter()
                    .copied()
                    .min()
                    .unwrap_or(usize::MAX);
                self.ready.insert((source, dependent));
            }
        }
        Ok(Some(self.groups[group_index].clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn item(name: &str, deps: &[&str]) -> Metadata {
        Metadata {
            name: name.into(),
            dependencies: deps.iter().map(|s| (*s).into()).collect(),
            members: None,
        }
    }
    fn inductive(name: &str, deps: &[&str], members: &[&str]) -> Metadata {
        Metadata {
            name: name.into(),
            dependencies: deps.iter().map(|s| (*s).into()).collect(),
            members: Some(members.iter().map(|s| (*s).into()).collect()),
        }
    }
    fn all(mut schedule: Schedule) -> Vec<Vec<usize>> {
        let mut result = Vec::new();
        while let Some(group) = schedule.next().unwrap() {
            result.push(group);
        }
        result
    }

    #[test]
    fn chains_forward_references_and_ready_source_priority() {
        let schedule = Schedule::new(
            vec![
                item("last", &["middle"]),
                item("free", &[]),
                item("middle", &["first"]),
                item("first", &[]),
            ],
            |_| false,
        )
        .unwrap();
        assert_eq!(all(schedule), vec![vec![1], vec![3], vec![2], vec![0]]);
        let schedule = Schedule::new(
            vec![item("a", &["missing"]), item("b", &["also-missing"])],
            |_| false,
        );
        assert!(matches!(schedule, Err((0, _))));
    }

    #[test]
    fn diamond_edges_are_deduplicated_and_independent_groups_ordered() {
        let schedule = Schedule::new(
            vec![
                item("root", &[]),
                item("left", &["root", "root"]),
                item("right", &["root"]),
                item("leaf", &["left", "right"]),
                item("free", &[]),
            ],
            |_| false,
        )
        .unwrap();
        assert_eq!(
            all(schedule),
            vec![vec![0], vec![1], vec![2], vec![3], vec![4]]
        );
    }

    #[test]
    fn reciprocal_inductive_group_preserves_member_order() {
        let schedule = Schedule::new(
            vec![
                inductive("A", &["B"], &["B", "A"]),
                inductive("B", &["A"], &["B", "A"]),
            ],
            |_| false,
        )
        .unwrap();
        assert_eq!(all(schedule), vec![vec![1, 0]]);
        assert!(Schedule::new(
            vec![
                inductive("A", &[], &["A", "B"]),
                inductive("B", &[], &["B", "A"])
            ],
            |_| false
        )
        .is_err());
        assert!(Schedule::new(vec![inductive("A", &[], &["A", "missing"])], |_| false).is_err());
    }

    #[test]
    fn cycles_and_invalid_groups_reject() {
        let mut self_cycle = Schedule::new(vec![item("A", &["A"])], |_| false).unwrap();
        assert!(self_cycle.next().is_err());
        let mut two_cycle =
            Schedule::new(vec![item("A", &["B"]), item("B", &["A"])], |_| false).unwrap();
        assert!(two_cycle.next().is_err());
        let mut self_with_ready =
            Schedule::new(vec![item("A", &["A"]), item("free", &[])], |_| false).unwrap();
        assert_eq!(self_with_ready.next().unwrap(), Some(vec![1]));
        assert!(self_with_ready.next().is_err());
        let singleton_inductive =
            Schedule::new(vec![inductive("I", &["I"], &["I"])], |_| false).unwrap();
        assert_eq!(all(singleton_inductive), vec![vec![0]]);
        assert!(Schedule::new(
            vec![inductive("A", &[], &["A", "B"]), item("B", &[])],
            |_| false
        )
        .is_err());
        assert!(Schedule::new(
            vec![
                inductive("A", &[], &["A", "B"]),
                inductive("B", &[], &["A", "B"]),
                inductive("C", &[], &["A", "C"])
            ],
            |_| false
        )
        .is_err());
    }

    #[test]
    fn builtins_and_duplicate_names() {
        let schedule =
            Schedule::new(vec![item("x", &["builtin"])], |name| name == "builtin").unwrap();
        assert_eq!(all(schedule), vec![vec![0]]);
        assert!(Schedule::new(vec![item("x", &[]), item("x", &[])], |_| false).is_err());
        assert!(Schedule::new(vec![item("x", &["unknown"])], |_| false).is_err());
    }

    #[test]
    fn full_limit_schedules() {
        let metadata = (0..MAX_DECLARATIONS)
            .map(|index| item(&format!("n{index}"), &[]))
            .collect();
        let schedule = Schedule::new(metadata, |_| false).unwrap();
        assert_eq!(all(schedule).len(), MAX_DECLARATIONS);
    }
}
