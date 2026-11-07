//! Dependency metadata schedules work, never supplies checking authority.
//! Resolve and release one declaration's string dependencies at a time; retain
//! numeric compressed adjacency lists, including explicit mutual groups.
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap};

pub(super) const MAX_DECLARATIONS: usize = 4096;

pub(super) struct Metadata {
    pub name: String,
    pub dependencies: BTreeSet<String>,
    pub members: Option<Vec<String>>,
}

pub(super) struct Schedule {
    members: Vec<usize>,
    group_offsets: Vec<usize>,
    dependents: Vec<usize>,
    dependent_offsets: Vec<usize>,
    remaining: Vec<usize>,
    ready: BinaryHeap<Reverse<usize>>,
    done: Vec<bool>,
    completed: usize,
}

impl Schedule {
    #[cfg(test)]
    pub(super) fn new(
        metadata: Vec<Metadata>,
        builtin: impl Fn(&str) -> std::result::Result<bool, String>,
    ) -> Result<Self, (usize, String)> {
        Self::with_limit(metadata, builtin, MAX_DECLARATIONS)
    }

    #[cfg(test)]
    pub(super) fn with_limit(
        metadata: Vec<Metadata>,
        builtin: impl Fn(&str) -> std::result::Result<bool, String>,
        max_declarations: usize,
    ) -> Result<Self, (usize, String)> {
        let names: Vec<_> = metadata.iter().map(|item| item.name.clone()).collect();
        let mut items = metadata.into_iter();
        Self::from_source(
            names.len(),
            |index| names[index].as_str(),
            |_| Ok(items.next().expect("metadata count is exact")),
            builtin,
            max_declarations,
        )
    }

    pub(super) fn from_source<'a>(
        count: usize,
        name: impl Fn(usize) -> &'a str,
        mut metadata: impl FnMut(usize) -> Result<Metadata, String>,
        builtin: impl Fn(&str) -> Result<bool, String>,
        max_declarations: usize,
    ) -> Result<Self, (usize, String)> {
        // Borrow names from the immutable source directory. Never allocate
        // proportional to the selected limit, or inspect beyond its boundary.
        let visible_count = count.min(max_declarations);
        let mut by_name = HashMap::with_capacity(visible_count);
        let mut duplicate = None;
        for index in 0..visible_count {
            let key = name(index);
            if by_name.insert(key, index).is_some() && duplicate.is_none() {
                duplicate = Some((index, format!("duplicate kernel declaration '{key}'")));
            }
        }

        let mut dependencies = Vec::new();
        let mut dependency_offsets = Vec::with_capacity(visible_count + 1);
        dependency_offsets.push(0);
        let mut membership = Vec::with_capacity(visible_count);
        let mut dependency_error = None;
        for index in 0..visible_count {
            // Parse errors retain precedence over schedule errors, as in the
            // original complete inventory pass. No body survives this call.
            let item = metadata(index).map_err(|why| (index, why))?;
            if item.name != name(index) {
                return Err((index, "kernel declaration metadata changed identity".into()));
            }
            if count <= max_declarations && duplicate.is_none() && dependency_error.is_none() {
                for dependency in &item.dependencies {
                    if let Some(&target) = by_name.get(dependency.as_str()) {
                        dependencies.push(target);
                        continue;
                    }
                    match builtin(dependency) {
                        Ok(true) => {}
                        Ok(false) => {
                            dependency_error =
                                Some((index, format!("unknown kernel declaration '{dependency}'")));
                            break;
                        }
                        Err(why) => {
                            dependency_error = Some((
                                index,
                                format!("checking builtin dependency '{dependency}': {why}"),
                            ));
                            break;
                        }
                    }
                }
            }
            membership.push(item.members);
            dependency_offsets.push(dependencies.len());
        }
        if count > max_declarations {
            return Err((max_declarations, "kernel declaration limit exceeded".into()));
        }
        if let Some(error) = duplicate.or(dependency_error) {
            return Err(error);
        }

        let mut members = Vec::with_capacity(count);
        let mut group_offsets = Vec::with_capacity(count + 1);
        group_offsets.push(0);
        let mut group_of = vec![usize::MAX; count];
        let mut inductive = Vec::new();
        for index in 0..count {
            if group_of[index] != usize::MAX {
                continue;
            }
            let group_index = group_offsets.len() - 1;
            let start = members.len();
            let invalid = || {
                (
                    index,
                    "mutual group membership must be identical on every inductive member".into(),
                )
            };
            if let Some(reported) = &membership[index] {
                if reported.is_empty() || reported.len() > 16 {
                    return Err(invalid());
                }
                let mut seen = BTreeSet::new();
                if !reported.iter().all(|member| seen.insert(member.as_str()))
                    || !seen.contains(name(index))
                {
                    return Err(invalid());
                }
                for member in reported {
                    let Some(&member_index) = by_name.get(member.as_str()) else {
                        return Err((index, format!("unknown mutual group family '{member}'")));
                    };
                    if membership[member_index].as_ref() != Some(reported)
                        || group_of[member_index] != usize::MAX
                    {
                        return Err(invalid());
                    }
                    members.push(member_index);
                }
            } else {
                members.push(index);
            }
            for &member in &members[start..] {
                group_of[member] = group_index;
            }
            inductive.push(membership[index].is_some());
            group_offsets.push(members.len());
        }
        // Groups are in ascending minimum-source-index order; explicit member
        // order remains intact within each group.
        drop(by_name);
        drop(membership);

        let groups = group_offsets.len() - 1;
        let mut prerequisites = Vec::new();
        let mut prerequisite_offsets = Vec::with_capacity(groups + 1);
        prerequisite_offsets.push(0);
        let mut remaining = Vec::with_capacity(groups);
        let mut dependent_counts = vec![0usize; groups];
        let mut edges = Vec::new();
        for group in 0..groups {
            edges.clear();
            for &source in &members[group_offsets[group]..group_offsets[group + 1]] {
                for &target in
                    &dependencies[dependency_offsets[source]..dependency_offsets[source + 1]]
                {
                    let prerequisite = group_of[target];
                    // Only validated explicit inductive groups omit internal
                    // edges. Ordinary self references remain cycles.
                    if prerequisite != group || !inductive[group] {
                        edges.push(prerequisite);
                    }
                }
            }
            edges.sort_unstable();
            edges.dedup();
            remaining.push(edges.len());
            for &prerequisite in &edges {
                dependent_counts[prerequisite] += 1;
            }
            prerequisites.extend_from_slice(&edges);
            prerequisite_offsets.push(prerequisites.len());
        }
        drop(edges);
        drop(dependencies);
        drop(dependency_offsets);
        drop(group_of);
        drop(inductive);

        let mut dependent_offsets = Vec::with_capacity(groups + 1);
        dependent_offsets.push(0usize);
        for count in dependent_counts {
            let end = dependent_offsets
                .last()
                .unwrap()
                .checked_add(count)
                .ok_or((
                    0,
                    "kernel declaration schedule edge count overflow".to_owned(),
                ))?;
            dependent_offsets.push(end);
        }
        let mut dependents = vec![0usize; prerequisites.len()];
        let mut positions = dependent_offsets[..groups].to_vec();
        for dependent in 0..groups {
            for &prerequisite in
                &prerequisites[prerequisite_offsets[dependent]..prerequisite_offsets[dependent + 1]]
            {
                dependents[positions[prerequisite]] = dependent;
                positions[prerequisite] += 1;
            }
        }
        let ready = remaining
            .iter()
            .enumerate()
            .filter_map(|(group, &count)| (count == 0).then_some(Reverse(group)))
            .collect();
        Ok(Self {
            members,
            group_offsets,
            dependents,
            dependent_offsets,
            remaining,
            ready,
            done: vec![false; groups],
            completed: 0,
        })
    }

    fn group(&self, index: usize) -> &[usize] {
        &self.members[self.group_offsets[index]..self.group_offsets[index + 1]]
    }
    fn source_priority(&self, index: usize) -> usize {
        self.group(index).iter().copied().min().unwrap_or(0)
    }
    pub(super) fn next(&mut self) -> Result<Option<Vec<usize>>, (usize, String)> {
        let Some(Reverse(group)) = self.ready.pop() else {
            if self.completed == self.remaining.len() {
                return Ok(None);
            }
            let source = self
                .done
                .iter()
                .position(|done| !done)
                .map(|index| self.source_priority(index))
                .unwrap_or(0);
            return Err((
                source,
                "cyclic kernel declaration dependencies are forbidden; use structural induction"
                    .into(),
            ));
        };
        if self.done[group] {
            return Err((
                self.source_priority(group),
                "kernel declaration schedule state is inconsistent".into(),
            ));
        }
        self.done[group] = true;
        self.completed += 1;
        for &dependent in
            &self.dependents[self.dependent_offsets[group]..self.dependent_offsets[group + 1]]
        {
            self.remaining[dependent] -= 1;
            if self.remaining[dependent] == 0 {
                self.ready.push(Reverse(dependent));
            }
        }
        Ok(Some(self.group(group).to_vec()))
    }
}

#[cfg(test)]
#[path = "schedule_model_tests.rs"]
mod model_tests;

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
            |_| Ok(false),
        )
        .unwrap();
        assert_eq!(all(schedule), vec![vec![1], vec![3], vec![2], vec![0]]);
        let schedule = Schedule::new(
            vec![item("a", &["missing"]), item("b", &["also-missing"])],
            |_| Ok(false),
        );
        assert!(matches!(schedule, Err((0, _))));
    }

    #[test]
    fn selected_count_and_default_capacity_validate_after_metadata_collection() {
        let metadata: Vec<_> = (0..=MAX_DECLARATIONS)
            .map(|i| item(&format!("n{i}"), &[]))
            .collect();
        assert!(Schedule::new(metadata, |_| Ok(false)).is_err());
        let selected: Vec<_> = (0..=MAX_DECLARATIONS)
            .map(|i| item(&format!("n{i}"), &[]))
            .collect();
        let schedule = Schedule::with_limit(selected, |_| Ok(false), MAX_DECLARATIONS + 1).unwrap();
        assert_eq!(all(schedule).len(), MAX_DECLARATIONS + 1);
        let mut late_unknown: Vec<_> = (0..=MAX_DECLARATIONS)
            .map(|i| item(&format!("n{i}"), &[]))
            .collect();
        late_unknown[MAX_DECLARATIONS]
            .dependencies
            .insert("missing".into());
        assert!(matches!(
            Schedule::with_limit(late_unknown, |_| Ok(false), MAX_DECLARATIONS + 1),
            Err((MAX_DECLARATIONS, message)) if message.contains("unknown kernel declaration 'missing'")
        ));
        assert!(matches!(
            Schedule::with_limit(vec![item("late", &["missing"])], |_| Ok(false), 0),
            Err((0, _))
        ));
        let cycle = vec![item("a", &["b"]), item("b", &["a"])];
        let mut schedule = Schedule::with_limit(cycle, |_| Ok(false), 2).unwrap();
        assert!(schedule.next().is_err());
    }

    #[test]
    fn builtin_lookup_error_is_propagated_with_dependency_context() {
        let schedule = Schedule::new(vec![item("uses-builtin", &["builtin"])], |_| {
            Err("directory is corrupt".into())
        });
        let (index, error) = match schedule {
            Err(error) => error,
            Ok(_) => panic!("builtin lookup error was swallowed"),
        };
        assert_eq!(index, 0);
        assert!(error.contains("checking builtin dependency 'builtin'"));
        assert!(error.contains("directory is corrupt"));
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
            |_| Ok(false),
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
            |_| Ok(false),
        )
        .unwrap();
        assert_eq!(all(schedule), vec![vec![1, 0]]);
        assert!(Schedule::new(
            vec![
                inductive("A", &[], &["A", "B"]),
                inductive("B", &[], &["B", "A"])
            ],
            |_| Ok(false)
        )
        .is_err());
        assert!(
            Schedule::new(vec![inductive("A", &[], &["A", "missing"])], |_| Ok(false)).is_err()
        );
    }

    #[test]
    fn cycles_and_invalid_groups_reject() {
        let mut self_cycle = Schedule::new(vec![item("A", &["A"])], |_| Ok(false)).unwrap();
        assert!(self_cycle.next().is_err());
        let mut two_cycle =
            Schedule::new(vec![item("A", &["B"]), item("B", &["A"])], |_| Ok(false)).unwrap();
        assert!(two_cycle.next().is_err());
        let mut self_with_ready =
            Schedule::new(vec![item("A", &["A"]), item("free", &[])], |_| Ok(false)).unwrap();
        assert_eq!(self_with_ready.next().unwrap(), Some(vec![1]));
        assert!(self_with_ready.next().is_err());
        let singleton_inductive =
            Schedule::new(vec![inductive("I", &["I"], &["I"])], |_| Ok(false)).unwrap();
        assert_eq!(all(singleton_inductive), vec![vec![0]]);
        assert!(Schedule::new(
            vec![inductive("A", &[], &["A", "B"]), item("B", &[])],
            |_| Ok(false)
        )
        .is_err());
        assert!(Schedule::new(
            vec![
                inductive("A", &[], &["A", "B"]),
                inductive("B", &[], &["A", "B"]),
                inductive("C", &[], &["A", "C"])
            ],
            |_| Ok(false)
        )
        .is_err());
    }

    #[test]
    fn builtins_and_duplicate_names() {
        let schedule =
            Schedule::new(vec![item("x", &["builtin"])], |name| Ok(name == "builtin")).unwrap();
        assert_eq!(all(schedule), vec![vec![0]]);
        assert!(Schedule::new(vec![item("x", &[]), item("x", &[])], |_| Ok(false)).is_err());
        assert!(Schedule::new(vec![item("x", &["unknown"])], |_| Ok(false)).is_err());
    }

    #[test]
    fn full_limit_schedules() {
        let metadata = (0..MAX_DECLARATIONS)
            .map(|index| item(&format!("n{index}"), &[]))
            .collect();
        let schedule = Schedule::new(metadata, |_| Ok(false)).unwrap();
        assert_eq!(all(schedule).len(), MAX_DECLARATIONS);
    }
}
