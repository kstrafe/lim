use super::*;
use std::collections::{BTreeSet, HashMap, HashSet};

fn item(name: &str, deps: &[&str]) -> Metadata {
    Metadata {
        name: name.into(),
        dependencies: deps.iter().map(|dep| (*dep).into()).collect(),
        members: None,
    }
}

fn mutual(name: &str, deps: &[&str], members: &[&str]) -> Metadata {
    Metadata {
        name: name.into(),
        dependencies: deps.iter().map(|dep| (*dep).into()).collect(),
        members: Some(members.iter().map(|member| (*member).into()).collect()),
    }
}

fn copy(item: &Metadata) -> Metadata {
    Metadata {
        name: item.name.clone(),
        dependencies: item.dependencies.clone(),
        members: item.members.clone(),
    }
}

fn run(mut schedule: Schedule) -> Result<Vec<Vec<usize>>, (usize, String)> {
    let mut output = Vec::new();
    loop {
        match schedule.next()? {
            Some(group) => output.push(group),
            None => return Ok(output),
        }
    }
}

// Deliberately model the graph with names and sets, independently of the
// production scheduler's indexed adjacency representation.
fn reference(
    items: &[Metadata],
    builtins: &HashSet<String>,
) -> Result<Vec<Vec<usize>>, (usize, String)> {
    let mut positions = HashMap::new();
    for (index, item) in items.iter().enumerate() {
        if positions.insert(item.name.as_str(), index).is_some() {
            return Err((
                index,
                format!("duplicate kernel declaration '{}'", item.name),
            ));
        }
    }
    for (index, item) in items.iter().enumerate() {
        for dep in &item.dependencies {
            if !positions.contains_key(dep.as_str()) && !builtins.contains(dep) {
                return Err((index, format!("unknown kernel declaration '{dep}'")));
            }
        }
    }

    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut assigned = vec![false; items.len()];
    for (index, item) in items.iter().enumerate() {
        if assigned[index] {
            continue;
        }
        if let Some(members) = &item.members {
            if members.is_empty() || members.len() > 16 {
                return Err((
                    index,
                    "mutual group membership must be identical on every inductive member".into(),
                ));
            }
            let distinct: HashSet<_> = members.iter().collect();
            if distinct.len() != members.len() || !distinct.contains(&item.name) {
                return Err((
                    index,
                    "mutual group membership must be identical on every inductive member".into(),
                ));
            }
            let mut group = Vec::new();
            for name in members {
                let Some(&member_index) = positions.get(name.as_str()) else {
                    return Err((index, format!("unknown mutual group family '{name}'")));
                };
                if items[member_index].members.as_ref() != Some(members) || assigned[member_index] {
                    return Err((
                        index,
                        "mutual group membership must be identical on every inductive member"
                            .into(),
                    ));
                }
                group.push(member_index);
            }
            for &member in &group {
                assigned[member] = true;
            }
            groups.push(group);
        }
    }
    for (index, was_assigned) in assigned.iter().enumerate() {
        if !was_assigned {
            groups.push(vec![index]);
        }
    }
    groups.sort_by_key(|group| *group.iter().min().unwrap());

    let mut group_of = vec![0; items.len()];
    for (g, group) in groups.iter().enumerate() {
        for &member in group {
            group_of[member] = g;
        }
    }
    let mut prerequisites = vec![BTreeSet::new(); groups.len()];
    for (source, item) in items.iter().enumerate() {
        let from = group_of[source];
        for dep in &item.dependencies {
            if let Some(&target) = positions.get(dep.as_str()) {
                let to = group_of[target];
                if from == to && (groups[from].len() > 1 || item.members.is_some()) {
                    continue;
                }
                prerequisites[from].insert(to);
            }
        }
    }

    let priority: Vec<_> = groups
        .iter()
        .map(|group| *group.iter().min().unwrap())
        .collect();
    let mut emitted = vec![false; groups.len()];
    let mut output = Vec::new();
    while output.len() < groups.len() {
        let candidate = (0..groups.len())
            .filter(|&g| !emitted[g] && prerequisites[g].iter().all(|&p| emitted[p]))
            .min_by_key(|&g| priority[g]);
        let Some(g) = candidate else {
            let source = (0..groups.len())
                .filter(|&g| !emitted[g])
                .map(|g| priority[g])
                .min()
                .unwrap_or(0);
            return Err((
                source,
                "cyclic kernel declaration dependencies are forbidden; use structural induction"
                    .into(),
            ));
        };
        emitted[g] = true;
        output.push(groups[g].clone());
    }
    Ok(output)
}

fn streamed(
    items: &[Metadata],
    builtins: &HashSet<String>,
) -> Result<Vec<Vec<usize>>, (usize, String)> {
    let names: Vec<_> = items.iter().map(|item| item.name.clone()).collect();
    let schedule = Schedule::from_source(
        items.len(),
        |index| names[index].as_str(),
        |index| Ok(copy(&items[index])),
        |name| Ok(builtins.contains(name)),
        usize::MAX,
    )?;
    run(schedule)
}

#[test]
fn generated_graphs_match_independent_reference() {
    for seed in 0..200usize {
        let count = seed % 17;
        let names: Vec<_> = (0..count).map(|i| format!("n{i}")).collect();
        let mut state = seed as u32 + 1;
        let mut items = Vec::new();
        for source in 0..count {
            let mut deps = Vec::new();
            for target in 0..count {
                state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                if (seed % 2 != 0 || target < source) && state % 5 == 0 {
                    deps.push(names[target].as_str());
                }
            }
            // Repeated dependency declarations collapse to the same edge.
            if !deps.is_empty() && seed % 3 == 0 {
                deps.push(deps[0]);
            }
            items.push(item(&names[source], &deps));
        }
        let builtins = HashSet::from(["builtin".to_string()]);
        assert_eq!(
            streamed(&items, &builtins),
            reference(&items, &builtins),
            "seed {seed}"
        );
    }
}

#[test]
fn cycles_groups_unknowns_and_builtin_failures_match_reference() {
    let cases = vec![
        vec![item("self", &["self"])],
        vec![item("a", &["b"]), item("b", &["a"])],
        vec![item("a", &["absent"])],
        vec![
            mutual("A", &["B"], &["B", "A"]),
            mutual("B", &["A"], &["B", "A"]),
        ],
        vec![mutual("I", &["I"], &["I"])],
    ];
    let builtins = HashSet::from(["core".to_string()]);
    for items in cases {
        assert_eq!(streamed(&items, &builtins), reference(&items, &builtins));
    }
    let items = vec![item("uses-core", &["core"])];
    assert_eq!(streamed(&items, &builtins), Ok(vec![vec![0]]));
    let names = vec!["uses-core".to_string()];
    let failure = Schedule::from_source(
        1,
        |i| names[i].as_str(),
        |_| Ok(item("uses-core", &["core"])),
        |_| Err("lookup failed".into()),
        10,
    );
    assert!(
        matches!(failure, Err((0, message)) if message.contains("checking builtin dependency 'core'") && message.contains("lookup failed"))
    );
}

#[test]
fn explicit_member_order_and_duplicate_edges_are_preserved_correctly() {
    let items = vec![
        mutual("A", &["B", "root"], &["B", "A"]),
        mutual("B", &["A", "root"], &["B", "A"]),
        item("root", &[]),
        item("leaf", &["A", "B", "A"]),
    ];
    let result = streamed(&items, &HashSet::new()).unwrap();
    assert_eq!(result, vec![vec![2], vec![1, 0], vec![3]]);
    assert_eq!(result, reference(&items, &HashSet::new()).unwrap());
}

#[test]
fn stream_parse_failure_precedes_later_validation_errors() {
    let names = vec![
        "first".to_string(),
        "broken".to_string(),
        "first".to_string(),
    ];
    let mut parsed = 0;
    let result = Schedule::from_source(
        names.len(),
        |index| names[index].as_str(),
        |index| {
            parsed += 1;
            if index == 1 {
                return Err("malformed declaration".into());
            }
            Ok(if index == 0 {
                item("first", &[])
            } else {
                mutual("first", &["unknown"], &["missing-member"])
            })
        },
        |_| Ok(false),
        10,
    );
    assert!(matches!(result, Err((1, message)) if message == "malformed declaration"));
    assert_eq!(parsed, 2);
}

#[test]
fn late_parse_failure_overrides_earlier_dependency_and_membership_errors() {
    for first in [
        item("first", &["unknown"]),
        mutual("first", &[], &["first", "missing-member"]),
    ] {
        let names = ["first", "middle", "broken"];
        let mut parsed = 0;
        let result = Schedule::from_source(
            names.len(),
            |index| names[index],
            |index| {
                parsed += 1;
                match index {
                    0 => Ok(copy(&first)),
                    1 => Ok(item("middle", &[])),
                    _ => Err("malformed final declaration".into()),
                }
            },
            |_| Ok(false),
            10,
        );
        assert!(matches!(result, Err((2, message)) if message == "malformed final declaration"));
        assert_eq!(parsed, 3);
    }
}

#[test]
fn source_limit_checks_the_prefix_without_reading_or_resolving_beyond_it() {
    for invalid_prefix in [false, true] {
        let mut parsed = 0;
        let result = Schedule::from_source(
            3,
            |index| ["first", "second"][index],
            |index| {
                parsed += 1;
                if invalid_prefix && index == 1 {
                    Err("invalid second declaration".into())
                } else {
                    Ok(item(["first", "second"][index], &["unknown"]))
                }
            },
            |_| panic!("count limit must precede dependency validation"),
            2,
        );
        assert_eq!(parsed, 2);
        if invalid_prefix {
            assert!(matches!(result, Err((1, message)) if message == "invalid second declaration"));
        } else {
            assert!(
                matches!(result, Err((2, message)) if message == "kernel declaration limit exceeded")
            );
        }
    }
}
