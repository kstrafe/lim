use super::*;

const NODE_COUNT: usize = 384;
const MAX_MODEL_DEPTH: usize = 8;

struct ModelNode {
    expression: Expression,
    depth: usize,
}

struct FixedRng(u32);

impl FixedRng {
    fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        self.0
    }

    fn below(&mut self, upper: usize) -> usize {
        ((self.next() >> 16) as usize) % upper
    }
}

fn choose_child(rng: &mut FixedRng, nodes: &[ModelNode], max_depth: usize) -> usize {
    let count = nodes.iter().filter(|node| node.depth <= max_depth).count();
    let selected = rng.below(count);
    nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.depth <= max_depth)
        .nth(selected)
        .map(|(id, _)| id)
        .unwrap()
}

fn generate_model() -> Vec<ModelNode> {
    let mut rng = FixedRng(0x51a7_c0de);
    let mut nodes = vec![
        ModelNode {
            expression: Expression::Var(0),
            depth: 1,
        },
        {
            let expression = Expression::String("é\0𝄞".into());
            let (depth, _) = super::super::strings::dimensions(match &expression {
                Expression::String(value) => value,
                _ => unreachable!(),
            })
            .unwrap();
            ModelNode { expression, depth }
        },
    ];

    while nodes.len() < NODE_COUNT {
        let kind = rng.below(16);
        let (expression, depth) = if kind < 3 {
            // Aliases are common and always point backward.
            let child = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH);
            (Expression::Alias(child), nodes[child].depth)
        } else if kind < 9 {
            // Reuse a child often to create shared application subgraphs.
            let left = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            let right = if rng.below(3) == 0 {
                left
            } else {
                choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1)
            };
            (
                Expression::App(left, right),
                1 + nodes[left].depth.max(nodes[right].depth),
            )
        } else if kind < 11 {
            let ty = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            let body = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            (
                Expression::Lam(ty, body),
                1 + nodes[ty].depth.max(nodes[body].depth),
            )
        } else if kind < 13 {
            let ty = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            let body = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            (
                Expression::Pi(ty, body),
                1 + nodes[ty].depth.max(nodes[body].depth),
            )
        } else if kind == 13 {
            let ty = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            let value = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            let body = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            (
                Expression::Let(ty, value, body),
                1 + nodes[ty]
                    .depth
                    .max(nodes[value].depth)
                    .max(nodes[body].depth),
            )
        } else if kind == 14 {
            let subject = choose_child(&mut rng, &nodes, MAX_MODEL_DEPTH - 1);
            (
                Expression::Project(2, rng.below(5), subject),
                1 + nodes[subject].depth,
            )
        } else {
            // Leaves make the generated graph mixed and exercise external
            // name/universe lookup and compact natural payload storage.
            match rng.below(5) {
                0 => (Expression::Var(rng.below(4)), 1),
                1 => (Expression::Sort(rng.below(2)), 1),
                2 => (Expression::Global(1 + rng.below(2), vec![rng.below(2)]), 1),
                3 => (
                    Expression::Natural(
                        Natural::parse(&(rng.next() % 1_000_000).to_string()).unwrap(),
                    ),
                    1,
                ),
                _ => {
                    let value = ["", "a", "é", "𝄞\0", "x\u{1}y"][rng.below(5)];
                    let (depth, _) = super::super::strings::dimensions(value).unwrap();
                    (Expression::String(value.into()), depth)
                }
            }
        };
        assert!(depth <= MAX_MODEL_DEPTH);
        // All generated references are validated at insertion time here as
        // well as being selected strictly from the existing prefix.
        let current = nodes.len();
        let mut references = Vec::new();
        match &expression {
            Expression::Alias(a) => references.push(*a),
            Expression::Sort(_) | Expression::Var(_) => {}
            Expression::Global(_, _) | Expression::Natural(_) | Expression::String(_) => {}
            Expression::App(a, b) | Expression::Lam(a, b) | Expression::Pi(a, b) => {
                references.extend([*a, *b]);
            }
            Expression::Let(a, b, c) => references.extend([*a, *b, *c]),
            Expression::Project(_, _, a) => references.push(*a),
        }
        assert!(references.into_iter().all(|id| id < current));
        nodes.push(ModelNode { expression, depth });
    }
    nodes
}

fn model_names() -> names::Names {
    let mut names = names::Names::new();
    for key in ["Model.Pair", "Model.Box"] {
        names
            .push(Name {
                key: key.into(),
                display: key.into(),
                depth: 0,
            })
            .unwrap();
    }
    names
}

fn assert_model_coverage(nodes: &[ModelNode]) {
    let mut seen = [false; 11];
    let mut alias_edges = 0;
    let mut incoming_edges = vec![0usize; nodes.len()];
    for node in nodes {
        match &node.expression {
            Expression::Var(_) => seen[0] = true,
            Expression::Sort(_) => seen[1] = true,
            Expression::Global(_, _) => seen[2] = true,
            Expression::App(a, b) => {
                seen[3] = true;
                incoming_edges[*a] += 1;
                incoming_edges[*b] += 1;
            }
            Expression::Lam(a, b) => {
                seen[4] = true;
                incoming_edges[*a] += 1;
                incoming_edges[*b] += 1;
            }
            Expression::Pi(a, b) => {
                seen[5] = true;
                incoming_edges[*a] += 1;
                incoming_edges[*b] += 1;
            }
            Expression::Let(a, b, c) => {
                seen[6] = true;
                incoming_edges[*a] += 1;
                incoming_edges[*b] += 1;
                incoming_edges[*c] += 1;
            }
            Expression::Project(_, _, a) => {
                seen[7] = true;
                incoming_edges[*a] += 1;
            }
            Expression::Natural(_) => seen[8] = true,
            Expression::Alias(a) => {
                seen[9] = true;
                alias_edges += 1;
                incoming_edges[*a] += 1;
            }
            Expression::String(_) => seen[10] = true,
        }
    }
    assert!(
        seen.into_iter().all(|present| present),
        "model omitted an expression variant"
    );
    assert!(alias_edges > 0, "model omitted aliases");
    assert!(
        incoming_edges.iter().any(|&count| count > 1),
        "model omitted shared edge reuse"
    );
}

#[test]
fn fixed_seed_mixed_dag_matches_eager_across_spill_and_record_cleanup() {
    let names = model_names();
    let levels =
        levels::Levels::try_from(vec![Level::number(0).unwrap(), Level::number(2).unwrap()])
            .unwrap();
    let nodes = generate_model();
    assert_eq!(nodes.len(), NODE_COUNT);
    assert!(nodes.iter().all(|node| node.depth <= MAX_MODEL_DEPTH));
    assert_model_coverage(&nodes);

    let mut eager = Expressions::new(true);
    // 256 entry slots leave a substantial prefix in memory before spilling.
    let mut compact = Expressions::with_limit(false, std::mem::size_of::<Entry>() * 256);
    let mut live_prefix_roots = Vec::new();
    let mut compared = 0;

    for (id, node) in nodes.iter().enumerate() {
        eager
            .push(node.expression.clone(), node.depth, 0, &names, &levels)
            .unwrap();
        let reference = eager.get(id, &names, &levels).unwrap();
        let source_payload = payload(&reference);
        compact
            .push(
                node.expression.clone(),
                node.depth,
                source_payload,
                &names,
                &levels,
            )
            .unwrap();

        if matches!(id, 32 | 80 | 128 | 192 | 240 | 288 | 352 | 383) {
            let actual = compact.get(id, &names, &levels).unwrap();
            assert!(Kernel::new().same_syntax(&reference, &actual).unwrap());
            compared += 1;
            if id <= 240 {
                live_prefix_roots.push(actual);
            }
        }

        if id % 64 == 63 {
            compact.end_record();
        }
    }

    assert!(compact.is_spilled());
    assert!(live_prefix_roots.len() >= 4);
    // These strong roots span the transition and multiple record boundaries.
    for (index, id) in [32, 80, 128, 192, 240].into_iter().enumerate() {
        let expected = eager.get(id, &names, &levels).unwrap();
        assert!(Kernel::new()
            .same_syntax(&expected, &live_prefix_roots[index])
            .unwrap());
    }

    drop(live_prefix_roots);
    compact.end_record();
    // A small deterministic sample exercises reconstruction after memo cleanup.
    for id in [17, 63, 127, 191, 255, 319, 383] {
        let expected = eager.get(id, &names, &levels).unwrap();
        let actual = compact.get(id, &names, &levels).unwrap();
        assert!(
            Kernel::new().same_syntax(&expected, &actual).unwrap(),
            "root {id}"
        );
        drop((expected, actual));
        compact.end_record();
    }
    assert_eq!(compared, 8);
}
