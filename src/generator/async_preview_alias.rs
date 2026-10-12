//! Compile-time lifetimes of stationary, nonowning guard payload aliases.
use crate::generator::async_exec::{Action, Graph, Pattern};
use crate::linearcheck::LinearTypes;
use crate::typed_body::BindingId;
use crate::typed_ir::{resolve_type, Declarations};
use crate::Type;
use std::collections::{HashMap, HashSet, VecDeque};

pub(crate) struct Plan {
    pub patterns: HashMap<BindingId, Pattern>,
    pub entry: Vec<HashSet<BindingId>>,
}
impl Plan {
    pub fn new(
        graph: &Graph,
        types: &LinearTypes,
        declarations: &Declarations,
    ) -> Result<Self, String> {
        let mut patterns = HashMap::new();
        for located in graph.blocks.iter().flat_map(|block| &block.actions) {
            let Action::Preview(pattern) = &located.action else {
                continue;
            };
            for &binding in &pattern.bindings {
                let ty = resolve_type(&graph.bindings[binding.0].ty, &declarations.aliases)?;
                if types.requires_move(&ty)
                    && !matches!(ty, Type::Reference { .. } | Type::PinnedReference { .. })
                {
                    if patterns.insert(binding, pattern.clone()).is_some() {
                        return Err("guard alias has more than one preview definition".into());
                    }
                }
            }
        }
        if patterns.is_empty() {
            return Ok(Self {
                patterns,
                entry: vec![HashSet::new(); graph.blocks.len()],
            });
        }
        let mut states = vec![None; graph.blocks.len()];
        states[graph.entry.0] = Some(HashSet::new());
        let mut pending = VecDeque::from([graph.entry]);
        while let Some(block) = pending.pop_front() {
            let mut active = states[block.0].clone().unwrap();
            for located in &graph.blocks[block.0].actions {
                match &located.action {
                    Action::Preview(pattern) => {
                        active.extend(
                            pattern
                                .bindings
                                .iter()
                                .filter(|binding| patterns.contains_key(binding))
                                .copied(),
                        );
                    }
                    Action::Commit(pattern) | Action::EndPreview(pattern) => {
                        for binding in &pattern.bindings {
                            active.remove(binding);
                        }
                    }
                    _ => {}
                }
            }
            for successor in graph.successors(block) {
                match &states[successor.0] {
                    Some(previous) if previous != &active => {
                        return Err(
                            "guard alias lifetime is inconsistent at a control-flow join".into(),
                        )
                    }
                    Some(_) => {}
                    None => {
                        states[successor.0] = Some(active.clone());
                        pending.push_back(successor);
                    }
                }
            }
        }
        Ok(Self {
            patterns,
            entry: states.into_iter().map(Option::unwrap_or_default).collect(),
        })
    }
}
