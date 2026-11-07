//! Conservative graph of the checked program. A positive path is structural:
//! branches, loops, and calls need not belong to a feasible execution.
//! Witnesses use shortest paths, with lexically sorted ties and primitives.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::typed_body::{Control, Instruction, NodeId, NodeKind, PlaceRoot, Projection};
use crate::typed_ir::{DeclarationId, Declarations};
use crate::{Item, Program};

const EFFECTS: &[&str] = &[
    "allocation",
    "io",
    "global-write",
    "unsafe",
    "external",
    "asm",
    "mutation",
];

pub(crate) struct Graph {
    /// Only actual function identities occur here, never builtin spellings.
    pub edges: BTreeMap<String, BTreeSet<String>>,
    effects: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
    builtins: BTreeMap<String, BTreeSet<String>>,
    unsafe_sites: BTreeMap<String, BTreeSet<String>>,
    statics: BTreeSet<crate::typed_ir::GlobalId>,
    global_accesses: BTreeSet<String>,
}

impl Graph {
    pub fn new(program: &Program, declarations: &Declarations) -> Self {
        let mut graph = Self {
            edges: BTreeMap::new(),
            effects: BTreeMap::new(),
            builtins: BTreeMap::new(),
            unsafe_sites: BTreeMap::new(),
            global_accesses: BTreeSet::new(),
            statics: program
                .items
                .iter()
                .filter_map(|item| match item {
                    Item::Static { name, .. } => declarations.global_id(name),
                    _ => None,
                })
                .collect(),
        };
        // Register all declarations before recording any edges.
        for item in &program.items {
            match item {
                Item::Function(function) => {
                    graph.edges.entry(function.name.clone()).or_default();
                }
                Item::ThreadTask {
                    generated_functions,
                    ..
                } => {
                    for function in generated_functions {
                        graph.edges.entry(function.name.clone()).or_default();
                    }
                }
                _ => {}
            }
        }
        let statics: BTreeSet<_> = program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Static { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        for item in &program.items {
            match item {
                Item::ThreadTask {
                    worker,
                    generated_functions,
                    ..
                } => {
                    for function in generated_functions {
                        // Native helpers hide execution and runtime effects. Both
                        // spawn and join conservatively expose the worker.
                        graph.edge(&function.name, worker);
                        graph.unknown(&function.name, "#thread-task");
                    }
                }
                Item::Function(function) => {
                    let name = &function.name;
                    if function.external {
                        graph.unknown(name, name);
                        continue;
                    }
                    // The unsafe-call flag is a caller obligation, not an
                    // unsafe primitive. Inspect the actual checked internals.
                    let Some(body) = declarations.bodies.get(name) else {
                        graph.unknown(name, "<unavailable checked body>");
                        continue;
                    };
                    graph.instructions(name, &body.instructions);
                    for (index, node) in body.nodes.iter().enumerate() {
                        match &node.kind {
                            NodeKind::Block(instructions) | NodeKind::Loop(instructions) => {
                                let head = if matches!(&node.kind, NodeKind::Block(_)) {
                                    "block"
                                } else {
                                    "loop"
                                };
                                graph.primitive(name, head);
                                graph.instructions(name, instructions);
                            }
                            NodeKind::If { .. } => graph.primitive(name, "if"),
                            NodeKind::Match { .. } => graph.primitive(name, "match"),
                            NodeKind::Labeled(_, _) => graph.primitive(name, "label"),
                            NodeKind::Declaration(DeclarationId::Global(id))
                                if node.ty.is_some() =>
                            {
                                graph.global_accesses.insert(name.clone());
                                let global =
                                    declarations.declaration_name(DeclarationId::Global(*id));
                                if statics.contains(global) {
                                    graph.effect(name, "unsafe", "#static");
                                }
                            }
                            NodeKind::Form {
                                callee: Some(id), ..
                            } => {
                                graph.edge(name, &declarations.function(*id).name);
                            }
                            NodeKind::Form { head, .. } if node.ty.is_some() => {
                                if let Some(hook) =
                                    declarations.clone_hook_name(body, NodeId(index))
                                {
                                    graph.edge(name, &hook);
                                }
                                graph.primitive(name, head);
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        graph
    }

    fn edge(&mut self, from: &str, to: &str) {
        if !self.edges.contains_key(to) {
            // A retained interface may resolve a callee whose implementation
            // is absent from this Program. It is still an actual identity,
            // but its effects cannot be proved empty.
            self.unknown(to, to);
        }
        self.edges.entry(to.to_owned()).or_default();
        self.edges
            .entry(from.to_owned())
            .or_default()
            .insert(to.to_owned());
    }

    fn effect(&mut self, function: &str, effect: &str, site: &str) {
        self.effects
            .entry(function.into())
            .or_default()
            .entry(effect.into())
            .or_default()
            .insert(site.into());
        if effect == "unsafe" {
            self.unsafe_sites
                .entry(function.into())
                .or_default()
                .insert(site.into());
        }
    }

    fn unknown(&mut self, function: &str, site: &str) {
        // Unknown code may allocate, perform IO, or modify any shared state.
        // No negative effect assertion may rely on its implementation.
        for effect in EFFECTS {
            self.effect(function, effect, site);
        }
    }

    fn primitive(&mut self, function: &str, head: &str) {
        let builtin = normalize_builtin(head);
        self.builtins
            .entry(function.into())
            .or_default()
            .insert(builtin.clone());
        let site = builtin.as_str();
        match head {
            "asm" | "linux-syscall" | "thread-task-spawn" | "thread-task-join" => {
                self.unknown(function, site);
            }
            "print" | "println" | "eprint" | "eprintln" | "panic" | "assert" | "debug-assert" => {
                self.effect(function, "io", site);
            }
            "alloc" | "allocate" | "realloc" | "dealloc" => {
                self.effect(function, "allocation", site);
            }
            _ => {}
        }
        if matches!(
            head,
            "addr-of"
                | "addr-of-mut"
                | "ptr-read"
                | "ptr-write"
                | "ptr-offset"
                | "ptr-borrow"
                | "ptr-borrow-mut"
                | "pin-ptr-borrow"
                | "pin-ptr-borrow-mut"
                | "pin-read"
                | "pin-get-payload-unchecked"
                | "pin-get-payload-unchecked-mut"
                | "word-read"
                | "word-take"
                | "word-forget"
                | "word-write"
                | "word-view"
                | "pin-write"
                | "pin-own-of"
                | "pin-release"
                | "pin-share-clone"
                | "pin-shared-borrow-mut"
                | "pin-shared-release"
        ) {
            self.effect(function, "unsafe", site);
        }
        if matches!(
            head,
            "deref-set"
                | "pin-own-of"
                | "ptr-write"
                | "word-write"
                | "word-take"
                | "word-forget"
                | "pin-write"
                | "pin-set-field"
                | "atomic-store"
                | "atomic-fetch-add"
                | "atomic-exchange"
                | "atomic-compare-exchange"
                | "atomic-compare-exchange-weak"
        ) {
            self.effect(function, "mutation", site);
            // An indirect destination may refer to global storage.
            self.effect(function, "global-write", site);
        }
    }

    fn instructions(&mut self, function: &str, instructions: &[Instruction]) {
        for instruction in instructions {
            let head = match &instruction.control {
                Control::Bind(_, _, mutable) => Some(if *mutable { "let-mut" } else { "let" }),
                Control::Destructure { otherwise, .. } => Some(if otherwise.is_some() {
                    "let-else"
                } else {
                    "let"
                }),
                Control::Assign(_, projection, _) => Some(match projection {
                    Projection::Local => "set",
                    Projection::Array(_) => "set-index",
                    Projection::Field(_) | Projection::Tuple(_) => "set-field",
                    Projection::Payload(_, _) => "set-payload",
                }),
                Control::While(_, _) => Some("while"),
                Control::Loop(_) => Some("loop"),
                Control::For(_, _, _, _) => Some("for"),
                Control::Labeled(_, _) => Some("label"),
                Control::Return(_) => Some("return"),
                Control::Break(label, _) => {
                    Some(if label.is_some() { "break-to" } else { "break" })
                }
                Control::Continue(label) => Some(if label.is_some() {
                    "continue-to"
                } else {
                    "continue"
                }),
                Control::Evaluate(_) => None,
            };
            if let Some(head) = head {
                self.builtins
                    .entry(function.into())
                    .or_default()
                    .insert(normalize_builtin(head));
            }
            match &instruction.control {
                Control::Assign(root, projection, _) => {
                    if matches!(root, PlaceRoot::Global(_)) {
                        self.effect(function, "global-write", "#set-global");
                        if let PlaceRoot::Global(id) = root {
                            if self.statics.contains(id) {
                                self.effect(function, "unsafe", "#static");
                            }
                        }
                    }
                    if !matches!((root, projection), (PlaceRoot::Local(_), Projection::Local)) {
                        self.effect(function, "mutation", "#set");
                    }
                }
                Control::While(_, body) | Control::Loop(body) => self.instructions(function, body),
                Control::For(init, _, step, body) => {
                    self.instructions(function, std::slice::from_ref(init.as_ref()));
                    self.instructions(function, std::slice::from_ref(step.as_ref()));
                    self.instructions(function, body);
                }
                Control::Labeled(_, inner) => {
                    self.instructions(function, std::slice::from_ref(inner.as_ref()));
                }
                Control::Destructure {
                    otherwise: Some(body),
                    ..
                } => self.instructions(function, body),
                _ => {}
            }
        }
    }

    fn require_function(&self, function: &str) -> Result<(), String> {
        if self.edges.contains_key(function) {
            Ok(())
        } else {
            Err(format!("unknown function '{function}'"))
        }
    }

    /// Direct paths contain one call edge; transitive calls require a nonempty path.
    pub fn path(&self, from: &str, to: &str, direct: bool) -> Result<Option<Vec<String>>, String> {
        self.require_function(from)?;
        self.require_function(to)?;
        if direct {
            return Ok(self.edges[from]
                .contains(to)
                .then(|| vec![from.into(), to.into()]));
        }
        if from == to {
            return Ok(None);
        } // Checked runtime calls are acyclic.
        Ok(self.search(from, |_| false, |function| (function == to).then(Vec::new)))
    }

    pub fn forbidden_effect(
        &self,
        from: &str,
        effect: &str,
    ) -> Result<Option<Vec<String>>, String> {
        self.require_function(from)?;
        if !EFFECTS.contains(&effect) {
            return Err(format!("unknown effect '{effect}'"));
        }
        Ok(self.search(
            from,
            |_| false,
            |function| {
                self.effects
                    .get(function)?
                    .get(effect)?
                    .first()
                    .map(|site| vec![site.clone()])
            },
        ))
    }

    pub(super) fn accesses_globals(&self, from: &str) -> Result<bool, String> {
        self.require_function(from)?;
        Ok(self
            .search(
                from,
                |_| false,
                |name| self.global_accesses.contains(name).then(Vec::new),
            )
            .is_some())
    }

    #[cfg(test)]
    pub fn builtin_path(&self, from: &str, builtin: &str) -> Result<Option<Vec<String>>, String> {
        self.require_function(from)?;
        let builtin = normalize_builtin(builtin);
        Ok(self.search(
            from,
            |_| false,
            |function| {
                self.builtins
                    .get(function)?
                    .contains(&builtin)
                    .then(|| vec![builtin.clone()])
            },
        ))
    }

    /// Allowed functions are trusted boundaries; other functions, including
    /// known unsafe functions, are opened and inspected for unsafe primitives.
    pub fn unsafe_outside(
        &self,
        from: &str,
        allowed: &BTreeSet<String>,
    ) -> Result<Option<Vec<String>>, String> {
        self.require_function(from)?;
        let primitives: BTreeSet<_> = allowed
            .iter()
            .filter(|name| name.starts_with('#'))
            .map(|name| normalize_builtin(name))
            .collect();
        Ok(self.search(
            from,
            |function| allowed.contains(function),
            |function| {
                self.unsafe_sites
                    .get(function)?
                    .iter()
                    .find(|site| !allowed.contains(*site) && !primitives.contains(*site))
                    .map(|site| vec![site.clone()])
            },
        ))
    }

    fn search(
        &self,
        from: &str,
        skip: impl Fn(&str) -> bool,
        terminal: impl Fn(&str) -> Option<Vec<String>>,
    ) -> Option<Vec<String>> {
        let mut queue = VecDeque::from([from.to_owned()]);
        let mut parents = BTreeMap::from([(from.to_owned(), None::<String>)]);
        while let Some(function) = queue.pop_front() {
            if skip(&function) {
                continue;
            }
            if let Some(mut suffix) = terminal(&function) {
                let mut path = vec![function.clone()];
                let mut current = &function;
                while let Some(parent) = &parents[current] {
                    path.push(parent.clone());
                    current = parent;
                }
                path.reverse();
                // External function identities already appear in the path.
                if suffix.first() == path.last() {
                    suffix.remove(0);
                }
                path.extend(suffix);
                return Some(path);
            }
            for callee in self.edges.get(&function).into_iter().flatten() {
                if !parents.contains_key(callee) {
                    parents.insert(callee.clone(), Some(function.clone()));
                    queue.push_back(callee.clone());
                }
            }
        }
        None
    }
}

fn normalize_builtin(name: &str) -> String {
    let source = if name.starts_with('#') {
        name.to_owned()
    } else {
        format!("#{name}")
    };
    let internal = crate::names::numeric_operation(&source)
        .unwrap_or_else(|| name.trim_start_matches('#').to_owned());
    crate::names::numeric_source(&internal).unwrap_or_else(|| {
        format!(
            "#{}",
            match internal.as_str() {
                "array-of" => "array",
                other => other,
            }
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(source: &str) -> Graph {
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        Graph::new(&program, checked.declarations())
    }

    #[test]
    fn checked_calls_and_numeric_builtins_keep_distinct_identities() {
        let graph = graph(
            "(#fn u64-add-wrap ((a #u64) (b #u64)) #u64 (#return a))
             (#fn middle () #u64 (#return (#u64::add-wrap 1u64 2u64)))
             (#fn main () #u64 (#return (#call middle (:))))",
        );
        assert_eq!(
            graph.path("main", "middle", true).unwrap(),
            Some(vec!["main".into(), "middle".into()])
        );
        assert_eq!(graph.path("main", "u64-add-wrap", false).unwrap(), None);
        assert_eq!(
            graph.builtin_path("main", "#u64::add-wrap").unwrap(),
            Some(vec![
                "main".into(),
                "middle".into(),
                "#u64::add-wrap".into()
            ])
        );
        assert_eq!(
            graph.builtin_path("main", "u64.+.wrap").unwrap(),
            graph.builtin_path("main", "#u64::add-wrap").unwrap()
        );
        assert!(graph.path("missing", "middle", false).is_err());
        assert!(graph.path("main", "missing", false).is_err());
        assert!(graph.forbidden_effect("main", "missing").is_err());
    }

    #[test]
    fn local_scalar_assignment_has_no_observable_mutation() {
        let graph = graph("(#fn main () #u64 (#let-mut x #u64 0u64) (#set x 1u64) (#return x))");
        assert_eq!(graph.forbidden_effect("main", "mutation").unwrap(), None);
        assert_eq!(
            graph.forbidden_effect("main", "global-write").unwrap(),
            None
        );
    }

    #[test]
    fn unsafe_flag_opens_internals_and_allowed_functions_bound_them() {
        let graph = graph(
            "(#unsafe-fn harmless () #u64 (#return 0u64))
             (#fn main () #u64 (#return (#unsafe (#unsafe-call harmless (:)))))",
        );
        assert_eq!(
            graph.unsafe_outside("main", &BTreeSet::new()).unwrap(),
            None
        );
        assert_eq!(graph.forbidden_effect("main", "unsafe").unwrap(), None);
    }

    #[test]
    fn reference_writes_are_observable() {
        let graph = graph(
            "(#fn change ((value (#ref-mut #u64))) () (#deref-set value 1u64) (#return ()))
             (#fn main () #u64 (#return 0u64))",
        );
        assert!(graph
            .forbidden_effect("change", "mutation")
            .unwrap()
            .is_some());
        assert_eq!(graph.forbidden_effect("change", "unsafe").unwrap(), None);
    }

    #[test]
    fn paths_are_sorted_structural_and_cycle_safe() {
        let mut graph = graph("(#fn main () #u64 (#return 0u64))");
        graph.edge("main", "z");
        graph.edge("main", "a");
        graph.edge("z", "end");
        graph.edge("a", "end");
        graph.edge("a", "main");
        assert_eq!(
            graph.path("main", "end", false).unwrap(),
            Some(vec!["main".into(), "a".into(), "end".into()])
        );
        assert_eq!(graph.path("main", "end", true).unwrap(), None);
        assert_eq!(graph.path("end", "main", false).unwrap(), None);
        assert_eq!(graph.path("main", "main", false).unwrap(), None);
    }

    #[test]
    fn unknown_execution_blocks_all_negative_effect_claims() {
        let mut graph = graph("(#fn main () #u64 (#return 0u64))");
        graph.unknown("main", "#asm");
        for effect in EFFECTS {
            assert_eq!(
                graph.forbidden_effect("main", effect).unwrap(),
                Some(vec!["main".into(), "#asm".into()])
            );
        }
        assert!(graph
            .unsafe_outside("main", &BTreeSet::new())
            .unwrap()
            .is_some());
        assert_eq!(
            graph
                .unsafe_outside("main", &BTreeSet::from(["#asm".into()]))
                .unwrap(),
            None
        );
    }
}
