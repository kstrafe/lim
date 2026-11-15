//! Declared prerequisites only. Nodes are semantic obligations; edges retain
//! declaration origins without materializing every route through a diamond.
use super::*;
use crate::{DiagnosticCode, SourceError, Span, SpannedExpr};

const NODE_LIMIT: usize = 1024;
const EDGE_LIMIT: usize = 8192;
const DEPTH_LIMIT: usize = 64;
const WORK_LIMIT: usize = 200_000;
const EXPRESSION_LIMIT: usize = 4096;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Dependency {
    pub node: usize,
    /// The predicate's declared #requires expression, before substitution.
    pub span: Option<Span>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Obligation {
    pub expression: Expr,
    pub prerequisites: Vec<Dependency>,
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Requirements {
    pub nodes: Vec<Obligation>,
    /// One entry per written root, including duplicate roots and their spans.
    pub roots: Vec<Dependency>,
    /// Prerequisites precede every use, independent of declaration order.
    pub order: Vec<usize>,
}
impl Requirements {
    pub fn ordered(&self) -> impl Iterator<Item = &Expr> {
        self.order.iter().map(|&i| &self.nodes[i].expression)
    }
    /// Select one explanatory route only when reporting an error. All other
    /// origins remain available as graph edges to tooling.
    pub fn trace(&self, target: usize) -> Vec<(Span, String)> {
        fn find(
            graph: &Requirements,
            edge: &Dependency,
            target: usize,
            seen: &mut [bool],
            route: &mut Vec<(Span, String)>,
            root: bool,
        ) -> bool {
            if seen[edge.node] {
                return false;
            }
            seen[edge.node] = true;
            let len = route.len();
            if let Some(span) = edge.span {
                let kind = if root {
                    "root requirement"
                } else {
                    "prerequisite"
                };
                route.push((
                    span,
                    format!("{kind} {:?}", graph.nodes[edge.node].expression),
                ));
            }
            if edge.node == target
                || graph.nodes[edge.node]
                    .prerequisites
                    .iter()
                    .any(|next| find(graph, next, target, seen, route, false))
            {
                return true;
            }
            route.truncate(len);
            false
        }
        let mut route = Vec::new();
        let mut seen = vec![false; self.nodes.len()];
        for root in &self.roots {
            if find(self, root, target, &mut seen, &mut route, true) {
                break;
            }
        }
        route
    }
}

fn fail(message: impl Into<String>, span: Option<Span>) -> SourceError {
    let error = SourceError::new(message, DiagnosticCode::Contract);
    if let Some(span) = span {
        error.at(span)
    } else {
        error
    }
}
fn budget(span: Option<Span>) -> SourceError {
    fail(
        "predicate prerequisite expansion budget exhausted; no partial interface was accepted",
        span,
    )
}

/// Charge emitted syntax, including substitutions, before cloning it. This
/// bounds growing arguments as well as graph size and the number of edges.
fn instantiate(
    expr: &Expr,
    bindings: &HashMap<String, Expr>,
    work: &mut usize,
    span: Option<Span>,
) -> Result<Expr, SourceError> {
    fn copy(
        expr: &Expr,
        bindings: &HashMap<String, Expr>,
        work: &mut usize,
        size: &mut usize,
        depth: usize,
        span: Option<Span>,
    ) -> Result<Expr, SourceError> {
        *work += match expr {
            Expr::Symbol(s) | Expr::Function(s) | Expr::String(s) | Expr::Float(s) => {
                s.len().saturating_add(1)
            }
            _ => 1,
        };
        *size += 1;
        if *work > WORK_LIMIT || *size > EXPRESSION_LIMIT || depth > DEPTH_LIMIT {
            return Err(budget(span));
        }
        match expr {
            Expr::Symbol(name) if bindings.contains_key(name) => copy(
                &bindings[name],
                &HashMap::new(),
                work,
                size,
                depth + 1,
                span,
            ),
            Expr::List(xs) => {
                let empty = HashMap::new();
                let mut out = Vec::new();
                for (index, x) in xs.iter().enumerate() {
                    let literal = index == 0
                        || (head(expr) == "get" && index == 2)
                        || (matches!(head(expr), "as" | "literal" | "array" | "tuple")
                            && index == if head(expr) == "as" { 2 } else { 1 });
                    out.push(copy(
                        x,
                        if literal { &empty } else { bindings },
                        work,
                        size,
                        depth + 1,
                        span,
                    )?);
                }
                Ok(Expr::List(out.into()))
            }
            Expr::Block(_)
            | Expr::Loop(_)
            | Expr::Labeled { .. }
            | Expr::Quote(_)
            | Expr::QuasiQuote(_)
            | Expr::Unquote(_)
            | Expr::UnquoteSplicing(_) => {
                Err(fail("unsupported predicate prerequisite expression", span))
            }
            Expr::Symbol(s) | Expr::Function(s) | Expr::String(s) if s.len() > 16 * 1024 => {
                Err(budget(span))
            }
            _ => Ok(expr.clone()),
        }
    }
    copy(expr, bindings, work, &mut 0, 0, span)
}

fn root_spans(program: &Program, name: &str, count: usize) -> Vec<Option<Span>> {
    fn split(source: &SpannedExpr, spans: &mut Vec<Option<Span>>) {
        let normalized = crate::normalize_keywords(source.expr.clone());
        if matches!(head(&normalized), "bool.&&" | "&&") {
            for child in source.children.iter().skip(1) {
                split(child, spans);
            }
        } else {
            spans.push(Some(source.span));
        }
    }
    let mut spans = Vec::new();
    let f = &program.contracts.originals[name];
    for (index, statement) in f.body.iter().enumerate() {
        if matches!(statement, Statement::Expr(e) if head(e) == "requires") {
            if let Some(source) = program.statement_expressions.get(&(name.into(), index)) {
                if let Some(predicate) = source.children.get(1) {
                    split(predicate, &mut spans);
                }
            }
        }
    }
    // Signature refinement roots have no written #requires expression.
    spans.resize(count, None);
    spans
}

struct Builder<'a> {
    program: &'a Program,
    spans: &'a BTreeMap<String, Vec<Option<Span>>>,
    graph: Requirements,
    memo: HashMap<String, usize>,
    active: Vec<String>,
    edges: usize,
    work: &'a mut usize,
}
impl Builder<'_> {
    fn node(&mut self, expression: Expr, span: Option<Span>) -> Result<usize, SourceError> {
        let predicate = match parts(&expression).first() {
            Some(Expr::Function(name)) => Some(name.clone()),
            _ => None,
        };
        if predicate
            .as_ref()
            .is_some_and(|name| self.active.contains(name))
        {
            let mut cycle = self.active.clone();
            cycle.push(predicate.unwrap());
            return Err(fail(
                format!("cyclic predicate prerequisites: {}", cycle.join(" -> ")),
                span,
            ));
        }
        let key = format!("{expression:?}");
        if let Some(&node) = self.memo.get(&key) {
            return Ok(node);
        }
        if self.graph.nodes.len() >= NODE_LIMIT || self.active.len() >= DEPTH_LIMIT {
            return Err(budget(span));
        }
        let node = self.graph.nodes.len();
        self.graph.nodes.push(Obligation {
            expression: expression.clone(),
            prerequisites: Vec::new(),
        });
        if let Some(name) = predicate {
            let f = self
                .program
                .contracts
                .originals
                .get(&name)
                .ok_or_else(|| fail(format!("unknown predicate '{name}'"), span))?;
            if parts(&expression).len() != f.parameters.len() + 1 {
                return Err(fail(
                    format!("predicate '{name}' has incorrect arity"),
                    span,
                ));
            }
            let bindings = f
                .parameters
                .iter()
                .zip(&parts(&expression)[1..])
                .map(|(p, arg)| (p.name.clone(), arg.clone()))
                .collect();
            self.active.push(name.clone());
            for index in 0..self.program.contracts.clauses[&name].requires.len() {
                self.edges += 1;
                if self.edges > EDGE_LIMIT {
                    return Err(budget(span));
                }
                let origin = self.spans[&name][index];
                let prerequisite = instantiate(
                    &self.program.contracts.clauses[&name].requires[index],
                    &bindings,
                    self.work,
                    origin,
                )?;
                let child = self.node(prerequisite, origin)?;
                self.graph.nodes[node].prerequisites.push(Dependency {
                    node: child,
                    span: origin,
                });
            }
            self.active.pop();
        }
        self.memo.insert(key, node);
        self.graph.order.push(node);
        Ok(node)
    }
}

pub(super) fn expand(program: &mut Program) -> Result<(), SourceError> {
    let spans: BTreeMap<String, Vec<Option<Span>>> = program
        .contracts
        .clauses
        .iter()
        .map(|(name, clauses)| {
            (
                name.clone(),
                root_spans(program, name, clauses.requires.len()),
            )
        })
        .collect();
    let mut effective = BTreeMap::new();
    let mut work = 0;
    for (name, clauses) in &program.contracts.clauses {
        let mut builder = Builder {
            program,
            spans: &spans,
            graph: Requirements::default(),
            memo: HashMap::new(),
            active: Vec::new(),
            edges: 0,
            work: &mut work,
        };
        for (index, root) in clauses.requires.iter().enumerate() {
            builder.edges += 1;
            if builder.edges > EDGE_LIMIT {
                return Err(budget(spans[name][index]));
            }
            let span = spans[name][index];
            let expression = instantiate(root, &HashMap::new(), builder.work, span)?;
            let node = builder.node(expression, span)?;
            builder.graph.roots.push(Dependency { node, span });
        }
        effective.insert(name.clone(), builder.graph);
    }
    program.contracts.effective_requires = effective;
    Ok(())
}

/// Resolve the exact written call within the current statement, including a
/// nested #if-valid call. Matching normalized syntax distinguishes arguments.
pub(super) fn call_span(
    program: &Program,
    function: &str,
    current: Option<Span>,
    call: &Expr,
) -> Option<Span> {
    fn same_expression(left: &Expr, right: &Expr) -> bool {
        match (left, right) {
            (Expr::List(left), Expr::List(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right.iter())
                        .all(|(a, b)| same_expression(a, b))
            }
            _ => left == right,
        }
    }
    fn find(program: &Program, source: &SpannedExpr, call: &Expr) -> Option<Span> {
        let h = head(&source.expr);
        if matches!(h, "#call" | "call") || program.contracts.originals.contains_key(h) {
            let expression = crate::normalize_keywords(source.expr.clone());
            if normalized(&expression, program)
                .ok()
                .is_some_and(|expression| same_expression(&expression, call))
            {
                return Some(source.span);
            }
        }
        source
            .children
            .iter()
            .find_map(|child| find(program, child, call))
    }
    program
        .statement_expressions
        .iter()
        .filter(|((name, _), source)| {
            name == function
                && current.is_none_or(|span| {
                    source.span.source_id == span.source_id
                        && source.span.start <= span.start
                        && source.span.end >= span.end
                })
        })
        .find_map(|(_, source)| find(program, source, call))
}

#[cfg(test)]
mod tests {
    #[test]
    fn shared_prerequisite_keeps_one_obligation_and_all_origin_edges() {
        let source = r#"
#fn base { #params = ((value #u64)); #returns = #bool;
  #body = ( (#return true) ); }
#fn left { #params = ((value #u64)); #returns = #bool;
  #body = ( (#requires (#call base ((value value)))) (#return true) ); }
#fn right { #params = ((value #u64)); #returns = #bool;
  #body = ( (#requires (#call base ((value value)))) (#return true) ); }
#fn consume { #params = ((value #u64)); #returns = ();
  #body = ( (#requires (#call left ((value value))))
            (#requires (#call right ((value value))))
            (#requires (#call base ((value value))))
            (#requires (#call left ((value value)))) (#return ()) ); }
"#;
        let program = crate::parse_program(source).unwrap();
        let graph = &program.contracts.effective_requires["consume"];
        assert_eq!(program.contracts.clauses["consume"].requires.len(), 4);
        assert_eq!(graph.roots.len(), 4);
        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.order.len(), 3);
        let base = graph.order[0];
        assert_eq!(graph.roots[2].node, base);
        assert_eq!(graph.roots[0].node, graph.roots[3].node);
        assert_ne!(graph.roots[0].span, graph.roots[3].span);
        let left = &graph.nodes[graph.roots[0].node].prerequisites[0];
        let right = &graph.nodes[graph.roots[1].node].prerequisites[0];
        assert_eq!(left.node, base);
        assert_eq!(right.node, base);
        assert_ne!(left.span, right.span);
        assert!(left.span.is_some() && right.span.is_some());
    }
}
