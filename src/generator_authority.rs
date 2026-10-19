//! Authority travels with syntax references, never with their spelling.
use crate::{Expr, Span, SpannedExpr};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Clone, Debug)]
pub(crate) struct Syntax {
    pub expr: Expr,
    // Preorder symbol ordinals. Empty for caller input and manufactured names.
    marks: BTreeMap<usize, Span>,
}

fn count(expr: &Expr) -> usize {
    match expr {
        Expr::Symbol(_) | Expr::Generate => 1,
        Expr::List(items) => items.iter().map(count).sum(),
        Expr::Quote(inner)
        | Expr::QuasiQuote(inner)
        | Expr::Unquote(inner)
        | Expr::UnquoteSplicing(inner) => count(inner),
        _ => 0,
    }
}

impl From<Expr> for Syntax {
    fn from(expr: Expr) -> Self {
        Self {
            expr,
            marks: BTreeMap::new(),
        }
    }
}

impl Syntax {
    pub fn authored(expr: Expr, author: Option<Span>) -> Self {
        let marks = author.map_or_else(BTreeMap::new, |span| {
            (0..count(&expr)).map(|index| (index, span)).collect()
        });
        Self { expr, marks }
    }

    pub fn authority(&self) -> Option<Span> {
        self.marks.get(&0).copied()
    }
    pub fn has_authority(&self) -> bool {
        !self.marks.is_empty()
    }

    pub fn identity(&self, caller: &str, context: impl Fn(Span) -> String) -> String {
        let permissions = self
            .marks
            .iter()
            .filter_map(|(index, author)| {
                let authority = context(*author);
                (authority != caller).then_some((*index, authority))
            })
            .collect::<Vec<_>>();
        format!("{:?}:{permissions:?}", self.expr)
    }

    pub fn list(values: Vec<Self>) -> Self {
        if values.iter().all(|value| value.marks.is_empty()) {
            return Expr::List(values.into_iter().map(|value| value.expr).collect()).into();
        }
        let mut marks = BTreeMap::new();
        let mut offset = 0;
        let mut expressions = Vec::with_capacity(values.len());
        for value in values {
            marks.extend(
                value
                    .marks
                    .into_iter()
                    .map(|(index, span)| (index + offset, span)),
            );
            offset += count(&value.expr);
            expressions.push(value.expr);
        }
        Self {
            expr: Expr::List(expressions),
            marks,
        }
    }

    pub fn parts(self) -> Option<Vec<Self>> {
        let Expr::List(items) = self.expr else {
            return None;
        };
        if self.marks.is_empty() {
            return Some(items.into_iter().map(Self::from).collect());
        }
        let mut offset = 0;
        Some(
            items
                .into_iter()
                .map(|expr| {
                    let end = offset + count(&expr);
                    let marks = self
                        .marks
                        .range(offset..end)
                        .map(|(index, span)| (index - offset, *span))
                        .collect();
                    offset = end;
                    Self { expr, marks }
                })
                .collect(),
        )
    }

    pub fn wrap(self, constructor: fn(Box<Expr>) -> Expr) -> Self {
        Self {
            expr: constructor(Box::new(self.expr)),
            marks: self.marks,
        }
    }

    pub fn attach(&self, tree: &SpannedExpr, target: &mut HashMap<Span, Span>) {
        fn walk(
            tree: &SpannedExpr,
            marks: &BTreeMap<usize, Span>,
            index: &mut usize,
            target: &mut HashMap<Span, Span>,
        ) {
            if matches!(tree.expr, Expr::Symbol(_) | Expr::Generate) {
                if let Some(author) = marks.get(index) {
                    target.insert(tree.span, *author);
                }
                *index += 1;
            }
            for child in &tree.children {
                walk(child, marks, index, target);
            }
        }
        walk(tree, &self.marks, &mut 0, target);
    }

    pub fn from_tree(tree: &SpannedExpr, references: &HashMap<Span, Span>) -> Self {
        fn walk(
            tree: &SpannedExpr,
            references: &HashMap<Span, Span>,
            index: &mut usize,
            marks: &mut BTreeMap<usize, Span>,
        ) {
            if matches!(tree.expr, Expr::Symbol(_) | Expr::Generate) {
                if let Some(author) = references.get(&tree.span) {
                    marks.insert(*index, *author);
                }
                *index += 1;
            }
            for child in &tree.children {
                walk(child, references, index, marks);
            }
        }
        let mut marks = BTreeMap::new();
        walk(tree, references, &mut 0, &mut marks);
        Self {
            expr: tree.expr.clone(),
            marks,
        }
    }
}

pub(crate) fn add_operations<'a>(
    forms: impl IntoIterator<Item = &'a SpannedExpr>,
    references: &HashMap<Span, Span>,
    target: &mut HashMap<Span, Span>,
) {
    if references.is_empty() {
        return;
    }
    fn walk(
        tree: &SpannedExpr,
        references: &HashMap<Span, Span>,
        target: &mut HashMap<Span, Span>,
    ) {
        for child in &tree.children {
            walk(child, references, target);
        }
        // Never grant a declaration or enclosing control-flow block blanket
        // authority: missing child spans must fail closed, not fall back to a
        // privileged function/statement span. Projection rights come from the
        // actual selector/type operand, not merely a template-authored #get.
        let Some(head) = tree.children.first() else {
            return;
        };
        let Expr::Symbol(head_name) = &head.expr else {
            return;
        };
        let reference = match head_name.as_str() {
            "#get" | "#set-field" | "#pin-set-field" | "#pin-get-field-mut" => tree.children.get(2),
            "#struct-literal" | "#enum-literal" => tree.children.get(1),
            "#clone" => Some(head),
            "#borrow" | "#borrow-mut" | "#pin-borrow-mut" | "#borrow-slice"
            | "#borrow-slice-mut" | "#set" | "#deref-set" => tree.children.get(1),
            name if name.contains('.') && !name.starts_with('#') => Some(head),
            _ => None,
        };
        if let Some(author) = reference
            .and_then(|node| {
                references
                    .get(&node.span)
                    .or_else(|| target.get(&node.span))
            })
            .copied()
        {
            target.insert(tree.span, author);
        }
    }
    for form in forms {
        walk(form, references, target);
    }
}

const HEADER: &str = "; lim-reference-authority-v1 ";

// This metadata is part of the digest-checked cache payload. It is ignored by
// the ordinary reader: copying a generated file into source grants nothing.
pub(crate) fn append_metadata(source: &mut String, forms: &[Syntax]) {
    if forms.iter().all(|form| form.marks.is_empty()) {
        return;
    }
    use std::fmt::Write;
    let mut groups = BTreeMap::<(u32, usize, usize, usize, usize), Vec<usize>>::new();
    let mut offset = 0;
    for form in forms {
        for (index, span) in &form.marks {
            groups
                .entry((span.source_id, span.start, span.end, span.line, span.column))
                .or_default()
                .push(offset + index);
        }
        offset += count(&form.expr);
    }
    for ((source_id, start, end, line, column), indices) in groups {
        let _ = write!(
            source,
            "\n{HEADER}{source_id} {start} {end} {line} {column}"
        );
        for index in indices {
            let _ = write!(source, " {index}");
        }
        source.push('\n');
    }
}

pub(crate) fn restore(source: &str, expressions: Vec<Expr>) -> Option<Vec<Syntax>> {
    if !source.contains(HEADER) {
        return Some(expressions.into_iter().map(Syntax::from).collect());
    }
    let mut marks = BTreeMap::new();
    let total: usize = expressions.iter().map(count).sum();
    for line in source.lines().filter_map(|line| line.strip_prefix(HEADER)) {
        let mut values = line.split_whitespace().map(str::parse::<usize>);
        let source_id = u32::try_from(values.next()?.ok()?).ok()?;
        let span = Span {
            source_id,
            start: values.next()?.ok()?,
            end: values.next()?.ok()?,
            line: values.next()?.ok()?,
            column: values.next()?.ok()?,
        };
        if span.start > span.end || span.line == 0 || span.column == 0 {
            return None;
        }
        for index in values {
            let index = index.ok()?;
            if index >= total || marks.insert(index, span).is_some() {
                return None;
            }
        }
    }
    Syntax {
        expr: Expr::List(expressions),
        marks,
    }
    .parts()
}

pub(crate) fn valid_authors(forms: &[Syntax], allowed: &HashSet<Span>) -> bool {
    forms
        .iter()
        .all(|form| form.marks.values().all(|span| allowed.contains(span)))
}

/// A compiler builtin is a trusted syntax transformer, but its substituted
/// operands are not. Transfer only operand references (including associated
/// names derived from an explicitly supplied root), never blanket authority.
pub(crate) fn transfer_builtin(
    input: &SpannedExpr,
    output: &SpannedExpr,
    authorities: &mut HashMap<Span, Span>,
) {
    fn inputs(
        node: &SpannedExpr,
        authorities: &HashMap<Span, Span>,
        names: &mut HashMap<String, Option<Span>>,
    ) {
        if let Expr::Symbol(name) = &node.expr {
            let author = authorities.get(&node.span).copied();
            names
                .entry(name.clone())
                .and_modify(|existing| {
                    if *existing != author {
                        *existing = None;
                    }
                })
                .or_insert(author);
        }
        for child in &node.children {
            inputs(child, authorities, names);
        }
    }
    fn outputs(
        node: &SpannedExpr,
        names: &HashMap<String, Option<Span>>,
        authorities: &mut HashMap<Span, Span>,
    ) {
        if let Expr::Symbol(name) = &node.expr {
            let matched = names.get(name).or_else(|| {
                names
                    .iter()
                    .filter(|(root, _)| {
                        name.strip_prefix(root.as_str())
                            .is_some_and(|tail| tail.starts_with("::") || tail.starts_with('.'))
                    })
                    .max_by_key(|(root, _)| root.len())
                    .map(|(_, author)| author)
            });
            if let Some(Some(author)) = matched {
                authorities.insert(node.span, *author);
            }
        }
        for child in &node.children {
            outputs(child, names, authorities);
        }
    }
    let mut names = HashMap::new();
    inputs(input, authorities, &mut names);
    outputs(output, &names, authorities);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_round_trip_distinguishes_identical_symbol_spellings() {
        let author = Span::new(1, 9, 1, 2);
        let form = Syntax::list(vec![
            Syntax::authored(Expr::Symbol("secret".into()), Some(author)),
            Expr::Symbol("secret".into()).into(),
        ]);
        let mut source = crate::expression_source(&form.expr).unwrap();
        append_metadata(&mut source, &[form.clone()]);
        let expressions = crate::parse(&source)
            .unwrap()
            .into_iter()
            .map(|node| node.expr)
            .collect();
        let restored = restore(&source, expressions).unwrap();
        assert_eq!(restored[0].expr, form.expr);
        assert_eq!(restored[0].marks, form.marks);
        assert!(valid_authors(&restored, &HashSet::from([author])));
        assert!(!valid_authors(&restored, &HashSet::new()));
    }

    #[test]
    fn malformed_cache_metadata_fails_closed() {
        for row in ["0 0 1 1 1 2", "0 0 1 1 1 0 0", "0 0 1 0 1 0", "not-a-span"] {
            let source = format!("secret\n{HEADER}{row}\n");
            assert!(restore(&source, vec![Expr::Symbol("secret".into())]).is_none());
        }
    }

    #[test]
    fn trusted_operator_cannot_authorize_an_untrusted_selector_or_function() {
        let author = Span::new(1, 9, 1, 2);
        let expression = Syntax::list(vec![
            Syntax::authored(Expr::Symbol("#get".into()), Some(author)),
            Expr::Symbol("value".into()).into(),
            Expr::Symbol("capacity".into()).into(),
        ]);
        let tree = crate::parse(&crate::expression_source(&expression.expr).unwrap())
            .unwrap()
            .remove(0);
        let mut references = HashMap::new();
        expression.attach(&tree, &mut references);
        let mut operations = references.clone();
        add_operations([&tree], &references, &mut operations);
        assert!(!operations.contains_key(&tree.span));

        let tree = crate::parse("(#fn main () #u64 (#return 42u64))")
            .unwrap()
            .remove(0);
        let template = Syntax::authored(tree.expr.clone(), Some(author));
        references.clear();
        template.attach(&tree, &mut references);
        operations = references.clone();
        add_operations([&tree], &references, &mut operations);
        assert!(!operations.contains_key(&tree.span));
        assert!(!operations.contains_key(&tree.children[4].span));
    }
}
