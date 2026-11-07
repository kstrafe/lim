//! Declaration locations for mathematical-only native proof artifacts.
//! Locations and names schedule work; every loaded body is parsed and checked
//! again by the common kernel adapter. This is not a general import frontend.
use super::native_file::Snapshot;
use super::{DeclarationSource, Expr, Item, Result};
use crate::{source_forms, source_forms::SourceForms, Span};
use std::collections::{BTreeSet, HashMap, HashSet};

pub(super) const SOURCE_BYTES: usize = 8 * 1024 * 1024;

pub(super) struct Source<'a> {
    text: Backing<'a>,
    records: Vec<Record>,
    names: HashMap<String, usize>,
    limits: crate::NativeProofLimits,
}
enum Backing<'a> {
    Memory(&'a str),
    File(Snapshot),
}
struct Record {
    name: String,
    span: Span,
    theorem: bool,
}

impl<'a> Source<'a> {
    pub(super) fn new(text: &'a str) -> Result<Self> {
        Self::with_limits(text, crate::NativeProofLimits::default())
    }
    pub(super) fn with_limits(text: &'a str, limits: crate::NativeProofLimits) -> Result<Self> {
        Self::inventory(text, false, limits)
    }
    /// A conservative probe, not an alternate interpretation of source errors.
    /// Anything needing ordinary source processing goes through that frontend.
    pub(super) fn standalone(text: &'a str) -> Option<Self> {
        Self::inventory(
            text,
            true,
            crate::NativeProofLimits {
                max_directory_bytes: 32 * 1024 * 1024,
                ..Default::default()
            },
        )
        .ok()
    }
    fn inventory(
        text: &'a str,
        standalone: bool,
        limits: crate::NativeProofLimits,
    ) -> Result<Self> {
        if text.len() > limits.max_bytes {
            return Err("proof-source byte limit exceeded".into());
        }
        let mut source = Self {
            text: Backing::Memory(text),
            records: vec![],
            names: HashMap::new(),
            limits,
        };
        let mut directory_bytes = 0usize;
        if text.len() <= SOURCE_BYTES {
            let mut forms = SourceForms::new(text);
            while let Some(form) = forms.next()? {
                account_form(&mut source, &mut directory_bytes, form, standalone, limits)?;
            }
        } else {
            let mut forms = crate::source_reader::ReaderForms::new(
                std::io::Cursor::new(text.as_bytes()),
                SOURCE_BYTES,
            );
            while let Some(form) = forms.next()? {
                let parsed = source_forms::parse_fragment(&form.text, form.span)?;
                account_form(
                    &mut source,
                    &mut directory_bytes,
                    parsed,
                    standalone,
                    limits,
                )?;
            }
        }
        Ok(source)
    }
    fn push(
        &mut self,
        form: crate::SpannedExpr,
        standalone: bool,
        remaining: Option<usize>,
    ) -> Result<usize> {
        let span = form.span;
        if standalone
            && (!context_free(&form.expr) || crate::validate_primitive_spelling(&form).is_err())
        {
            return Err("proof source requires the general frontend".into());
        }
        let Item::Proof { name, proposition } =
            parse_item(form.expr).map_err(|why| at(span, why))?
        else {
            unreachable!()
        };
        if self.records.len() >= self.limits.max_declarations {
            return Err(at(span, "kernel declaration limit exceeded".into()));
        }
        // Cover both name copies and conservative vector/table overhead. This
        // directory is bounded independently of the on-disk source length.
        let weight = name
            .len()
            .checked_mul(2)
            .and_then(|bytes| bytes.checked_add(512))
            .ok_or("proof source directory accounting overflow")?;
        if weight > self.limits.max_directory_bytes || remaining.is_some_and(|limit| weight > limit)
        {
            return Err("proof source directory byte limit exceeded".into());
        }
        if self
            .names
            .insert(name.clone(), self.records.len())
            .is_some()
        {
            return Err(at(span, format!("duplicate kernel declaration '{name}'")));
        }
        let theorem = matches!(&proposition,Expr::List(parts) if matches!(parts.first(),Some(Expr::Symbol(head)) if head=="#proof-theorem"));
        self.records.push(Record {
            name,
            span,
            theorem,
        });
        Ok(weight)
    }
    pub(super) fn item(&self, index: usize) -> Result<Item> {
        let record = self
            .records
            .get(index)
            .ok_or("unknown proof source declaration")?;
        let form = match &self.text {
            Backing::Memory(text) => source_forms::parse_at(text, self.span(index))?,
            Backing::File(snapshot) => {
                let text = snapshot.range(record.span.start, record.span.end)?;
                source_forms::parse_fragment(&text, record.span)?
            }
        };
        let item = parse_item(form.expr).map_err(|why| at(record.span, why))?;
        if !matches!(&item, Item::Proof { name, .. } if name == &record.name) {
            return Err("immutable proof declaration location changed identity".into());
        }
        Ok(item)
    }
    pub(super) fn span(&self, index: usize) -> Span {
        self.records
            .get(index)
            .map_or(Span::new(0, 0, 1, 1), |record| record.span)
    }
    pub(super) fn is_theorem(&self, name: &str) -> bool {
        self.names
            .get(name)
            .is_some_and(|id| self.records[*id].theorem)
    }
    pub(super) fn named_span(&self, name: &str) -> Option<Span> {
        self.names.get(name).map(|index| self.span(*index))
    }
    pub(super) fn proof_limits(&self) -> crate::NativeProofLimits {
        self.limits
    }
    pub(super) fn check(
        &self,
        budget: crate::ProofBudget,
    ) -> std::result::Result<(), (String, String)> {
        super::check_declarations_with_limits(self, budget, &HashSet::new(), self.limits).map_err(
            |(name, why)| {
                let why = self
                    .names
                    .get(&name)
                    .map_or_else(|| why.clone(), |id| at(self.span(*id), why.clone()));
                (name, why)
            },
        )
    }
    /// Called after checking every declaration, including unreachable bodies.
    pub(super) fn foundation_dependencies(&self, target: &str) -> Result<Vec<String>> {
        let mut pending = Vec::new();
        let mut seen = vec![false; self.len()];
        let mut foundations = BTreeSet::new();
        self.enqueue(target, &mut pending, &mut seen, &mut foundations)?;
        let facts = HashSet::new();
        while let Some(id) = pending.pop() {
            let expression = self.declaration(id)?;
            let mut parsed = super::parse_declaration(self.name(id), &expression, &facts)?;
            if let super::Body::Inductive { members, .. } = parsed.body {
                parsed
                    .dependencies
                    .extend(members.into_iter().filter(|name| name != self.name(id)));
            }
            for name in parsed.dependencies {
                self.enqueue(&name, &mut pending, &mut seen, &mut foundations)?;
            }
        }
        Ok(foundations.into_iter().collect())
    }
    fn enqueue(
        &self,
        name: &str,
        pending: &mut Vec<usize>,
        seen: &mut [bool],
        foundations: &mut BTreeSet<String>,
    ) -> Result<()> {
        if let Some(label) = super::core::foundation::label(name) {
            foundations.insert(label.into());
        } else if matches!(name, "#pt-nat" | "#pt-false") {
        } else if let Some(id) = self.names.get(name).copied() {
            if !std::mem::replace(&mut seen[id], true) {
                pending.push(id);
            }
        } else {
            return Err(format!("unknown declaration '{name}' in foundation audit"));
        }
        Ok(())
    }
}

fn account_form(
    source: &mut Source<'_>,
    directory_bytes: &mut usize,
    form: crate::SpannedExpr,
    standalone: bool,
    limits: crate::NativeProofLimits,
) -> Result<()> {
    if form.span.end.saturating_sub(form.span.start) > SOURCE_BYTES {
        return Err("proof-source form byte limit exceeded".into());
    }
    *directory_bytes = directory_bytes
        .checked_add(source.push(
            form,
            standalone,
            Some(limits.max_directory_bytes.saturating_sub(*directory_bytes)),
        )?)
        .ok_or("proof source directory accounting overflow")?;
    Ok(())
}

impl Source<'static> {
    pub(super) fn standalone_snapshot(snapshot: Snapshot) -> Option<Self> {
        let limits = crate::NativeProofLimits {
            max_bytes: 128 * 1024 * 1024,
            max_directory_bytes: 32 * 1024 * 1024,
            ..Default::default()
        };
        Self::snapshot_inventory(snapshot, true, limits).ok()
    }
    pub(super) fn snapshot(snapshot: Snapshot) -> Result<Self> {
        Self::snapshot_with_limits(snapshot, crate::NativeProofLimits::default())
    }
    pub(super) fn snapshot_with_limits(
        snapshot: Snapshot,
        limits: crate::NativeProofLimits,
    ) -> Result<Self> {
        if snapshot.len() > limits.max_bytes {
            return Err("proof-source byte limit exceeded".into());
        }
        Self::snapshot_inventory(snapshot, false, limits)
    }
    fn snapshot_inventory(
        snapshot: Snapshot,
        standalone: bool,
        limits: crate::NativeProofLimits,
    ) -> Result<Self> {
        let mut forms = crate::source_reader::ReaderForms::new(snapshot.reader(), SOURCE_BYTES);
        let mut source = Self {
            text: Backing::File(snapshot),
            records: vec![],
            names: HashMap::new(),
            limits,
        };
        let mut directory_bytes = 0usize;
        while let Some(form) = forms.next()? {
            if form.span.end.saturating_sub(form.span.start) > SOURCE_BYTES {
                return Err("proof-source form byte limit exceeded".into());
            }
            let parsed = source_forms::parse_fragment(&form.text, form.span)?;
            directory_bytes = directory_bytes
                .checked_add(source.push(
                    parsed,
                    standalone,
                    Some(limits.max_directory_bytes.saturating_sub(directory_bytes)),
                )?)
                .ok_or("proof source directory accounting overflow")?;
        }
        Ok(source)
    }
}

/// Authored syntax in this subset must already mean exactly its literal name.
/// In particular, compiler-generated names remain allowed in strict artifacts,
/// but cannot enter through the authored standalone-source shortcut.
fn context_free(expression: &Expr) -> bool {
    match expression {
        Expr::List(parts) => parts.iter().all(context_free),
        Expr::Symbol(name) => {
            !crate::gensym::reserved(name)
                && name != "$lim-file-import"
                && !name.contains('@')
                && crate::file_access::split(name).is_none()
                && (!name.starts_with('#')
                    || name.starts_with("#pt-")
                    || matches!(
                        name.as_str(),
                        "#theorem"
                            | "#math-definition"
                            | "#math-opaque"
                            | "#math-inductive"
                            | "#universes"
                            | "#parameters"
                            | "#parameter"
                            | "#statement"
                            | "#proof"
                            | "#mutual"
                            | "#indices"
                    ))
        }
        Expr::String(value) => crate::file_access::split(value).is_none(),
        Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_) | Expr::Char(_) => true,
        _ => false,
    }
}
impl DeclarationSource for Source<'_> {
    fn len(&self) -> usize {
        self.records.len()
    }
    fn name(&self, index: usize) -> &str {
        self.records
            .get(index)
            .map_or("<unknown>", |record| record.name.as_str())
    }
    fn declaration(&self, index: usize) -> Result<Expr> {
        let Item::Proof { proposition, .. } = self.item(index)? else {
            unreachable!()
        };
        Ok(proposition)
    }
}

fn at(span: Span, message: String) -> String {
    format!("{message} at line {}, column {}", span.line, span.column)
}
fn parse_item(expression: Expr) -> Result<Item> {
    if !matches!(&expression, Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head))
        if matches!(head.as_str(), "#theorem" | "#math-definition" | "#math-opaque" | "#math-inductive")))
    {
        return Err("native proof source accepts only mathematical declarations".into());
    }
    crate::validate_prefixed_forms(&expression)?;
    if let Expr::List(parts) = &expression {
        if let Some(Expr::Symbol(name)) = parts.get(1) {
            crate::names::require(name, "value")?;
        }
    }
    let item = crate::parse_item(&crate::normalize_keywords(expression))?;
    if !matches!(&item, Item::Proof { proposition, .. } if super::is_declaration(proposition)) {
        return Err("native proof source accepts only mathematical declarations".into());
    }
    Ok(item)
}

#[cfg(test)]
#[path = "native_source_tests.rs"]
mod tests;
