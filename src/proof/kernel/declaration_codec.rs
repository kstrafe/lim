//! Bounded binary storage for checked declarations. This codec preserves the
//! exact term DAG and declaration metadata; it performs no kernel validation.
use super::super::{
    term, Constructor, Declaration, Family, Level, Natural, NestedCase, RecursionCase, Result,
    Term, T,
};
use std::{collections::HashMap, sync::Arc};

const MAX_BYTES: usize = 32 * 1024 * 1024;
const MAX_NODES: usize = 1_000_000;
const MAX_DEPTH: usize = 256;
const MAX_ALLOCATED: usize = 256 * 1024 * 1024;
const MAGIC: &[u8; 4] = b"DCL1";

struct W(Vec<u8>);
impl W {
    fn raw(&mut self, b: &[u8]) -> Result<()> {
        if b.len() > MAX_BYTES.saturating_sub(self.0.len()) {
            return Err("declaration codec byte limit exceeded".into());
        }
        self.0.extend_from_slice(b);
        Ok(())
    }
    fn u8(&mut self, x: u8) -> Result<()> {
        self.raw(&[x])
    }
    fn n(&mut self, x: usize) -> Result<()> {
        let x = u32::try_from(x).map_err(|_| "declaration codec count overflow")?;
        self.raw(&x.to_le_bytes())
    }
    fn s(&mut self, x: &str) -> Result<()> {
        self.n(x.len())?;
        self.raw(x.as_bytes())
    }
    fn ss(&mut self, x: &[String]) -> Result<()> {
        self.n(x.len())?;
        for s in x {
            self.s(s)?
        }
        Ok(())
    }
    fn lev(&mut self, x: &Level) -> Result<()> {
        let p = x.storage_parts();
        self.n(p.len())?;
        for (b, g, o) in p {
            match b {
                None => self.u8(0)?,
                Some(b) => {
                    self.u8(1)?;
                    self.s(&b)?
                }
            }
            self.ss(&g)?;
            self.n(o as usize)?
        }
        Ok(())
    }
    fn levels(&mut self, x: &[Level]) -> Result<()> {
        self.n(x.len())?;
        for l in x {
            self.lev(l)?
        }
        Ok(())
    }
    fn id(&mut self, x: u32) -> Result<()> {
        self.raw(&x.to_le_bytes())
    }
}
struct R<'a> {
    b: &'a [u8],
    p: usize,
    allocated: usize,
}
impl<'a> R<'a> {
    fn charge(&mut self, n: usize) -> Result<()> {
        self.allocated = self
            .allocated
            .checked_add(n)
            .ok_or("declaration allocation limit exceeded")?;
        if self.allocated > MAX_ALLOCATED {
            return Err("declaration allocation limit exceeded".into());
        }
        Ok(())
    }
    fn raw(&mut self, n: usize) -> Result<&'a [u8]> {
        let e = self.p.checked_add(n).ok_or("invalid declaration length")?;
        let x = self.b.get(self.p..e).ok_or("truncated declaration")?;
        self.p = e;
        Ok(x)
    }
    fn u8(&mut self) -> Result<u8> {
        Ok(self.raw(1)?[0])
    }
    fn n(&mut self) -> Result<usize> {
        Ok(u32::from_le_bytes(self.raw(4)?.try_into().unwrap()) as usize)
    }
    fn count(&mut self, min: usize) -> Result<usize> {
        let n = self.n()?;
        if n > MAX_NODES || n > self.b.len().saturating_sub(self.p) / min.max(1) {
            return Err("invalid declaration count".into());
        }
        Ok(n)
    }
    fn s(&mut self) -> Result<String> {
        let n = self.n()?;
        if n > self.b.len().saturating_sub(self.p) {
            return Err("invalid declaration string length".into());
        }
        self.charge(n)?;
        String::from_utf8(self.raw(n)?.to_vec()).map_err(|_| "invalid declaration UTF-8".into())
    }
    fn ss(&mut self) -> Result<Vec<String>> {
        let n = self.count(4)?;
        self.charge(
            n.checked_mul(std::mem::size_of::<String>())
                .ok_or("declaration allocation limit exceeded")?,
        )?;
        let mut x = Vec::with_capacity(n);
        for _ in 0..n {
            x.push(self.s()?)
        }
        Ok(x)
    }
    fn lev(&mut self) -> Result<Level> {
        let n = self.count(9)?;
        self.charge(
            n.checked_mul(std::mem::size_of::<(Option<String>, Vec<String>, u32)>())
                .ok_or("declaration allocation limit exceeded")?,
        )?;
        let mut p = Vec::with_capacity(n);
        for _ in 0..n {
            let b = match self.u8()? {
                0 => None,
                1 => Some(self.s()?),
                _ => return Err("invalid level base tag".into()),
            };
            p.push((
                b,
                self.ss()?,
                u32::try_from(self.n()?).map_err(|_| "invalid level offset")?,
            ))
        }
        let level = Level::from_storage_parts(p)?;
        self.charge(level.storage_memory_weight())?;
        Ok(level)
    }
    fn levels(&mut self) -> Result<Vec<Level>> {
        let n = self.count(4)?;
        self.charge(
            n.checked_mul(std::mem::size_of::<Level>())
                .ok_or("declaration allocation limit exceeded")?,
        )?;
        let mut x = Vec::with_capacity(n);
        for _ in 0..n {
            x.push(self.lev()?)
        }
        Ok(x)
    }
    fn ids(&mut self, nodes: &[T], at: usize) -> Result<Vec<T>> {
        let n = self.count(4)?;
        self.charge(
            n.checked_mul(std::mem::size_of::<T>())
                .ok_or("declaration allocation limit exceeded")?,
        )?;
        let mut x = Vec::with_capacity(n);
        for _ in 0..n {
            let i = self.n()?;
            if i >= at {
                return Err("invalid or forward declaration term reference".into());
            }
            x.push(Arc::clone(&nodes[i]))
        }
        Ok(x)
    }
    fn id(&mut self, nodes: &[T], at: usize) -> Result<T> {
        let i = self.n()?;
        if i >= at {
            return Err("invalid or forward declaration term reference".into());
        }
        Ok(Arc::clone(&nodes[i]))
    }
}
fn kids(t: &Term) -> Vec<T> {
    match t {
        Term::Pi(a, b)
        | Term::Lam(a, b)
        | Term::App(a, b)
        | Term::Sigma(a, b)
        | Term::Refl(a, b) => vec![a.clone(), b.clone()],
        Term::Let(a, b, c)
        | Term::Pair(a, b, c)
        | Term::Eq(a, b, c)
        | Term::QuotMake(_, a, b, c) => vec![a.clone(), b.clone(), c.clone()],
        Term::First(a) | Term::Second(a) => vec![a.clone()],
        Term::Project { subject, .. } => vec![subject.clone()],
        Term::QuotType(_, a, b) => vec![a.clone(), b.clone()],
        Term::QuotLift {
            ty,
            relation,
            target,
            function,
            respect,
            subject,
            ..
        } => vec![
            ty.clone(),
            relation.clone(),
            target.clone(),
            function.clone(),
            respect.clone(),
            subject.clone(),
        ],
        Term::QuotInduct {
            ty,
            relation,
            motive,
            branch,
            subject,
            ..
        } => vec![
            ty.clone(),
            relation.clone(),
            motive.clone(),
            branch.clone(),
            subject.clone(),
        ],
        Term::EqElim {
            ty,
            left,
            motive,
            base,
            right,
            proof,
        } => vec![
            ty.clone(),
            left.clone(),
            motive.clone(),
            base.clone(),
            right.clone(),
            proof.clone(),
        ],
        Term::Ctor {
            parameters, fields, ..
        } => parameters.iter().chain(fields).cloned().collect(),
        Term::Induct {
            parameters,
            indices,
            motive,
            branches,
            subject,
            ..
        } => parameters
            .iter()
            .chain(indices)
            .cloned()
            .chain(std::iter::once(motive.clone()))
            .chain(branches.iter().cloned())
            .chain(std::iter::once(subject.clone()))
            .collect(),
        Term::MutualInduct {
            parameters,
            indices,
            cases,
            subject,
            ..
        } => {
            parameters
                .iter()
                .chain(indices)
                .cloned()
                .chain(cases.iter().flat_map(|c| {
                    std::iter::once(c.motive.clone()).chain(c.branches.iter().cloned())
                }))
                .chain(std::iter::once(subject.clone()))
                .collect()
        }
        Term::NestedInduct {
            parameters,
            indices,
            cases,
            subject,
            ..
        } => parameters
            .iter()
            .chain(indices)
            .cloned()
            .chain(cases.iter().flat_map(|c| {
                [c.selector.clone(), c.motive.clone()]
                    .into_iter()
                    .chain(c.branches.iter().cloned())
            }))
            .chain(std::iter::once(subject.clone()))
            .collect(),
        Term::SelfAt(xs) | Term::Recur(_, xs) => xs.clone(),
        _ => vec![],
    }
}
fn decoded_term_weight(t: &Term) -> usize {
    let mut n = std::mem::size_of::<Term>() + 64 + kids(t).len() * std::mem::size_of::<T>();
    match t {
        Term::Global(s, l) => {
            n += s.capacity() + l.iter().map(Level::storage_memory_weight).sum::<usize>()
        }
        Term::NatLiteral { family, value } => n += family.capacity() + value.decimal().len(),
        Term::Project { family, .. } => n += family.capacity(),
        Term::Sort(l) | Term::QuotType(l, _, _) | Term::QuotMake(l, _, _, _) => {
            n += l.storage_memory_weight()
        }
        Term::QuotLift {
            source_level,
            target_level,
            ..
        } => n += source_level.storage_memory_weight() + target_level.storage_memory_weight(),
        Term::QuotInduct { level, .. } => n += level.storage_memory_weight(),
        Term::Ctor {
            family,
            levels,
            constructor,
            ..
        } => {
            n += family.capacity()
                + constructor.capacity()
                + levels
                    .iter()
                    .map(Level::storage_memory_weight)
                    .sum::<usize>()
        }
        Term::Induct { family, levels, .. }
        | Term::MutualInduct { family, levels, .. }
        | Term::NestedInduct { family, levels, .. } => {
            n += family.capacity()
                + levels
                    .iter()
                    .map(Level::storage_memory_weight)
                    .sum::<usize>()
        }
        Term::Recur(name, ..) => n += name.capacity(),
        _ => (),
    }
    match t {
        Term::MutualInduct { cases, .. } => {
            for c in cases {
                n += c.family.capacity() + c.branches.capacity() * std::mem::size_of::<T>()
            }
        }
        Term::NestedInduct { cases, .. } => {
            for c in cases {
                n += c.branches.capacity() * std::mem::size_of::<T>()
            }
        }
        _ => (),
    }
    n
}
struct Graph {
    records: Vec<Vec<u8>>,
    ids: HashMap<usize, u32>,
    active: HashMap<usize, ()>,
    heights: HashMap<usize, usize>,
    bytes: usize,
}
impl Graph {
    fn visit(&mut self, t: &T, d: usize) -> Result<u32> {
        if d > MAX_DEPTH {
            return Err("declaration term depth limit exceeded".into());
        }
        let p = Arc::as_ptr(t) as usize;
        if let Some(i) = self.ids.get(&p) {
            if d.saturating_add(self.heights[&p] - 1) > MAX_DEPTH {
                return Err("declaration term depth limit exceeded".into());
            }
            return Ok(*i);
        }
        if self.active.insert(p, ()).is_some() {
            return Err("cyclic declaration term graph".into());
        }
        let ch = kids(t);
        let mut ci = Vec::with_capacity(ch.len());
        for x in &ch {
            ci.push(self.visit(x, d + 1)?)
        }
        self.active.remove(&p);
        if self.records.len() >= MAX_NODES {
            return Err("declaration term node limit exceeded".into());
        }
        let mut w = W(vec![]);
        encode_node(&mut w, t, &ci)?;
        self.bytes = self
            .bytes
            .checked_add(w.0.len() + 4)
            .ok_or("declaration codec byte limit exceeded")?;
        if self.bytes > MAX_BYTES {
            return Err("declaration codec byte limit exceeded".into());
        }
        let height = 1 + ch
            .iter()
            .map(|x| self.heights[&(Arc::as_ptr(x) as usize)])
            .max()
            .unwrap_or(0);
        if d.saturating_add(height - 1) > MAX_DEPTH {
            return Err("declaration term depth limit exceeded".into());
        }
        let i = self.records.len() as u32;
        self.records.push(w.0);
        self.ids.insert(p, i);
        self.heights.insert(p, height);
        Ok(i)
    }
}
fn encode_node(w: &mut W, t: &Term, c: &[u32]) -> Result<()> {
    let mut i = 0;
    macro_rules! tag {
        ($x:expr) => {
            w.u8($x)?
        };
    }
    macro_rules! id {
        () => {{
            let x = c[i];
            i += 1;
            w.id(x)?
        }};
    }
    macro_rules! ids {
        ($n:expr) => {{
            let n = $n;
            w.n(n)?;
            for _ in 0..n {
                id!()
            }
        }};
    }
    macro_rules! strv {
        ($x:expr) => {
            w.s($x)?
        };
    }
    match t {
        Term::Sort(x) => {
            tag!(0);
            w.lev(x)?
        }
        Term::Var(x) => {
            tag!(1);
            w.n(*x)?
        }
        Term::Global(x, l) => {
            tag!(2);
            strv!(x);
            w.levels(l)?
        }
        Term::NatLiteral { family, value } => {
            tag!(3);
            strv!(family);
            strv!(&value.decimal())
        }
        Term::Pi(..) => {
            tag!(4);
            id!();
            id!()
        }
        Term::Lam(..) => {
            tag!(5);
            id!();
            id!()
        }
        Term::Let(..) => {
            tag!(6);
            id!();
            id!();
            id!()
        }
        Term::App(..) => {
            tag!(7);
            id!();
            id!()
        }
        Term::Sigma(..) => {
            tag!(8);
            id!();
            id!()
        }
        Term::Pair(..) => {
            tag!(9);
            id!();
            id!();
            id!()
        }
        Term::First(..) => {
            tag!(10);
            id!()
        }
        Term::Second(..) => {
            tag!(11);
            id!()
        }
        Term::Project { family, index, .. } => {
            tag!(12);
            strv!(family);
            w.n(*index)?;
            id!()
        }
        Term::Eq(..) => {
            tag!(13);
            id!();
            id!();
            id!()
        }
        Term::Refl(..) => {
            tag!(14);
            id!();
            id!()
        }
        Term::QuotType(l, ..) => {
            tag!(15);
            w.lev(l)?;
            id!();
            id!()
        }
        Term::QuotMake(l, ..) => {
            tag!(16);
            w.lev(l)?;
            id!();
            id!();
            id!()
        }
        Term::QuotLift {
            source_level,
            target_level,
            ..
        } => {
            tag!(17);
            w.lev(source_level)?;
            w.lev(target_level)?;
            for _ in 0..6 {
                id!()
            }
        }
        Term::QuotInduct { level, .. } => {
            tag!(18);
            w.lev(level)?;
            for _ in 0..5 {
                id!()
            }
        }
        Term::EqElim { .. } => {
            tag!(19);
            for _ in 0..6 {
                id!()
            }
        }
        Term::Ctor {
            family,
            levels,
            parameters,
            constructor,
            fields,
        } => {
            tag!(20);
            strv!(family);
            w.levels(levels)?;
            strv!(constructor);
            ids!(parameters.len());
            ids!(fields.len())
        }
        Term::Induct {
            family,
            levels,
            parameters,
            indices,
            branches,
            ..
        } => {
            tag!(21);
            strv!(family);
            w.levels(levels)?;
            ids!(parameters.len());
            ids!(indices.len());
            id!();
            ids!(branches.len());
            id!()
        }
        Term::MutualInduct {
            family,
            levels,
            parameters,
            indices,
            cases,
            ..
        } => {
            tag!(22);
            strv!(family);
            w.levels(levels)?;
            ids!(parameters.len());
            ids!(indices.len());
            w.n(cases.len())?;
            for x in cases {
                strv!(&x.family);
                id!();
                ids!(x.branches.len())
            }
            id!()
        }
        Term::NestedInduct {
            family,
            levels,
            parameters,
            selected,
            indices,
            cases,
            ..
        } => {
            tag!(23);
            strv!(family);
            w.levels(levels)?;
            w.n(*selected)?;
            ids!(parameters.len());
            ids!(indices.len());
            w.n(cases.len())?;
            for x in cases {
                id!();
                id!();
                ids!(x.branches.len())
            }
            id!()
        }
        Term::SelfType => tag!(24),
        Term::SelfAt(xs) => {
            tag!(25);
            ids!(xs.len())
        }
        Term::Recur(n, xs) => {
            tag!(26);
            strv!(n);
            ids!(xs.len())
        }
    }
    if i != c.len() {
        return Err("declaration child metadata mismatch".into());
    }
    Ok(())
}
pub(super) fn encode(d: &Declaration) -> Result<Vec<u8>> {
    let mut g = Graph {
        records: vec![],
        ids: HashMap::new(),
        active: HashMap::new(),
        heights: HashMap::new(),
        bytes: 8,
    };
    let ty = g.visit(&d.ty, 1)?;
    let value = match &d.value {
        Some(x) => Some(g.visit(x, 1)?),
        None => None,
    };
    let family = if let Some(f) = &d.family {
        let mut cs = Vec::new();
        for c in &f.constructors {
            let fields = c
                .fields
                .iter()
                .map(|x| g.visit(x, 1))
                .collect::<Result<Vec<_>>>()?;
            let indices = c
                .result_indices
                .iter()
                .map(|x| g.visit(x, 1))
                .collect::<Result<Vec<_>>>()?;
            cs.push((c, fields, indices));
        }
        let p = f
            .parameters
            .iter()
            .map(|x| g.visit(x, 1))
            .collect::<Result<Vec<_>>>()?;
        let ix = f
            .indices
            .iter()
            .map(|x| g.visit(x, 1))
            .collect::<Result<Vec<_>>>()?;
        Some((f, p, ix, cs))
    } else {
        None
    };
    let mut w = W(vec![]);
    w.raw(MAGIC)?;
    w.n(g.records.len())?;
    for r in &g.records {
        w.n(r.len())?;
        w.raw(r)?
    }
    w.ss(&d.universes)?;
    w.id(ty)?;
    match value {
        None => w.u8(0)?,
        Some(i) => {
            w.u8(1)?;
            w.id(i)?
        }
    }
    match family {
        None => w.u8(0)?,
        Some((f, p, ix, cs)) => {
            w.u8(1)?;
            w.ss(&f.group)?;
            w.lev(&f.sort)?;
            w.u8(u8::from(f.large))?;
            w.n(p.len())?;
            for i in p {
                w.id(i)?
            }
            w.n(ix.len())?;
            for i in ix {
                w.id(i)?
            }
            w.n(cs.len())?;
            for (c, fields, indices) in cs {
                w.s(&c.name)?;
                w.n(fields.len())?;
                for i in fields {
                    w.id(i)?
                }
                w.n(c.recursive.len())?;
                for r in &c.recursive {
                    match r {
                        None => w.u8(0)?,
                        Some(s) => {
                            w.u8(1)?;
                            w.s(s)?
                        }
                    }
                }
                w.n(indices.len())?;
                for i in indices {
                    w.id(i)?
                }
            }
        }
    }
    Ok(w.0)
}

/// Conservative owned-memory estimate, bounded independently at 256 MiB.
pub(super) fn weight(d: &Declaration) -> Result<usize> {
    fn add(n: &mut usize, x: usize) -> Result<()> {
        *n = n.checked_add(x).ok_or("declaration weight overflow")?;
        if *n > MAX_ALLOCATED {
            return Err("declaration weight limit exceeded".into());
        }
        Ok(())
    }
    fn walk(
        t: &T,
        depth: usize,
        seen: &mut HashMap<usize, ()>,
        active: &mut HashMap<usize, ()>,
        n: &mut usize,
        count: &mut usize,
        heights: &mut HashMap<usize, usize>,
    ) -> Result<()> {
        if depth > MAX_DEPTH {
            return Err("declaration term depth limit exceeded".into());
        }
        let p = Arc::as_ptr(t) as usize;
        if seen.contains_key(&p) {
            if depth.saturating_add(heights[&p] - 1) > MAX_DEPTH {
                return Err("declaration term depth limit exceeded".into());
            }
            return Ok(());
        }
        if active.insert(p, ()).is_some() {
            return Err("cyclic declaration term graph".into());
        }
        *count += 1;
        if *count > MAX_NODES {
            return Err("declaration term node limit exceeded".into());
        }
        add(n, std::mem::size_of::<Term>() + 64)?;
        let payload = match &**t {
            Term::Global(s, l) => {
                s.capacity()
                    + l.capacity() * std::mem::size_of::<Level>()
                    + l.iter().map(Level::storage_memory_weight).sum::<usize>()
            }
            Term::NatLiteral { family, value } => family.capacity() + value.decimal().len(),
            Term::Project { family, .. } => family.capacity(),
            Term::Ctor {
                family,
                levels,
                constructor,
                parameters,
                fields,
            } => {
                family.capacity()
                    + constructor.capacity()
                    + levels.capacity() * std::mem::size_of::<Level>()
                    + levels
                        .iter()
                        .map(Level::storage_memory_weight)
                        .sum::<usize>()
                    + (parameters.capacity() + fields.capacity()) * std::mem::size_of::<T>()
            }
            Term::Induct {
                family,
                levels,
                parameters,
                indices,
                branches,
                ..
            } => {
                family.capacity()
                    + levels.capacity() * std::mem::size_of::<Level>()
                    + levels
                        .iter()
                        .map(Level::storage_memory_weight)
                        .sum::<usize>()
                    + (parameters.capacity() + indices.capacity() + branches.capacity())
                        * std::mem::size_of::<T>()
            }
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                ..
            } => {
                family.capacity()
                    + levels.capacity() * std::mem::size_of::<Level>()
                    + levels
                        .iter()
                        .map(Level::storage_memory_weight)
                        .sum::<usize>()
                    + (parameters.capacity() + indices.capacity()) * std::mem::size_of::<T>()
                    + cases.capacity() * std::mem::size_of::<RecursionCase>()
                    + cases
                        .iter()
                        .map(|c| {
                            c.family.capacity() + c.branches.capacity() * std::mem::size_of::<T>()
                        })
                        .sum::<usize>()
            }
            Term::NestedInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                ..
            } => {
                family.capacity()
                    + levels.capacity() * std::mem::size_of::<Level>()
                    + levels
                        .iter()
                        .map(Level::storage_memory_weight)
                        .sum::<usize>()
                    + (parameters.capacity() + indices.capacity()) * std::mem::size_of::<T>()
                    + cases.capacity() * std::mem::size_of::<NestedCase>()
                    + cases
                        .iter()
                        .map(|c| c.branches.capacity() * std::mem::size_of::<T>())
                        .sum::<usize>()
            }
            Term::Recur(s, x) => s.capacity() + x.capacity() * std::mem::size_of::<T>(),
            Term::SelfAt(x) => x.capacity() * std::mem::size_of::<T>(),
            Term::Sort(l) | Term::QuotType(l, _, _) | Term::QuotMake(l, _, _, _) => {
                l.storage_memory_weight()
            }

            Term::QuotLift {
                source_level,
                target_level,
                ..
            } => source_level.storage_memory_weight() + target_level.storage_memory_weight(),
            Term::QuotInduct { level, .. } => level.storage_memory_weight(),
            _ => 0,
        };
        add(n, payload)?;
        for c in kids(t) {
            walk(&c, depth + 1, seen, active, n, count, heights)?
        }
        active.remove(&p);
        seen.insert(p, ());
        heights.insert(
            p,
            1 + kids(t)
                .iter()
                .map(|c| heights[&(Arc::as_ptr(c) as usize)])
                .max()
                .unwrap_or(0),
        );
        Ok(())
    }
    let mut n = std::mem::size_of::<Declaration>() + 64;
    let mut count = 0;
    let (mut seen, mut active, mut heights) = (HashMap::new(), HashMap::new(), HashMap::new());
    walk(
        &d.ty,
        1,
        &mut seen,
        &mut active,
        &mut n,
        &mut count,
        &mut heights,
    )?;
    if let Some(t) = &d.value {
        walk(
            t,
            1,
            &mut seen,
            &mut active,
            &mut n,
            &mut count,
            &mut heights,
        )?
    }
    add(
        &mut n,
        d.universes.capacity() * std::mem::size_of::<String>()
            + d.universes.iter().map(String::capacity).sum::<usize>(),
    )?;
    if let Some(f) = &d.family {
        add(
            &mut n,
            f.group.capacity() * std::mem::size_of::<String>()
                + f.group.iter().map(String::capacity).sum::<usize>()
                + f.sort.storage_memory_weight()
                + f.constructors.capacity() * std::mem::size_of::<Constructor>()
                + f.parameters.capacity() * std::mem::size_of::<T>()
                + f.indices.capacity() * std::mem::size_of::<T>(),
        )?;
        for t in f.parameters.iter().chain(&f.indices) {
            walk(
                t,
                1,
                &mut seen,
                &mut active,
                &mut n,
                &mut count,
                &mut heights,
            )?
        }
        for c in &f.constructors {
            add(
                &mut n,
                c.name.capacity()
                    + c.recursive.capacity() * std::mem::size_of::<Option<String>>()
                    + c.recursive
                        .iter()
                        .map(|x| x.as_ref().map_or(0, String::capacity))
                        .sum::<usize>()
                    + c.fields.capacity() * std::mem::size_of::<T>()
                    + c.result_indices.capacity() * std::mem::size_of::<T>(),
            )?;
            for t in c.fields.iter().chain(&c.result_indices) {
                walk(
                    t,
                    1,
                    &mut seen,
                    &mut active,
                    &mut n,
                    &mut count,
                    &mut heights,
                )?
            }
        }
    }
    Ok(n)
}

pub(super) fn decode(bytes: &[u8]) -> Result<Declaration> {
    if bytes.len() > MAX_BYTES {
        return Err("declaration codec byte limit exceeded".into());
    }
    let mut r = R {
        b: bytes,
        p: 0,
        allocated: 0,
    };
    if r.raw(4)? != MAGIC {
        return Err("invalid declaration codec magic".into());
    }
    let n = r.count(5)?;
    r.charge(
        n.checked_mul(std::mem::size_of::<T>() + std::mem::size_of::<(usize, usize)>())
            .ok_or("declaration allocation limit exceeded")?,
    )?;
    let mut nodes: Vec<T> = Vec::with_capacity(n);
    let mut depths: HashMap<usize, usize> = HashMap::with_capacity(n);
    for at in 0..n {
        let len = r.n()?;
        if len > r.b.len().saturating_sub(r.p) {
            return Err("invalid declaration node length".into());
        }
        let end = r.p + len;
        let tag = r.u8()?;
        macro_rules! one {
            () => {
                r.id(&nodes, at)?
            };
        }
        macro_rules! many {
            () => {
                r.ids(&nodes, at)?
            };
        }
        let t = match tag {
            0 => Term::Sort(r.lev()?),
            1 => Term::Var(r.n()?),
            2 => Term::Global(r.s()?, r.levels()?),
            3 => Term::NatLiteral {
                family: r.s()?,
                value: Natural::parse(&r.s()?)?,
            },
            4 => Term::Pi(one!(), one!()),
            5 => Term::Lam(one!(), one!()),
            6 => Term::Let(one!(), one!(), one!()),
            7 => Term::App(one!(), one!()),
            8 => Term::Sigma(one!(), one!()),
            9 => Term::Pair(one!(), one!(), one!()),
            10 => Term::First(one!()),
            11 => Term::Second(one!()),
            12 => Term::Project {
                family: r.s()?,
                index: r.n()?,
                subject: one!(),
            },
            13 => Term::Eq(one!(), one!(), one!()),
            14 => Term::Refl(one!(), one!()),
            15 => Term::QuotType(r.lev()?, one!(), one!()),
            16 => Term::QuotMake(r.lev()?, one!(), one!(), one!()),
            17 => {
                let a = r.lev()?;
                let b = r.lev()?;
                Term::QuotLift {
                    source_level: a,
                    target_level: b,
                    ty: one!(),
                    relation: one!(),
                    target: one!(),
                    function: one!(),
                    respect: one!(),
                    subject: one!(),
                }
            }
            18 => Term::QuotInduct {
                level: r.lev()?,
                ty: one!(),
                relation: one!(),
                motive: one!(),
                branch: one!(),
                subject: one!(),
            },
            19 => Term::EqElim {
                ty: one!(),
                left: one!(),
                motive: one!(),
                base: one!(),
                right: one!(),
                proof: one!(),
            },
            20 => {
                let family = r.s()?;
                let levels = r.levels()?;
                let constructor = r.s()?;
                let parameters = many!();
                let fields = many!();
                Term::Ctor {
                    family,
                    levels,
                    parameters,
                    constructor,
                    fields,
                }
            }
            21 => {
                let family = r.s()?;
                let levels = r.levels()?;
                let parameters = many!();
                let indices = many!();
                let motive = one!();
                let branches = many!();
                let subject = one!();
                Term::Induct {
                    family,
                    levels,
                    parameters,
                    indices,
                    motive,
                    branches,
                    subject,
                }
            }
            22 => {
                let family = r.s()?;
                let levels = r.levels()?;
                let parameters = many!();
                let indices = many!();
                let n = r.count(12)?;
                r.charge(
                    n.checked_mul(std::mem::size_of::<RecursionCase>())
                        .ok_or("declaration allocation limit exceeded")?,
                )?;
                let mut cases = Vec::with_capacity(n);
                for _ in 0..n {
                    cases.push(RecursionCase {
                        family: r.s()?,
                        motive: one!(),
                        branches: many!(),
                    })
                }
                let subject = one!();
                Term::MutualInduct {
                    family,
                    levels,
                    parameters,
                    indices,
                    cases,
                    subject,
                }
            }
            23 => {
                let family = r.s()?;
                let levels = r.levels()?;
                let selected = r.n()?;
                let parameters = many!();
                let indices = many!();
                let n = r.count(12)?;
                r.charge(
                    n.checked_mul(std::mem::size_of::<NestedCase>())
                        .ok_or("declaration allocation limit exceeded")?,
                )?;
                let mut cases = Vec::with_capacity(n);
                for _ in 0..n {
                    cases.push(NestedCase {
                        selector: one!(),
                        motive: one!(),
                        branches: many!(),
                    })
                }
                let subject = one!();
                Term::NestedInduct {
                    family,
                    levels,
                    parameters,
                    selected,
                    indices,
                    cases,
                    subject,
                }
            }
            24 => Term::SelfType,
            25 => Term::SelfAt(many!()),
            26 => Term::Recur(r.s()?, many!()),
            _ => return Err("invalid declaration term tag".into()),
        };
        if r.p != end {
            return Err("invalid declaration node payload".into());
        }
        let node = term(t);
        r.charge(decoded_term_weight(&node))?;
        let depth = kids(&node)
            .iter()
            .filter_map(|child| depths.get(&(Arc::as_ptr(child) as usize)).map(|d| d + 1))
            .max()
            .unwrap_or(1);
        if depth > MAX_DEPTH {
            return Err("declaration term depth limit exceeded".into());
        }
        depths.insert(Arc::as_ptr(&node) as usize, depth);
        nodes.push(node);
    }
    let universes = r.ss()?;
    let ty = r.id(&nodes, n)?;
    let value = match r.u8()? {
        0 => None,
        1 => Some(r.id(&nodes, n)?),
        _ => return Err("invalid declaration value tag".into()),
    };
    let family = match r.u8()? {
        0 => None,
        1 => {
            let group = r.ss()?;
            let sort = r.lev()?;
            let large = match r.u8()? {
                0 => false,
                1 => true,
                _ => return Err("invalid family flag".into()),
            };
            let getterms = |r: &mut R<'_>| -> Result<Vec<T>> {
                let n = r.count(4)?;
                r.charge(
                    n.checked_mul(std::mem::size_of::<T>())
                        .ok_or("declaration allocation limit exceeded")?,
                )?;
                let mut v = Vec::with_capacity(n);
                for _ in 0..n {
                    v.push(r.id(&nodes, nodes.len())?)
                }
                Ok(v)
            };
            let parameters = getterms(&mut r)?;
            let indices = getterms(&mut r)?;
            let n = r.count(12)?;
            r.charge(
                n.checked_mul(std::mem::size_of::<Constructor>())
                    .ok_or("declaration allocation limit exceeded")?,
            )?;
            let mut constructors = Vec::with_capacity(n);
            for _ in 0..n {
                let name = r.s()?;
                let fields = getterms(&mut r)?;
                let nr = r.count(1)?;
                r.charge(
                    nr.checked_mul(std::mem::size_of::<Option<String>>())
                        .ok_or("declaration allocation limit exceeded")?,
                )?;
                let mut recursive = Vec::with_capacity(nr);
                for _ in 0..nr {
                    recursive.push(match r.u8()? {
                        0 => None,
                        1 => Some(r.s()?),
                        _ => return Err("invalid recursive target tag".into()),
                    })
                }
                let result_indices = getterms(&mut r)?;
                if recursive.len() != fields.len() {
                    return Err("constructor recursive metadata length mismatch".into());
                }
                constructors.push(Constructor {
                    name,
                    fields,
                    recursive,
                    result_indices,
                })
            }
            Some(Family {
                group,
                parameters,
                indices,
                sort,
                constructors,
                large,
            })
        }
        _ => return Err("invalid declaration family tag".into()),
    };
    if r.p != bytes.len() {
        return Err("trailing declaration bytes".into());
    }
    Ok(Declaration {
        universes,
        ty,
        value,
        family,
    })
}

#[cfg(test)]
#[path = "declaration_codec_tests.rs"]
mod tests;
