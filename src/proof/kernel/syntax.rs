//! Bounded structural equality for kernel syntax.
use super::*;
use std::collections::HashSet;

impl Kernel {
    pub(super) fn same_syntax(&mut self, left: &T, right: &T) -> Result<bool> {
        self.charge_transformation(32)?;
        let mut pending = vec![(left.clone(), right.clone())];
        let mut visited = HashSet::new();

        while let Some((left, right)) = pending.pop() {
            // Terms are immutable. An identical subtree is structurally equal
            // without inspecting its descendants or allocating a visited row.
            // This is syntax comparison only; source scope and type checking
            // remain separate, including for erased or otherwise unused terms.
            if Arc::ptr_eq(&left, &right) {
                self.tick(0)?;
                self.charge_transformation(0)?;
                continue;
            }
            let key = (Arc::as_ptr(&left) as usize, Arc::as_ptr(&right) as usize);
            if visited.contains(&key) {
                continue;
            }
            self.tick(0)?;
            // Cover the hash table entry and growth before allocating it.
            self.charge_transformation(64)?;
            visited.insert(key);

            macro_rules! child {
                ($a:expr, $b:expr) => {{
                    self.charge_transformation(32)?;
                    pending.push(($a.clone(), $b.clone()))
                }};
            }
            macro_rules! children {
                ($a:expr, $b:expr) => {{
                    if $a.len() != $b.len() {
                        return Ok(false);
                    }
                    self.charge_transformation(
                        $a.len()
                            .checked_mul(32)
                            .ok_or("kernel allocation limit exceeded")?,
                    )?;
                    pending.extend($a.iter().zip($b).map(|(a, b)| (a.clone(), b.clone())));
                }};
            }

            match (left.as_ref(), right.as_ref()) {
                (
                    Term::NatLiteral {
                        family: a,
                        value: x,
                    },
                    Term::NatLiteral {
                        family: b,
                        value: y,
                    },
                ) if a == b && x == y => {}
                (Term::QuotType(u, a, r), Term::QuotType(v, b, s)) if u == v => {
                    child!(a, b);
                    child!(r, s);
                }
                (Term::QuotMake(u, a, r, x), Term::QuotMake(v, b, s, y)) if u == v => {
                    child!(a, b);
                    child!(r, s);
                    child!(x, y);
                }
                (
                    Term::QuotLift {
                        source_level: u,
                        target_level: v,
                        ty: a,
                        relation: r,
                        target: b,
                        function: f,
                        respect: h,
                        subject: q,
                    },
                    Term::QuotLift {
                        source_level: w,
                        target_level: z,
                        ty: c,
                        relation: s,
                        target: d,
                        function: g,
                        respect: i,
                        subject: p,
                    },
                ) if u == w && v == z => {
                    for (a, b) in [a, r, b, f, h, q].into_iter().zip([c, s, d, g, i, p]) {
                        child!(a, b);
                    }
                }
                (
                    Term::QuotInduct {
                        level: u,
                        ty: a,
                        relation: r,
                        motive: m,
                        branch: b,
                        subject: q,
                    },
                    Term::QuotInduct {
                        level: v,
                        ty: c,
                        relation: s,
                        motive: n,
                        branch: d,
                        subject: p,
                    },
                ) if u == v => {
                    for (a, b) in [a, r, m, b, q].into_iter().zip([c, s, n, d, p]) {
                        child!(a, b);
                    }
                }
                (Term::Sort(a), Term::Sort(b)) if a == b => {}
                (Term::Var(a), Term::Var(b)) if a == b => {}
                (Term::Global(a, al), Term::Global(b, bl)) if a == b && al == bl => {}
                (Term::Pi(a1, a2), Term::Pi(b1, b2))
                | (Term::Lam(a1, a2), Term::Lam(b1, b2))
                | (Term::App(a1, a2), Term::App(b1, b2))
                | (Term::Sigma(a1, a2), Term::Sigma(b1, b2)) => {
                    child!(a1, b1);
                    child!(a2, b2);
                }
                (Term::Let(a1, a2, a3), Term::Let(b1, b2, b3))
                | (Term::Pair(a1, a2, a3), Term::Pair(b1, b2, b3))
                | (Term::Eq(a1, a2, a3), Term::Eq(b1, b2, b3)) => {
                    child!(a1, b1);
                    child!(a2, b2);
                    child!(a3, b3);
                }
                (Term::Refl(a1, a2), Term::Refl(b1, b2)) => {
                    child!(a1, b1);
                    child!(a2, b2);
                }
                (Term::First(a), Term::First(b)) | (Term::Second(a), Term::Second(b)) => {
                    child!(a, b)
                }
                (
                    Term::Project {
                        family: af,
                        index: ai,
                        subject: a,
                    },
                    Term::Project {
                        family: bf,
                        index: bi,
                        subject: b,
                    },
                ) if af == bf && ai == bi => child!(a, b),
                (
                    Term::EqElim {
                        ty: at,
                        left: al,
                        motive: am,
                        base: ab,
                        right: ar,
                        proof: ap,
                    },
                    Term::EqElim {
                        ty: bt,
                        left: bl,
                        motive: bm,
                        base: bb,
                        right: br,
                        proof: bp,
                    },
                ) => {
                    child!(at, bt);
                    child!(al, bl);
                    child!(am, bm);
                    child!(ab, bb);
                    child!(ar, br);
                    child!(ap, bp);
                }
                (
                    Term::Ctor {
                        family: af,
                        levels: au,
                        parameters: ap,
                        constructor: ac,
                        fields: ax,
                    },
                    Term::Ctor {
                        family: bf,
                        levels: bu,
                        parameters: bp,
                        constructor: bc,
                        fields: bx,
                    },
                ) if af == bf && au == bu && ac == bc => {
                    children!(ap, bp);
                    children!(ax, bx);
                }
                (
                    Term::Induct {
                        family: af,
                        levels: au,
                        parameters: ap,
                        indices: ai,
                        motive: am,
                        branches: ab,
                        subject: asu,
                    },
                    Term::Induct {
                        family: bf,
                        levels: bu,
                        parameters: bp,
                        indices: bi,
                        motive: bm,
                        branches: bb,
                        subject: bsu,
                    },
                ) if af == bf && au == bu => {
                    children!(ap, bp);
                    children!(ai, bi);
                    child!(am, bm);
                    children!(ab, bb);
                    child!(asu, bsu);
                }
                (
                    Term::MutualInduct {
                        family: af,
                        levels: au,
                        parameters: ap,
                        indices: ai,
                        cases: ac,
                        subject: asu,
                    },
                    Term::MutualInduct {
                        family: bf,
                        levels: bu,
                        parameters: bp,
                        indices: bi,
                        cases: bc,
                        subject: bsu,
                    },
                ) if af == bf && au == bu => {
                    children!(ap, bp);
                    children!(ai, bi);
                    if ac.len() != bc.len() {
                        return Ok(false);
                    }
                    for (a, b) in ac.iter().zip(bc) {
                        if a.family != b.family {
                            return Ok(false);
                        }
                        child!(&a.motive, &b.motive);
                        children!(&a.branches, &b.branches);
                    }
                    child!(asu, bsu);
                }
                (
                    Term::NestedInduct {
                        family: af,
                        levels: au,
                        parameters: ap,
                        selected: ase,
                        indices: ai,
                        cases: ac,
                        subject: asu,
                    },
                    Term::NestedInduct {
                        family: bf,
                        levels: bu,
                        parameters: bp,
                        selected: bse,
                        indices: bi,
                        cases: bc,
                        subject: bsu,
                    },
                ) if af == bf && au == bu && ase == bse => {
                    children!(ap, bp);
                    children!(ai, bi);
                    if ac.len() != bc.len() {
                        return Ok(false);
                    }
                    for (a, b) in ac.iter().zip(bc) {
                        child!(&a.selector, &b.selector);
                        child!(&a.motive, &b.motive);
                        children!(&a.branches, &b.branches);
                    }
                    child!(asu, bsu);
                }
                (Term::SelfType, Term::SelfType) => {}
                (Term::SelfAt(a), Term::SelfAt(b)) => children!(a, b),
                (Term::Recur(an, a), Term::Recur(bn, b)) if an == bn => children!(a, b),
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
#[path = "syntax_shared_tests.rs"]
mod shared_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn compare(a: T, b: T) -> Result<bool> {
        Kernel::new().same_syntax(&a, &b)
    }

    #[test]
    fn distinguishes_atoms_levels_and_shapes() {
        assert!(!compare(
            term(Term::Global("a".into(), vec![])),
            term(Term::Global("b".into(), vec![]))
        )
        .unwrap());
        assert!(!compare(
            term(Term::Sort(Level::number(0).unwrap())),
            term(Term::Sort(Level::number(1).unwrap()))
        )
        .unwrap());
        assert!(!compare(term(Term::Var(0)), term(Term::Var(1))).unwrap());
        assert!(!compare(
            term(Term::First(term(Term::Var(0)))),
            term(Term::Second(term(Term::Var(0))))
        )
        .unwrap());
        assert!(!compare(term(Term::SelfType), term(Term::SelfAt(vec![]))).unwrap());
    }

    #[test]
    fn shared_and_unshared_trees_compare_structurally() {
        fn unshared(depth: usize) -> T {
            if depth == 0 {
                return term(Term::Var(7));
            }
            term(Term::App(unshared(depth - 1), unshared(depth - 1)))
        }
        let mut shared = term(Term::Var(7));
        for _ in 0..10 {
            shared = term(Term::App(shared.clone(), shared.clone()));
        }
        assert!(compare(shared, unshared(10)).unwrap());
    }

    #[test]
    fn shared_dag_is_visited_once_per_pointer_pair() {
        let mut dag = term(Term::Var(3));
        let mut other = term(Term::Var(3));
        for _ in 0..80 {
            dag = term(Term::App(dag.clone(), dag.clone()));
            other = term(Term::App(other.clone(), other.clone()));
        }
        let mut kernel = Kernel::new();
        assert!(kernel.same_syntax(&dag, &other).unwrap());
        assert_eq!(kernel.work, 81);
        kernel.reset_budget();
        assert!(kernel.same_syntax(&dag, &dag).unwrap());
        assert_eq!(kernel.work, 1);
    }

    #[test]
    fn structural_comparison_accounts_for_its_pending_and_visited_storage() {
        let value = term(Term::Var(0));
        let other = term(Term::Var(0));
        let mut kernel = Kernel::new();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 95;
        assert!(kernel
            .same_syntax(&value, &other)
            .unwrap_err()
            .contains("allocation limit"));
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 96;
        assert!(kernel.same_syntax(&value, &other).unwrap());
        assert_eq!(kernel.transformed_bytes, 64 * 1024 * 1024);
        kernel.reset_budget();
        kernel.work = WORK;
        assert!(kernel
            .same_syntax(&value, &value)
            .unwrap_err()
            .contains("resource limit"));
    }
}
