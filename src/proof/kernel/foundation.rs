//! The fixed logical basis, named explicitly at every source use.
//! These are axioms, not proved lemmas or a general declaration/admit interface.
use super::*;

type Signature = fn() -> T;
// The readable formulas are an independent test specification. Production
// installs only the directly constructed kernel syntax, never parsed postulates.
const FOUNDATIONS: &[(&str, &str, &[&str], &str, Signature)] = &[
    (
        "#pt-foundation-propext",
        "propext",
        &[],
        r#"
      (#pt-pi ((P #pt-prop) (Q #pt-prop)
        (forward (#pt-pi ((p P)) Q)) (backward (#pt-pi ((q Q)) P)))
        (#pt-eq #pt-prop P Q))"#,
        propext_signature,
    ),
    (
        "#pt-foundation-choice",
        "Classical.choice",
        &["u"],
        r#"
      (#pt-pi ((A (#pt-sort u))
        (inhabited (#pt-pi ((P #pt-prop) (consume (#pt-pi ((value A)) P))) P))) A)"#,
        choice_signature,
    ),
    (
        "#pt-foundation-quot-sound",
        "Quot.sound",
        &["u"],
        r#"
      (#pt-pi ((A (#pt-sort u))
        (relation (#pt-pi ((x A) (y A)) #pt-prop))
        (left A) (right A) (related (#pt-app relation left right)))
        (#pt-eq (#pt-quot u A relation)
          (#pt-quot-make u A relation left) (#pt-quot-make u A relation right)))"#,
        quotient_signature,
    ),
];

fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn prop() -> T {
    term(Term::Sort(Level::number(0).expect("Prop level")))
}
fn pi(domain: T, range: T) -> T {
    term(Term::Pi(domain, range))
}

fn propext_signature() -> T {
    // Context of the result: P, Q, forward, backward.
    pis(
        &[prop(), prop(), pi(var(1), var(1)), pi(var(1), var(3))],
        term(Term::Eq(prop(), var(3), var(2))),
    )
}

fn choice_signature() -> T {
    let universe = term(Term::Sort(Level::variable("u".into())));
    // Under A: forall P:Prop, (A -> P) -> P.
    let nonempty = pi(prop(), pi(pi(var(1), var(1)), var(1)));
    pis(&[universe, nonempty], var(1))
}

fn quotient_signature() -> T {
    let level = Level::variable("u".into());
    let universe = term(Term::Sort(level.clone()));
    let relation = pi(var(0), pi(var(1), prop()));
    let related = apps(var(2), &[var(1), var(0)]);
    // Context of the result: A, relation, left, right, related.
    let quotient = term(Term::QuotType(level.clone(), var(4), var(3)));
    let make = |value| term(Term::QuotMake(level.clone(), var(4), var(3), value));
    pis(
        &[universe, relation, var(1), var(2), related],
        term(Term::Eq(quotient, make(var(2)), make(var(1)))),
    )
}

pub(in crate::proof::kernel) fn label(name: &str) -> Option<&'static str> {
    FOUNDATIONS
        .iter()
        .find(|entry| entry.0 == name)
        .map(|entry| entry.1)
}

impl Kernel {
    /// Only compiler-owned fixed signatures enter here. An input cannot provide
    /// a proposition, body, name or signature to install as an axiom.
    pub(super) fn ensure_logical_foundation(
        &mut self,
        requested: &str,
        depth: usize,
    ) -> Result<()> {
        if !requested.starts_with("#pt-foundation-") {
            return Ok(());
        }
        if self.declarations.contains_key(requested)? {
            return Ok(());
        }
        if let Some((name, _, universes, _, signature)) =
            FOUNDATIONS.iter().find(|entry| entry.0 == requested)
        {
            let ty = signature();
            let universes = universes
                .iter()
                .map(|u| (*u).to_owned())
                .collect::<Vec<_>>();
            self.scope(&universes, &[ty.clone()])?;
            self.sort(&[], &ty, depth + 1)?;
            self.declarations.insert(
                (*name).into(),
                Declaration {
                    universes,
                    ty,
                    value: None,
                    family: None,
                },
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fixed_foundations_are_typed_opaque_and_have_exact_universe_arities() {
        let mut kernel = Kernel::new();
        assert!(FOUNDATIONS
            .iter()
            .all(|(name, ..)| !kernel.declarations.contains_key(*name).unwrap()));
        for (name, label, universes, source, _) in FOUNDATIONS {
            assert_eq!(super::label(name), Some(*label));
            kernel.ensure_logical_foundation(name, 0).unwrap();
            let declaration = kernel.declarations.get(*name).unwrap().unwrap().clone();
            assert_eq!(declaration.universes.len(), universes.len());
            assert!(declaration.value.is_none());
            assert!(declaration.family.is_none());
            kernel.reset_budget();
            kernel.sort(&[], &declaration.ty, 0).unwrap();
            let parsed = crate::proof::kernel::parse_closed_template(source, universes).unwrap();
            kernel.reset_budget();
            assert!(
                kernel.same_syntax(&declaration.ty, &parsed).unwrap(),
                "{name}"
            );
        }
        assert_eq!(super::label("#pt-foundation-admit"), None);
        assert_eq!(super::label("Classical.choice"), None);
    }

    #[test]
    fn lazy_foundations_cannot_be_rebound_or_reset_the_work_budget() {
        let mut kernel = Kernel::new();
        assert!(kernel
            .definition(
                "#pt-foundation-choice",
                vec![],
                term(Term::Sort(Level::number(1).unwrap())),
                term(Term::Global("#pt-nat".into(), vec![])),
                false
            )
            .is_err());
        kernel.reset_budget();
        kernel.work = WORK - 1;
        assert!(kernel
            .ensure_logical_foundation("#pt-foundation-choice", 0)
            .unwrap_err()
            .contains("resource limit"));
        assert!(kernel.work >= WORK);
        assert!(!kernel
            .declarations
            .contains_key("#pt-foundation-choice")
            .unwrap());
    }
}
