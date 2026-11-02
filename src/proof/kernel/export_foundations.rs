//! Opt-in pinned axiom declarations get checked opaque native initializers.
//! No input supplies an axiom schema, proof bypass, or kernel reduction rule.
use super::*;
use quotient::standard;

impl Replay {
    pub(super) fn axiom_record(&mut self, body: &Json) -> Result<()> {
        if self.foundation_policy != LeanFoundationPolicy::Lean4 {
            return Err("export axioms are not authorized; no theorem was established".into());
        }
        let data = fields(body, &["name", "levelParams", "type", "isUnsafe"])?;
        if boolean(&data["isUnsafe"])? {
            return Err("unsafe axiom records are forbidden".into());
        }
        let name = self.name(&data["name"])?;
        let kind = if name.key == standard(&["Classical", "choice"]) {
            "choice"
        } else if name.key == standard(&["propext"]) {
            "propext"
        } else if name.key == standard(&["Quot", "sound"]) {
            "quot-sound"
        } else {
            return Err("only the three pinned Lean logical axioms are authorized".into());
        };
        let universes = self.universes(&data["levelParams"])?;
        if universes.len() != usize::from(kind != "propext") {
            return Err("axiom universe parameter count mismatch".into());
        }
        match kind {
            "choice" => self.check_nonempty()?,
            "propext" => {
                self.check_quotient_equality()?;
                self.check_iff()?;
            }
            _ => {
                if self.quotient_stage != 4 {
                    return Err("Quot.sound requires the complete checked Quot package".into());
                }
                self.check_quotient_equality()?;
            }
        }
        let (expected, value) = self.axiom_schema(kind, &universes)?;
        let ty = self.expression(&data["type"])?;
        let dependencies = dependencies(&[ty.clone(), value.clone()])?;
        self.dependencies_known(&dependencies, &[])?;
        self.room(1)?;
        self.reset_budget()?;
        self.kernel
            .scope(&universes, &[ty.clone(), expected.clone(), value.clone()])?;
        // Check the supplied signature before conversion can erase anything.
        self.kernel.sort(&[], &ty, 0)?;
        if !self.kernel.convertible(&[], &ty, &expected, 0)? {
            return Err("exported axiom signature differs from the fixed checked schema".into());
        }
        self.reset_budget()?;
        self.kernel
            .opaque_definition(&name.key, universes, ty, value.clone())?;
        if self.retain_bodies {
            self.bodies.insert(name.key.clone(), value);
        }
        self.remember(&name, "axiom", dependencies)
    }

    fn axiom_template(&self, source: &str, universes: &[String]) -> Result<T> {
        let parsed = crate::proof::kernel::parse_closed_template(source, &["u"])?;
        let names = [
            ("eq", &["Eq"][..]),
            ("refl", &["Eq", "refl"][..]),
            ("iff", &["Iff"][..]),
            ("iff-intro", &["Iff", "intro"][..]),
            ("nonempty", &["Nonempty"][..]),
            ("nonempty-intro", &["Nonempty", "intro"][..]),
            ("quot", &["Quot"][..]),
            ("make", &["Quot", "mk"][..]),
        ]
        .into_iter()
        .map(|(name, parts)| (name.into(), standard(parts)))
        .collect();
        let levels = ["u"]
            .into_iter()
            .zip(universes)
            .map(|(name, level)| (name.into(), Level::variable(level.clone())))
            .collect();
        source::correspondence::relocate_template(&parsed, &names, &levels)
    }

    fn compare_standard_type(&mut self, name: &str, signature: &str) -> Result<()> {
        let declaration = self
            .kernel
            .declarations
            .get(name)?
            .ok_or("missing checked logical datatype declaration")?;
        let expected = self.axiom_template(signature, &declaration.universes)?;
        self.reset_budget()?;
        self.kernel
            .scope(&declaration.universes, &[expected.clone()])?;
        self.kernel.sort(&[], &expected, 0)?;
        if !self
            .kernel
            .convertible(&[], &declaration.ty, &expected, 0)?
        {
            return Err("logical datatype signature differs from the fixed checked schema".into());
        }
        Ok(())
    }

    fn check_nonempty(&mut self) -> Result<()> {
        let name = standard(&["Nonempty"]);
        let intro = standard(&["Nonempty", "intro"]);
        let declaration = self
            .kernel
            .declarations
            .get(&name)?
            .ok_or("choice requires the checked standard Nonempty family")?;
        let family = declaration
            .family
            .as_ref()
            .ok_or("Nonempty must be inductive")?;
        if !self.checked.contains_key(&name)
            || !self.checked.contains_key(&intro)
            || declaration.universes.len() != 1
            || family.group != [name.clone()]
            || family.parameters.len() != 1
            || !family.indices.is_empty()
            || !family.sort.zero()
            || family.constructors.len() != 1
            || family.constructors[0].name != intro
            || family.constructors[0].fields.len() != 1
            || !family.constructors[0].result_indices.is_empty()
            || !matches!(family.constructors[0].fields[0].as_ref(), Term::Var(0))
            || self
                .kernel
                .declarations
                .get(&intro)?
                .is_none_or(|d| d.universes.len() != 1)
        {
            return Err("choice requires the standard checked Nonempty/intro shape".into());
        }
        self.compare_standard_type(&name, "(#pt-pi ((A (#pt-sort u))) #pt-prop)")?;
        self.compare_standard_type(
            &intro,
            "(#pt-pi ((A (#pt-sort u)) (value A)) (#pt-app (#pt-use nonempty (u)) A))",
        )
    }

    fn check_iff(&mut self) -> Result<()> {
        let name = standard(&["Iff"]);
        let intro = standard(&["Iff", "intro"]);
        let declaration = self
            .kernel
            .declarations
            .get(&name)?
            .ok_or("propext requires the checked standard Iff family")?;
        let family = declaration.family.as_ref().ok_or("Iff must be inductive")?;
        if !self.checked.contains_key(&name)
            || !self.checked.contains_key(&intro)
            || !declaration.universes.is_empty()
            || family.group != [name.clone()]
            || family.parameters.len() != 2
            || !family.indices.is_empty()
            || !family.sort.zero()
            || family.constructors.len() != 1
            || family.constructors[0].name != intro
            || family.constructors[0].fields.len() != 2
            || !family.constructors[0].result_indices.is_empty()
            || self
                .kernel
                .declarations
                .get(&intro)?
                .is_none_or(|d| !d.universes.is_empty())
        {
            return Err("propext requires the standard checked Iff/intro shape".into());
        }
        self.compare_standard_type(&name, "(#pt-pi ((P #pt-prop) (Q #pt-prop)) #pt-prop)")?;
        self.compare_standard_type(&intro,r#"(#pt-pi ((P #pt-prop) (Q #pt-prop)
          (forward (#pt-pi ((p P)) Q)) (backward (#pt-pi ((q Q)) P))) (#pt-app (#pt-use iff ()) P Q))"#)
    }

    fn axiom_schema(&self, kind: &str, universes: &[String]) -> Result<(T, T)> {
        let (signature, value) = match kind {
            "choice" => (
                r#"(#pt-pi ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A))) A)"#,
                r#"(#pt-lambda ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A)))
                  (#pt-app (#pt-use #pt-foundation-choice (u)) A
                    (#pt-lambda ((P #pt-prop) (consume (#pt-pi ((value A)) P)))
                      (#pt-induct nonempty (u) (A)
                        (#pt-lambda ((subject (#pt-app (#pt-use nonempty (u)) A))) P)
                        (consume) evidence))))"#,
            ),
            "propext" => (
                r#"(#pt-pi ((P #pt-prop) (Q #pt-prop) (evidence (#pt-app (#pt-use iff ()) P Q)))
                  (#pt-app (#pt-use eq (1)) #pt-prop P Q))"#,
                r#"(#pt-lambda ((P #pt-prop) (Q #pt-prop) (evidence (#pt-app (#pt-use iff ()) P Q)))
                  (#pt-eq-elim #pt-prop P
                    (#pt-lambda ((endpoint #pt-prop) (equality (#pt-eq #pt-prop P endpoint)))
                      (#pt-app (#pt-use eq (1)) #pt-prop P endpoint))
                    (#pt-app (#pt-use refl (1)) #pt-prop P) Q
                    (#pt-app (#pt-use #pt-foundation-propext ()) P Q
                      (#pt-project iff 0 evidence) (#pt-project iff 1 evidence))))"#,
            ),
            "quot-sound" => (
                r#"(#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((x A) (y A)) #pt-prop))
                  (left A) (right A) (related (#pt-app relation left right)))
                  (#pt-app (#pt-use eq (u)) (#pt-app (#pt-use quot (u)) A relation)
                    (#pt-app (#pt-use make (u)) A relation left) (#pt-app (#pt-use make (u)) A relation right)))"#,
                r#"(#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((x A) (y A)) #pt-prop))
                  (left A) (right A) (related (#pt-app relation left right)))
                  (#pt-eq-elim (#pt-quot u A relation) (#pt-quot-make u A relation left)
                    (#pt-lambda ((endpoint (#pt-quot u A relation))
                      (equality (#pt-eq (#pt-quot u A relation) (#pt-quot-make u A relation left) endpoint)))
                      (#pt-app (#pt-use eq (u)) (#pt-quot u A relation) (#pt-quot-make u A relation left) endpoint))
                    (#pt-app (#pt-use refl (u)) (#pt-quot u A relation) (#pt-quot-make u A relation left))
                    (#pt-quot-make u A relation right)
                    (#pt-app (#pt-use #pt-foundation-quot-sound (u)) A relation left right related)))"#,
            ),
            _ => return Err("unknown fixed axiom schema".into()),
        };
        Ok((
            self.axiom_template(signature, universes)?,
            self.axiom_template(value, universes)?,
        ))
    }

    pub(super) fn target_axioms(&self, target: &str) -> Result<Vec<String>> {
        let mut pending = vec![target.to_owned()];
        let mut visited = HashSet::new();
        let mut declared = BTreeSet::new();
        let mut actual = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if let Some(label) = foundation::label(&name) {
                actual.insert(label.to_owned());
                continue;
            }
            let index = self
                .checked
                .get(&name)
                .ok_or("unchecked target dependency in axiom audit")?;
            let record = &self.reports[*index];
            if record.kind == "axiom" {
                declared.insert(record.name.clone());
            }
            pending.extend(record.dependencies.iter().cloned());
        }
        if declared != actual {
            return Err("target logical foundations differ from its declared axiom closure".into());
        }
        Ok(actual.into_iter().collect())
    }
}
