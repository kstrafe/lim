//! Pinned quotient records become ordinary checked wrappers around primitives.
//! No exported type, record kind or name can install an axiom or reduction rule.
use super::*;

pub(super) fn standard(parts: &[&str]) -> String {
    parts.iter().fold("$lean:".to_owned(), |mut result, part| {
        result.push_str(&format!("s{}:{part}", part.len()));
        result
    })
}

impl Replay {
    pub(super) fn quotient_record(&mut self, body: &Json) -> Result<()> {
        let data = fields(body, &["name", "levelParams", "type", "kind"])?;
        let name = self.name(&data["name"])?;
        let kind = string(&data["kind"])?;
        let (expected_name, expected_kind, count) = match self.quotient_stage {
            0 => (standard(&["Quot"]), "type", 1),
            1 => (standard(&["Quot", "mk"]), "ctor", 1),
            2 => (standard(&["Quot", "lift"]), "lift", 2),
            3 => (standard(&["Quot", "ind"]), "ind", 1),
            _ => return Err("duplicate quotient package".into()),
        };
        if name.key != expected_name || kind != expected_kind {
            return Err(
                "quotient records must have the pinned identities, kinds and package order".into(),
            );
        }
        let universes = self.universes(&data["levelParams"])?;
        if universes.len() != count {
            return Err("quotient universe parameter count mismatch".into());
        }
        self.check_quotient_equality()?;
        let (expected, value) = self.quotient_schema(kind, &universes)?;
        let ty = self.expression(&data["type"])?;
        let dependencies = dependencies(&[ty.clone(), value.clone()])?;
        self.dependencies_known(&dependencies, &[])?;
        self.room(1)?;
        self.reset_budget()?;
        self.kernel
            .scope(&universes, &[ty.clone(), expected.clone(), value.clone()])?;
        self.kernel.sort(&[], &ty, 0)?;
        if !self.kernel.convertible(&[], &ty, &expected, 0)? {
            return Err("exported quotient signature differs from the fixed checked schema".into());
        }
        self.reset_budget()?;
        self.kernel
            .definition(&name.key, universes, ty, value, false)?;
        self.remember(&name, &format!("quotient-{kind}"), dependencies)?;
        self.quotient_stage += 1;
        Ok(())
    }

    fn quotient_template(&mut self, source: &str, universes: &[String]) -> Result<T> {
        let parsed = crate::proof::kernel::parse_closed_template(source, &["u", "v"])?;
        let names = HashMap::from([
            ("eq".into(), standard(&["Eq"])),
            ("quot".into(), standard(&["Quot"])),
            ("make".into(), standard(&["Quot", "mk"])),
        ]);
        let levels = ["u", "v"]
            .into_iter()
            .zip(universes)
            .map(|(name, value)| (name.into(), Level::variable(value.clone())))
            .collect();
        source::correspondence::relocate_template(&parsed, &names, &levels)
    }

    pub(super) fn check_quotient_equality(&mut self) -> Result<()> {
        let name = standard(&["Eq"]);
        let refl = standard(&["Eq", "refl"]);
        let declaration = self
            .kernel
            .declarations
            .get(&name)?
            .ok_or("quotient primitives require the checked standard Eq family")?;
        let family = declaration
            .family
            .as_ref()
            .ok_or("quotient Eq must be inductive")?;
        if !self.is_checked(&name)?
            || !self.is_checked(&refl)?
            || declaration.universes.len() != 1
            || family.group != [name.clone()]
            || family.parameters.len() != 2
            || family.indices.len() != 1
            || !family.sort.zero()
            || family.constructors.len() != 1
            || family.constructors[0].name != refl
            || !family.constructors[0].fields.is_empty()
            || family.constructors[0].result_indices.len() != 1
            || !matches!(
                family.constructors[0].result_indices[0].as_ref(),
                Term::Var(0)
            )
        {
            return Err(
                "quotient equality does not have the standard checked Eq/refl shape".into(),
            );
        }
        let expected = self.quotient_template(
            "(#pt-pi ((A (#pt-sort u)) (left A) (right A)) #pt-prop)",
            &declaration.universes,
        )?;
        self.reset_budget()?;
        if !self
            .kernel
            .convertible(&[], &declaration.ty, &expected, 0)?
        {
            return Err("quotient Eq signature mismatch".into());
        }
        let constructor = self
            .kernel
            .declarations
            .get(&refl)?
            .ok_or("missing checked Eq.refl")?;
        if constructor.universes.len() != 1 {
            return Err("quotient Eq.refl universe mismatch".into());
        }
        let expected = self.quotient_template(
            "(#pt-pi ((A (#pt-sort u)) (value A)) (#pt-app (#pt-use eq (u)) A value value))",
            &constructor.universes,
        )?;
        self.reset_budget()?;
        if !self
            .kernel
            .convertible(&[], &constructor.ty, &expected, 0)?
        {
            return Err("quotient Eq.refl signature mismatch".into());
        }
        Ok(())
    }

    fn quotient_schema(&mut self, kind: &str, universes: &[String]) -> Result<(T, T)> {
        let (ty, value) = match kind {
            "type" => (
                "(#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))) (#pt-sort u))",
                "(#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))) (#pt-quot u A relation))"),
            "ctor" => (
                "(#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop)) (value A)) (#pt-app (#pt-use quot (u)) A relation))",
                "(#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop)) (value A)) (#pt-quot-make u A relation value))"),
            "lift" => (r#"
                (#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))
                  (B (#pt-sort v)) (function (#pt-pi ((value A)) B))
                  (respect (#pt-pi ((left A) (right A) (related (#pt-app relation left right)))
                    (#pt-app (#pt-use eq (v)) B (#pt-app function left) (#pt-app function right))))
                  (subject (#pt-app (#pt-use quot (u)) A relation))) B)
            "#, r#"
                (#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))
                  (B (#pt-sort v)) (function (#pt-pi ((value A)) B))
                  (respect (#pt-pi ((left A) (right A) (related (#pt-app relation left right)))
                    (#pt-app (#pt-use eq (v)) B (#pt-app function left) (#pt-app function right))))
                  (subject (#pt-app (#pt-use quot (u)) A relation)))
                  (#pt-quot-lift (u v) A relation B function
                    (#pt-lambda ((left A) (right A) (related (#pt-app relation left right)))
                      (#pt-induct eq (v) (B (#pt-app function left)) (#indices (#pt-app function right))
                        (#pt-lambda ((endpoint B)
                          (evidence (#pt-app (#pt-use eq (v)) B (#pt-app function left) endpoint)))
                          (#pt-eq B (#pt-app function left) endpoint))
                        ((#pt-refl B (#pt-app function left)))
                        (#pt-app respect left right related))) subject))
            "#),
            "ind" => (r#"
                (#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))
                  (motive (#pt-pi ((value (#pt-app (#pt-use quot (u)) A relation))) #pt-prop))
                  (branch (#pt-pi ((value A)) (#pt-app motive (#pt-app (#pt-use make (u)) A relation value))))
                  (subject (#pt-app (#pt-use quot (u)) A relation))) (#pt-app motive subject))
            "#, r#"
                (#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((left A) (right A)) #pt-prop))
                  (motive (#pt-pi ((value (#pt-app (#pt-use quot (u)) A relation))) #pt-prop))
                  (branch (#pt-pi ((value A)) (#pt-app motive (#pt-app (#pt-use make (u)) A relation value))))
                  (subject (#pt-app (#pt-use quot (u)) A relation)))
                  (#pt-quot-induct u A relation motive branch subject))
            "#),
            _ => return Err("unknown quotient schema".into()),
        };
        Ok((
            self.quotient_template(ty, universes)?,
            self.quotient_template(value, universes)?,
        ))
    }
}
