//! Indexed NDJSON primitive tables. Only backward references are accepted.
use super::expressions::Expression;
use super::*;

impl Replay {
    pub(super) fn name_record(&mut self, value: &Json) -> Result<()> {
        let Json::Object(data) = value else {
            unreachable!()
        };
        if index(&data["in"])? != self.names.len() || self.names.len() >= MAX_NAMES {
            return Err("name IDs must be contiguous and within the name table limit".into());
        }
        let (pre, part, key) = if let Some(value) = data.get("str") {
            fields(value, &["pre", "str"])?;
            let part = string(value.get("str").ok_or("missing name string")?)?;
            let display = if !part.is_empty()
                && part
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphabetic() || c == '_')
                && part
                    .chars()
                    .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\''))
            {
                part.to_owned()
            } else {
                crate::diagnostic_json::quoted(part)
            };
            (
                self.name(value.get("pre").ok_or("missing name prefix")?)?,
                display,
                format!("s{}:{part}", part.len()),
            )
        } else if let Some(value) = data.get("num") {
            let value = fields(value, &["pre", "i"])?;
            let Json::Number(number) = &value["i"] else {
                return Err("numeric name component must be an unsigned integer".into());
            };
            if number.is_empty() || !number.bytes().all(|b| b.is_ascii_digit()) {
                return Err("numeric name component must be an unsigned integer".into());
            }
            (
                self.name(&value["pre"])?,
                format!("[{number}]"),
                format!("n{number};"),
            )
        } else {
            return Err("unsupported name record".into());
        };
        let name = Name {
            key: format!("{}{key}", pre.key),
            display: if pre.depth == 0 {
                part
            } else {
                format!("{}.{part}", pre.display)
            },
            depth: pre.depth + 1,
        };
        if name.depth > 256 || name.key.len() > 16_384 || name.display.len() > 16_384 {
            return Err("export name size or depth limit exceeded".into());
        }
        self.name_bytes = self
            .name_bytes
            .checked_add(name.key.len() + name.display.len())
            .ok_or("name byte count overflow")?;
        if self.name_bytes > MAX_NAME_BYTES {
            return Err("export name byte limit exceeded".into());
        }
        if !self.name_keys.insert(name.key.clone()) {
            return Err("duplicate interned export name".into());
        }
        self.names.push(name);
        Ok(())
    }
    pub(super) fn level_record(&mut self, value: &Json) -> Result<()> {
        let Json::Object(data) = value else {
            unreachable!()
        };
        if index(&data["il"])? != self.levels.len() || self.levels.len() >= MAX_LEVELS {
            return Err(
                "universe IDs must be contiguous and within the universe table limit".into(),
            );
        }
        let level = if let Some(value) = data.get("succ") {
            self.level(value)?.successor()?
        } else if let Some(value) = data.get("max") {
            let pair = array(value, 2)?;
            if pair.len() != 2 {
                return Err("universe max requires exactly two references".into());
            }
            self.level(&pair[0])?.maximum(&self.level(&pair[1])?)?
        } else if let Some(value) = data.get("imax") {
            let pair = array(value, 2)?;
            if pair.len() != 2 {
                return Err("universe imax requires exactly two references".into());
            }
            self.level(&pair[0])?.imax(&self.level(&pair[1])?)?
        } else if let Some(value) = data.get("param") {
            let name = self.name(value)?;
            if name.depth == 0 {
                return Err("anonymous universe parameter".into());
            }
            if name.key.len() > 512 {
                return Err("export universe parameter name byte limit exceeded".into());
            }
            Level::variable(name.key)
        } else {
            return Err("unsupported universe record".into());
        };
        let weight = level.memory_weight();
        if weight > 64 * 1024 {
            return Err("export universe payload limit exceeded".into());
        }
        self.payload_bytes = self.payload_bytes.saturating_add(weight);
        if self.payload_bytes > 64 * 1024 * 1024 {
            return Err("export primitive payload limit exceeded".into());
        }
        self.levels.push(level);
        Ok(())
    }
    pub(super) fn expression_record(&mut self, value: &Json) -> Result<()> {
        let Json::Object(data) = value else {
            unreachable!()
        };
        if index(&data["ie"])? != self.expressions.len()
            || self.expressions.len() >= MAX_EXPRESSIONS
        {
            return Err(
                "expression IDs must be contiguous and within the expression table limit".into(),
            );
        }
        let expression = if let Some(value) = data.get("bvar") {
            Expression::Var(index(value)?)
        } else if let Some(value) = data.get("sort") {
            Expression::Sort(self.level_id(value)?)
        } else if let Some(value) = data.get("const") {
            let value = fields(value, &["name", "us"])?;
            let name = self.name_id(&value["name"])?;
            let levels = array(&value["us"], 32)?
                .iter()
                .map(|v| self.level_id(v))
                .collect::<Result<_>>()?;
            Expression::Global(name, levels)
        } else if let Some(value) = data.get("app") {
            let value = fields(value, &["fn", "arg"])?;
            Expression::App(
                self.expression_id(&value["fn"])?,
                self.expression_id(&value["arg"])?,
            )
        } else if data.contains_key("lam") || data.contains_key("forallE") {
            let lambda = data.contains_key("lam");
            let value = fields(
                &data[if lambda { "lam" } else { "forallE" }],
                &["name", "type", "body", "binderInfo"],
            )?;
            self.name_id(&value["name"])?;
            if !matches!(
                string(&value["binderInfo"])?,
                "default" | "implicit" | "strictImplicit" | "instImplicit"
            ) {
                return Err("invalid exported binder style".into());
            }
            let domain = self.expression_id(&value["type"])?;
            let body = self.expression_id(&value["body"])?;
            if lambda {
                Expression::Lam(domain, body)
            } else {
                Expression::Pi(domain, body)
            }
        } else if let Some(value) = data.get("letE") {
            let value = fields(value, &["name", "type", "value", "body", "nondep"])?;
            self.name_id(&value["name"])?;
            boolean(&value["nondep"])?;
            Expression::Let(
                self.expression_id(&value["type"])?,
                self.expression_id(&value["value"])?,
                self.expression_id(&value["body"])?,
            )
        } else if let Some(value) = data.get("proj") {
            let value = fields(value, &["typeName", "idx", "struct"])?;
            Expression::Project(
                self.name_id(&value["typeName"])?,
                index(&value["idx"])?,
                self.expression_id(&value["struct"])?,
            )
        } else if let Some(value) = data.get("mdata") {
            let value = fields(value, &["expr", "data"])?;
            if !matches!(value["data"], Json::Object(_)) {
                return Err("expression metadata must be an object".into());
            }
            Expression::Alias(self.expression_id(&value["expr"])?)
        } else if let Some(value) = data.get("natVal") {
            let value = Natural::parse(string(value)?)?;
            self.natural_literals = true;
            Expression::Natural(value)
        } else if data.contains_key("strVal") {
            return Err("string literal replay is not implemented".into());
        } else {
            return Err("unsupported exported expression; free variables, metavariables and unknown term forms are forbidden".into());
        };
        // Bound unused graphs too: dropping a final Arc in a long chain must
        // not recurse through an unbounded number of expression allocations.
        let child_depth = |value: &Json, key: &str| {
            self.expression_depth(value.get(key).ok_or("missing expression child")?)
        };
        let depth = if let Some(value) = data.get("app") {
            1 + child_depth(value, "fn")?.max(child_depth(value, "arg")?)
        } else if let Some(value) = data.get("lam").or_else(|| data.get("forallE")) {
            1 + child_depth(value, "type")?.max(child_depth(value, "body")?)
        } else if let Some(value) = data.get("letE") {
            1 + child_depth(value, "type")?
                .max(child_depth(value, "value")?)
                .max(child_depth(value, "body")?)
        } else if let Some(value) = data.get("proj") {
            1 + child_depth(value, "struct")?
        } else if let Some(value) = data.get("mdata") {
            child_depth(value, "expr")?
        } else {
            1
        };
        if depth > MAX_EXPRESSION_DEPTH {
            return Err("export expression depth limit exceeded".into());
        }
        let payload = match &expression {
            Expression::Natural(value) => {
                "$lean:s3:Nat".len().saturating_add(value.decimal().len())
            }
            Expression::Sort(id) => self.levels[*id].memory_weight(),
            Expression::Global(name, levels) => levels
                .iter()
                .fold(self.names[*name].key.len(), |total, id| {
                    total.saturating_add(self.levels[*id].memory_weight())
                }),
            Expression::Project(name, ..) => self.names[*name].key.len(),
            Expression::Alias(id) => self
                .expressions
                .payload(*id)
                .ok_or("missing expression child")?,
            _ => 0,
        };
        self.payload_bytes = self
            .payload_bytes
            .saturating_add(128)
            .saturating_add(payload);
        if self.payload_bytes > 64 * 1024 * 1024 {
            return Err("export primitive payload limit exceeded".into());
        }
        self.expressions
            .push(expression, depth, payload, &self.names, &self.levels)
    }
    pub(super) fn check_natural_signature(&self) -> Result<()> {
        let nat = "$lean:s3:Nat";
        let zero = "$lean:s3:Nats4:zero";
        let succ = "$lean:s3:Nats4:succ";
        let family = self
            .kernel
            .declarations
            .get(nat)
            .and_then(|d| d.family.as_ref())
            .ok_or("Nat literals require the previously checked standard Nat declaration")?;
        let valid = family.group == [nat]
            && family.parameters.is_empty()
            && family.indices.is_empty()
            && family.sort.equivalent(&Level::number(1)?)?
            && family.constructors.len() == 2
            && family.constructors[0].name == zero
            && family.constructors[0].fields.is_empty()
            && family.constructors[1].name == succ
            && family.constructors[1].fields.len() == 1
            && matches!(family.constructors[1].fields[0].as_ref(),Term::Global(name,levels) if name == nat && levels.is_empty())
            && self.checked.contains_key(nat);
        if !valid {
            return Err(
                "Nat literal declaration does not have the standard checked Nat signature".into(),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_literal_payload_counts_every_owned_decimal_digit() {
        let decimal = "9".repeat(4096);
        let input = object([("ie", number_json(0)), ("natVal", text_json(&decimal))]);
        let bytes = 128 + "$lean:s3:Nat".len() + decimal.len();
        let mut replay = Replay::new();
        replay.payload_bytes = 64 * 1024 * 1024 - bytes;
        replay.expression_record(&input).unwrap();
        assert_eq!(replay.payload_bytes, 64 * 1024 * 1024);
        let input = object([("ie", number_json(1)), ("natVal", text_json(&decimal))]);
        assert!(replay
            .expression_record(&input)
            .unwrap_err()
            .contains("primitive payload limit"));
    }
}
