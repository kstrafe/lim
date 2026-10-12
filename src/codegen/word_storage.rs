//! Unsafe flat-word accesses. No async semantics or initialization sidecar.
use super::*;

impl FunctionContext<'_> {
    pub(super) fn word_storage_address(&mut self, source: &Expr) -> Result<(), String> {
        let ty = self
            .expression_type(source)
            .ok_or_else(|| "word storage source lost its checked slice type".to_owned())?;
        self.expression_as_expected(source, &ty)?;
        // Preserve descending-stack metadata, discard packed-byte metadata:
        // every entry in this storage is one complete value word.
        self.output.push_str("    btr rax, 62\n");
        Ok(())
    }

    pub(super) fn word_storage_expression(
        &mut self,
        operator: &str,
        items: &[Expr],
    ) -> Result<(), String> {
        let ty = resolve_type(&parse_type(items.get(1))?, &self.aliases)?;
        if operator == "word-view" && matches!(ty, Type::Slice(_) | Type::MutableSlice(_)) {
            let source = self
                .expression_type(&items[2])
                .ok_or_else(|| "word view source lost its checked reference type".to_owned())?;
            let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) = &source
            else {
                return Err("word-slice view requires a checked reference".into());
            };
            let words = storage_word_count(target, &self.structs, &self.enums)?;
            self.expression_as_expected(&items[2], &source)?;
            // This unsafe reinterpretation requires flat value-word backing.
            // Preserve descending storage; packed-byte metadata is inapplicable.
            self.output
                .push_str(&format!("    btr rax, 62\n    mov rdx, {words}\n"));
            return Ok(());
        }
        self.word_storage_address(&items[2])?;
        if operator == "word-view" {
            return Ok(());
        }
        if matches!(operator, "word-read" | "word-take") {
            return self.load_reference_value(&ty);
        }
        let words = storage_word_count(&ty, &self.structs, &self.enums)?;
        self.push_rax();
        if words <= VALUE_REGISTERS.len() {
            self.expression_as_expected(&items[3], &ty)?;
            if ty == Type::F32 {
                self.output.push_str("    movd eax, xmm0\n");
            }
            if ty == Type::F64 {
                self.output.push_str("    movq rax, xmm0\n");
            }
            self.output.push_str("    pop r11\n");
            self.stack_depth -= 1;
            let ascending = self.label("word_write_ascending");
            let done = self.label("word_write_done");
            self.output.push_str(&format!(
                "    test r11, r11\n    jns {ascending}\n    btr r11, 63\n"
            ));
            for (index, register) in VALUE_REGISTERS.iter().take(words).enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [r11-{}], {register}\n",
                    index * 8
                ));
            }
            self.output
                .push_str(&format!("    jmp {done}\n{ascending}:\n"));
            for (index, register) in VALUE_REGISTERS.iter().take(words).enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [r11+{}], {register}\n",
                    index * 8
                ));
            }
            self.output
                .push_str(&format!("{done}:\n    xor eax, eax\n"));
            return Ok(());
        }
        let base = self
            .aggregate_temp_base
            .ok_or_else(|| "large word write has no aggregate temporary".to_owned())?
            + (self.aggregate_argument_regions + self.aggregate_projection_depth)
                * self.aggregate_temp_words;
        self.aggregate_projection_depth += 1;
        let result = self.store_value_to_slots(&items[3], &ty, &flat_slots(base, words));
        self.aggregate_projection_depth -= 1;
        result?;
        self.output.push_str("    pop r11\n");
        self.stack_depth -= 1;
        let ascending = self.label("large_word_write_ascending");
        let done = self.label("large_word_write_done");
        self.output.push_str(&format!(
            "    test r11, r11\n    jns {ascending}\n    btr r11, 63\n"
        ));
        for index in 0..words {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                (base + index) * 8,
                index * 8
            ));
        }
        self.output
            .push_str(&format!("    jmp {done}\n{ascending}:\n"));
        for index in 0..words {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11+{}], rax\n",
                (base + index) * 8,
                index * 8
            ));
        }
        self.output
            .push_str(&format!("{done}:\n    xor eax, eax\n"));
        Ok(())
    }
}
