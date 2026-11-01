//! Exact frame word geometry for generated cancellation. Geometry supplies
//! addresses only; checked typed word reads still supply payload provenance.
use crate::{Expr, Item};
use std::collections::HashMap;

pub(super) struct Layout {
    pub fields: HashMap<String, (usize, usize)>,
    pub words: usize,
}

impl Layout {
    pub fn new(
        source: &str,
        frame: &str,
        declarations: &crate::typed_ir::Declarations,
    ) -> Result<Self, String> {
        let parsed = crate::parse(source).map_err(|error| error.to_string())?;
        let mut structs = declarations.structs.clone();
        let mut enums = declarations.enums.clone();
        // These are already-resolved compiler layouts, not a new source graph.
        // Parsing them through the public loader would reinterpret their file
        // identities as dependencies and lose the original declaration owner.
        for layout in parsed.iter().filter(|value| matches!(&value.expr, Expr::List(parts)
            if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#struct" || head == "#enum"))) {
            let item = crate::parse_item(&crate::normalize_keywords(layout.expr.clone()))?;
            match item {
                Item::Struct { name, fields, .. } => {
                    structs.insert(name, fields);
                }
                Item::Enum { name, variants, .. } => {
                    enums.insert(name, variants);
                }
                _ => {}
            }
        }
        let mut words = 0usize;
        for fields in structs.values_mut() {
            for field in fields {
                field.ty = crate::typed_ir::resolve_type(&field.ty, &declarations.aliases)?;
            }
        }
        for variants in enums.values_mut() {
            for variant in variants {
                for field in &mut variant.fields {
                    *field = crate::typed_ir::resolve_type(field, &declarations.aliases)?;
                }
            }
        }
        let mut fields = HashMap::new();
        for field in structs
            .get(frame)
            .ok_or_else(|| "word cleanup lost its frame layout".to_string())?
        {
            let width = crate::codegen::storage_word_count(&field.ty, &structs, &enums)?;
            fields.insert(field.name.clone(), (words, width));
            words = words
                .checked_add(width)
                .ok_or_else(|| "word cleanup frame is too large".to_string())?;
        }
        Ok(Self { fields, words })
    }

    pub fn slice(start: usize, length: usize) -> String {
        format!(
            "(#slice-mut-range task {start}usize {}usize)",
            start + length
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_cleanup_layout_resolves_aliases_and_zero_length_markers() {
        let program = crate::parse_program("(#type Number #u64)").unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let layout = Layout::new(
            "(#enum Slot () ((Slot.Empty) (Slot.Full Number)))
             (#struct Frame () (: pc #u32 : value Slot : marker (#array Unmaterialized 0)))",
            "Frame",
            &declarations,
        )
        .unwrap();
        assert_eq!(layout.words, 3);
        assert_eq!(layout.fields["pc"], (0, 1));
        assert_eq!(layout.fields["value"], (1, 2));
        assert_eq!(layout.fields["marker"], (3, 0));
        assert_eq!(Layout::slice(1, 2), "(#slice-mut-range task 1usize 3usize)");
    }
}
