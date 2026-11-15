//! Locate runtime calls using the surface reader's original source spans.
//! Recovery is suffix-only: editor requests never repair or save user source.

use crate::{Expr, Span, SpannedExpr as Node, TokenKind as T};

pub(crate) struct Call {
    pub callee: Span,
    pub argument: Option<String>,
    /// Source used for declaration lookup; all authored byte offsets are intact.
    pub source: String,
}

fn symbol(node: &Node) -> Option<&str> {
    match &node.expr {
        Expr::Symbol(name) | Expr::Function(name) => Some(name),
        _ => None,
    }
}

fn head(node: &Node) -> &str {
    node.children
        .first()
        .and_then(symbol)
        .and_then(|name| name.strip_prefix('#'))
        .unwrap_or("")
}

struct Open<'a> {
    kind: &'a T,
    terms: Vec<&'a T>,
    position: usize,
}

fn call_arguments(open: &Open<'_>) -> Option<usize> {
    match open.terms.first()? {
        T::Symbol(name) if matches!(name.as_str(), "#call" | "#unsafe-call") => Some(2),
        T::Symbol(name) if crate::surface_syntax::callable_name(name) => Some(1),
        _ => None,
    }
}

/// Close missing final delimiters and the final named value/record terminator.
/// This intentionally does not guess at malformed syntax in the middle of a file.
pub(crate) fn recover(source: &str) -> Option<String> {
    if crate::parse_source_unit(source).is_ok() {
        return Some(source.to_owned());
    }
    let tokens = crate::lex(source).ok()?;
    let mut stack: Vec<Open<'_>> = Vec::new();
    for token in &tokens {
        match &token.kind {
            T::LParen | T::LBrace | T::LBracket => {
                let position = if let Some(parent) = stack.last_mut() {
                    let position = parent.terms.len();
                    parent.terms.push(&token.kind);
                    position
                } else {
                    0
                };
                stack.push(Open {
                    kind: &token.kind,
                    terms: Vec::new(),
                    position,
                });
                if stack.len() > crate::MAX_PARSE_NESTING {
                    return None;
                }
            }
            T::RParen | T::RBrace | T::RBracket => {
                let open = stack.pop()?;
                if !matches!(
                    (open.kind, &token.kind),
                    (T::LParen, T::RParen) | (T::LBrace, T::RBrace) | (T::LBracket, T::RBracket)
                ) {
                    return None;
                }
            }
            _ => {
                if let Some(parent) = stack.last_mut() {
                    parent.terms.push(&token.kind);
                }
            }
        }
    }
    if stack.is_empty() {
        return None;
    }
    let mut recovered = source.to_owned();
    // A closing delimiter must not become part of an unfinished line comment.
    if crate::source_comments(source)
        .last()
        .is_some_and(|comment| comment.span.end == source.len())
    {
        recovered.push('\n');
    }
    while let Some(open) = stack.last() {
        match open.kind {
            T::LParen => {
                let named_pair = stack.len() >= 3
                    && stack[stack.len() - 2].kind == &T::LParen
                    && call_arguments(&stack[stack.len() - 3])
                        == Some(stack[stack.len() - 2].position)
                    && open.terms.len() == 1
                    && matches!(open.terms.first(), Some(T::Symbol(name)) if !name.starts_with('#') && name != "$");
                if named_pair {
                    recovered.push_str(" 0u64");
                } else if call_arguments(open) == Some(2) && open.terms.len() == 2 {
                    recovered.push_str(" ()");
                } else if matches!(open.terms.last(), Some(T::Symbol(name)) if !name.starts_with('#') && !name.ends_with(':'))
                    && open.terms.len() >= 2
                    && matches!(open.terms[open.terms.len() - 2], T::Colon)
                    && open.terms.iter().filter(|term| matches!(term, T::Colon)
                        || matches!(term, T::Symbol(name) if name.ends_with(':') && !name.ends_with("::"))).count() >= 2
                {
                    // The final inline colon pair has its label but no value.
                    recovered.push_str(" 0u64");
                } else if matches!(open.terms.last(), Some(T::Colon))
                    || matches!(open.terms.last(), Some(T::Symbol(name)) if name.ends_with(':') && !name.ends_with("::"))
                {
                    recovered.push_str(" ()");
                }
                if open.terms.iter().any(|term| term == &&T::Semicolon)
                    && open.terms.last() != Some(&&T::Semicolon)
                {
                    recovered.push(';');
                }
                recovered.push(')');
            }
            T::LBrace => {
                let entry = open
                    .terms
                    .rsplit(|term| term == &&T::Semicolon)
                    .next()
                    .unwrap_or_default();
                if !entry.is_empty() {
                    if matches!(entry.last(), Some(T::Equal | T::Colon))
                        || matches!(entry.last(), Some(T::Symbol(name)) if name.ends_with(':') && !name.ends_with("::"))
                    {
                        recovered.push_str(" 0u64");
                    } else if entry.len() == 1 {
                        recovered.push_str(" = 0u64");
                    }
                    recovered.push(';');
                }
                recovered.push('}');
            }
            T::LBracket => recovered.push(']'),
            _ => return None,
        }
        stack.pop();
    }
    crate::parse_source_unit(&recovered).ok()?;
    Some(recovered)
}

/// Find the innermost runtime call containing the cursor, including its named
/// argument label. The reader already lowers braces, puns, layout and colons.
pub(crate) fn call(source: &str, byte: usize) -> Option<Call> {
    if !source.is_char_boundary(byte) {
        return None;
    }
    let recovered = recover(source)?;
    let forms = crate::parse_source_unit(&recovered).ok()?;
    let (callee, argument) = forms
        .iter()
        .find_map(|node| runtime(node, byte, &recovered))?;
    Some(Call {
        callee,
        argument,
        source: recovered,
    })
}

fn contains(node: &Node, byte: usize, source: &str) -> bool {
    node.span.start <= byte
        && (byte < node.span.end
            // Colon groups have no closing delimiter of their own. Their
            // extent ends just after the operand being entered in the editor.
            || byte == node.span.end
                && (source.as_bytes().get(node.span.start) == Some(&b':')
                    || !matches!(source.as_bytes().get(node.span.start), Some(b'(' | b'{' | b'['))
                        && !matches!(node.span.end.checked_sub(1).and_then(|end| source.as_bytes().get(end)), Some(b')' | b'}' | b']' | b';'))))
}

fn nested_function(node: &Node, byte: usize, source: &str) -> Option<(Span, Option<String>)> {
    if !contains(node, byte, source) || matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
        return None;
    }
    if matches!(head(node), "fn" | "unsafe-fn") {
        return runtime(node, byte, source);
    }
    node.children
        .iter()
        .find_map(|child| nested_function(child, byte, source))
}

/// Refinement predicates are value expressions within an explicit type.
fn type_predicates(node: &Node, byte: usize, source: &str) -> Option<(Span, Option<String>)> {
    if !contains(node, byte, source) || matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
        return None;
    }
    if head(node) == "where" {
        if let Some(binding) = node
            .children
            .get(1)
            .filter(|binding| binding.children.len() == 2)
        {
            return type_predicates(&binding.children[1], byte, source).or_else(|| {
                node.children
                    .iter()
                    .skip(2)
                    .find_map(|predicate| runtime(predicate, byte, source))
            });
        }
        return None;
    }
    node.children
        .iter()
        .find_map(|child| type_predicates(child, byte, source))
}

fn runtime(node: &Node, byte: usize, source: &str) -> Option<(Span, Option<String>)> {
    if !contains(node, byte, source) || matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
        return None;
    }
    let children = &node.children;
    if matches!(
        children.first().map(|child| &child.expr),
        Some(Expr::Generate)
    ) {
        return children
            .iter()
            .skip(2)
            .find_map(|child| nested_function(child, byte, source));
    }
    match head(node) {
        "gn" | "gn-fn" | "gn-call" | "syntax" | "distributed-enum" | "capability" | "alias"
        | "export" | "generated-context" => return None,
        "fn" | "unsafe-fn" | "extern-fn" => {
            let name = if head(node) == "extern-fn" { 2 } else { 1 };
            if let Some(parameters) = children.get(name + 1) {
                for parameter in &parameters.children {
                    let index = usize::from(head(parameter) == "mut") + 1;
                    if let Some(found) = parameter
                        .children
                        .get(index)
                        .and_then(|kind| type_predicates(kind, byte, source))
                    {
                        return Some(found);
                    }
                }
            }
            if let Some(found) = children
                .get(name + 2)
                .and_then(|kind| type_predicates(kind, byte, source))
            {
                return Some(found);
            }
            return children
                .iter()
                .skip(name + 3)
                .find_map(|child| runtime(child, byte, source));
        }
        "type" => {
            return children
                .get(2)
                .and_then(|kind| type_predicates(kind, byte, source))
        }
        "struct" | "enum" => {
            return children.get(3).and_then(|fields| {
                fields.children.iter().find_map(|field| {
                    field
                        .children
                        .iter()
                        .skip(1)
                        .find_map(|kind| type_predicates(kind, byte, source))
                })
            });
        }
        "let" | "let-mut" | "static" | "const" => {
            return children
                .get(2)
                .and_then(|kind| type_predicates(kind, byte, source))
                .or_else(|| {
                    children
                        .get(3)
                        .and_then(|child| runtime(child, byte, source))
                });
        }
        _ => {}
    }
    let parts = match head(node) {
        "call" | "unsafe-call" => children
            .get(1)
            .filter(|callee| symbol(callee).is_some())
            .map(|callee| (callee, children.get(2))),
        _ if children.len() == 2
            && children
                .first()
                .and_then(symbol)
                .is_some_and(crate::surface_syntax::callable_name)
            && crate::named_argument_list(&children[1].expr) =>
        {
            Some((&children[0], Some(&children[1])))
        }
        _ => None,
    };
    if let Some((callee, arguments)) = parts {
        if byte < callee.span.end {
            return None;
        }
        if let Some(arguments) = arguments {
            for pair in &arguments.children {
                if contains(pair, byte, source) {
                    if let Some(call) = pair
                        .children
                        .get(1)
                        .and_then(|value| runtime(value, byte, source))
                    {
                        return Some(call);
                    }
                    return Some((
                        callee.span,
                        pair.children.first().and_then(symbol).map(str::to_owned),
                    ));
                }
            }
        }
        return Some((callee.span, None));
    }
    if let Some(callee) = children.first() {
        if let Some(name) = symbol(callee).filter(|name| {
            // Infix lowering also creates scalar-operation heads, but their
            // source is punctuation rather than an authored callable token.
            source.get(callee.span.start..callee.span.end) == Some(*name)
        }) {
            if let Ok(Some(declaration)) = crate::intrinsics::declaration(name) {
                if byte < callee.span.end {
                    return None;
                }
                let operands = &children[1..];
                if let Some(nested) = operands
                    .iter()
                    .find_map(|operand| runtime(operand, byte, source))
                {
                    return Some(nested);
                }
                let index = operands
                    .iter()
                    .position(|operand| byte <= operand.span.end)
                    .unwrap_or(operands.len());
                return Some((
                    callee.span,
                    declaration
                        .parameters
                        .get(index)
                        .map(|parameter| parameter.name.clone()),
                ));
            }
        }
    }
    children
        .iter()
        .find_map(|child| runtime(child, byte, source))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Runtime expressions are probed inside a source declaration; raw quoted
    // syntax in the expression remains data for the signature scanner.
    fn source_unit(source: &str) -> String {
        if source.trim_start().starts_with('#') {
            source.to_owned()
        } else {
            format!(
                "#fn probe {{ #params = (); #returns = #u64; #body = (\n{}",
                source.lines()
                    .map(|line| format!("  {line}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        }
    }

    fn locate(source: &str) -> (String, Option<String>) {
        let source = source_unit(source);
        let byte = source.find('|').unwrap();
        let source = source.replacen('|', "", 1);
        let call = call(&source, byte).unwrap_or_else(|| panic!("no call: {source}"));
        (
            source[call.callee.start..call.callee.end].to_owned(),
            call.argument,
        )
    }

    #[test]
    fn canonical_surface_layout_and_punned_calls_keep_named_arguments() {
        for source in [
            "(#call choose ((right 2|) (left 1)))",
            "(#unsafe-call choose ((right 2|) (left 1)))",
            "(choose ((right 2|) (left 1)))",
            "choose { right = 2|; left = 1; }",
            "(#call choose { right = 2|; left = 1; })",
            "(#call choose (($ ri|ght) ($ left)))",
            "#fn main { #params = {}; #returns = #u64; #body:\n  #return choose {\n    right:\n      2|\n    left = 1;\n  };\n}",
            "(#return : choose : : right 2|)",
        ] {
            assert_eq!(locate(source), ("choose".into(), Some("right".into())), "{source}");
        }
    }

    #[test]
    fn nested_calls_select_innermost_active_runtime_call() {
        assert_eq!(
            locate("(#call outer ((value (#u64::add-wrap 1 (#call inner ((item 2|)))))))"),
            ("inner".into(), Some("item".into()))
        );
        assert_eq!(
            locate("(#call outer ((value (#call inner ((item 2)))|)))"),
            ("outer".into(), Some("value".into()))
        );
    }

    #[test]
    fn refinement_type_predicates_keep_runtime_call_roles() {
        for source in [
            "#type Refined (#where (value #u64) (#call valid ((input value|))))\n",
            "#fn work { #params = ((value (#where (item #u64) (valid ((input item|)))))); #returns = #u64; #body = ( (#return value) ); }\n",
            "#struct Refined () ((field (#where (item #u64) (valid ((input item|))))))\n",
        ] {
            assert_eq!(locate(source), ("valid".into(), Some("input".into())), "{source}");
        }
        let source = "#type Refined (valid ((input item)))\n";
        assert!(call(source, source.find("item").unwrap()).is_none());
    }

    #[test]
    fn bare_function_names_do_not_become_keyword_roles() {
        for name in [
            "type", "alias", "fn", "call", "syntax", "struct", "enum", "where", "let",
        ] {
            let source = format!("({name} ((value 1|)))");
            assert_eq!(locate(&source), (name.to_owned(), Some("value".into())));
        }
        for source in [
            "#type ((value 1))\n",
            "#alias ((value 1))\n",
            "#fn ((value 1))\n",
        ] {
            assert!(
                call(source, source.find('1').unwrap()).is_none(),
                "{source}"
            );
        }
    }

    #[test]
    fn positional_scalar_intrinsics_use_compiler_parameter_order() {
        for (source, callee, argument) in [
            ("(#u64::add-wrap 1| 2)", "#u64::add-wrap", "left"),
            ("(#u64::add-wrap 1 2|)", "#u64::add-wrap", "right"),
            ("(#bool::not tru|e)", "#bool::not", "value"),
            ("(#u64::lt 1 2|)", "#u64::lt", "right"),
            ("(#u64::add-wrap 1 |", "#u64::add-wrap", "right"),
            ("(#u64::add-wrap |", "#u64::add-wrap", "left"),
            (
                "(#call choose ((right (#u64::add-wrap 1 2|))))",
                "#u64::add-wrap",
                "right",
            ),
            (
                "(#u64::add-wrap 1 (#call nested ((item 2|))))",
                "nested",
                "item",
            ),
            (
                "(#call choose ((right [#u64 #wrap; 1 + 2|])))",
                "choose",
                "right",
            ),
        ] {
            assert_eq!(
                locate(source),
                (callee.into(), Some(argument.into())),
                "{source}"
            );
        }
        for source in [
            "(#u64::add 1 2|)",
            "(#bool::and true false|)",
            "(#u64::add-wrap 1 2)|",
            "'(#u64::add-wrap 1 2|)",
            "#generate generator ((value (#u64::add-wrap 1 2|)))\n",
        ] {
            let source = source_unit(source);
            let byte = source.find('|').unwrap();
            let source = source.replacen('|', "", 1);
            assert!(call(&source, byte).is_none(), "{source}");
        }
    }

    #[test]
    fn incomplete_suffixes_preserve_callee_offsets() {
        for source in [
            "(#call choose|",
            "(#call choose (|",
            "(#call choose ((right|",
            "#fn main { #params = (); #returns = #u64; #body = ( (#return (#call choose ((right 2|",
            "choose { right = |",
            "choose { right|",
            "choose { right = 2|",
            "#fn main { #params = (); #returns = #u64; #body = ( (#return : choose : : right |",
        ] {
            let (callee, _) = locate(source);
            assert_eq!(callee, "choose", "{source}");
        }
    }

    #[test]
    fn literal_and_generator_data_and_completed_calls_have_no_signature() {
        for source in [
            "'(#call choose ((right 2|)))",
            "`(#call choose ((right 2|)))",
            "#generate generator ((value (#call choose ((right 2|)))))\n",
            "#gn generator () (#call choose ((right 2|)))\n",
            "\"(#call choose ((right 2|)))\"",
            "// (#call choose ((right 2|)))",
            "(#call choose ((right 2)))|",
        ] {
            let source = source_unit(source);
            let byte = source.find('|').unwrap();
            let source = source.replacen('|', "", 1);
            assert!(call(&source, byte).is_none(), "{source}");
        }
        assert_eq!(
            locate("#generate generator ((value (#fn work () #u64 (#return (#call choose ((right 2|)))))))\n"),
            ("choose".into(), Some("right".into()))
        );
    }
}
