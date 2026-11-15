//! Default layout for concrete surface syntax. The reader remains authoritative:
//! speculative whitespace changes are returned only after a syntax roundtrip.
use crate::{Expr, SpannedExpr, TokenKind};

const WIDTH: usize = 100;
const STEP: usize = 2;

/// Format one source form, without its surrounding comments or final newline.
/// Both source-unit and standalone-syntax callers can use this entry point.
pub(crate) fn format_surface(node: &SpannedExpr, source: &str) -> String {
    let original = &source[node.span.start..node.span.end];
    let mut quoted = Vec::new();
    quote_spans(node, &mut quoted);
    let Some(tokens) = tokens(original, node.span.start, &quoted) else {
        return crate::surface_syntax::format_surface(node, source);
    };
    let candidate = proposal(original, &tokens);
    // Check the formatter's fixed point without calling either public
    // formatting entry point (which would recurse through this module).
    if let Ok(forms) = crate::parse(&candidate) {
        let mut quoted = Vec::new();
        for form in &forms {
            quote_spans(form, &mut quoted);
        }
        if let Some(tokens) = self::tokens(&candidate, 0, &quoted) {
            if proposal(&candidate, &tokens) == candidate {
                return candidate;
            }
        }
    }
    crate::surface_syntax::format_surface(node, source)
}

fn proposal(original: &str, tokens: &[Token<'_>]) -> String {
    let mut cursor = 0;
    let nodes = tree(tokens, &mut cursor, None);
    let candidate = sequence(&nodes, original, 0, true);
    if equivalent(original, &candidate) {
        return candidate;
    }
    // Colon operands end at physical line boundaries. Reindent those lines
    // without moving their boundaries when structural layout would change them.
    let candidate = layout_lines(original, tokens);
    if equivalent(original, &candidate) {
        return candidate;
    }
    original.to_owned()
}

/// Call after the outer formatter's conventional declaration spacing, before
/// emitting a form. `gap` starts at its last emitted source/comment cursor.
pub(crate) fn preserve_blank_lines(output: &mut String, gap: &str) {
    let wanted = gap.bytes().filter(|byte| *byte == b'\n').count();
    let present = output.bytes().rev().take_while(|byte| *byte == b'\n').count();
    for _ in present..wanted {
        output.push('\n');
    }
}

fn equivalent(before: &str, after: &str) -> bool {
    let spellings = |text: &str| {
        crate::lex(text).ok().map(|tokens| {
            tokens.into_iter()
                .map(|token| text[token.span.start..token.span.end].to_owned())
                .collect::<Vec<_>>()
        })
    };
    let comments = |text: &str| -> Vec<String> {
        crate::source_comments(text).into_iter()
            .map(|comment| comment.text)
            .collect::<Vec<_>>()
    };
    let blanks = |text: &str| text.lines().filter(|line| line.trim().is_empty()).count();
    if spellings(before) != spellings(after)
        || comments(before) != comments(after)
        || blanks(before) != blanks(after)
    {
        return false;
    }
    if let Ok(before) = crate::parse_source_unit(before) {
        let Ok(after) = crate::parse_source_unit(after) else {
            return false;
        };
        if !before.iter().map(|node| &node.expr)
            .eq(after.iter().map(|node| &node.expr))
        {
            return false;
        }
    }
    let expressions = |text: &str| {
        crate::parse(text).map(|forms| forms.into_iter().map(|node| node.expr).collect::<Vec<_>>())
    };
    match (expressions(before), expressions(after)) {
        (Ok(before), Ok(after)) => before == after,
        _ => false,
    }
}

fn quote_spans(node: &SpannedExpr, spans: &mut Vec<(usize, usize)>) {
    if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
        spans.push((node.span.start, node.span.end));
    } else {
        for child in &node.children {
            quote_spans(child, spans);
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Open(char),
    Close(char),
    Atom,
    Comment,
    Frozen,
}

#[derive(Clone)]
struct Token<'a> {
    text: &'a str,
    start: usize,
    end: usize,
    kind: Kind,
}

fn tokens<'a>(source: &'a str, base: usize, quoted: &[(usize, usize)]) -> Option<Vec<Token<'a>>> {
    let mut result = Vec::new();
    for token in crate::lex(source).ok()? {
        if quoted.iter().any(|&(start, end)| {
            start <= base + token.span.start && base + token.span.start < end
        }) {
            continue;
        }
        let kind = match token.kind {
            TokenKind::LParen => Kind::Open('('),
            TokenKind::RParen => Kind::Close(')'),
            TokenKind::LBrace => Kind::Open('{'),
            TokenKind::RBrace => Kind::Close('}'),
            TokenKind::LBracket => Kind::Open('['),
            TokenKind::RBracket => Kind::Close(']'),
            TokenKind::String(_) | TokenKind::Char(_) => Kind::Frozen,
            _ => Kind::Atom,
        };
        result.push(Token {
            text: &source[token.span.start..token.span.end],
            start: token.span.start,
            end: token.span.end,
            kind,
        });
    }
    for &(start, end) in quoted {
        let (start, end) = (start.checked_sub(base)?, end.checked_sub(base)?);
        result.push(Token {
            text: source.get(start..end)?,
            start,
            end,
            kind: Kind::Frozen,
        });
    }
    for comment in crate::source_comments(source) {
        if quoted.iter().any(|&(start, end)| {
            start <= base + comment.span.start && base + comment.span.start < end
        }) {
            continue;
        }
        result.push(Token {
            text: &source[comment.span.start..comment.span.end],
            start: comment.span.start,
            end: comment.span.end,
            kind: Kind::Comment,
        });
    }
    result.sort_by_key(|token| token.start);
    Some(result)
}

struct Node<'a> {
    first: Token<'a>,
    last: Token<'a>,
    children: Option<Vec<Node<'a>>>,
}

fn tree<'a>(tokens: &[Token<'a>], cursor: &mut usize, closing: Option<char>) -> Vec<Node<'a>> {
    let mut result = Vec::new();
    while let Some(first) = tokens.get(*cursor) {
        if matches!(first.kind, Kind::Close(c) if Some(c) == closing) {
            break;
        }
        let first = first.clone();
        *cursor += 1;
        let (children, last) = if let Kind::Open(open) = first.kind {
            let close = match open {
                '(' => ')',
                '{' => '}',
                _ => ']',
            };
            let children = tree(tokens, cursor, Some(close));
            let last = tokens.get(*cursor).cloned().unwrap_or_else(|| first.clone());
            *cursor += usize::from(*cursor < tokens.len());
            (Some(children), last)
        } else {
            (None, first.clone())
        };
        result.push(Node { first, last, children });
    }
    result
}

fn gap_lines(source: &str, left: usize, right: usize) -> usize {
    source[left..right].bytes().filter(|byte| *byte == b'\n').count()
}

fn colon(node: &Node<'_>) -> bool {
    node.children.is_none()
        && node.first.kind == Kind::Atom
        && (node.first.text == ":"
            || (node.first.text.ends_with(':') && !node.first.text.ends_with("::")))
}

fn flat(node: &Node<'_>, source: &str) -> Option<String> {
    if node.first.kind == Kind::Comment || node.first.text.contains('\n') {
        return None;
    }
    let Some(children) = &node.children else {
        return Some(node.first.text.to_owned());
    };
    if node.first.text == "{" && children.iter().any(|child| {
        matches!(child.first.text, "#params" | "#params:" | "#body" | "#body:")
    }) {
        return None;
    }
    if body_header(children).is_some_and(|header| children.len() > header) {
        return None;
    }
    if children.windows(2).any(|pair| {
        let lines = gap_lines(source, pair[0].last.end, pair[1].first.start);
        lines > 1 || (lines > 0 && children.iter().any(colon))
    }) {
        return None;
    }
    let mut text = node.first.text.to_owned();
    if node.first.text == "{" && !children.is_empty() {
        text.push(' ');
    }
    for (index, child) in children.iter().enumerate() {
        if index > 0 && child.first.text != ";" {
            text.push(' ');
        }
        text.push_str(&flat(child, source)?);
    }
    if node.first.text == "{" && !children.is_empty() {
        text.push(' ');
    }
    text.push_str(node.last.text);
    Some(text)
}

fn column(text: &str) -> usize {
    text.rsplit('\n').next().unwrap_or("").chars().count()
}

fn body_header(children: &[Node<'_>]) -> Option<usize> {
    match children.first()?.first.text {
        "#while" | "#if" | "#match" | "#case" => Some(2),
        "#for" | "#for-range" => Some(4),
        "#loop" | "#block" | "#unsafe" => Some(1),
        _ => None,
    }
}

fn render(node: &Node<'_>, source: &str, indent: usize, start_column: usize) -> String {
    let Some(children) = &node.children else {
        return node.first.text.to_owned();
    };
    let record = node.first.text == "{" && children.iter().any(|child| {
        matches!(child.first.text, "#params" | "#params:" | "#body" | "#body:")
    });
    let separators = children.iter().filter(|child| child.first.text == ";").count();
    let semicolon_list = separators > 1
        && (node.first.text == "("
            || (node.first.text == "{" && flat(node, source)
                .map_or(true, |text| start_column + text.chars().count() > WIDTH)));
    let body = body_header(children).filter(|&header| children.len() > header);
    let flat = flat(node, source);
    if !record && !semicolon_list && body.is_none() {
        if let Some(flat) = flat.as_ref().filter(|text| start_column + text.chars().count() <= WIDTH) {
            return flat.clone();
        }
    }
    let list_of_forms = node.first.text == "("
        && children.len() > 1
        && children.iter().all(|child| child.children.is_some())
        && children.iter().any(|child| child.children.as_ref().is_some_and(|parts| {
            parts.first().is_some_and(|part| matches!(part.first.text,
                "#let" | "#let-mut" | "#return" | "#set" | "#while" | "#for"
                    | "#for-range" | "#loop" | "#if" | "#break" | "#continue"))
        }));
    if record || semicolon_list || list_of_forms || body.is_some() {
        let header = body.unwrap_or(0).min(children.len());
        let mut output = node.first.text.to_owned();
        if header > 0 {
            output.push_str(&sequence(&children[..header], source, indent, false));
        }
        let mut row_start = header;
        for index in header..children.len() {
            let child = &children[index];
            let boundary = child.first.text == ";"
                || (!record && !semicolon_list)
                || child.first.kind == Kind::Comment;
            if !boundary && index + 1 < children.len() {
                continue;
            }
            let end = index + 1;
            output.push('\n');
            if row_start > header
                && gap_lines(source,
                    children[row_start - 1].last.end,
                    children[row_start].first.start) > 1
            {
                output.push('\n');
            }
            output.push_str(&" ".repeat(indent + STEP));
            output.push_str(&sequence(
                &children[row_start..end], source, indent + STEP, true,
            ));
            row_start = end;
        }
        output.push('\n');
        output.push_str(&" ".repeat(indent));
        output.push_str(node.last.text);
        return output;
    }
    let mut output = node.first.text.to_owned();
    let inner = sequence_at(
        children,
        source,
        indent + STEP,
        start_column + 1 + usize::from(node.first.text == "{" && !children.is_empty()),
        true,
    );
    if node.first.text == "{" && !children.is_empty() {
        output.push(' ');
    }
    output.push_str(&inner);
    if node.first.text == "{" && !children.is_empty() {
        output.push(' ');
    }
    output.push_str(node.last.text);
    output
}

fn sequence(nodes: &[Node<'_>], source: &str, indent: usize, wrap: bool) -> String {
    sequence_at(nodes, source, indent, indent, wrap)
}

fn sequence_at(
    nodes: &[Node<'_>],
    source: &str,
    indent: usize,
    start_column: usize,
    wrap: bool,
) -> String {
    let mut output = String::new();
    // Do not introduce a newline into an implicit operand. Explicit child
    // delimiters still provide safe opportunities for wrapping their contents.
    let wrap = wrap && !nodes.iter().any(colon);
    for (index, node) in nodes.iter().enumerate() {
        let previous = index.checked_sub(1).map(|index| &nodes[index]);
        let blank = previous.is_some_and(|previous| {
            gap_lines(source, previous.last.end, node.first.start) > 1
        });
        let comment_line = previous.is_some_and(|previous| {
            previous.first.kind == Kind::Comment
                || (node.first.kind == Kind::Comment
                    && gap_lines(source, previous.last.end, node.first.start) > 0)
        });
        let space = index > 0 && node.first.text != ";";
        let current_column = if output.contains('\n') {
            column(&output)
        } else {
            start_column + column(&output)
        };
        let mut text = render(node, source, indent, current_column + usize::from(space));
        let overflow = wrap && space && current_column + 1
            + text.lines().next().unwrap_or("").chars().count() > WIDTH - STEP;
        if blank || comment_line || overflow {
            output.push('\n');
            if blank {
                output.push('\n');
            }
            let continuation = indent.max(STEP);
            output.push_str(&" ".repeat(continuation));
            text = render(node, source, continuation, continuation);
        } else if space {
            output.push(' ');
        }
        output.push_str(&text);
    }
    output
}

/// Normalize indentation ranks while retaining layout's physical line breaks.
fn layout_lines(source: &str, tokens: &[Token<'_>]) -> String {
    let mut output = String::new();
    let mut levels = vec![0];
    let mut offset = 0;
    for (index, line) in source.split_inclusive('\n').enumerate() {
        let end = offset + line.len();
        let protected = tokens.iter().any(|token| {
            token.kind == Kind::Frozen && token.text.contains('\n')
                && token.start < end && token.end > offset
        });
        if protected {
            output.push_str(line);
            offset = end;
            continue;
        }
        let leading = line.len() - line.trim_start_matches([' ', '\t']).len();
        let content = line[leading..].trim_end_matches(['\r', '\n', ' ', '\t']);
        if content.is_empty() {
            if line.ends_with('\n') {
                output.push('\n');
            }
            offset = end;
            continue;
        }
        if index > 0 {
            while levels.len() > 1 && leading < *levels.last().unwrap() {
                levels.pop();
            }
            if leading > *levels.last().unwrap() {
                levels.push(leading);
            }
            output.push_str(&" ".repeat((levels.len() - 1) * STEP));
        }
        // Concrete spellings, including comments, remain untouched. Only gaps
        // between tokens on this line are normalized.
        let items = tokens.iter()
            .filter(|token| token.start >= offset && token.end <= end);

        let mut previous: Option<&Token<'_>> = None;
        for token in items {
            if previous.is_some_and(|previous| {
                !matches!(token.kind, Kind::Close(')' | ']'))
                    && token.text != ";"
                    && !matches!(previous.kind, Kind::Open('(' | '['))
            }) {
                output.push(' ');
            }
            output.push_str(token.text);
            previous = Some(token);
        }
        if line.ends_with('\n') {
            output.push('\n');
        }
        offset = end;
    }
    output.trim_end_matches('\n').to_owned()
}
