# Machine-readable diagnostics

Pass `--diagnostic-format=json` anywhere in a compiler command to receive
newline-delimited JSON diagnostic objects on stderr. Human formatting remains
the default (`--diagnostic-format=human`). Successful output stays on stdout;
diagnostics never mix raw assembler/linker stderr into the JSON stream.
Subprocess output is captured in diagnostic notes.

Schema version 1 has these fields:

- `schema_version`: integer 1.
- `severity`: `error` or `warning`. Warnings do not change a successful exit status.
- `code`: stable high-level code, such as `E4000`, `W8000` (unused type),
  or `W8001` (a contract covering no inputs).
- `category`: `lex`, `parse`, `generator`, `type`, `borrow`, `linear`,
  `unsafe`, `proof`, `codegen`, `link`, `cli` (`E7000`), or `unused_type` (`W8000`).
- `proof_outcome`: a typed proof failure outcome, or null for other diagnostics
  and nonfatal proof-coverage warnings. Successful theorem checks have their
  own stdout record; a warning is not a proof failure.
- `message`: explanatory prose; do not use it as a machine identifier.
- `path`: source path, or an empty string when no source applies.
- `location`: a location object, or null for failures without source ranges.
- `labels`: primary and secondary messages and locations.
- `expansion_provenance`: invocation locations, innermost first, when the
  compiler has a generated-source map for the failure.
- `notes`: additional strings, including captured tool output.

A location contains `path`, compilation-local `source_id`, `byte_start`,
`byte_end`, `line`, and `column`. Ranges are zero-based, half-open UTF-8 byte
offsets in that source file. Lines and columns are one-based; columns count
Unicode scalar values, not UTF-8 bytes, grapheme clusters, or terminal cells.
Consumers should use byte ranges to underline original text. Human diagnostic
rendering separately accounts for tabs and displayed character widths.

Imported and generated sources keep their own paths and ranges. Cold and
cached semantic expansion failures carry the same invocation provenance.
CLI/IO failures can lack a source range; consumers must handle null locations.
## Ownership and unsafe source identity

Borrow, linear, and unsafe violations carry the failing AST node identity
and a structural focus (operand, operation, or binding). The immutable
analysis pass resolves these identities through named-call reordering,
aggregate lowering, shadowing, and nested statement forms into source spans.
English diagnostic messages are not searched for names or error kinds.
Loans retain their creation site and moved places retain their consuming
site; conflicts can label those sites separately from the failing access.
Diagnostic-only scope guards restore the active site on return or unwinding
and isolate concurrent compiler calls. No AST address escapes into the public
diagnostic or cache. Regression tests replace error wording while checking
the exact primary and secondary ranges.
