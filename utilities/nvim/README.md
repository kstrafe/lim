# Lim syntax for Vim and Neovim

Add this directory to your runtime path before enabling filetype detection and
syntax highlighting, or copy `ftdetect/lim.vim` and `syntax/lim.vim` into your
editor's corresponding runtime directories.

Keywords use separate highlight groups, linked to your colorscheme's standard
groups by default:

| Lim group | Examples | Default link |
| --- | --- | --- |
| `limType` | `#u64`, `#bool`, `#f32` | `Type` |
| `limTypeForm` | `#ref-mut`, `#slice` | `Type` |
| `limOperator` | `#u64.+.wrap`, `#u128.%` | `Operator` |
| `limDeclaration` | `#fn`, `#let-mut`, `#struct` | `StorageClass` |
| `limConditional` | `#if`, `#case`, `#let-else` | `Conditional` |
| `limRepeat` | `#while`, `#loop` | `Repeat` |
| `limControl` | `#return`, `#break` | `Statement` |
| `limUnsafe` | `#unsafe`, `#unsafe-fn` | `Exception` |
| `limGeneratorKeyword` | `#gn`, `#gn-for-each` | `PreProc` |
| `limCfg` | `#cfg-if`, `#cfg-is` | `PreProc` |
| `limGenerated` | `@vec`, `@async-fn` | `Special` |
| `limKeyword` | Other `#` builtins | `Keyword` |

Colors depend on your colorscheme. Override individual groups after loading it,
for example `highlight limType guifg=#80c0ff ctermfg=117`.
Bare names such as `u64` are ordinary identifiers, not builtin types.

## Language server

Enable `filetype plugin on` and add this directory to your runtime path to load
`ftplugin/lim.lua`. It uses Neovim's built-in LSP client (`vim.lsp.start` and
`vim.fs.root`, Neovim 0.10 or newer) and runs `lim lsp`. Set
`vim.g.lim_lsp_cmd = { '/absolute/path/to/lim', 'lsp' }` before opening a Lim
buffer to select a development binary. Additional `--cfg KEY=VALUE` and
`--module-path PATH` arguments can be included in that command list.
Set `vim.g.lim_lsp_autostart = false` before opening a Lim buffer when
`nvim-lspconfig` or another integration manages server startup. This keeps
the bundled syntax highlighting without starting a duplicate client.
Explicit cfg settings apply to the whole server session. The server also
discovers the nearest `lim.project` for each buffer and adds its source root
and module directories, just like the build CLI.

The server checks full unsaved buffers, including open imported files that do
not exist on disk, and publishes compiler diagnostics with UTF-16 positions.
Checks do not save buffers or create generator cache artifacts. Saving and
closing a document rechecks open importers; closing clears stale diagnostics.
Formatting returns a full-document edit using the compiler formatter; apply it
with `vim.lsp.buf.format()`. Formatter options are accepted but the compiler's
canonical style determines the result.

Document symbols cover direct top-level function, struct, enum, and global
declarations. Goto definition resolves explicit `#call` callee symbols to a
unique same-document top-level function declaration, and declaration names to
their own span. Generated calls and explicit type annotations/struct-literal
types resolve through the checked expansion, including unsaved imported buffers.
Navigation publishes the selected expanded source as a content-addressed
`.lim/generated/editor-*.lim` snapshot next to the requesting source, with
invocation provenance and exact UTF-16 name ranges. Existing identical snapshots
are not rewritten; diagnostic checks remain write-free and no generator-cache
entries are created. Invalid expansions return no generated location.
Other references, locals, fields, ordinary imported symbols, quoted templates,
and ambiguous duplicate functions return no location.
Generated diagnostics point to file-backed invocation provenance;
expansion provenance is also included as related diagnostic locations.
No completion, rename, incremental edits, filesystem watching, or workspace
symbol index is provided. Changes to unopened files are picked up on the next
open-buffer change/save/close event. The server handles local absolute `file:`
URIs and rejects remote authorities and malformed percent escapes.

Run the highlighting regression tests from the repository root:

```sh
nvim --headless -u NONE -i NONE -n -S utilities/nvim/tests/syntax.vim
```
