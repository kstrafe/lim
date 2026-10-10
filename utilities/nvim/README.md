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

Run the highlighting regression tests from the repository root:

```sh
nvim --headless -u NONE -i NONE -n -S utilities/nvim/tests/syntax.vim
```
