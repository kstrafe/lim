# Check command

`lim --check INPUT [--cfg KEY=VALUE]... [--target TARGET]` runs Lim's normal
front end and semantic validation without writing an assembly file or native
binary. It loads imports relative to the source and applies the `source-root`
and `module-path` settings from `lim.project`. `--target` is accepted and
validated for command-line compatibility, but check mode is target-independent:
it does not invoke the native backend or perform target ABI/code-generation
checks. Compile-time selection is controlled by explicit `--cfg` options.

The check includes lexing, parsing, generator expansion, type checking, borrow
checking, and linearity checking. Generator cache and inspectable generated
sources may be written under the input directory's `.lim` directory, matching
normal compilation. Diagnostics go to stderr; append
`--diagnostic-format=json` for one JSON diagnostic record with source paths and
byte spans.

Example:

```sh
lim --check src/main.lim --cfg feature=enabled --target x86_64-sysv \
  --diagnostic-format=json
```
