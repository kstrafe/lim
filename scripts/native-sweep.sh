#!/usr/bin/env bash
set -euo pipefail

# Use the production assembler/linker and compare exact declared outcomes.
ulimit -c 0
cargo test --test native_examples -- --nocapture
