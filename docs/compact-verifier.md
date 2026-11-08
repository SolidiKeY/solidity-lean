# Compiled verifier

The implementation is [Tools/DirectRuntime.lean](../Solidity/Tools/DirectRuntime.lean)
and the corresponding native/browser build scripts. Admission and regression
controls define support. Unsupported and undecided requests remain unknown.
An ordinary compiled-verifier result is a trusted executable decision, not a
fresh kernel certificate; `certify: true` uses a separate checked path.

## Build

Use the repository's pinned native Lean prefix and matching source checkout:

```sh
LEAN_NUM_THREADS=1 python3 scripts/build-direct-native.py \
  /path/to/pinned-lean /path/to/matching-lean-source .lake/direct-native
bash web/tools/build-lean-browser.sh --compact-only
SOLIDITY_BROWSER_DIRECT="$PWD/web/.lean-browser-build/direct" npm run build --prefix web
npm run build:single --prefix web
```

Observe [resource bounds](refactoring-progress.md#resource-bounds-and-resuming-work).
Keep source/compiler/runtime freshness checks. A stale binary, scalar harness
guard or successful AST admission cannot substitute for source semantics or
whole-pipeline correspondence.
