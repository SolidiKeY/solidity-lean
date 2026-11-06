# Compiled verifier dependencies

The packaged verifier includes Lean 4.24.0 (Apache-2.0), GMP 6.2.1
(LGPL-3.0-or-later or GPL-2.0-or-later), libuv and Emscripten 4.0.15 runtime
components. License texts and upstream notices are in `runtime/direct/licenses/` and
`runtime/native/licenses/`. The optional standalone native executable uses the
pinned Lean runtime and is built by `scripts/build-direct-native.py`.

Corresponding sources and rebuild instructions:

- https://github.com/leanprover/lean4/tree/v4.24.0
- https://github.com/alisw/GMP/tree/v6.2.1
- https://github.com/emscripten-core/emscripten/tree/4.0.15
- https://github.com/SolidiKeY/solidity-lean/blob/master/docs/compact-verifier.md

The compact verifier is built by `scripts/build-direct-runtime.py` and the
browser toolchain in `web/tools/lean-wasm/`. It can be rebuilt and relinked
with modified runtime libraries using those sources and scripts.
