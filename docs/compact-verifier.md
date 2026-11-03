# Compact compiled verifier

Version 0.5.4 runs supported Solidity specifications through Lean-generated C
compiled to a standalone WebAssembly module. The website and desktop extension
use the same module. It imports no Lean environment, constructs no Lean syntax
for a supported request, and creates no per-result kernel certificate. The
result is a trusted verifier decision: correct, wrong with a concrete model
prestate, or unknown. Explicit `certify: true` and precondition-audit requests
continue through the general frontend.

## What changed

`Tools.DirectRuntime` reads compiler ASTs into the existing raw Solidity source
syntax and uses the existing intrinsic `specObligation`. It does not introduce
an untyped verification IR. Admission deliberately supports a small fragment:
scalar `uint256`, `int256` and `bool`, ordinary assignments, blocks, conditionals,
returns, builtin require/assert, and scalar requires/ensures specifications.
Loops, calls, inheritance, reference values, narrow integers and unsupported
compiler constant expressions use the general frontend. An unsupported function
body currently sends its whole contract to that fallback, including a request
selecting another function.

`Tools.DirectArithmetic` performs bounded affine consequence propagation and a
bounded derivative walk over the existing exact input reduction. Its successful
branches carry Lean soundness proofs that the compiler erases. Exhaustion is
undecided. This closes the simple maximum/store-maximum/choice examples without
invoking the tactic frontend. Source proofs are checked during development;
there is no proof construction or kernel replay for each IDE result.

The generated-C closure extractor retains reachable functions, closure values,
ordered closed-data initializers and runtime ABI callbacks. It rejects unknown
initializers and unresolved Lean symbols, and removes unused frontend registration
and environment code. The resulting optimized module is about 15 MB, compared
with 129 MB for the unpruned prototype. The complete offline HTML remains about
900 MB because it also embeds the general verifier and its libraries.

Supported desktop requests do not run Lake. A fallback request builds the general
frontend lazily, retaining source/runtime freshness checks and the request's
absolute deadline. Intermediate artifacts from that owned build do not interrupt
it. Repository content digests are cached by file identity and nanosecond
metadata, normal requests scan the frontend’s transitive dependency closure, and duplicate
scans within one verification request were removed;
a final freshness check still precedes publication. Build input checks continue
to scan all project sources.

Edits discard obsolete results immediately. Short running browser checks may
drain while keeping the loaded module; a one-second grace limit stops a stuck
worker. Shared startup can continue after an individual deadline. Hard execution
timeouts and explicit restarts replace the worker.

## Rebuild

Build the pinned Lean/GMP browser runtime first with
`bash web/tools/build-lean-browser.sh`. With the matching Emscripten SDK activated:

```sh
LEAN_NUM_THREADS=1 python3 scripts/build-direct-runtime.py \
  /path/to/native/lean-4.24.0 \
  web/.lean-browser-build/build64/stage1 \
  .lake/direct-runtime
SOLIDITY_BROWSER_DIRECT="$PWD/.lake/direct-runtime" \
SOLIDITY_BROWSER_LEAN="$PWD/web/.lean-browser-build/assets" \
  npm run build --prefix web
npm run build:single --prefix web
```

The second argument must contain the browser runtime's `lib/temp` generated C,
`lib/lean/libleanrt.a`, libuv and GMP libraries. Set `LEAN_WASM_SOURCE` when the
source checkout is elsewhere. The builder verifies both native and browser Lean
commits, records compiler/header/runtime/C/source hashes, and checks that inputs
did not change during compilation. It invokes the required Lake target itself.

For a VSIX, copy `direct.js`, `direct.wasm` and `build.json` to
`vscode/runtime/direct/`, include the Lean/GMP/Emscripten license texts and upstream
notices, and package the extension. Generated binaries are excluded from Git.
The desktop loader accepts only a matching toolchain and complete project import
closure. `SOLIDITY_LEAN_DIRECT=0` disables the compact route for comparisons;
`SOLIDITY_LEAN_DIRECT_DIR` selects a different matching build. Missing, stale,
unsupported or undecided compact results use the general frontend.

## Validation and measurements

The benchmark scripts keep cached report retrieval separate from fresh proof
work. `vscode/test/compare-dafny-speed.cjs` uses persistent servers, one worker/core,
fresh document URIs and method names, and disables Dafny's verification cache.
It waits for current-document resolution and final verification status in either
notification order. Every Solidity result is checked against the source hash;
all 18 must use one compiled worker. This is a comparison of small source
submissions, not identical language semantics or algorithms. In particular,
Dafny's increment precondition excludes entries where Solidity would revert.

See the recorded measurements in the adjacent benchmark JSON files and the
current results in [native-extension-performance.md](native-extension-performance.md).
The compact route does not establish universal Dafny or SolKey performance.

Admission regressions cover lexical scopes and shadowing, user functions named
require/assert, rational compiler constants, unnamed default returns, positive
and negative specifications, and reverting executions. A read-only finder and
skeptic review found scope, builtin-identity, stale-job, worker ownership, build
race and deadline issues; those confirmed findings were fixed and covered.
The final semantic review found no further blocker.
