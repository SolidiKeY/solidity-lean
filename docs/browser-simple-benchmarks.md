# Small-program verifier measurements

The browser is still slower than SolKey. Reusing successful audits of immutable
imports improves warm proof checking substantially; it does not fix cold startup.
The detailed measurements separate that improvement from cached proof results.

## Inputs and method

Six programs cover a constant return, identity, storage assignment, increment,
a two-way maximum, and a false constant postcondition. Both verifiers receive
identical source bytes from `web/test/simple-programs.cjs`, with Solidity 0.8.34
and the pinned compiler SHA. Return values are named because SolKey refuses an
obligation for an unnamed return. All five positive cases prove; the false case
stays open in SolKey and pending in Lean.

Each suite runs three rounds. A different trailing comment changes the source
hash in every round. The browser asserts the returned SHA against the edited
source and requires fresh search timings. SolKey's harness hashes each input
before invoking Java; its server retains the JVM, rules and compiler, but each
new input still gets a fresh proof session. Native Lean retains its imports in
one process and uses a distinct namespace for every obligation. No proof-result
cache lookup is included in the measured proof executions.

The warm figures below are the median of rounds 1 and 2, after the first round.
These are small local samples, not throughput guarantees. Browser proof time
covers the proof RPC, including model import, search, kernel checking and axiom
audit; its separate compiler/editor synchronization time is also retained in
the evidence. SolKey wall time includes its compiler and request transport.
Native command time sums model import, obligation generation and testing, and
excludes the one-time imported environment load.

The machine runs Linux x86-64, Lean 4.24.0 at
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, and SolKey at
`473da8944ca7329e6b76819863591407db26e7ec`. Java is Temurin 21.0.9,
with Graal compiler 23.1.7. Lean uses one thread and a 128 MiB thread stack;
Java has a 2 GiB heap and two active processors. Native builds run sequentially
in 4 GiB, no-swap containers. Checks retain the repository's 12 GiB available
memory reserve. The browser's Wasm linear-memory limit remains 4 GiB.

SolKey's optional Besu EVM execution dependency was unavailable under the
network policy. The [recorded patch](benchmarks/solkey-proof-only-build.patch)
excludes that runtime package and makes `--solc` EVM execution unavailable.
Its proof checker, strategy, rules and source compiler are unchanged. The build
uses the already available, checksum-verified compiler. The evidence records
the commit, exact patch/JAR hashes, Java version and input hashes.

## Results

| Program | Browser before (ms) | Browser after (ms) | Browser incl. compiler/sync (ms) | SolKey wall (ms) |
|---|---:|---:|---:|---:|
| constant | 2376 | 554 | 718 | 203 |
| identity | 2793 | 760 | 936 | 214 |
| assignment | 3248 | 1400 | 1570 | 170 |
| increment | 4162 | 2663 | 2848 | 277 |
| branch | 6188 | 4327 | 4504 | 299 |
| false-constant | 529 | 513 | 709 | 171 |

Fresh-page startup to a ready kernel took 17.84 s; the first
constant proof RPC took 17.17 s including the cold library import.
Page open through the first result took 35.21 s.
SolKey's separate cold JVM check took 10.32 s.
The audit memo improves warm checks; the cold path remains slow.

| Native Lean command time (ms) | Before memo | After memo | Compiled diagnostic (-O0) |
|---|---:|---:|---:|
| constant | 1765 | 403 | 321 |
| identity | 2097 | 533 | 465 |
| assignment | 2559 | 1001 | 898 |
| increment | 3227 | 1650 | 1399 |
| branch | 4072 | 2653 | 2464 |
| false-constant | 295 | 318 | 223 |

Full per-round timings, source hashes, artifact identities and phase events are
in [the machine-readable record](benchmarks/simple-programs-2026-11-02.json).
Individual reports retain their measured frontend/artifact hashes; the archive
also records the final reproduction-tool hashes.
The browser artifact uses the same optimized Wasm kernel as the previous port;
the project frontend remains interpreted in the website.

## What consumed the time

The original successful browser checks repeatedly spent about 1.6–1.8 seconds
walking the transitive axiom closure. The new policy memo remembers only checked
imported declarations from successful audits. Its key is the identity of the
nonempty imported module-data array, with the imported environment retained.
Generated contracts and proof declarations never enter the memo, so changed
programs and reused names are audited again. A different imported snapshot
invalidates the memo. Failed audits never extend it. Full counterexample axiom
inventories still use the original uncached collector.

The compiled native control builds all 312 project modules in the frontend
closure as C, loads them as a Lean plugin and retains kernel and axiom checks.
A marker in a separate diagnostic C copy confirms 18 measured command entries
actually executed compiled code. This is a measurement control, not a browser
backend. At `-O0`, compilation gives a modest improvement after audit reuse;
it does not remove the remaining multi-second branch check. This does not
establish the best possible native performance at higher optimization levels.

For the branch's final compiled diagnostic round, symbolic execution took
about 26 ms, goal-closing preparation 1,632 ms, final solving 157 ms and kernel
checking 412 ms. Lean's built-in profiler attributes most preparation time to
three `simp` passes. Thus being implemented in Lean is not an adequate
explanation for the measured delay: the main remaining cost is how this
frontend prepares typed goals for closing, plus the cold environment load.
The shared dynamic logic does not make those implementation costs identical.

Two further simplifier experiments were not promoted. Trying the solver earlier
did not improve the branch; combining the three passes helped assignment but
left the branch slow. A derivation-based route helped storage examples while
slowing the branch and false control. Their traces are retained locally under
`web/artifacts/simple-{early,combined}-profile.log` and the isolated scratch
probes remain outside the shipped implementation.

## Reproduce

Build the pinned browser assets using `web/tools/build-lean-browser.sh`, or use
already prepared matching assets as described in `web/README.md`. Build
`Solidity.Frontend.Testing` before generating native inputs. Apply the repository's
writer lock and resource guards to these commands; run heavy jobs sequentially.

```sh
node scripts/measure-simple.mjs .lake/simple-measurement
node scripts/measure-native.mjs .lake/simple-measurement
node web/test/measure-simple.cjs --single
node scripts/measure-solkey.mjs /path/to/pinned/solkey .lake/simple-measurement/inputs.json
node web/test/performance.cjs --single --benchmark
lake env lean -j1 --tstack=131072 tests/automation/ImportedAudit.lean
```

Set `SOLKEY_ROOT` and `SOLJSON_DIR` for input generation, `SOLKEY_JAVA_HOME` for
SolKey, `BENCH_REPEATS` for repeated measurements, and `BENCH_REPORT` for browser
output. Each runner creates its own report directories. To bypass Lake's source
freshness check for a deliberately frozen artifact, the native control accepts
`BENCH_LEAN=/path/to/pinned/bin/lean` with an explicit matching `LEAN_PATH` and `BENCH_FRONTEND` pointing to the
actual loaded `Solidity/Frontend/Testing.olean`.

For a fresh A/B comparison at this revision, apply
[the full-traversal control patch](benchmarks/disable-imported-audit-memo.patch),
rebuild the frontend and browser assets, and repeat the runners. It disables
only imported-audit reuse; every kernel and full axiom check remains. The
captured before-memo build predates the later fine-profiler option and is
identified separately in the evidence.

The optional native compilation control is:

```sh
python3 scripts/build-frontend-plugin.py /path/to/pinned/lean
BENCH_PLUGIN=.lake/frontend-native/libSolidity_Frontend_Testing.so \
  node scripts/measure-native.mjs .lake/simple-measurement
```

`BENCH_C_OPT` selects C optimization, defaulting to `-O0`. Add
`BENCH_NATIVE_PROBE=1` when building the diagnostic plugin to confirm native
execution; the runner asserts one marker per measured command. Generated native
objects are keyed by source bytes, Lean commit, optimization and export mode.

`set_option sol.benchmark true` enables command and per-function phase records.
`set_option sol.benchmark.tactics true` additionally splits specification search
into symbolic execution, closing preparation and solver time. These extra tactic
frames can hit the browser stack limit (observed on Counter), so use native Lean
for that detail. `BENCH_TACTICS=1` enables it in generated native wrappers.
`#solkey_benchmark "phase" in command` times a command. The test phase contains
its nested search/kernel/audit phases; add only disjoint phases. Recursive paths
do not yet have the complete per-stage breakdown. Phase records are collected
separately from the bounded diagnostic log, so multi-function measurements are
not silently truncated.

## Validation and review

The native frontend build passed 313 jobs. MCP diagnostics for the changed
frontend and the audit regression reported success, no errors and no timeout.
The audit regression is now part of the Pages workflow's native validation.
All 18 final browser cases, the 19 SolKey checks (one cold plus 18 server
checks), and 18 compiled native diagnostic checks passed with matched hashes.

Fourteen real single-file Chromium checks pass on artifact
`4eecf9c789998136e76aaf99ce9eacfc847b9cb2fac647dc47db65f871c74dd7`.
They include changed false claims, certified counterexamples, cancellation and
a new proof after restarting both workers with the static server stopped and
network disconnected. The certified counterexample retains all three standard
axioms in its exact inventory. Peak aggregate process RSS was 4.17 GiB.
The separate Counter benchmark passes, preserves all four function search
events beyond the 20-line diagnostic tail, and takes 4.32 s for a genuine
comment-edit recheck. Its 18.8 ms unchanged-result lookup is a cache control,
not a fresh proof. Calldata rows in that benchmark are admission-only listings.

Six protocol tests pass; the layering check reports 194 core modules with no
elaborator dependency. No proof budget was raised and no admitted theorem or
persistent axiom was introduced. Fine per-tactic Counter profiling did hit
`BROWSER_STACK_LIMIT`; no result was accepted. Per-tactic profiling is now
separately opt-in, and the final coarse-timer Counter run passes.

Read-only finder and skeptic reviews caught incomplete counterexample axiom
metadata, truncated phase events, absent clean-checkout report directories,
and missing input/build provenance in the comparison harness. These were fixed.
The memo additionally excludes unresolved imported names and retains the import
snapshot rather than a generated proof environment. Neither review used Lean's
server. The extra axiom test compares cached decisions with full traversal,
warms the memo, reuses a generated name for a nonstandard dependency, checks
failed-audit recovery, switches imports, and checks state restoration.
