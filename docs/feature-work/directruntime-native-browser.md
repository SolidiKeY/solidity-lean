# Direct runtime native/browser lane — blocked fresh native/browser baseline

Batch: `solidity-directruntime-20261104`; branch:
`codex/solidity-directruntime-20261104/native-browser`.
Repository: `/workspace/solidity-lean`.
Pinned base: `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
Dispatch rendered-prompt SHA-256:
`d24253025c9bec8f160834a4695112e2d8b112a2f2dda1f0ed0ec74f5b38e7e6`.
The generated VM handoff records the full checkpoint head after commit.
This is a reviewable checkpoint, **not completion** and not `RUNTIME_GATE_PASS`.

## Queue accounting

| Work item | State |
|---|---|
| 1. Before integration, current 83-function baseline | Fresh native AST, native LSP and real browser 83 × 3 matrices passed. Cold native metrics incomplete; no A integration. |
| 2. Closure/bridge audit and committed A integration | Static audits and current native evidence recorded; confirmed production fixes and A handoff pending. |
| 3. Fresh native/browser B Identity, controls, C controls and existing regressions | Existing native suite/control evidence recorded. Existing browser controls have one stack-overflow failure. B/C sources and exact Identity diamond twin pending. |
| 4. Matched after baseline, ≥3 rounds, performance and final handoff | Pending. No after measurement or slowdown verdict. |

## Current native evidence

Evidence lives in `docs/benchmarks/directruntime-2026-11-04/`.
Raw log/text/trace/TSV captures are committed as byte-preserving `.gz` archives;
`raw-captures.json` pins both original and compressed hashes. The VM retains raw files.
To restore or verify them, run
`python3 tests/directruntime-20261104/native-browser/restore-raw-evidence.py`.
An initial full whitespace check flagged raw CRs/command spaces; compressed originals
preserve every observation while the derived CSV uses LF line endings.
The immutable `before/inputs/` contains all 83 newly compiled Solidity workloads,
source/AST/request hashes and unchanged harness identities. No historical verdict was used as a current result.

- Primary native latency matrix: **249/249 proved**, 83 functions × 3 rounds.
  Median of per-function medians: **0.838905 ms**; nearest-rank p95:
  **4.069482 ms**. Process-ready startup: **7.561709 ms**.
  These are precompiled-AST requests; Solidity compilation is separate.
- A separate 249-request native-only resource run passed; peak child RSS:
  **36,068 KiB**. Its throughput wall time is not a per-request latency measurement.
- Existing direct controls: 14 executed on the fresh binary. Six ordinary controls
  were freshly compiled; the initial eight specification cases used the committed AST.
  An additional owned wrapper freshly compiled current `ClosedSpecs.sol` and passed
  all eight exact specification verdicts (five proved, three refuted).
  Thus fresh-source evidence covers all fourteen distinct existing controls.
- Existing two synthetic closure tests and five additional closure regressions passed.
  They test extraction mechanics, not Solidity semantic equivalence.
- Native binary: **20,738,808 bytes**, SHA-256
  `4ade5e55eae99ba7c45e39ab148de066858ea5897fecca9a8debcd371c03cfd5`.
  Runtime path: `/workspace/solidity-lean/.lake/direct-native/direct-check`.
- Native identity inventory pins current Lean sources, generated C, extracted C,
  compiler executables, all Lean headers, runtime archives, bridge, binary and closure.
  Native runtime source commit:
  `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; source checkout is clean.
- An independent untimed syscall run completed 249/249 requests, with no observed
  serialized-environment reads or Lean/Lake subprocess execution.
  Request-wire hashes identify the bytes actually sent; the binary does not attest
  source hashes. Wrapper-assigned `environmentImports: 0` alone is not evidence.

## Commands, outcomes and failures

Commands run from the repository. Bounded commands use Docker
`--memory=12g --memory-swap=12g --cpus=1 --user=1000:1000`,
`LEAN_NUM_THREADS=1`, explicit Lean `-j1` through the ignored alternate config,
and the unchanged 4 GiB outer-cgroup reserve.

| Command / gate | Outcome and decisive evidence |
|---|---|
| `node tests/directruntime-20261104/native-browser/prepare-baseline.mjs` | PASS: 83 fresh workloads, inventory SHA `a4c66b77ffbdc4337be20a8822f176a4b22d50a91247b159acd8024969c11f43`; no verdicts. |
| Bounded `bash scripts/coord-tools/gate.sh per-file Solidity/KeySort.lean` | PASS: per-file elaboration, `setup/keys/gates.tsv.gz`. This is **not** the 377-taclet frozen sort-conformance gate. |
| First bounded `build-native-baseline.sh` | Lean target PASS: 337 jobs; 200 C modules compiled. Overall FAIL at bridge compilation because container `cc` alternatives link was absent. `before/native-build.log.gz`. Full cold-build wall/RSS was not captured; live guard started after launch. |
| Guarded native retry, explicit GCC executable | PASS, exit 0, 24.143623 s, `before/native-link-retry.json`; reused fresh C objects, so not a successful cold-build timing. |
| Guarded `native-baseline-checks.sh` | PASS, exit 0, 6.719507 s, `before/native-checks-gate.json`; 249 suite replies, 14 controls, 7 synthetic tests. |
| Guarded `audit-native.py` | Coarse symbol gate FAIL, exit 1, `before/native-audit.json`; semantic replies 249/249, forbidden traced loads zero. See structural resolution below. |
| `audit-native-stubs.py` | Separate structural receipt PASS: `before/native-stub-classification.json`; original failure preserved. |
| Guarded `measure-native-resource.py` | PASS, `before/native-resource-gate.json` and `native-process-resource.json`; native-only RSS 36,068 KiB. |
| Guarded `fresh-spec-controls.mjs` | PASS 8/8, `before/fresh-specs-gate.json`, `before/fresh-spec-controls/results.json`. |
| First `build-wasm-baseline.sh` | Pinned image provisioned, then first GMP preflight REFUSED insufficient initial reserve. `before/wasm-build.log.gz`. No WASM runtime built. |
| Python compile, Bash `-n`, Node `--check` for wrappers | PASS; no Lean server or proof claim. |
| Real browser 83 × 3, smoke/offline and edit/staleness controls | PASS; browser-checks, browser-smoke and browser-edit-controls receipts. |
| Browser complete negative controls | FAIL: 13/14 expected rows; one LFml.fitsM stack overflow. |
| Frozen sort checker | PASS: 377 taclets, 131 read-bearing, table covers 131; annotations match. |
| Per-file MCP | KeySort zero errors; DirectRuntime resource-stopped twice. Whole gate FAIL. |
| Final build and matched after gates | PENDING. |

Outer scope: 16 GiB, swap limit `max`, host swap zero. This is not the Lean gate
scope. Verified inner scope: memory.max=12884901888, memory.swap.max=0.
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. Outer CPU quota 4; bounded build quota 1.
Node v24.19.0; Chromium 154.0.8037.57.

The first WASM preflight's exact initial headroom was not persisted by runner v1;
it remains **unknown**, with only the refusal log. Do not reconstruct a number.
Runner v2 now atomically publishes non-overwriting preflight receipts with the
actual observed value and `childStarted:false`; v1 is archived under
`tests/directruntime-20261104/native-browser/history/`.
`setup/runner-versions.json` attributes prior receipts to v1.
`setup/cache-release.json` records POSIX_FADV_DONTNEED on owned disk artifacts,
without deletion, global cache dropping, budget or threshold changes.

## Structural classification and reviews

The coarse audit flagged three 57-byte initializer symbols from frontend-named
modules. Finder and skeptic independently inspected the actual binary, generated
bodies and matching object keys. The three retained helpers implement UTF-8
character membership, natural-number list membership and optional-natural equality.
The initializers only return standard IO success, with allocation/heartbeat/OOM
runtime calls. No frontend registration or state is initialized by these bodies.

The separate receipt records all six exact bodies/disassemblies/callees, original
and pruned C hashes, object hashes/keys, initializer-call-list links and unresolved
Lean import checks. It preserves the original `passed:false` receipt and its hash.
This is an artifact-specific, independently inspected structural conclusion;
callee checks are **not** a general purity proof and there is no namespace exemption.

Both read-only reviews used no Lean server. They confirmed source/request/object
identities, found the headroom-guard, overwrite and fresh-control provenance gaps,
and re-reviewed their fixes. Review records are in `setup/reviews.json`.
They support the recorded partial checkpoint only; final browser review is recorded separately in setup/reviews.json.

## Confirmed production work still to do

1. Native object keys/manifests omit complete header/compiler/runtime provenance.
   The external baseline inventory supplements this; production builders still need fixes.
2. Missing generated `l_`/`_init_l_` native roots now fail closed. Ten synthetic tests
   pass, including iterator roots; a bounded comparison preserved all 200 baseline
   extracted C module hashes. Arbitrary other ABI roots still require link validation.
   No rebuilt binary or after-performance result is claimed for this fix.
3. Both builders need initial/snapshot/final bridge and closure-script identities.
4. `DIRECT_RUNTIME_FULL=1` can produce an ordinary-loadable full runtime.
   Keep certification separate; owned builder enforcement and coordinated handoff
   to unowned browser/package/desktop loaders are required.
5. Native leanc links broad archives by default. Continue final symbol/import and
   runtime-load audits; a source-closure count alone is insufficient.

No DirectRuntime, translator, Source/Core, shared root/map/trust-pin or unowned
web/vscode producer file was edited. Ordinary trusted-verifier boundaries remain
unchanged. No axioms, sorry, premises, exclusions, proof budgets or statements changed.
No new Lean module exists; module-registration proposal: none. Central documentation
may later link this lane document through the normal owner-integrated handoff.

## Fresh browser and source-to-result evidence

`before/matched-before-summary.json` records complete denominators and boundaries.
Native LSP: 249/249, median of function medians 62.251926 ms, nearest-rank p95
75.866278 ms, initialization 127.573555 ms. Real Chromium: 249/249,
median 185.922378 ms, p95 224.386924 ms, startup 3428.200938 ms.
These source-to-result figures include editor submission and differ from native AST latency.
There is no after result or slowdown conclusion.

The freshly built WASM is 16,378,154 bytes, SHA-256
`4a5a55fef0cebd89fb85eb7ada60d4479bd6674656678b334fd28ea250328bef`.
The single HTML is 41,479,535 bytes. Source, compiler, bridge, runtime archive,
asset and binary identities are recorded in before/wasm-build.json,
wasm-runtime-source.json, html-build.json and web-asset-manifest.json.
The SDK is pinned Emscripten 4.0.15. The final WASM builder passed in 306.244866 s,
with sampled process RSS 2,643,546,112 bytes and minimum outer headroom
4,537,155,584 bytes. Earlier failures/refusals remain in the gate ledger.
GMP and the Lean runtime archive were freshly built separately.
Lake optional artifact export was disabled with LAKE_CACHE_DIR="" to avoid cache
copy pressure; no proof options changed. The same policy must hold for matched builds.

The unchanged website harness passed current-source specification, offline fresh-worker,
wrong-specification and stale-green controls. The edit harness passed supported edits
and unsupported calldata; cached retrieval checks are behavior checks, not fresh timings.

## Required browser failure and owner handoff

The completion diagnostic attempted seven groups covering fourteen expected rows.
Thirteen rows returned the expected results; the false invariantCountsToBound control
threw `RangeError: Maximum call stack size exceeded`. This is a **failed required gate**,
not pending, unsupported, or admission success. The same fresh source returns pending
on native. The initial wire audit stops at the error; its original incomplete report is
preserved. browser-control-attempts.jsonl and browser-control-completion.json record
all attempted groups, including the failed request before awaiting its result.

A diagnostic symbol-map relink produced a byte-identical WASM, with unchanged source,
fuel, compiler stack and default Chromium settings. The exact stack contains
LFml.fitsM (Solidity/Calculus/ReadBounds.lean:75) and its generated closures.
This identifies overflowing traversal frames, not the sole initiating cause or a proven
repair. before/browser-stack-handoff.json pins frames, source and both backend results.
D cannot edit ReadBounds/DirectRuntime/translator paths. No stack-size increase,
control exclusion, catch-to-pass, kernel fallback or proof-budget change was used.

Every bounded gate command, exit, wall and minimum headroom is indexed by
setup/gate-ledger.json; raw logs retain decisive output. The actual frozen sort checker
passed: `parsed 377 taclets, 131 read-bearing, table covers 131` and `OK — annotations match`.
MCP KeySort reported zero errors, but DirectRuntime checks twice crossed the reserve
and were killed; no successful DirectRuntime MCP or final policy gate is claimed.
**RUNTIME_GATE_PASS remains pending.**

## Scope questions and resume obligations

Self-contained questions and mutually exclusive options are in setup/producer-handoff.json:
Q-PRODUCERS requests retrievable A committed interface and B/C controls, or continued
pending handoff. Q-BROWSER-STACK requests an owner-supplied committed repair, an owned
bridge/compiler repair only if evidence establishes that cause, or continued blocked status.
No authorization, exclusion or recommendation is inferred from silence.

The narrow missing-generated-native-root hardening is implemented; the other production
hardening above remains unfinished. Independent authorized work is not exhausted. Resume with independent
owned fixes where possible, obtain the committed producer/stack resolutions, then run the
exact positive Identity diamond twin and false/default/alias/zero/OOB controls on both fresh
backends, C controls, existing regressions, complete cold-native metrics, matched ≥3-round
after performance, final policy checks and independent reviews. Investigate >10% slowdown.
The assignment is blocked and incomplete; no push, PR or merge was performed.
