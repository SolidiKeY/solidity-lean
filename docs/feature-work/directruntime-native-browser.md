# Direct runtime native/browser lane — partial native baseline

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
| 1. Before integration, current 83-function baseline | Native portion recorded; browser baseline pending. No A integration performed. |
| 2. Closure/bridge audit and committed A integration | Static audits and current native evidence recorded; confirmed production fixes and A handoff pending. |
| 3. Fresh native/browser B Identity, controls, C controls and existing regressions | Existing native suite/control evidence recorded. B/C sources, exact Identity diamond twin and browser modality pending. |
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
| Browser, actual frozen sort checker, MCP, final build and matched after gates | PENDING. |

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
They support this partial native checkpoint only.

## Confirmed production work still to do

1. Native object keys/manifests omit complete header/compiler/runtime provenance.
   The external baseline inventory supplements this; production builders still need fixes.
2. Closure extraction silently discards missing generated runtime callback roots.
   Add a rejecting regression and fix after the full before baseline is preserved.
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

## Dependency question

**Q-PRODUCERS** — sources: work queue 2–3 and committed-output-only boundary.
Where should this VM retrieve A's committed translator interface and B/C's committed
controls? The local checkout and remote advertised no such batch branches at audit.
Options: (1) supply committed SHAs with retrievable artifacts; (2) keep producer
integration pending until coordinator handoff. No recommendation or exclusion request.
No answer or new authorization is inferred.

## Resume order

1. Retry the serial WASM build with a fresh attempt ID after verifying reserve.
   Keep prior logs/refusals. Complete real browser baseline and existing browser controls.
2. Preserve a successful cold-C-build measurement, build/check RSS and all compiler/runtime
   identities; the failed cold build plus cached-link retry is not that measurement.
3. Run the actual frozen sort check and per-file MCP/final policy gates when appropriate.
4. Obtain committed A/B/C artifacts; integrate only authorized producer output.
   Complete exact positive Identity diamond twin and false/default/alias/zero/OOB controls
   through both fresh backends, plus C controls and all existing negative/staleness cases.
5. Fix owned production audit findings, coordinate unowned loader fixes, run matched
   ≥3-round before/after evidence, investigate >10% slowdown, and repeat independent
   reviews/final gates. No publication, push, PR or merge is authorized here.
