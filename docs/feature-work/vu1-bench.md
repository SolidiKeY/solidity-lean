# U01 benchmark inventory and unresolved prerequisites

Scope: [trust and usability U01](trust-usability.md#u--usability).
Pinned base: `ee6ed004f703ff47f5d5399e1793306338e064af`.
The inventory command is `node scripts/bench/inventory.mjs`. It reads the
checkout, hashes the existing tools, and emits an inventory only. The
`knownGapsAtPinnedBase` list is a manual review summary, not automatic detection. Its output
is not a benchmark baseline. No new verification implementation is introduced.

## Inventory

| Existing input | Measures today | Missing for U01 |
|---|---|---|
| [Velvet runner](../../scripts/testsuite-performance.mjs) | Compiles separately adapted Velvet functions; hashes sources, AST and requests; native server request wall time, startup separately | Compilation excluded from request wall time; no per-request RSS, walk/closing/kernel split, or full TestSuite/upstream/typical-contract corpus |
| [Velvet report](../../scripts/report-testsuite-performance.mjs) | Source-matched medians across native/editor/browser/SolKeY with count and status assertions | Old fixed output directory and fixed modes; no U01 quantiles, size model, calibrated budgets or certified-mode coverage |
| [Simple preparation](../../scripts/measure-simple.mjs) | Compiler wall time; generates import, obligations and test timing wrappers for simple programs | Small synthetic corpus; compilation amortization/process boundaries must be specified |
| [Simple measurement](../../scripts/measure-native.mjs) | Total subprocess wall time and three frontend command timers; exact source and frontend/plugin hashes | A native plugin is compiled acceleration, not automatically fast verdict mode; no per-function RSS or complete phase partition |
| [Replay costs](../../scripts/measure-replay-costs.py), [helper](../../tests/automation/ReplayCosts.lean) | Uncached equality certificates for walk/refutation and leaf decisions/lowering | Explicitly diagnostic components, not complete program proofs; do not sum these into certified latency |
| [Build measurement](../../scripts/build-measure.py) | Samples process-group Lean/Lake VmHWM, RSS, anonymous RSS, cgroup usage and module sightings | Module/process rather than function boundaries; short processes can be missed; watcher does not enforce limits |
| [Build audit](../audits/build-speed.md) | Cold module timings, profiles, cache caveats, kernel replay hotspots | Library build cost is not source-to-verdict cost |
| [Native plugin](../../vscode/src/native-plugin.cjs) | Checks toolchain, platform, module/file fingerprints, plugin bytes and optional native probe | Plugin loading does not choose verdict/certificate semantics; interpreted fallback must not be labelled native |
| [Direct native builder](../../scripts/build-direct-native.py) | Pinned generated-C direct runtime closure | Requires matching Lean source/toolchain and native build; no certified result |
| [Frontend testing](../../Solidity/Frontend/Testing.lean) | Command timers; certified search, instantiation, kernel and axiom audit; direct mode has explicit verification marker | Search may combine walk, closing and chunk kernel checks; the final kernel timer alone undercounts total checking; detailed tactic timers cover selected paths only; direct timers overlap |
| Existing `docs/benchmarks/*.json` | Historical measurements of different scopes and revisions | Must not relabel these as a fresh U01 baseline |

The requested `docs/kernel-replay-performance.md` does not exist at the pinned
base. The historical kernel JSON remains present; its `scope` explicitly says
“uncached kernel phase certificates; not complete program proofs”. The base's
coordination tools also explain that older evidence may live in the private
coordination archive. That is a citation drift, not permission to reconstruct
or promote the old data.

## Measurement boundaries

Fast mode returns a verdict and never a Lean theorem. Certified mode must
retain the existing kernel and transitive axiom checks. Native plugin
acceleration and direct verdict semantics are different axes. A subprocess
failure, unsupported function, timeout, missing phase or missing workload must
remain visible in the denominator; none can become a zero-duration success.

Record compiler/parse, import/elaboration, walk, closing, kernel, audit and
process overhead with explicit nesting. Do not add overlapping frontend timers.
A missing disjoint phase is unknown, not zero. Count static Solidity AST
statements separately from dynamic rule/walk steps. Per-function process peak
RSS includes mapped imports and must identify cold/warm process and cache state.
Historical measurements are context only; no current p50/p95/max or worst-ten
list is available until the actual suite has run.

## Waits and owner requests

- `VU1-R1` (resource-policy owner): required systemd hard scope cannot start on
  this container (PID 1 is `tail`; neither system nor user bus exists). Gates
  and heavy benchmarks await a systemd/delegated-cgroup environment or an
  explicitly authorized alternative hard limiter and reserve policy. The
  16 GiB container limit alone is not the required 12 GiB job bound.
- `VU1-D1` (documentation catalog owner): adding this requested document makes
  the generated catalog stale, but its output is outside this lane's lease.
  The coordinator selected option A: it will add the topic-guide link and
  regenerate the catalog during integration, then run unchanged checks.
  This is resolved ownership, not a gate waiver. The lane acknowledged
  `VU1-D1`; navigation remains pending until the combined tree passes.
  The exact required owner diffs are below; do not hand-edit generated output.
- Representative contracts: the frozen SolKeY snapshot contains benchmark
  ERC20 and wallet sources, but their presence is not evidence of frontend
  admission. No vault/multisig Solidity file was found in that snapshot.
  Upstream result records mark the old MultiSigWallet compilation suite as
  lacking a harness adapter. No exclusion or replacement is authorized.
- `VU1-I1` (measurement/frontend owner): locating admitted representative inputs
  and supplying disjoint telemetry requires owner direction before the suite
  interface can be frozen. The requested prior-art studies and Hard problems list were not located
  under the named paths at this base. Do not freeze a replacement measurement
  interface until their location or an owner direction is established.

## Exact out-of-scope owner diff

Generated by the catalog's sorted document listing; owner should run
`python3 scripts/check-doc-navigation.py --write` after integrating this file.
No catalog write is authorized in this lane.

```diff
--- a/docs/document-index.md
+++ b/docs/document-index.md
@@ -198,6 +198,7 @@
 - [docs/feature-work/transient-storage.md](feature-work/transient-storage.md)
 - [docs/feature-work/trust-usability.md](feature-work/trust-usability.md)
 - [docs/feature-work/v13-public-compiler-total.md](feature-work/v13-public-compiler-total.md)
+- [docs/feature-work/vu1-bench.md](feature-work/vu1-bench.md)
 - [docs/feature-work/vy5-composition.md](feature-work/vy5-composition.md)
 - [docs/feature-work/vy5-natural-account.md](feature-work/vy5-natural-account.md)
 - [docs/feature-work/vy5-source-release.md](feature-work/vy5-source-release.md)
```

The topic-guide addition belongs in the existing trust/usability guide:

```diff
--- a/docs/feature-work/trust-usability.md
+++ b/docs/feature-work/trust-usability.md
@@
-## Lanes
+U01 measurement inventory and prerequisites: [benchmark lane](vu1-bench.md).
+
+## Lanes
```

## Budget decision

The plan proposes fast p50 ≤ 1 s, p95 ≤ 10 s, and certified ≤ 60 s and
≤ 4 GiB per function. These remain proposals requiring user approval after
calibration. No absolute budget has been adopted and no CI threshold or
performance claim is justified by the inventory.

## Review log

Independent Codex finder and skeptic inventory reviews used read-only sandboxes
and no Lean server. Both confirmed citation drift, missing representative
admission evidence and the component-versus-complete-proof distinction.
The skeptic found that direct timers overlap and that certified chunk kernel
checks occur inside search, before the final kernel timer. The inventory and
measurement boundaries above incorporate these findings. Neither review
validates a fresh performance baseline; no such baseline exists yet.
The final finder corrected the catalog insertion point to follow the v13
entry. The final skeptic requested explicit labeling of the manual gap list
and informational-only inventory semantics; both corrections are incorporated.

## Checkpoint handoff

Inventory is partial until its reviews and required gates pass. Suite, fresh
baseline, calibrated report, budget approval, CI regression thresholds,
full lane-end validation and sealed handoff remain outstanding. No Lean file,
public theorem, axiom pin, heartbeat setting or generated root is changed.
