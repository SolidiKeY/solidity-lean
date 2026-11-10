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

- `VU1-R1` is resolved by standing user decision H232, which supersedes
  systemd/delegated-cgroup provisioning. Run unchanged heavy gates serially
  with `LEAN_NUM_THREADS=1`; do not wait for a systemd scope. The enforced
  host pre-gate remains 16 GiB with no swap before any merge. Operational
  limitation: no systemd scope on the cloud VM (H232).
- `VU1-D1`: the landing review requested the topic-guide link and catalog
  regeneration on this branch. The link is in the trust/usability guide; the
  catalog is generated with the unchanged navigation script. Branch checks
  do not establish ordinary factory integration or a merge receipt.
- `VU1-D2`: the merged master has an inherited catalog omission. The current
  catalog and navigation-generator owner is
  `plan-ci0-ci-green-1109/ci0-lean-checks`. Only that owner performs the unchanged
  generator repair; VU1 must not write either file or edit audit content.
  Coordinator delivery of the bounded repair remains pending under H418.
  Keep the navigation failure explicit until the published repair passes checks.
- `VU1-G2`: the merged master has a known unrecorded axiom pin for
  `Solidity/Backend/Passes/CompilerWholeScopePins.lean`. Its repair is already
  assigned outside VU1. Do not write the registries, baseline or theorem here;
  preserve the failed gate until the published repair is validated. This is
  inventory bookkeeping, not permission to add an axiom or weaken a proof.
- Representative contracts: the frozen SolKeY snapshot contains benchmark
  ERC20 and wallet sources, but their presence is not evidence of frontend
  admission. No vault/multisig Solidity file was found in that snapshot.
  Upstream result records mark the old MultiSigWallet compilation suite as
  lacking a harness adapter. No exclusion or replacement is authorized.
- `VU1-I1` follows the coordinator-confirmed H191 option A: existing owners
  provide exact admitted fixtures and complete disjoint telemetry; U01 waits
  for their published inputs. No instrumentation lease extension is authorized.
  The **coordinator remains the routing/publication waker** under the factory
  liveness protocol, rather than an unnamed-owner wait. This decision is
  acknowledged; the question is not reopened. H232 remains the later standing
  memory policy and removes the historical scope-provisioning requirement.
- The explicit user decision H413 authorizes a bounded producer proposal with
  owner review before implementation. `VU1-P1` routes proposal preparation to this existing lane,
  handle `VU1-P1-proposal`; no implementation or source ownership is assigned.
  The exact unapplied diff, minimized file map, acceptance contract and unresolved
  owner-review tickets belong in private evidence. CI0 retains its existing
  repair priority and receives no telemetry follow-up. Complete U01 still waits
  for a validated publication; proposal review does not freeze an interface.
- `VU1-G1` (#477) is resolved ownership: the existing producer is
  `plan-ci0-ci-green-1109/ci0-lean-checks`, branch
  `cloud/plan-ci0-ci-green-1109/ci0-lean-checks` (H383/H390, continued by H407).
  Its unchanged 600-second CI budget does not raise or satisfy this lane's
  300-second VM guard. Wake only after its reviewed repair, ordinary gates and
  landing, guarded cache publication, and exact-input compatibility for this
  lane. Retrieve published caches only with
  `scripts/ci/fetch-lake-cache.sh` (H88/H367); a different-master cache is not
  proof of a hit. Full acceptance remains pending. Do not rerun unchanged
  timed-out dependencies or infer delivery from this routing answer.
- This lane takes source preparation and admission evidence inside
  `scripts/bench/**` itself. Exact representative inputs still require demonstrated
  frontend admission, rather than an unnamed-owner wait. The request to the
  coordinator includes the required admitted token/vault/multisig paths.
- The requested prior-art studies and Hard problems list were not located under
  the named paths at this base; the coordinator request records the missing
  producer/interface prerequisites. No new telemetry interface is frozen here.

## In-scope admission preparation

`node scripts/bench/admission.mjs --help` wraps the existing source compiler and
frontend listing API. It does not rebuild the compiler, translator or verifier.
Build the frontend first with `lake build Solidity.Frontend.Testing`, then run
under the repository writer lock, for example:

```sh
LEAN_NUM_THREADS=1 node scripts/bench/admission.mjs --soljson "$SOLJSON_DIR" \
  --out .lake/bench/testsuite-admission.json \
  tests/migration/solkey/keyext.solidity.examples/TestSuite.sol
```

Outputs must be JSON reports and must not alias inputs, including through
symlinked parent directories. The compiler directory must contain the binary pinned by the vendored snapshot;
no sibling SolKeY checkout is needed. Every raw frontend row and compiler/tool
error is retained, including internal, skipped and unsupported rows. A successful
listing requires at least one ready row and the existing listing-success policy;
`readyRows` does not count internal/skipped rows as admitted functions. An
unfinished attempt never passes. The selected output is invalidated before input
discovery, hashing or Git setup; setup failures are saved as failed attempts.
Normalized selectors, timeout and compiler directory are recorded. Final source
bytes and every row source hash must match the initial snapshot, or the report
retains a source-identity error and fails.

These reports are admission evidence only: `verification` is `not-run`, and
`sourceToVerdictBaseline` is false. They contain no U01 wall-time/RSS baseline,
phase partition, kernel certification claim or native verdict. Save outputs in
ignored runtime storage and archive evidence privately, not in the code branch.
The trust-boundary controls are `node --test scripts/bench/admission.test.mjs`.

`node scripts/bench/sizes.mjs --admission REPORT --out FILE` reuses the pinned
compiler to attach static source sizes to admission rows. `declarationSpanBytes` is the UTF-8 span of the
whole declaration, including signature, modifiers and body. It joins by the
frontend's declaration ID and source hash, not by function name, and retains
refused/internal/skipped rows. Its metric counts executable Solidity statement
AST nodes in each source function body, with block containers excluded and loop
header statement nodes included. Modifiers and callees are not expanded; inline
assembly counts once. It records compiler identity and the input-report hash.

A bodyless declaration, synthesized constructor or missing source declaration
has an explicit unavailable size, never a fabricated zero. A genuinely empty
body has zero statements. These are static source metrics, not dynamic walk
steps, proof timings or a U01 baseline. Controls are
`node --test scripts/bench/sizes.test.mjs`.

## Documentation integration

The trust/usability topic guide links this inventory. After adding tracked
Markdown, the current catalog owner regenerates it with
`python3 scripts/check-doc-navigation.py --write`. VU1 runs only the unchanged
read-only navigation, document-path and generator checks and reports inherited
drift to that owner under VU1-D2. Keep ordinary integration and
landing with factoryd; passing branch checks is not a merge receipt.

## Native runtime preparation

The existing `scripts/build-direct-native.py` requires both the installed Lean
release and a Git checkout of its exact pinned commit, including
`stage0/stdlib` generated C. Pass those directories and an owned output directory
as its three arguments. Run under the writer lock with serial Lean and the
unchanged replay budget. Keep the generated binary and its provenance manifest
outside the code branch.

The existing `scripts/testsuite-performance.mjs --reuse --native` accepts the
prepared Velvet directory through `TESTSUITE_BENCH_DIR` and that binary through
`DIRECT_NATIVE`. Its warm request latency excludes source compilation and
process startup; even a passing run is neither a certified theorem nor the
requested disjoint end-to-end U01 baseline. Missing phases remain unknown.

The existing corpus generator launches multiple `lake lean` probes concurrently.
For serial full validation, use an external launcher that locks those probe
invocations and forwards their exact arguments, output and exit status to the
pinned Lake. Builds still require the outer serial gate and resource guard;
`LEAN_NUM_THREADS=1` alone does not serialize independent probe processes. Keep
the operational launcher and its provenance with the private handoff.

## Partial certified process measurements

H377 permits independent measurements while producer inputs are pending,
including measurements of current master. It gives no complete-U01 or full-gate
acceptance credit. `scripts/bench/process-totals.py` consumes a finished admission
report and invokes the existing certified CLI once per ready declaration, using
its exact signature and checking the returned declaration ID, contract and source
hash. Every input row remains in the report, including unsupported/internal rows.
Run under the writer lock after building the existing frontend:

```sh
LEAN_NUM_THREADS=1 python3 scripts/bench/process-totals.py \
  --admission /path/to/admission.json --soljson "$SOLJSON_DIR" \
  --work /path/to/new-evidence-directory
```

`--repo` selects the measured checkout; its committed head and CLI fingerprint
are recorded separately from the driver fingerprint. Each measurement uses a
fresh CLI process with warm imported artifacts, without rebuilding. Existing
supervisors retain the original per-tool timeout (at most 300 seconds); a function
can include multiple tool jobs. Exit 135 retries once and both attempts remain.
The new work directory prevents overwriting previous inputs or successes.

Wall time covers the CLI invocation, including source compilation and kernel
checking when successful. Linux `RUSAGE_CHILDREN.ru_maxrss` is the maximum
individual-process RSS, not an aggregate tree peak. Disjoint phases, dynamic walk
steps and aggregate peak RSS remain `null`; these partial totals are never a
complete baseline. Failed, ambiguous, native-marked or source-mismatched results
cannot become certified successes. Partial checkpoints survive interruption.

For a large inventory, `node scripts/bench/batch-checks.mjs --admission FILE
--soljson DIR --work NEW_DIR` reuses the existing batched testing API and its
original 32-row batches and per-tool supervisors capped at 300 seconds.
The batch runner preserves admission contract/function selectors and any smaller
admission timeout; effective selectors and timeout are recorded in its report. It retains a row
for every admission entry even when a batch checkpoint omits unrun declarations.
Missing or ambiguous observations cannot pass. Exit 135 retries once; both
attempts remain visible. This wrapper reports the existing per-row `elapsedMs`
as `functionReportedElapsedMs`, excluding source compilation and shared imports.
Whole-call `apiWallMs` includes checkpoint logging; it is never apportioned to
functions. Per-function source-to-verdict wall time, phases and RSS remain null.
Only unique certified-mode observations with attempted statuses (`proved`,
`refuted`, `pending`, `error`) and nonnegative safe-integer milliseconds expose
this derived timer. Import-only/unattempted placeholders, unknown statuses,
native markers and ambiguous identities expose null, while raw observations
remain unchanged. A genuine attempted zero is preserved. Correcting a derived
projection does not rerun or change the original measurement's provenance.
Isolated process totals and batched check timers must not be pooled.

`python3 scripts/bench/partial-report.py --process GROUP REPORT SIZES`
prints a partial JSON summary to stdout; repeat the three-argument option for
additional groups. Optional `--batch REPORT --batch-sizes SIZES` adds the separate
check-timer summary. Redirect stdout only to a new private evidence file.
Quantiles use nearest rank, retain failed completed functions, and include all
retry wall time in each function's total. Overlapping groups are not pooled;
the worst-function list selects the maximum observed total per exact identity.
Static statement correlation is descriptive, with no linear-scaling claim.
Report and attempt provenance errors remain visible. Every retry must bind
exactly one matching certified-mode identity; invalid attempts exclude the
entire function retry total from timings, RSS, correlation and worst lists.
Raw attempt errors and failure counts remain available. Valid failed outcomes
with matching identities remain comparable. Report provenance errors suppress
all comparable statistics; interrupted
runs are provisional because final identity checks have not completed. Duplicate
size/process identities are rejected, and batch identities/raw timers are checked
again. This consumer never promotes partial receipts to a complete baseline.

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

The H185/H186 decision update received independent read-only finder and skeptic
reviews with no Lean server and no findings. Both confirmed the owner-input
wait and provisioning requirement remain intact, with no gate waiver or
completion claim. Both coordination questions were acknowledged after recording
the selected option A decisions. H232 subsequently removes the memory-scope
provisioning dependency; the H185 owner-input dependency remains pending.

Independent read-only finder and skeptic reviews of the H232 update found no
scope, citation, trust or decision-fidelity issue. Neither used the Lean server.
The provisioning wait is removed; no gate or performance pass is inferred.

On an elan-free installation, set `LAKE_CACHE_DIR` explicitly to the directory
printed by the cache installer: its toolchain cache can differ from Lake's
XDG default. Verify the active path with `lake env printenv LAKE_CACHE_DIR`
before interpreting a cold rebuild as a cache miss for the pinned revision.

The admission-preparation milestone received independent read-only finder and
skeptic reviews with no Lean server. They identified stale-success retention on
setup failure, omitted effective selectors and unbound source identities. The
runner now invalidates pending output before discovery, records selectors,
preserves partial rows/errors, and fails on row-hash or final-source drift.
The no-Lean controls cover these cases; both reviewers confirmed the fixes.

The static-size preparation received independent read-only finder and skeptic
reviews with no compiler or Lean execution by reviewers. The finder identified
an input/output alias that could overwrite source data; shared canonical output
checks and regression controls now prevent it. The skeptic requested an exact
name for the whole-declaration byte span; `declarationSpanBytes` and its control
now distinguish it from the body-only statement metric. Both confirmed the fixes.

Independent read-only finder and skeptic reviews of the runtime-preparation
guidance found no issues. Both checked the existing builder/runner arguments,
the warm-request versus end-to-end boundary, and that `VU1-T1` executes H191
without reopening the decided question. Neither used a compiler or Lean server.

The final finder requested preserving the exact operational timing/RSS wrapper
for the single certified CLI sample; it is retained with private evidence and
identified by checksum. The skeptic confirmed the partial native denominator
and the explicit RSS and trust boundaries. Neither sample is a U01 baseline.

Independent read-only finder and skeptic reviews of the operational probe
launcher confirmed its argument, output and exit-status preservation. They
qualified that builds still rely on the outer guard and that PATH must resolve
through the launcher; the private routing diagnostic checks that resolution.
Neither reviewer executed Lean or a compiler.

The final finder and skeptic confirmed that `VU1-G1` is a replay dependency
request, distinct from the resolved memory policy and granting no gate waiver.

Independent read-only finder and skeptic reviews of the partial process driver
identified an admission-snapshot checksum race. Parsing and hashing now use the
same byte buffer, with an end-of-run identity check and a replacement control.
Runtime/toolchain identity and effective per-tool timeout are recorded. The
reviewers confirmed that refused rows and failed attempts remain visible, and
that the RSS metric is an individual-process maximum rather than a tree peak.

Independent read-only batch-wrapper reviews found two cross-credit risks: equal
bytes at different source paths, and duplicated inventory identities. Joins now
include normalized source paths, duplicate inventory keys are rejected, and
pure controls prevent either case from turning one observation into two checks.

Independent finder and skeptic reviews of the reporting correction identified
the actual import-only `excluded` outcome missing from a proposed denylist.
The final helper uses the exact attempted-status allowlist and safe-integer
milliseconds. Regression controls distinguish unattempted placeholders from
real attempted zero without changing proof-success classification.

Independent read-only proposal reviews found cross-subject span parents and
undetectable finish-event loss. The unapplied draft detaches subject-transition
roots and keeps completeness unknown until owner-approved loss detection.
Entry-condition auditing outside the function-check span is explicit. These
preparation reviews grant no source ownership, implementation approval or
coverage/type validation.

Independent read-only report-consumer reviews required preserving provenance
errors, rejecting duplicate/ambiguous size and observation identities, matching
raw timers, and labeling summed retries as per-function totals. The consumer
and pure controls now cover these cases. Invalid size provenance suppresses
size comparisons without hiding timing data; interrupted receipts remain
provisional. Neither reviewer executed Lean or a compiler.

Final finder and skeptic handoff review caught an owner-diff export truncated
at a heading inside a fenced patch. The private exporter now preserves the
complete fenced owner-edit section; regenerated handoff and checksum artifacts
retain the original measurement and reporting heads separately.

Landing finder and skeptic review identified omitted admission selectors in
the batched API call. The runner now forwards exact contract/function selectors
and bounded timeout, records them, and has a no-Lean API-call regression
control. Existing unselected measurements retain their original provenance.
The subsequent landing review requested the exact VU1-D1 documentation edits
on this branch. The topic-guide link and generated catalog are now included;
ordinary factory integration remains separate.

The documentation landing review identified the missing reachable topic-guide
link and stale generated catalog. The requested link is added and the catalog
is regenerated through its unchanged script, without weakening checks.
Independent read-only finder and skeptic reviews confirmed the exact edits and
that branch validation does not grant producer ownership or U01 acceptance.

Landing finder and skeptic review identified attempt-level identity errors
bypassing the report-level provenance filter. The consumer now validates each
returned identity and attempt error before including a complete retry total.
Finder review additionally required rejecting matching malformed declaration
IDs and retaining attempt evidence from unfinished rows. IDs must be integers
(including synthesized constructor -1); all row evidence is retained while only
completed valid rows enter statistics. Both cases have focused controls, along
with mismatches, missing/ambiguous returns, native markers, mixed retries and
valid failed neighboring rows. Finder review removed a missing-status confound
from the changed-identity controls so each tests its intended mutation.
Independent read-only finder and skeptic confirmed the implementation fixes.

Independent read-only finder and skeptic reviews of the merged-master catalog
drift confirmed the one-row generator repair without audit-content changes.
The VU1-D2 disposition assigns execution to the existing CI0 owner; the catalog
remains unchanged in this lane while coordinator delivery is pending.
The coordinator also assigned the inherited VU1-G2 pin-inventory repair outside
this lane; no inventory, baseline or theorem edit is made here.

## Checkpoint handoff

The lane-owned inventory and documentation repairs are complete. Current
merged-head validation inherits the catalog and axiom-inventory failures above;
ordinary factory integration remains separate. Suite, fresh baseline, calibrated
report, budget approval, CI regression thresholds,
full lane-end validation and sealed handoff remain outstanding. No Lean file,
public theorem, axiom pin, heartbeat setting or generated root is changed.
