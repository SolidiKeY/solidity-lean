# H62 item 6 — SolcValidation migration overlay

Status: **BLOCKED on owner migrations and the full-baseline resource gate**.
Both corrected full-build attempts and automatic collection have finished; neither full gate passed. No `RUNTIME_GATE_PASS`.

The coordinator resolved Q-PERF-1: a per-module time or memory increase does
not stop a migration lane. Record the module numbers and continue the matched
clean full-build comparison; the coordinator reports growth with cut-over
escalation. This supersedes the historical performance STOP below. The original
STOP record and interrupted run are retained as history, not current blockers.

## Identity and ownership

Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-6-20261106/migrate-solcvalidation`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The initial checkout was clean on `work` at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched origin master and the exact published base; verified the base is an
ancestor of fetched origin/master (`821e3e8f4` at setup), then created the assigned
branch at the exact base. No reset, push, merge, publication or PR occurred.
The assigned branch's committed head is recorded in the off-Git handoff JSON.

Only this document, the assigned tests directory and assigned scripts directory
are changed. The three original modules remain byte-for-byte identical to base.
No existing-file producer coordination was needed because no original was edited.
No ownership transfer, generated root/module-map/pin edit, or H55 work occurred.
The coordinator relay script is absent on this VM; exact requests are saved below
for coordinator retrieval. No claim of a delivered relay or owner permission.

## Checkpoints and frozen census

1. **Done:** all three original modules, 33 explicit declarations (32 public,
   one private), original import edges, constructor lines and unchanged budget
   options inventoried; clean v4.24.0 directory closure measured.
2. **Partial:** official pinned v4.35.0 installed and all three modules build
   unchanged. `DataLayout` emits two deprecated-name warnings (`dif_pos`,
   `dif_neg`), retained pending any owner-approved cleanup. Full acceptance blocked.
3. **Partial:** directory build and affected fixtures pass. A matched clean
   repository-wide attempts finished with identical settings: old resource-stopped, new failed.
   Per-module growth is recorded; external owner failures still prevent final acceptance.
4. **Partial:** reviewable patch, bundle, source/declaration hashes, dependency
   report and checksummed evidence exported. All 33 explicit original kernel
   records now match, including structural types and axiom lists. Generated API
   differences are reported separately; root acceptance remains pending.

Census: `/workspace/solcvalidation-evidence/census.json`.
Hashes named `source_sha256` and `block_sha256` are lexical hashes, including
bodies/comments for declaration blocks, **not elaborated type hashes**.
Unchanged complete module bytes preserve original statements, proof scripts,
representations and explicit resource options. `FrozenAudit.lean` checks every
public explicit declaration and prints axioms of all 12 public theorems on both
versions. Pretty-printer output differs (field notation and universe rendering);
its byte hashes must not be represented as matching structural interface hashes.
One private helper (`references_unique`) is accounted by source and build checks.
Generated recursors/deriving declarations are compiled through their parent files;
the 33 count refers to explicit source declarations, not all environment constants.

External dependency: `Solidity.Yul.Builtins`, unchanged and compiled from frozen
source in each clean closure. Reverse direct importers include the generated
`Solidity.lean` root (three edges), `Frontend/SolcJson/IrImport.lean`, and both
existing VT1 fixtures. The root remains read-only. Root-gate and frontend owners
retain their own migration/validation work. No new core module registration is
needed; test fixtures are invoked directly, so the registration fragment is empty.

## Toolchain and measurement

Coordinator input manifest verified at `/workspace/h62-coordinator-inputs/`.
Official asset: `lean-4.35.0-linux.tar.zst` from
`https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.
Observed and expected SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

Actual versions (`versions.json`):

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release;
  Lake `5.0.0-src+797c613`.
- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release;
  Lake `5.0.0-src+eb6cafb`.

VM: 16 GiB cgroup memory cap, four CPU quota, no host swap in use.
Heavy jobs run serially with `LEAN_NUM_THREADS=1` and explicit `-j1`.
Historical runs also used an extra 12 GiB per-process virtual-address limit;
that limit was removed during calibration after thread-creation failures.
Current runs retain the unchanged 16 GiB hard VM cap, sampled 12 GiB aggregate
RSS watchdog and estimated 4 GiB available-memory headroom guard. The estimate
uses host MemAvailable and cgroup free capacity plus reclaimable inactive_file;
it is not a guarantee of instantaneous free allocation.
No systemd-run, no old per-master cache, no external package dependency.
Private `enableArtifactCache=false`; new empty build destinations; logs show
all four closure modules built, no fetched artifacts. OS page caches were not
dropped; these are single clean Lake-output runs, not statistical benchmarks.
The first attempted runner could not find GNU time; it never started Lean.
The measured runs use monotonic wall time, kernel child maximum RSS and sampled
process-group RSS. Full-gate child maxRSS after group interruption is incomplete;
use its sampled group peak rather than inferring a complete build maximum.

| Measure | v4.24.0 | v4.35.0 | Change |
|---|---:|---:|---:|
| Whole closure wall | 5.676719 s | 4.306066 s | -24.145% |
| Kernel maximum child RSS | 284536 KiB | 538816 KiB | +89.367% |
| Sampled process-group peak | 339177472 B | 664158208 B | +95.814% |
| Assigned modules sum (rounded Lake log) | 1389 ms | 1498 ms | +7.847% |
| DataResolution alone (rounded Lake log) | 288 ms | 371 ms | +28.819% |

The wall saving is largely the external Builtins module (3.9 s to 2.5 s).
The directory cannot claim an unconditional improvement. The historical STOP
for DataResolution was lifted by the coordinator clarification. The first
full-gate group had been terminated with SIGTERM; unrelated workers were not
terminated. Checks resumed only after the explicit clarification.

## Commands and decisive evidence

Runner prefix (absolute path):
`python3 /workspace/solidity-lean/scripts/h62/item6/migrate-solcvalidation/migration.py`.
For each command below use `run --root DIR --toolchain TOOLCHAIN --dest PREFIX -- COMMAND`.
Evidence JSON stores the exact command array, working directory, toolchain,
exit, wall time, limits and associated log path. Options work on either side
of the action; all command arguments follow the literal `--` separator.

| Gate / command | Outcome | Evidence under `/workspace/solcvalidation-evidence/` |
|---|---|---|
| `lake build Solidity.SolcValidation.DataResolution` | old/new exit 0, 5 jobs | `old-build.{json,log}`, `new-build.{json,log}` |
| `lake build Solidity.KeySort` | old/new exit 0, 2 jobs | `old-keysort.{json,log}`, `new-keysort.{json,log}` |
| `lake env lean --tstack=131072 -j1 tests/fullscope-20261104/vt1/DialectChecks.lean` | both exit 0 | `{old,new}-DialectChecks.{json,log}` |
| same invocation on `ObjectDataChecks.lean` | both exit 0 | `{old,new}-ObjectDataChecks.{json,log}` |
| same invocation on `tests/h62/item6/migrate-solcvalidation/FrozenAudit.lean` | both exit 0 | `{old,new}-FrozenAudit.{json,log}` |
| same invocation on private-copy `tests/h62/item6/migrate-solcvalidation/Acceptance.lean` | both exit 0 | `{old,new}-Acceptance.{json,log}` |
| `bash ./run-lean.sh` in private full-new snapshot | interrupted, exit -15; external errors | `new-full-gate-retry.{json,log}` |
| `./scripts/check-doc-paths.sh` | exit 0 after correcting this document’s off-Git filename citation; existing ambiguities are warnings | `doc-paths.log` |
| deterministic census and audit regeneration, followed by `cmp` | exit 0 | `census-reproduced.json`, [FrozenAudit-reproduced.lean](/workspace/solcvalidation-evidence/FrozenAudit-reproduced.lean) |

The initial full-gate snapshot lacked Git metadata; that first attempt exited 2
before Lean. Initialized only the disposable snapshot's Git metadata and retried.
The retry passed layer checks (857 core modules, zero reach elaborator or checked
parser adapters), then reported external failures before performance STOP.
No required final gate is counted as passing from that partial run.

The clean snapshot preparation command is `prepare --root REPO --dest FRESH_DIR`.
Then run the target command with the bounded runner above. Snapshots contain the
frozen local source closure and private Lake config, including KeySort/checker
sources. Source manifests in the measured trees were reconstructed after builds;
they must not be described as pre-build attestation. Source bytes are compared to
base by the census. The full private snapshot came from `git archive` at base,
with only testing-only Lake options and lean-toolchain changed. Final tracked
lean-toolchain remains v4.24.0; changing it belongs to the root migration lane.

## Proof and external-test boundary

Existing object-data fixtures exercise actual retained byte intervals, endpoint
emptiness, inhabited tables, missing names, out-of-bounds rejection, duplicate
table rejection, tail lookup, unique references and complete selections.
New `tests/h62/item6/migrate-solcvalidation/Acceptance.lean` covers all seven object-only constructors, their arities,
wrapped naming, reversed mode distinction, the data constructor, empty artifact,
empty table, distinct-byte head/tail/duplicate raw-list selection, exact byte
access and generic resolver contracts. Its four fixture definitions and anonymous
examples add no producer theorem or premise. No `sorry`, new axiom, native_decide,
raised maxHeartbeats or trust shortcut was added. All twelve original public
theorem axiom sets match: only existing propext/Quot.sound where applicable.

These are Lean kernel-checked syntax/local-table facts, not solc execution,
compiler provenance, global object layout, optimizer correctness, gas adequacy,
physical memory copy, G49 composition, or full external differential tests.
No such external semantic claim is made or substituted for a proof.

## Independent reviews

Read-only finder and skeptic agents used no Lean process/server and edited no
files. Initial findings: incomplete reverse importer census, CLI REMAINDER option
ordering, resource-stop false-success race/termination handling, missing source
identity attestation, and confusing lexical hashes with elaborated type hashes.
Fixed importer enumeration, ancestry plus frozen byte checking, CLI separator
parsing, pinned-base importer contents (stable after staging), forced nonzero resource stop and SIGKILL fallback; clarified evidence
limits. Both confirmed exact frozen module bytes and matching twelve axiom sets.
Finder caught post-commit census reproducibility (fixed to ancestry check) and
manifest asymmetry (reconstructed and explicitly dated after builds). Skeptic
caught per-module slowdown hidden by closure improvement; that finding triggered
STOP. Both required a blocked handoff at that checkpoint; the timing STOP recommendation is now superseded. Actual versions and observed archive digest
were saved after the second review request. Review messages are summarized here;
no claim is made of a separate reviewer attestation file authored by the agents.

## Typed blockers and coordinator requests

- **PERFORMANCE_GROWTH_RECORDED / H62.3 (not a blocker):** DataResolution
  288→371 ms and RSS +89.367%. Coordinator clarification supersedes STOP;
  continue the matched clean full-build comparison and report growth at cut-over.
- **EXTERNAL_OWNER_MIGRATION / H62.3:** full-gate failures at
  `Solidity/Hash/CollisionBound.lean` (407, 660, 680 and guard messages),
  `Solidity/Language/FixedPoint.lean` (152, 170 and later arithmetic goals),
  `Solidity/Semantics/AbiAccess.lean` and
  `Solidity/Backend/AbiEntry/RawFreeTransport.lean`.
  Exact lines/messages are in `external-blockers.json`. Root migration gate
  must route to the owning directory lanes; these files are outside this task.
  Failed upstream proofs can introduce sorryAx in diagnostics; no pins were
  relaxed and no such partial result was accepted.
- **FINAL_GATE_PENDING / H62.3:** full affected validation, final run-lean,
  SolKey sort checker and frontend consumer validation remain outstanding.
  KeySort is independently passing on both toolchains; this is not the complete
  SolKey executable conformance gate.
- **GENERATED_API_REVIEW / H62.4 (scoped review complete):** all 33 explicit
  kernel records match exactly. All generated deltas are classified below.
  Downstream runtime acceptance remains part of the external-owner-blocked full gate.
- **ROOT_GATE_ACCEPTANCE_PENDING / H62.4:** root lane must retrieve patch/bundle,
  assess regressions, combine external owner migrations and run its own gate.

Historical Q-PERF-1, now resolved [sources: H62.3, comparison.json]:
For the pinned-base DataResolution single-run 288→371 ms slowdown and +89.367%
maximum RSS, which root-gate follow-up should own resolution?

1. Root gate performs controlled repeated matched measurements and determines
   whether the regression persists; this lane remains blocked pending its result.
2. Coordinator obtains exact-file owner coordination for a bounded performance
   repair in the assigned modules; then this lane remeasures and reruns gates.

Resolved by the coordinator: neither module timing growth nor memory growth
stops a migration lane. No further decision is requested for Q-PERF-1. Record
these numbers, continue matched clean full builds, and retain the external owner
blockers. No statement, budget or trust-policy change was authorized.

## Handoff and remaining queue

Original persistent goal remains unfinished. No get_goal tool was exposed;
coordinator explicitly confirmed this absence is not a blocker. Do not create,
reset or schedule another goal. This turn completed census/toolchain/fixture
work items and now hands the original VM/goal/branch to the coordinator for
fresh-thread continuation, respecting the 3–5 item boundary. The coordinator has now resolved the performance STOP; continue the matched
full builds and return to external-owner-blocked gates before accepting the queue. Remaining work is exactly the typed blockers above, not a completed queue.

Bulk evidence, toolchain archive and private snapshots stay off Git in
`/workspace/solcvalidation-evidence/`; the committed tests manifest records hashes.
Exported `original.patch`, `migration.bundle`, `handoff.json`, and `SHA256SUMS`
are in that same absolute directory. The coordinator retrieves committed artifacts
from this VM; nothing was pushed or deployed.


## Resumed comparison and actual kernel-interface hashes

The coordinator clarification is recorded verbatim in
`/workspace/solcvalidation-evidence/coordinator-resolution.json`.
Q-PERF-1 is resolved; current reports use `questions=[]`.
The matched full build uses fresh `matched-full-old` and `matched-full-new`
private snapshots exported with `git archive` from the exact pinned base.
All Lean source hashes and private Lake configurations are identical between
snapshots; only the private toolchain selector and actual binary toolchain differ.
Both began without `.lake` or a private cache. Original selected inputs are
recorded in matched-full-{old,new}-sources.json. The serial queue holds the task's
writer lock, uses the existing bounded runner, and invokes the same command:

`env SOLKEY_RULES=/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key bash ./run-lean.sh`

The explicit SolKey input prevents a missing-checkout warning from counting as
conformance. The old run is followed by the new run even if the old fails. A
failed, interrupted or resource-stopped run cannot supply an accepted successful
full-build ratio. Exact result JSON/log files use the matched-full-{old,new}-result
prefix. These builds do not change the repository or frozen owner files.

`tests/h62/item6/migrate-solcvalidation/KernelInventory.lean` is a test-only
metaprogram, checked on both toolchains with the same bounded `lake env lean`
flags. It enumerates imported constants by their actual originating module,
including the private helper and generated declarations available at enumeration.
It does not claim to force every possible lazy generated declaration.
The initial helper's inferred counter type failed on v4.35.0; explicitly typing
the test counter as Nat fixed it without changing any original declaration or
raising a proof budget. The checked final runs both exit 0.

The deterministic reducer validates the exact three-module scope and all
33 explicit declarations, rejects duplicate module counts, and compares the
union of record fields. The finder and skeptic independently verified all
33 hashes against the raw logs. The deterministic reducer is
`scripts/h62/item6/migrate-solcvalidation/reduce-inventory.py`:

`python3 scripts/h62/item6/migrate-solcvalidation/reduce-inventory.py --evidence /workspace/solcvalidation-evidence`

Bulk raw Expr inventories remain off Git in old-kernel-inventory.json and
new-kernel-inventory.json. Actual type and full-record SHA256 hashes are in
frozen-interface-hashes.json. All **33 explicit original declarations** match
byte-for-byte as complete kernel records: raw type Expr, universe parameters,
kind and exact axiom list. This includes private references_unique and every
original public theorem. Unchanged complete source bytes separately attest the
original definition bodies; matching types alone are not a body-semantics proof.

Loaded owned constants total 247 old versus 253 new: Dialect 159→162,
DataLayout 83→86, DataResolution 5→5. Among common names, 182 complete records
match and 64 generated records differ. One generated name is removed
(IrMode.toCtorIdx) and seven are added. Generated noConfusion signatures change
structurally, including index binders and heterogeneous equality. Generated
instReprObjectOp and instReprObjectOp.repr gain propext in their dependency lists;
no new axiom declaration is introduced, but all-generated axiom parity is **not**
claimed. These differences are supplied to the root gate for downstream review.
The read-only skeptic found no explicit repository source references to the
changed generated interfaces; complete downstream validation is still required.

Independent finder and skeptic reviewed the resumed inventory without Lean,
server access or edits. Both confirmed the origin-based enumeration boundary;
the skeptic independently verified equality for all 33 explicit records and
identified the generated API/axiom changes above. Their earlier STOP-related
recommendations are superseded by the coordinator's explicit clarification.


## Audit negative controls while full builds run

The additive script
`scripts/h62/item6/migrate-solcvalidation/check-inventory-controls.py` runs no
Lean process. It keeps valid logs and all tampered copies off Git and checks:

- The original complete inventory is accepted.
- A failed runtime result is rejected despite complete logs.
- Removing the same explicit declaration from both versions, while repairing
  both module counts, is rejected rather than accepted as matching subsets.
- Adding an otherwise allowlisted Classical.choice dependency to one explicit
  theorem is rejected by exact baseline parity.
- A duplicate module-count marker is rejected.

Command:
`python3 scripts/h62/item6/migrate-solcvalidation/check-inventory-controls.py --evidence /workspace/solcvalidation-evidence --output /workspace/solcvalidation-evidence/inventory-controls`

All five controls pass their expected acceptance/rejection condition. Results
and decisive reducer diagnostics are in inventory-controls/results.json and
its case subdirectories. These are external tests of the audit tooling, not new
kernel theorems or substitutions for downstream migration proofs.


## Full-build resource calibration

The first resumed old full attempt at matched-full-old was interrupted after
943.975 s, with generated Yul checks aborting on thread creation. That attempt
is **invalid for a successful full-build comparison**, not a module-growth STOP.
The queued new run was prevented from starting, and only task-owned processes
were stopped. Its observed aggregate sampled RSS peak was 4,523,896,832 bytes;
its child maxRSS after interruption does not account for all killed descendants.

The extra RLIMIT_AS=12 GiB in the original runner constrained reserved virtual
stacks. A live Lean process had approximately 11.3 GiB virtual size versus 2.7 GiB
RSS and 37 internal threads despite the explicit -j1 command. Cgroup OOM/max and
PID-limit event counts remained zero. Removing that extra virtual cap allowed
unchanged Solidity.Yul.Checks.Powers, which previously aborted, to build in a
bounded diagnostic (exit 0, 2.084 s wrapper wall, 538,247,168-byte group RSS peak).
This supports the calibration fix; it is not a completed repository gate.

The actual VM memory cap is unchanged at 16 GiB, host swap remains unused, and
the watchdog still stops above 12 GiB sampled RSS or below estimated 4 GiB
available headroom. The guard now recognizes inactive_file as reclaimable cache,
consistent with reserving available memory rather than total virtual mappings.
No statement, proof budget, heartbeat setting or original source was changed.

`migration.py prepare-full --dest FRESH_DIR --toolchain TOOLCHAIN` now reproduces
fresh exports from the exact pinned BASE, including Git metadata required by the
read-only root checks, private toolchain selectors, identical cache-disabled Lake
configs and explicit --tstack=131072/-j1 for all five libraries and three executables.
The corrected pair is matched-rss-old and matched-rss-new. Both source manifests
attest identical 7,311 Lean files and identical private config SHA256
4f3ec665aa7d14932b59a0605d220866ce505e4bf10888f036de7e243c26012a.
These private snapshots replace the invalid matched-full pair for comparison.
The independent finder and skeptic reviewed this correction read-only and found
no blocking setup defect; both required the historical/current distinction above.


## Calibrated SolKey conformance prerequisite

Actual old-toolchain `lake exe solkeycheck --key` passes with the explicit frozen
rule file: 377 parsed taclets, 131 read-bearing, table covers 131, annotations OK.
The new-toolchain invocation fails in Solidity.SortCheck.Parser at line 76:
String.trim is absent in v4.35.0, producing dependent field-notation errors and
failed executable evaluation. This is an **EXTERNAL_OWNER_MIGRATION** blocker,
not a failure to install the toolchain. KeySort itself already passed on both.
The exact-file request DEP-SORTCHECK-1 is saved in owner-requests.json for the
coordinator/root migration relay. No SortCheck source or pin is edited here.
The matched full attempts are now complete and nonpassing; a new full gate cannot be
accepted until its owning lane supplies a compatible parser overlay.


## Final independent work and producer-blocked handoff

Before each new item, fetched master and checked its log and relevant code.
Latest fetched master is `5f7bb1441566aaad64a34436904afc61de762fd2`. Its selector remains v4.24.0; the three
SolcValidation originals and SortCheck/Parser source hashes match pinned BASE.
No relevant migration implementation or dependency repair landed, so the latest
coordinator instruction's conditional rebase does not apply. Evidence is
latest-master-check.json. No duplicate producer work or branch rewrite occurred.

The scoped generated-API review is now **complete**. The deterministic
`scripts/h62/item6/migrate-solcvalidation/review-generated-api.py` accounts for
all 64 changed records: 28 noConfusion, 14 constructor injectivity, nine derived
sizeOf, five Repr and eight equation/match auxiliary records. One removal and
seven additions remain recorded, as do the two Repr propext dependency gains.
Literal full-name and namespace-relative searches return zero hits at both BASE
and fetched master. This does not cover all aliases, indirect or synthesized
references and is not a theorem of downstream compatibility. No unsolicited
source shim is justified by these results. Both independent read-only reviewers
repeated the classification/checksum/search checks and found no concrete defect.

The result collector is
`scripts/h62/item6/migrate-solcvalidation/collect-full-comparison.py`.
It starts no Lean process, edits no Git file and does not create a goal or Codex
continuation. One lightweight process waits at most eight hours, sleeping no
more than five seconds at a time, for the **existing** serial queue's completed
old/new JSON results. It then writes matched-full-comparison.json and a separate
matched-full-comparison-SHA256SUMS over completed outputs. Active logs are not
hashed as completed evidence. Future code changes must not overwrite this
pair's immutable snapshots/results.

The collector validates the exact full run-lean command with the explicit
existing SolKey input, each prepared lane's cwd and toolchain, fixed calibrated
resource bounds, pinned identical sources and identical private configuration.
Measurements and waiting bounds must be finite; RSS and wall must be positive.
A failed, interrupted or resource-stopped gate produces **no accepted ratio**.
The full wall threshold is strictly greater than ten percent, calculated with
Decimal; per-module time or RSS growth does not stop the lane. Even two passing
full builds leave root acceptance explicit. Eleven synthetic controls pass,
including exact ten versus over ten percent, failed/resource stops, subset
commands, duplicated toolchains, wrong cwd, nonfinite values and configuration
mismatch. These controls are tooling tests, not actual migration measurements.
Both independent read-only reviewers confirmed the false-success fixes.

Commands and decisive controls:

- `python3 scripts/h62/item6/migrate-solcvalidation/review-generated-api.py --evidence /workspace/solcvalidation-evidence --output /workspace/solcvalidation-evidence/generated-api-review.json`
- `python3 scripts/h62/item6/migrate-solcvalidation/collect-full-comparison.py --evidence /workspace/solcvalidation-evidence --wait-seconds 28800`
- generated-api-review.json records all 64 deltas and both zero-match searches.
- full-comparison-controls.log records all eleven passing synthetic controls.

The remaining accepted new-toolchain full gate requires an owner-produced
**Solidity/SortCheck/Parser.lean** migration (DEP-SORTCHECK-1: String.trim removed,
line 76 and dependent lines 77–82; frozen old executable passes 377/131/131).
Earlier complete diagnostic locations also include Hash/CollisionBound,
Language/FixedPoint, Semantics/AbiAccess and Backend/AbiEntry/RawFreeTransport;
these remain requests for the appropriate migration owners, not write scope here.
The completed corrected new run now supplies the full diagnostic set: 18 source files failed.
All required final passing validation and the accepted full-build ratio remain
unfinished until owner overlays are available. No statement, premise, proof
budget or trust pin has been weakened to bypass them.

The original goal is **blocked, not complete**, on these producer migrations.
The old→new measurement queue and lightweight collector have both finished;
their obsolete process/session IDs and completed outcomes are saved in handoff.json.
No additional Lean job or competing goal is started. The coordinator can wake
this original goal when owner migrations land, inspect the saved completed
comparison, and resume the final affected/full gate. The reviewed patch, bundle,
frozen-interface hashes, exact-file requests and checksum manifests are exported
for that handoff. Questions are empty; the per-module-growth question is resolved.


## H70 receipts and completed comparison — current authoritative state

The corrected queue and collector are finished. No Lean or collector process
remains active. The old clean full attempt stopped at the existing availability
reserve guard (exit 125, RESOURCE_STOP): 3019.171153 s wall and 8479391744 bytes
sampled process-group peak RSS. That peak is below the 12 GiB RSS cap, so the
available-headroom guard triggered; its exact instantaneous estimate was not
recorded. The interrupted run's kernel child maxRSS is not a complete subtree
peak and must not be substituted for the sampled group figure.
The new clean full attempt failed (exit 1): 249.754759 s wall and 3541495808 bytes
sampled process-group peak. Neither is a passing full build. The accepted wall
and RSS deltas are **null**. These attempt durations cannot support a speedup
or regression ratio. No bound was raised, source weakened, or cache-enabled run
substituted for a clean baseline.

The collector has sealed matched-full-comparison.json and
matched-full-comparison-SHA256SUMS. The deterministic follow-up is
`scripts/h62/item6/migrate-solcvalidation/seal-full-evidence.py`:

`python3 scripts/h62/item6/migrate-solcvalidation/seal-full-evidence.py --evidence /workspace/solcvalidation-evidence`

completed-full-evidence.json contains the complete diagnostics for 18 failed
new-toolchain source files and these seven successful module observations.
They are rounded Lake log durations, not a successful full-build comparison.
Both complete logs were produced without applying any H70 overlay.

| Module | Old rounded seconds | New rounded seconds |
|---|---:|---:|
| Solidity.KeySort | 1.4 | 1.4 |
| Solidity.Yul.Builtins | 2.0 | 1.6 |
| Solidity.SolcValidation.Dialect | 0.58 | 0.423 |
| Solidity.SolcValidation.DataLayout | 0.502 | 0.432 |
| Solidity.Frontend.SolcJson.IrImport | 0.576 | 0.475 |
| Solidity.SolcValidation.DataResolution | 0.284 | 0.238 |
| Solidity.Frontend.SolcJson.IrImportControls | 3.4 | 3.6 |

All three assigned modules and their direct IR importer/controls build on each version.
This additional affected-consumer evidence does not clear whole-repository gates.
Independent read-only finder and skeptic verified the attempt records, 18-file
failure census, module observations, and absence of an accepted ratio. Neither
used Lean/server or edited files.

The H70 owner payloads are preserved **off Git** under h70-inbox. Their exact
checksums match the coordinator-provided identities:

- Hash overlay: 3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff;
  ticket head 78c110f83dc1a30700acd1b5bd34b19f61da6ccd,
  source head 2a18afcdba00a85645b0b3079704f78ffcd78860.
- FixedPoint prerequisite: a3cbeea6c8a243df761166dd558825898f2bbda8c8fa7d8a74850cd27cb8ad82;
  ticket head 479f6e0079409a1867483dbffe5051932b8fa754,
  source head d8e1d9721455d3671882f19aa7155fbbd2d91415.

Read-only `git apply --check` passes for each payload against the pinned checkout.
**Neither patch was applied** to the branch or immutable measurement snapshots.
This is byte-identity and context applicability, not Lean validation, full owner
acceptance, or merge permission. The saved H70 disposition explicitly records
host delivery acceptance as unknown; the host relay journals decide that state.
Hash remains partial with full gates and Syntax.Raw pending. FixedPoint remains
partial with full migration gates pending. A local transcription context error
was corrected before the FixedPoint artifact matched its exact owner checksum;
no mismatching payload was applied or retained as authoritative.

Current waits remain exactly the H70 routing disposition: migrate-sortcheck for
Parser/String.trim, migrate-hash for CollisionBound, migrate-language for
FixedPoint, migrate-semantics for AbiAccess, and migrate-abientry for
RawFreeTransport. Current-owner delivery to migrate-abientry is still pending;
no agreement is inferred from routing. All other observed cross-directory errors
are retained in the completed report for migrate-root-gate. A successful clean
old full baseline under the unchanged memory/reserve bounds also remains
unresolved. There is no remaining authorized producer repair inside this lane.

The goal remains unfinished and acceptance **blocked**. Wait for owner-complete
migration inputs and root-gate handling of the old full-baseline resource stop.
Do not restart the same unpatched full builds, edit owner files, merge/push,
relax budgets, create a new goal or schedule a competing continuation.


## H82 final retirement checkpoint

Stopped for human-approved handoff to `solidity-h62-6-20261106/migrate-root-gate`.
No new proof implementation, Lean rerun, owner patch application or push occurred.
The committed retirement directory under tests/h62/item6/migrate-solcvalidation
contains the complete original visible assignment/objective, full original work
and backfill queues, exact scope/owner manifest, schema-v1 open waits, retirement
authority and all existing-evidence hashes. Its SHA256SUMS is carried in the
cumulative patch/bundle. The original renderer hash is provenance, not a falsely
asserted match to unavailable renderer bytes.

H78 public generated API preservation remains OPEN: prior static classification
and zero textual references do not waive any original public generated name/type.
Existing raw per-declaration signatures and axiom records are preserved off Git;
public visibility/completeness and compatibility shims remain successor work.
Implemented shims: none. Do not rewrite project consumers to evade those shapes.

The original task is not complete. The worker is retired/stopped, the requested
goal state is PAUSED, and no automatic implementation continuation is authorized.
The tool surface provides no pause action (only complete/blocked), so the worker
cannot set PAUSED and does not substitute another outcome or reset/create a goal.
H71 push permission text is unavailable; no push was attempted. Final exact head,
clean status, cumulative artifacts and hashes are in the retirement handoff JSON.
The successor is responsible for integration after the final stopped/head ack.
