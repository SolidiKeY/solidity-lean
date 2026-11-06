# H62 item 6 — SolcValidation migration overlay

Status: **BLOCKED**, not migration acceptance. No `RUNTIME_GATE_PASS`.

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
3. **Blocked:** directory build and affected fixtures pass, but performance STOP
   and repository final-gate failures prevent acceptance.
4. **Partial:** reviewable patch, bundle, source/declaration hashes, dependency
   report and checksummed evidence exported. Root acceptance and comparable
   elaborated-interface hashing remain pending.

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
All heavy jobs ran serially with `LEAN_NUM_THREADS=1`, library/executable
`weakLeanArgs` containing explicit `-j1`, a 12 GiB per-process virtual-address
limit and sampled aggregate RSS/headroom guard with 4 GiB reserve.
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
The directory cannot claim an unconditional improvement. **STOP** applies to the
observed DataResolution >10% slowdown; RSS regression is separately escalated.
No additional Lean checks were run after STOP. The owned full-gate group was
terminated with SIGTERM; unrelated workers were not terminated.

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
STOP. Both require a blocked handoff. Actual versions and observed archive digest
were saved after the second review request. Review messages are summarized here;
no claim is made of a separate reviewer attestation file authored by the agents.

## Typed blockers and coordinator requests

- **PERFORMANCE_REGRESSION_STOP / H62.3:** DataResolution 288→371 ms and RSS
  +89.367%. Preserve the STOP until root-gate assessment. No optimization or
  owner-file edit is authorized by merely asking for explanation.
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
- **INTERFACE_HASH_PENDING / H62.4:** normalized structural type comparison is
  pending; lexical hashes and public type/axiom output are supplied for review.
- **ROOT_GATE_ACCEPTANCE_PENDING / H62.4:** root lane must retrieve patch/bundle,
  assess regressions, combine external owner migrations and run its own gate.

ESCALATE Q-PERF-1 [sources: H62.3, comparison.json]:
For the pinned-base DataResolution single-run 288→371 ms slowdown and +89.367%
maximum RSS, which root-gate follow-up should own resolution?

1. Root gate performs controlled repeated matched measurements and determines
   whether the regression persists; this lane remains blocked pending its result.
2. Coordinator obtains exact-file owner coordination for a bounded performance
   repair in the assigned modules; then this lane remeasures and reruns gates.

No option authorizes a weakened statement, raised budget or trust-policy change.
No recommendation: single short measurements do not establish which repair is
needed. The frozen statement hashes are supplied as requested evidence only.

## Handoff and remaining queue

Original persistent goal remains unfinished. No get_goal tool was exposed;
coordinator explicitly confirmed this absence is not a blocker. Do not create,
reset or schedule another goal. This turn completed census/toolchain/fixture
work items and now hands the original VM/goal/branch to the coordinator for
fresh-thread continuation, respecting the 3–5 item boundary. Continue only after
the performance STOP is resolved; return to blocked gates before accepting the
queue. Remaining work is exactly the typed blockers above, not a completed queue.

Bulk evidence, toolchain archive and private snapshots stay off Git in
`/workspace/solcvalidation-evidence/`; the committed tests manifest records hashes.
Exported `original.patch`, `migration.bundle`, `handoff.json`, and `SHA256SUMS`
are in that same absolute directory. The coordinator retrieves committed artifacts
from this VM; nothing was pushed or deployed.
