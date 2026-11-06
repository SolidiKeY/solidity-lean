# H62-6 migrate-typing handoff

> H82 retirement supersedes all earlier resume instructions below. This worker is stopped and behaviorally PAUSED; only preservation is authorized. Successor: `solidity-h62-6-20261106/migrate-root-gate`. Read the [complete successor queue and waits](../../tests/h62/item6/migrate-typing/handoff/successor-queue-waits.json). No implementation continuation is authorized for this worker.

Status: **blocked; full assignment incomplete**. Pinned base is
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; isolated branch is
`codex/solidity-h62-6-20261106/migrate-typing`; checkout is
`/workspace/solidity-lean-migrate-typing`. Original clean checkout
`/workspace/solidity-lean` remains on `work`. Fetch verified the base is an
ancestor of published `origin/master` before the assigned worktree was created.
No push, merge, PR, master edit, deployment, freeze announcement or ownership
transfer occurred. The existing persistent goal was not created/reset; get_goal
is not exposed, which the coordinator explicitly says is not a blocker.

## Queue state

1. **Done:** census at pinned base; imports and old API inventory; clean old
   build with all 12 assigned files and their 64-module closure; independent
   finder/skeptic review and fixes.
2. **Blocked after provisioning:** identical official v4.35.0 release installed,
   archive hash and Lean/Lake versions recorded; source adaptation cannot be
   assessed until the Syntax migration owner supplies the dependency overlay.
3. **Blocked:** new clean build fails in out-of-scope Syntax.Raw. Full new
   Typing build, affected validation and comparable before/after measurement
   remain required. No timing improvement or runtime gate pass is claimed.
4. **Partial:** reviewable scripts/fixtures, old frozen-interface hashes,
   cross-directory report, exact owner ticket and patch/bundle export supplied.
   A fully passing migration patch and new elaborated-interface comparison
   remain outstanding for migrate-root-gate.

Backfill completed: complete source census, 6 scanner controls, 14 acceptance
controls, old elaborated API export and 8 isolated String proof examples. No
unclaimed cleanup candidate or H55 task was taken. Resume this same VM/branch
and existing goal after coordinator dependency input; do not create a goal or
self-launch a replacement thread. This is the coordinator handoff after these
work items, not completion of the whole assignment.

## Scope, frozen interfaces and proof boundaries

All 12 original `Solidity/Typing/*.lean` files are byte-identical to base.
`lean-toolchain`, lakefile, generated roots/maps and axiom pins are untouched.
No original declaration, statement, premise, exclusion, observation or proof
budget changed. Source census: 563 declaration sites and 707 branch-site lines
across 6,832 lines. A branch-site line can contain several alternatives; this is
not an alternative count. Whole-source hashes preserve every original case.
Old elaboration exports 1,317 constants from exactly the 12 Typing modules,
including private/generated declarations, exact Expr types and universe
parameters. Frozen hashes and axiom dependencies are off Git. Source hashes
alone are not claimed as cross-version elaborated-interface equality.

Axiom union of old Typing constants: `Classical.choice`, `Quot.sound`, `propext`.
Typing source trust sites (`sorry`, `axiom`, `native_decide`): zero. New such
sites: zero. No maxHeartbeats/maxRecDepth increase or trust shortcut was used.
The fixture's eight examples are kernel-checked proofs; Python controls test
scanner/acceptance behavior. Candidate String adapters do not prove full parser
semantics, general old/new equivalence, or migration of the Syntax producer.
The exporter is an audit command, not a new Solidity theorem. New helpers stay
under the authorized tests path and require no production module registration;
registration fragments: none. The core remains dependency-free and intrinsic.
History was inspected before changes; no earlier speed change was undone.

## Toolchain and resource evidence

Coordinator inputs in `/workspace/h62-coordinator-inputs` passed all SHA256
checks. Pin: `leanprover/lean4:v4.35.0`, official
`https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.
Archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Archive and extraction are under the evidence directory, outside Git.

- Old: Lean 4.24.0, release commit
  `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake
  `5.0.0-src+797c613 (Lean version 4.24.0)`.
- New: Lean 4.35.0, release commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
  `5.0.0-src+eb6cafb (Lean version 4.35.0)`.

VM cgroup cap: 16 GiB; system swap absent. CPU quota `400000 100000`, affinity
`[0,1,2,3,4]`, identical across measured runs. Writer lock:
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`. One compiler job at a
time; `LEAN_NUM_THREADS=1`, explicit `-j1 --tstack=131072 -M8192`;
per-process RLIMIT_AS 12 GiB; aggregate RSS sampled every 0.1 s with a 10 GiB
stop and preflight/runtime 4 GiB available reserve (host and cgroup). The RSS
stop is sampled, not a hard aggregate cgroup limit. VM hard cap remains 16 GiB.
No systemd-run was invoked. No resource stop occurred.

Each build uses a fresh output directory, explicit LEAN_PATH and no Lake/master
artifact cache. Toolchain standard-library artifacts are the official releases.
Baseline full closure hashes equal `git show BASE:path`; before/after hashes
show no source drift. These are **olean-only directory closure measurements**,
not a full Lake/native executable build or lean4checker replay. Setup/census
preparation is outside the reported compiler-loop wall time. Compiler logs
retain old and new pre-existing warnings. Direct bounded compiler checks are
the fallback because no Lean MCP tool is exposed; repository lean-verify skill
was read. The final `./run-lean.sh` gate remains pending behind the proven
upstream failure; it has not passed and was not redundantly launched.

## Commands, outcomes and decisive outputs

Run commands from the assigned checkout; `PYTHONDONTWRITEBYTECODE=1` is set for
Python commands. The runner supplies all Lean flags and the writer lock.

| Command | Outcome | Decisive evidence under `/workspace/migrate-typing-evidence` |
|---|---|---|
| `python3 scripts/h62/item6/migrate-typing/census.py` | 0 | `census-base.json`: 12 files, 64 local modules; 5 direct outbound and 14 inbound cross-directory edges |
| `python3 tests/h62/item6/migrate-typing/test_census.py` | 0 | `census-controls.log`: 6 tests, OK |
| `python3 tests/h62/item6/migrate-typing/test_compare.py` | 0 | `comparison-controls.log`: 14 tests, OK; failed build refused, >10% STOP, smaller regression escalates |
| `python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --output /workspace/migrate-typing-evidence/old-keysort --only-keysort` | 0 | `old-keysort/result.json`, KeySort exit 0 |
| `python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/migrate-typing-evidence/toolchain/lean-4.35.0-linux/bin/lean --output /workspace/migrate-typing-evidence/new-keysort --only-keysort --expect-base-sources` | 0 | `new-keysort/result.json`, KeySort exit 0 |
| `python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --output /workspace/migrate-typing-evidence/old-clean --expect-base-sources` | 0 | `old-clean/result.json`: 64/64 passed, 331.831856551 s wall; 930451456 bytes sampled aggregate RSS, 908900 KiB wait4 maximum child RSS |
| `python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/migrate-typing-evidence/toolchain/lean-4.35.0-linux/bin/lean --output /workspace/migrate-typing-evidence/new-clean --expect-base-sources` | 1 | `new-clean/result.json`: three modules pass, Syntax.Raw fails; 23.281713637 s partial time; **incomparable** |
| `python3 scripts/h62/item6/migrate-typing/compare.py /workspace/migrate-typing-evidence/old-clean/result.json /workspace/migrate-typing-evidence/new-clean/result.json` | 1, expected refusal | `comparison.json`: `INCOMPARABLE`; new full 64-module closure did not pass; timing delta null |
| `TYPING_API_OUTPUT=/workspace/migrate-typing-evidence/old-interfaces.json python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --output /workspace/migrate-typing-evidence/old-export-v2 --imports /workspace/migrate-typing-evidence/old-clean/lib --fixture tests/h62/item6/migrate-typing/ExportInterfaces.lean` | 0 | `old-export-v2/result.json` and module log: Exported 1317 Typing constants |
| `python3 scripts/h62/item6/migrate-typing/bounded-build.py --lean /workspace/migrate-typing-evidence/toolchain/lean-4.35.0-linux/bin/lean --output /workspace/migrate-typing-evidence/new-string-fixture-v2 --fixture tests/h62/item6/migrate-typing/StringAPIFixture.lean` | 0 | `new-string-fixture-v2/result.json`: all 8 proof examples compile |
| `python3 scripts/h62/item6/migrate-typing/freeze.py /workspace/migrate-typing-evidence/census-base.json /workspace/migrate-typing-evidence/old-interfaces.json` | 0 | `frozen-interfaces.json`: all 1317 constants hashed |
| `node scripts/check-layers.mjs` | 0 | `layers.log`: 857 core modules; zero reach elaborator or checked parser adapters |
| `bash scripts/coord-tools/register.sh --check` | 0 | `roots.log` |
| `bash scripts/coord-tools/fragments.sh --check` | 0 | `fragments.log` |
| `./run-lean.sh` | pending | known out-of-scope Syntax.Raw dependency prevents new-toolchain final gate |

Early audit attempts are retained as failures: `/usr/bin/time` was unavailable
(exit 127; no Lean ran), exporter v1 had a mutable-variable shadowing error,
and fixture v1 could not reduce three concrete decidable goals. The exporter
name was corrected and the same fixture statements were proved via standard
String lemmas, without budget increases. Only `*-v2` results are final passes.
No failed attempt is counted as a passing required gate.

## Typed blockers and exact owner relay

`B-SYNTAX-RAW-435` (external-owner migration dependency):
`Solidity/Syntax/Raw.lean:597,650,665,682,684`. New String.drop yields Slice;
Slice.toList is absent; a Slice is passed where String is required; polymorphic
endsWith requires eta expansion; String.dropRight is absent. Exact compiler
errors are in `new-clean/Solidity.Syntax.Raw.log`. Source and archive hashes,
requested action and candidate fixture are in
`tests/h62/item6/migrate-typing/owner-request.json`. All 12 assigned modules
remain to be built on the new toolchain. No Syntax file was edited.

`B-OWNER-RELAY-UNAVAILABLE` (coordination transport): `relay.sh` is not present
in the checkout or workspace. No reply is inferred. The saved request is for
the coordinator/migrate-root-gate to relay to the Syntax migration owner.
It requests an owner-reviewed overlay on this pinned base/toolchain, preserving
interfaces and semantics, plus explicit producer coordination before any
existing owned Typing edits. Further blockers may surface after Syntax is fixed.

`B-PREFIX-RSS-435` (resource regression escalation/STOP): the new passing prefix
already peaks at 1,546,231,808 sampled RSS bytes versus 930,451,456 for the
complete old closure (+66.18%). KeySort increases from 256,090,112 to 519,520,256
bytes (+102.87%); AST from 731,336,704 to 1,546,231,808 (+111.43%); SpecSyntax
from 581,120,000 to 1,456,537,600 (+150.64%). These are matching-source,
matching-resource observations, not a completed new build or wall slowdown.
ESCALATE: migrate-root-gate must investigate the official toolchain's RSS
regression under existing budgets before further Lean work. No threshold
exception is assumed. Exact prefix records: `rss-regression.json`; the summary
also carries them. No more Lean jobs ran after this observation.

Comparison-policy resume limitation: the current comparator intentionally
requires identical unchanged-base closure sources. An approved Syntax/Typing
overlay changing source will remain INCOMPARABLE. Root must establish a common
approved final-source tree/baseline and explicit comparison policy, preserving
frozen-interface/semantic checks and resource budgets, before adjusting this
guard; do not silently interpret expected migration edits as timing acceptance.

After owner input and resolution of the RSS stop: apply only an explicitly coordinator-approved private test
overlay, rerun the clean closure and affected validation with identical settings,
export the new API and compare all frozen types/universes/axioms, escalate any
regression and stop above 10%, complete required repository final gates/reviews,
then commit and re-export. Final tracked lean-toolchain change belongs to root.
No scope question or exclusion approval is requested.

## Independent reviews

Milestone 1 finder `/root/finder` and skeptic `/root/skeptic` worked read-only,
without Lean/server. Findings fixed: reserve preflight, child cleanup on
interrupt/monitor failure, TERM-to-KILL fallback and missing-group handling,
source hashes against Git base and before/after, branch and CPU/resource
provenance, attributed declaration handling. Clarifications retained: source
identity differs from elaborated interface equality; branch sites count lines;
RSS guard is sampled and RLIMIT_AS is per process. Both final reviews found no
remaining blocking tooling finding and inspected all six census controls.

Milestone 2 finder and skeptic independently checked fixtures, controls, API
manifest and handoff read-only, with no Lean/server. Both verified the current
blocked result and source/API integrity. Findings fixed: exact release-identity
checks; complete unique module/hash coverage; clean mode; finite positive
measurements; null exit rejection; strict >10% threshold using Decimal; 14
acceptance controls now cover these failures. No failed build is accepted.
Their final follow-ups confirmed earlier fixes. Finder's final null-exit edge
was then fixed and covered by a passing control. Artifact creation/verification
is performed after the final commit and recorded externally.

## Artifacts and integrity

Bulk outputs remain off Git. Deterministic generators and reproduction commands
are committed; `tests/h62/item6/migrate-typing/summary.json` retains compact
source/API hashes and metrics. External full manifests contain each frozen
constant. Aggregate old interface hash:
`8844d2b7374c085fbf07aafa1d50202f19c4228314dd6dc84b0dfc28f80bb67a`.

- Original patch: `/workspace/migrate-typing-evidence/migrate-typing.patch`
- Bundle: `/workspace/migrate-typing-evidence/migrate-typing.bundle`
- Handoff: `/workspace/solidity-lean-migrate-typing/docs/feature-work/h62-6-migrate-typing.md`
- Evidence: `/workspace/migrate-typing-evidence`
- Compact evidence archive: `/workspace/migrate-typing-evidence/receipts.tar.zst`
- Checksum manifest: `/workspace/migrate-typing-evidence/SHA256SUMS`
- Full committed head and artifact hashes: external `artifact-index.json` and
  final CLOUDVM-RESULT (avoids a self-referential commit/patch hash in this file).


## H82 final retirement checkpoint

Human-authorized lane-specific stop-and-handoff takes precedence over generic
implementation broadcasts. This worker finishes preservation only, then is
behaviorally PAUSED. No implementation continuation, new proof, timing STOP
rerun, merge, master push, goal creation/reset or VM replacement is authorized.
Successor: `solidity-h62-6-20261106/migrate-root-gate`. Its queue relay was
reported accepted by the coordinator; no source takeover precedes this
worker's final stopped/head acknowledgement. Integration is the successor's job.

The complete original visible first user assignment is committed at
`tests/h62/item6/migrate-typing/handoff/original-assignment.txt`, including the
full owner map, constraints and report format. The original goal objective is
`original-goal-objective.txt` in the same directory. Exact queues are also saved
separately as `original-work-backfill-queue.md`; the original 15-entry scope is
`exact-scope-manifest.json`. That directory's `SHA256SUMS` authenticates all
nine instruction/state/pin files. These are actual committed file contents,
not coordinator-local path references. The reported frozen rendered-prompt hash
is retained as provenance; its renderer preimage is unavailable, so the UTF-8
assignment file has its own reported SHA256 rather than a claimed rendered
hash match. Source was the complete original message visible in this thread.

`successor-queue-waits.json` records all four original checkpoints, every
backfill category, schema-v1 `{lane,item}` waits, old API limitations, and
validation boundaries. Scanner/census, negative controls, eight isolated proof
fixtures and reproduction/timing tooling backfill are done. No cleanup candidate
was separately assigned/claimed. New validation of all 12 Typing files,
complete new exported API/axioms (including generated public declarations),
common-tree before/after measurements and full affected/final gates remain open.
No independent implementation item is authorized to this retired worker.

Waits retained for the successor: migrate-syntax Raw.lean migration input;
migrate-root-gate RSS STOP disposition; H78 complete public generated inventory
and exact shim records. Existing old exports contain 1,317 constants but do not
separately export full visibility provenance. No new Typing export or shim was
implemented. The H78 inline ticket is saved as `routed-H78-owner-ticket.json`;
its declared source file/head/hash and unretrieved paths are distinguished in
`input-provenance.json`. No remote retrieval, authentication or delivery is
inferred from the inline message. No new commands or source application are
implied by that ticket.

H82 standing agreements supersede the old blanket exact-file prerequisite for
statement-preserving proof-only/additive/split/import/doc edits. Any such prior
request is withdrawn, not left as a wait. Statement, dependent definition body,
interface, budget, axiom and exclusion changes still require their owner;
frozen ones retain H57 versioned-pair rules. This policy update does not revoke
retirement or authorize proof work now. `relay.sh` is host-only and its VM
absence is not an installation task or remaining worker blocker.

No H71 push authorization is available in this thread or local coordinator
inputs. The original no-push rule remains; no branch was pushed. The final
cumulative patch and named-branch bundle will be under
`/workspace/migrate-typing-retirement`, with archive, artifact index and
SHA256SUMS. They include this full committed preservation checkpoint and all
original assignment/queue/scope files. The previous off-Git original artifacts and archived handoff bytes remain
unchanged in `/workspace/migrate-typing-evidence`. Its old artifact-index.json
is historical: its handoff entry names the live doc now superseded by this
retirement update. The original bytes still exist as
`/workspace/migrate-typing-evidence/handoff.md` and inside the original receipts.
The new retirement index hashes this current live document. The final head and exact
artifact hashes are external to avoid self-reference.

Goal pause limitation: available goal tooling exposes only `stop_goal` with
`complete|blocked`; no get/update/pause operation is exposed. It cannot express
PAUSED. A previous stop call also reported missing trusted goal/source-turn
context. No complete/blocked substitute, goal reset or replacement was invoked
for this retirement. User-directed behavioral pause is honored and no automatic
implementation continuation is authorized. The final report records this
precise limitation; it does not claim a backend PAUSED transition.

This retirement turn adds documentation/data only. No Lean source, proof budget,
axiom set, signature or exclusion changed. Existing validation is preserved;
no known timing STOP was rerun. Read-only finder/skeptic preservation review and
exact-patch/bundle/hash verification complete this smallest safe checkpoint.

Preservation review: independent read-only finder verified full original assignment, all 123 owner-map entries, exact scope/queue extraction and hashes; skeptic verified provenance, pending obligations and pause/push limits. Skeptic requested an overriding retirement pointer on the old handoff; the notice at the top now supplies it. Neither reviewer used Lean/server or wrote files.
