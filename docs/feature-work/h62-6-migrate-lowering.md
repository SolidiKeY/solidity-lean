# H62 item 6: migrate-lowering

Assignment: `solidity-h62-6-20261106/migrate-lowering`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-lowering`.
Checkout: `/workspace/migrate-lowering` (isolated worktree).
Original checkout `/workspace/solidity-lean` was clean on `work` at
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4` and was preserved.
Fetched the exact base and `origin/master`; base ancestry succeeded against
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`. Assigned remote branch was absent.

## Status and boundaries

All four migration checkpoints remain incomplete. This checkpoint saves the
census, reproduction/resource tooling, and initial evidence. No production Lean
files, declarations, frozen statements, proof budgets, toolchain file, generated
roots, central maps, or axiom pins were changed. No new Lean axioms or `sorry`.
This is an isolated migration overlay; live producer ownership is unchanged.
Existing originals require exact-file coordination before any future edit.
No coordinator relay.sh is present in the discovered checkout/tools.

Coordinator inputs under `/workspace/h62-coordinator-inputs` were independently
verified against their SHA256 manifest. The exact active goal was supplied in
this thread; get_goal is not exposed, as the coordinator explicitly permits.

## Census and reproducibility

Run `python3 scripts/h62/item6/migrate-lowering/census.py --output OUTPUT.json`
from this checkout. The output includes every Lowering source path, whole-file
SHA256, direct imports, transitive project closure, lexical declarations and
budget directives. It is not an elaborated type or axiom audit.

Pinned census: 661 modules; families G19 36, P8 37, P8b 4, P9 15, Readonly 93,
StorageOps 92, V07 164, V08 220. There are 146 direct external import edges and
1,063 project modules in the transitive closure (402 outside Lowering).
Lexical declaration counts: 5,256 definitions, 5,480 theorems, 329 abbreviations,
42 instances, 62 structures, 103 examples, 22 inductives. No local heartbeat or
recursion-budget directives were found by the lexical scanner.

Direct external dependencies include Backend, Source, Frontend, Roadmap,
Language, Semantics, TypeGraph, Yul, Theory and Syntax. External migrations are
owner dependencies; no changes to them are authorized here.

Frozen whole-source hashes (not elaborated type hashes):

- P8/FrozenInterface.lean: `25d6c7e77168309e23710540cfd7d3ba5479d0a3b1727c1caa2b1aa4357ab662`
- P8b/Frozen.lean: `76c73f38899a03bc7d4a94571995427b2139fcf31baeccc79a93be6c04b06e64`

The generated complete census is off Git at
`/workspace/migrate-lowering-artifacts/evidence/census-base.json`.
The repository-wide `bash scripts/check-doc-paths.sh` failed (exit 1) on one
pre-existing reference in docs/feature-work/after-roadmap-va1.md:198 to the
uninstalled Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean. The same
reference is present at the pinned base. It is outside this lane; no fix was
attempted. No missing reference from this new handoff was reported.

Regression controls:
`PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-lowering/census_controls.py`
passed for local/private instances, examples, comment-hidden imports, dependency
order and cycle rejection. These are external tooling tests, not Lean proofs.

## Toolchains and measurements

Official coordinator pin: `leanprover/lean4:v4.35.0`, asset
`lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Downloaded archive matched exactly before extraction.

Old: Lean 4.24.0 release, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake `5.0.0-src+797c613` (Lean 4.24.0).
New: Lean 4.35.0 release, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb` (Lean 4.35.0).

VM: 16 GiB hard cgroup cap, CPU quota four cores, no configured host swap.
The runner uses LEAN_NUM_THREADS=1, a 4 GiB host/cgroup available reserve,
250 ms process-group RSS sampling, and foreground command/process-group
assumptions. Per-process Lean memory is bounded with -M11000; this is not a
separate hard 12 GiB aggregate job cgroup. No systemd-run is used.

Both prerequisites passed:
`lean -j1 -M11000 --tstack=131072 Solidity/KeySort.lean` with each absolute
versioned binary. Old: exit 0, 3.012218324 s, sampled peak 257,933,312 bytes.
New: exit 0, 2.276659811 s, sampled peak 506,077,184 bytes.
The RSS increase is about 96%, while wall time improved about 24%.
QPERF1 was resolved by the coordinator on this continuation. Verbatim answer:

> a per-module time or memory increase does not stop a migration lane. Record
> the before/after numbers for that module and continue to the matched clean
> full-build comparison the task requires; the coordinator reports memory/time
> growth to the human with the cut-over escalation.

The KeySort numbers are retained as escalation evidence. They do not block the
matched clean full-build comparison. No RUNTIME_GATE_PASS claim.

The first old full gate was INVALIDATED: its timing/guard runner died across
the previous turn boundary while its child continued. The skeptic detected
this on resume. Only the verified owned orphan group was stopped; partial
logs and build were preserved under invalid-* artifacts and are not accepted
measurements.

The clean old full gate is restarted via a detached `supervise.py` using
`nohup setsid -f`, then `./run-lean.sh`, using a private config
created by `prepare_config.py`: cache disabled, fresh .lake/build, private empty
XDG cache, and -j1 -M11000 on all Lean libraries/executables. A process snapshot
confirmed one Lean worker and the actual bounded arguments. Its final outcome
and complete wall/RSS measurement remain pending. Old/master artifact caches
are not used. The configuration and full log are off Git.

The initial waiting pipeline also died and was not accepted. The replacement
`supervise.py` starts `pipeline.py` only after a passing old gate. It waits
for old results, acquire the writer lock, verify source/configuration provenance,
preserve the old build, create an empty new build, and pass the same held lock
into the new bounded run. Both wall and sampled RSS regressions escalate;
either exceeding 10% stops. Failed/incomplete measurements cannot pass.
No performance comparison is accepted until both complete equivalent runs pass.

## Independent reviews

Read-only finder `/root/finder_setup` and skeptic `/root/skeptic_setup` used no
Lean server or Lean checks. Findings and resolutions:

- Added omitted instances/examples and then seven local instances; regenerated
  census. Skeptic checked all 661 source hashes and counted 42 instances/103 examples.
- Added cycle rejection and explicit dependency-order controls.
- Runner now rereads Git status, checks host reserve and configured host swap,
  and states its sampled/foreground limits. Explicit -j1 verified in active ps.
- Pipeline now acquires lock before reading old result, transfers the same fd
  to its child without an unlocked transition, checks provenance, and compares
  both wall and RSS. Missing metrics now have a typed blocker/nonzero exit.

The resumed finder additionally found two deriving commands and two instance
attribute commands missing from the lexical inventory. API directives are now
recorded, with regression controls and explicit pinned-base source/path checks.

The resumed skeptic detected the dead runner/pipeline and invalidated the old
run. Both reviewers checked the replacement detached supervisor, atomic
five-second runner heartbeats/results, inherited-lock transfer, and reliable
owned-group cleanup even after a leader exits. Lightweight controls passed for
normal completion, inherited locks, signals/descendants, and dead-leader cleanup.
The detached smoke process survived a tool return. Monitoring continuity and
complete final metrics remain required before accepting the restarted run.

Both reviewers confirmed those fixes. Full migration milestone reviews remain
pending; these reviews accept no unrun gate or semantic compatibility claim.

## Outstanding work and handoff

1. Complete clean old baseline and census/API compatibility (checkpoint 1).
2. Obtain exact-file owner coordination for any required edit;
   compile with the identical new toolchain, fixing only assigned originals
   and preserving all types/semantics/proof budgets (checkpoint 2).
3. Build every assigned module, final repository gate, before/after wall/RSS
   comparison and independent migration reviews (checkpoint 3).
4. Export final migration patch/bundle, accepted frozen-interface hashes and
   cross-directory report to migrate-root-gate (checkpoint 4).

No whole-goal completion, push, merge, PR, cut-over, or freeze announcement.
Saved tooling patch/bundle and immutable evidence manifest live under
`/workspace/migrate-lowering-artifacts`; live build logs are not checksum-bound
until closed. See the external handoff for exact committed head and current state.

## Continuation checkpoint: repaired monitoring and explicit acceptance

QPERF1 is resolved; questions are empty. The original goal is still unfinished.
The repaired supervisor is PID 34201, runner 34202, build group 34224. Repeated
independent finder/skeptic snapshots confirmed adopted supervisor, live runner,
advancing heartbeats and one bounded Lean worker across tool returns. Current
state is in `supervisor.json` and `old-clean-full.live.json` under the external
evidence directory. The earlier unguarded run cannot establish a baseline.

`acceptance.py` writes off-Git `evidence/acceptance.json`: explicit all-661-module
accounting from build logs, per-module reported durations, current-byte hashes
for the 402 external project dependency modules, and the 146 direct external
edges. These dependency hashes are not elaborated interface hashes. Module
growth is recorded for escalation under QPERF1. Missing modules never count as
built, failed gates dominate pending results, and both full reports require
positive finite wall/RSS values. The matched full comparison alone governs
the performance stop. Pipeline writes this report after its new full gate;
rerun the report manually after an old-gate failure or to refresh progress.

`acceptance_controls.py` passed module-growth-with-improved-full-metrics,
missing module, missing result, old failure without new result, failed/resource
stopped run and zero/nonfinite/missing metric cases. Finder and skeptic reviewed
these rules independently; their confirmed classification findings were fixed.
No full migration gate is accepted by these tooling reviews.

Three useful backfill/tooling items are saved: complete lexical/directive census
and controls; repaired detached serial supervision and lifecycle controls; and
deterministic acceptance/dependency reporting with negative controls. Fresh-thread
handoff goes to the coordinator with this same VM, branch and original goal;
no replacement goal or competing continuation was created. Full migration work
continues through the saved supervisor, followed by the still-pending owner/API
work, affected validation, performance comparison and migration reviews.

## Second continuation: reserve accounting and master inspection

Fetched origin/master before new work; it is now `96788a953` and still selects
Lean 4.24.0. Its post-base Lowering diff is empty: no landed Lowering migration
to reuse or rebase onto. The pinned migration branch/source tree is retained.
The pipeline repeats fetch/log/owned-code/toolchain inspection before starting
the new-toolchain item. Relevant master changes stop for rebase review so a
pinned old baseline cannot be silently compared against a different source tree.

The first supervised restart stopped safely with exit 125 after
1,123.051359 seconds: raw cgroup charge reached the guard threshold while the
sampled process-group peak was 6,240,215,040 bytes. No new gate started, and no
baseline or slowdown result is accepted. This failed run is preserved under
`evidence/attempts/old-reserve-stop`; its generated build is retained separately.
The machine reported no OOM and roughly 6 GB of charged file cache after stop.

The repaired guard keeps the same 16 GiB VM cap, 4 GiB available-memory reserve,
no swap, -j1 and -M11000. It credits only clean unmapped file-LRU cache when
estimating cgroup availability; mapped, dirty/writeback, shared and unevictable
pages are excluded. Host MemAvailable is checked independently. This is a
sampled availability estimate, not a guarantee of 4 GiB of uncharged memory.
Both matched measurements restart clean under the identical repaired policy.
Snapshots, minimum sampled availability, and guard/configuration SHA256s are
recorded; mismatched policies/configurations cannot yield an accepted comparison.
Kernel page cache is not forcibly dropped; Lean/Lake artifact caches are empty
and disabled for each clean measurement.

Finder and skeptic independently reviewed the availability definition. Skeptic's
transient-over-cap arithmetic and inconsistent-stat cache-credit findings were
fixed and added to controls. Memory controls cover cache-heavy usage, protected
pages, true low availability, swap, cap overshoot, and inconsistent statistics;
runner lifecycle controls pass under the repaired policy. No proof budget,
production source, frozen statement, root registration or toolchain pin changed.

The repaired run passed the previously incomplete Backend/Scalar/PowerBounds
module (reported 228 seconds) and continued. At the observation after completion,
sampled process-group peak was 8,387,137,536 bytes and minimum estimated cgroup
availability 8,037,072,896 bytes. This validates progress past the previous stop,
not completion of the full baseline. Runtime guard/configuration files are now
held fixed throughout the matched measurement pair.

The running log also exposed Lake's informational-success marker. Acceptance
now counts `ℹ ... Built` (including its optional variation selector), alongside
success and warning markers, and still excludes failed `✖ ... Building` rows.
Negative controls and independent finder/skeptic review confirmed this fix.

H70 disposition was received for the earlier 263d92c4d checkpoint: no verified
owner-ticket payload or recipients recovered; relay.sh is host-only; routing
grants no original-file edit permission. The running supervisor is preserved.
No original production file has been edited. Census/API follow-up waits for the
serial supervisor to finish, as requested; no full comparison is inferred.

## H70 continuation: proof-budget classification and owner waits

The latest routing names three pending inputs for elaborated API/axiom
comparison: `Solidity.Syntax.Raw` from migrate-syntax,
`Solidity.Hash.CollisionBound` from migrate-hash, and `Solidity.Source.Ctor`
from migrate-source. All three are in the pinned dependency closure and remain
read-only here. Current-owner delivery pending was reported as none; host relay
journals, owner agreement and actual validation are distinct, and none is
inferred locally from routing. No original-file edit permission was granted.

No saved 224-file classification manifest was recovered in this checkout or its
artifacts. The deterministic proof_budgets.py report covers all 661 assigned
source files, preserving their pinned hashes and marking the requested 224-file
subset unreconciled. It does not invent a membership list or declare that subset
finished. The generated report remains off Git as
`/workspace/migrate-lowering-artifacts/evidence/proof-budget-classification.json`.

Every file has no recognized explicit local budget option. Both installed
source trees declare maxHeartbeats 200000 and defaultMaxRecDepth 512. Source
hashes are recorded, and equality is labelled source_defaults_equal: this does
not establish effective elaborated command options. Lexical decide candidates
occur in 248 files, +kernel candidates in 138, with 28 overlapping; term uses
are included and labelled as candidates. No lexical +native/native_decide uses
were found. Comments, strings and quoted identifiers are excluded. These are
source classifications, not tactic elaboration, proof, API or axiom acceptance.

Controls passed masking, qualified-reference exclusion, modifier chains,
explicit-option detection and source-only wording. Independent read-only finder
and skeptic confirmed the counts/hashes and boundaries; skeptic's stronger
inherited-default wording was corrected to no-explicit-source-option. Neither
reviewer used Lean or changed files. The active supervisor/heartbeat is preserved;
no extra Lean job, restart or original production-file edit was performed.

## H70 partial Hash input receipt

Received the coordinator's inline CollisionBound overlay from reported Hash
owner head `a3f49ee0ec1829e63022c90194048d5a1ffe0d22`, reported source
`2a18afcd`. Owner full affected gates remain pending. The host receipt path is
not available in this VM; reconstructing the supplied bytes matched its exact
advertised SHA256:
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
This establishes payload identity, not host-journal acceptance or owner validation.

The frozen original blob is
`b54c93a5b24340a19160c1fb378d057ccee60f84`. `git apply --check` passed.
A read-only in-memory replay of seven hunks produced
`092971eda8c7d6997276a92ba19b25b7ce05844e`, matching the advertised target
prefix. No production or test Lean source was patched. The reported owner
commit identifiers were not independently verified as local Git objects.

The exact raw patch is off Git at
`/workspace/migrate-lowering-artifacts/evidence/owner-inputs/collision-bound-overlay.patch`.
A small versioned JSON line-array fixture losslessly regenerates those bytes;
normal whitespace checks remain intact. inspect_hash_overlay.py verifies the
receipt SHA, single target, exact base, context/counts, applicability, candidate
blob and unchanged production bytes. Its replay routine supports this fixed
patch format, not arbitrary patches. Controls reject corrupted contexts/counts
and empty patches, and verify the Git empty-blob identity.

Read-only finder and skeptic found no visible statement/premise/budget/axiom or
trust-shortcut change in the eight proof-body edits. Both confirmed that all
Lean, API/axiom and performance acceptance stays pending. No Lean job was run
for this receipt, and the existing serial supervisor was preserved. CollisionBound
therefore changes from input missing to partial input received, awaiting affected
validation; Raw and Ctor inputs/comparisons also remain pending. No routing or
receipt check is treated as original-file edit permission.

## H82 retirement: STOPPED, handoff to migrate-root-gate

Human-approved retirement explicitly selected successor
solidity-h62-6-20261106/migrate-root-gate and prohibits automatic implementation
continuation. This lane stopped its verified runner43924 via SIGTERM. The runner
cleaned process group43946 and supervisor43923 exited without starting the new
stage. No live owned supervisor/runner/group remains. The old run ended with
exit125 after9911.253174743s and sampled aggregate peak9010499584 bytes; this
intentional retirement interruption is NOT an accepted clean baseline or a
completed performance comparison. It built333 of661 assigned old-toolchain
modules; zero new-toolchain modules were built. All four checkpoints remain
incomplete. Historical running-job sections above are superseded by this section.

The later generic H82 standing message says Continue, conflicting with the
specific retirement/accepted-successor instruction. QRETIRE1 was raised; no
reply was available during preservation. No proof work resumed. The latest
standing rules and retirement text are both retained in the handoff packet.

PAUSED cannot be requested with the exposed goal tool: only complete|blocked
outcomes exist. No pause/get-goal tool is exposed. Do not claim a PAUSED tool
transition or goal completion. The final exported report records the actual
available halt-tool outcome and the capability failure; no automatic
implementation continuation is authorized. No new/reset goal or VM was created.

The authenticated patch/bundle includes files under
`tests/h62/item6/migrate-lowering/handoff/`: the full visible original assignment
transcribed from this thread, original goal objective, original work/backfill
queues, exact664-entry scope manifest (661 original Lean files plus three support
paths), owner map, later H82 messages, all open items/waits, and SHA256SUMS.
No local raw launcher/thread export was found. The saved visible assignment is
honestly distinguished from unestablished byte identity to launcher hash762a63…;
its actual hash is recorded. This is not a fabricated matching launcher export.

No H71 push grant was supplied or found in the available records. This lane did
not push any branch; master was never pushed or merged. All original production
sources, frozen statements, budgets and the tracked toolchain remain unchanged.
Successor is responsible for integrating the final stopped head. Original VM,
branch, source tree, build/cache diagnostics and bulk evidence are preserved.
The final cumulative exports and closed evidence archive are under
`/workspace/migrate-lowering-artifacts/retirement/`; the exported report supplies
exact final head, clean/dirty status, absolute paths and checksums.

Final coordinator resolution: KEEP RETIREMENT AND HANDOFF. QRETIRE1 is resolved;
generic Continue broadcasts, producer tickets, cache notices and router advice
cannot revoke this lane-specific stop. No further implementation is authorized.
The attempted available halt call stop_goal(blocked) returned InvalidArguments:
"stop_goal requires trusted goal and source-turn context from CCA." No goal
transition was established. PAUSED is also unsupported by the exposed schema.
The coordinator explicitly will set the existing goal paused after the final
head report and idle turn. No human decision or new goal is needed. Physical
jobs remain stopped, and the successor receives the final stopped-head ack.
