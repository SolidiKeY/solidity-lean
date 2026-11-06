# H28 semantic mutation testing

Status: partial. Three concrete guard/control development cases have checked
semantic witnesses; the frozen assignment is not complete. The full candidate
manifest is not frozen, the general runner has passed its committed six-case pilot, and no full-assignment mutation
score or scope-complete acceptance is claimed.

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h28-sol-20261104/mutation-testing`.
No production input, statement, premise, exclusion, refusal, intrinsic type,
proof budget, shared root or producer implementation has changed.

## Checked concrete witnesses

The development cases are
[guard-cases.draft.json](../../tests/h28-sol/mutation-testing/guard-cases.draft.json).
They are a source-hashed subset for developing the checker, not the exhaustive
assignment manifest.

| Exact ID | One-change edit | Inhabited counterexample |
|---|---|---|
| `guard.require-success-false` | `requireSimple` success guard `true` to `false` | `require(true)` succeeds, but both mutant antecedents are false, so the premise admits a false postcondition. |
| `guard.require-revert-true` | `requireSimple` revert guard `false` to `true` | `require(false)` reverts, but the mutant again admits the false postcondition. This adds the opposite-polarity negative control. |
| `control.revert-diamond-true` | `revertDiamond` closes to `true` instead of `false` | The actual revert cannot satisfy a diamond, while the mutant closes even with a false postcondition. Its edit is independent of the two guard edits. |

Each witness proves an actual constructor instance (`source_link`), an inhabited
`State`, premise acceptance of false, real modal rejection of false, and
`¬ Premise.Sound` for the same statement, premise and state. The proof uses a
concrete continuation, frames and postcondition to refute the universally
quantified soundness interface; it does not replace that interface or weaken it.
The normal baselines independently check the original constructor and typed run.

[Isolated evidence](../../tests/h28-sol/mutation-testing/evidence/guard-checked-isolated/result.json)
contains all 18 validated checks: for each case, fresh normal and mutant source
trees each compile production Rules, check the original oracle, and check the
semantic witness. The original oracle passes only on the normal tree; the
witness passes only on the mutant tree. Rejections must be exactly the expected
source-link type mismatch; errors are never semantic kill evidence by themselves.
The successful witness and its source link supply the checked semantic evidence.

Actual theorem signatures, axiom sets, executed oracle snapshots, commands,
exits, timings, RSS, hashes and one-change diffs are retained per case.
Successful declarations use only `propext`, `Classical.choice`, `Quot.sound`.
Expected failing source-link checks can print Lean's error-recovery `sorryAx`;
those nonzero checks are not accepted proofs. The successful-proof validator
rejects `sorryAx`, unexpected axioms, warnings, missing signatures and errors.
No source `sorry`, axiom, unsafe code, native_decide or heartbeat increase was added.

The isolated run took 103.795428 seconds across 18 checks; maximum actual Lean
child RSS was 1,461,844 KiB. Cgroup peak charged memory was 548,257,792 bytes.
These are different measurements: shared mapped pages may be charged to a
parent cgroup. Neither number is substituted for the other.

## Bounded execution and cache trust

[bounded.py](../../tests/h28-sol/mutation-testing/tools/bounded.py) runs one Lean
process at a time with `LEAN_NUM_THREADS=1`, explicit `-j1`, unchanged stack and
heartbeat settings, a hard 6 GiB Docker limit, zero swap allowance, no network,
read-only source/runtime/cache mounts and a 4 GiB headroom guard. Only `.lake`
artifacts are writable. Docker inspection checks the requested bounds, mount
permissions, network mode, OOM status and measured exit consistency. The
external [measure.c](../../tests/h28-sol/mutation-testing/tools/measure.c)
helper records wait4 child RSS and elapsed time; it is instrumentation, not a
Lean trust mechanism. Tool/runtime and log hashes are recorded in the latest
backend controls.

The supplied old `.lake` artifacts were stale. The
[dependency bootstrap](../../tests/h28-sol/mutation-testing/evidence/cache-bootstrap/manifest.json)
rebuilt all 68 oracle dependency modules from the exact pinned base, without
reusing any existing olean, in 424.262461 seconds. Source and output hashes and
all commands/exits/cgroup peaks are retained. Those earlier bootstrap checks
predate the wait4 helper, so per-process RSS is unavailable there; cgroup peaks
are explicitly labelled. Cache tree:
`/workspace/h28-runtime/prepared-base-6f3eedf0`.

Every probe has a fresh private artifact overlay. Cached reverse dependencies
of Rules are unavailable; the allowlist excludes the original Rules, Taclet
and CallbackRules artifacts. `/cache` is not on LEAN_PATH. The reviewed oracles
import only Rules and PremiseSound, so no cached theorem about a changed rule
can be reused. Input source hashes are checked before and after Lean commands.
This older scoped development driver supports Rules targets only; the
committed-manifest engine and its executed pilot are documented below.

## Validation and reviews

[Final launcher controls](../../tests/h28-sol/mutation-testing/evidence/backend-controls-final/result.json)
pass all four actual checks: an allowed cache import succeeds; an excluded
cached Taclet import is refused; a source write fails and its hash is unchanged;
a timed-out container is removed. These IO fixtures are external launcher tests,
not semantic proof oracles.

[Initial unit controls](../../tests/h28-sol/mutation-testing/evidence/validator-selftests-final.log):
27 passed at the pre-engine checkpoint. They cover false-kill classifications, missing/extra diagnostics,
axioms/signatures, malformed output, infrastructure errors, unrun accounting,
unique edits and disabled general execution. Synthetic parser messages are
never used as semantic proof evidence.

[Saved-output replay](../../tests/h28-sol/mutation-testing/evidence/validation-replay.log)
revalidates the exact six phase keys, executed-source snapshots, log hashes,
18 semantic checks and four final backend controls. This is validation of saved
results, not a new Lean run.

Separate read-only finder and skeptic reviews, neither using Lean server,
confirmed the substantive witnesses. They found the unfiltered cache fallback
and an infrastructure-error false-pass path in two launcher controls. Both
were fixed, with isolated reruns and regressions. Final verdict: safe as the
three-case partial development checkpoint, not assignment acceptance. See
[reviews](../../tests/h28-sol/mutation-testing/evidence/reviews-guard.json).

Actual Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613. The earlier permitted KeySort probe passed with explicit
`-j1`, an 8 GiB hard cap, zero swap and over 4 GiB headroom:
[KeySort gate](../../tests/h28-sol/mutation-testing/evidence/runtime-keysort.json).
RUNTIME_GATE_PASS applies to that runtime readiness probe only.

Failed development attempts remain visible: the initial stale/missing artifact
probes and the signature parser's refusal of abbreviated #check names. Their
logs are retained in `evidence/guard-development` and `evidence/guard-checked`.
The fully qualified signature probes and rebuilt cache address those failures.
Earlier unit timing collection also records that `/usr/bin/time` was absent;
Python resource accounting was used for those Python test processes.

## Inventory, publication and full queue

The reproducible
[draft census](../../tests/h28-sol/mutation-testing/inventory.draft.json)
contains 215 constructor rows: 181 Taclet, 28 LeanTaclet, four CallbackTaclet and
two Rule wrappers, with source hashes. Family classification is heuristic;
clause/operator-instance coverage and the exhaustive candidate manifest remain
unaccepted. Eight standalone oracle files have a
[local registration manifest](../../tests/h28-sol/mutation-testing/registration.json).
No central root or shared module map changed.

The coordinator's published master update was fetched and verified as
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`, including ancestry from the H28 base.
The assigned branch was not merged or rebased; H28 production inputs stay frozen
at its original base. The new producer APIs are not duplicated or needed by
these pinned rule probes. The coordinator's global gates are not claimed as
this lane's final acceptance.

1. Inventory: partial. Finish every constructor clause and operator-instance
   disposition in the nine assigned families, select exact edits and semantic
   oracles, review and freeze the exhaustive manifest.
2. Runner: partial. The committed-manifest engine now implements provenance checks, dynamic
   reverse-dependency filtering, fresh source-audited trees, checked kill and
   equivalence certificates, visible survivors and score denominators. The frozen six-case pilot passes; integrate the remaining families
   and whole-assignment acceptance.
3. Semantic witnesses: partial. The three cases above are checked; they do not
   complete the whole guard family. Overflow, division/minimum, index bounds,
   push dirty tail/length ordering, pop/delete, alias capture once,
   rollback/payment and callback frames remain open, together with any remaining
   selected guard clauses. Preserve inhabited controls and exact axiom signatures.
4. Full manifest execution, final repository gates, independent scope-complete
   acceptance and the final immutable seal/handoff: pending.
5. Backfill: partial. Opposite guard polarity is covered; continue additional
   negative controls within the selected families, never producer repairs.

The persistent goal remains unfinished and needs no new scope authorization.
Continue in the same VM and branch. Keep every statement, premise, exclusion,
refusal, observation, budget, intrinsic type, H16/H19/H25 Source freeze, frozen
H22 Core ExtCall and H21/shared registry boundary intact. Do not push or merge.


## Committed runner implementation and executed pilot

`tools/engine.py` requires a clean assigned branch, exact base ancestry, a
committed schema-2 frozen manifest, committed inventory/cache metadata/oracles,
all frozen source and theorem signature hashes, and unchanged runtime binaries.
It dynamically excludes every cached reverse dependency of the mutated module.
A single advisory writer lock covers each run. Evidence is written outside the
checkout, preserving clean input provenance. Checks retain commands, exits,
timings, RSS, hashes, source inventories and actual one-change diffs.

`manifests/runner-pilot.json` freezes exactly six cases with scope `pilot`: the
two guard mutations, the independent revert known kill, a branch-label semantic
equivalence control, malformed guard syntax for invalid compilation, and a
transparent duplicate guard edit observed by a deliberately weak primary oracle.
The last case must remain `surviving` even though its concrete semantic witness
and stronger regression demonstrate the defect. The regression must pass on
the normal baseline. It is an unscored runner self-test, not a relabelled scored
mutant. Known-kill independence and every score exclusion are explicit.

`GuardEquivalent.lean` has a real universal constructor link and equality of
premise formulas for all contracts, contexts, simple conditions, modalities,
fresh counters, continuations, frames and postconditions, plus an inhabited
input. It passes against the normal production rule. The executed pilot also checks it against the actual changed-label constructor;
the universal certificate passes on both normal and mutant trees.

The implementation unit gate passes 61 tests. The final actual launcher gate
passes four controls in `evidence/backend-controls-engine-final`. Read-only
finder/skeptic reviews confirmed fixes for control-gated scoring, independent
baseline regression validation and cleanup priority. Unconfirmed teardown now
aborts subsequent heavy checks before parsing can mask the cleanup failure.
Neither runner completion nor a pilot score can set `scope_complete=true`.

Two conservative memory-guard refusals remain visible in
`evidence/backend-controls-engine*`: no Lean ran in the first; only the allowed
import ran in the retry. The retry's raw intermediate JSON incorrectly emitted
pass=true for a completed subset although its CLI exited 1. A retained
failure.json explains this defect; control summaries now require all declared
checks and list unrun IDs. No failed attempt is counted as a passing gate.

The available-memory guard now distinguishes strictly unused cgroup bytes from
estimated reclaimable clean inactive-file cache, subtracts dirty/writeback
bytes, caps against OS MemAvailable, and records each quantity. Missing or
malformed counters give zero reclaim or refusal. The reserve is estimated
available headroom after reclaim, not already-unused RAM; hard6GiB/no-swap
limits and the 4GiB reserve are unchanged. Both reviewers checked this
interpretation. OOM, timeout and cleanup failures still remain errors/stops.

The inputs were committed and the entire six-case pilot executed from
`31518385cd7f130e66796faedd730464519cef37` into
`/workspace/h28-runner-pilot-31518385`. The subsequent evidence commit changes
only documentation/evidence; it does not change those executed inputs. Continue
the unchanged nine-family queue; this pilot is not whole-family or
whole-assignment completion.


## Pilot outcomes and immutable input identity

The executed manifest hash is
`16a05d59974830d848051b58873f1004e6f960dd6537f0dbc77f1250bf18fc1d`.
All six cases completed and all 35 phase logs have exact commands, exits,
elapsed times, actual child RSS, cgroup limits/availability, cleanup confirmation
and hashes. Source/archive identities, proof signatures and axioms are retained
in `evidence/runner-pilot-31518385`, with the original SHA256SUMS unchanged.
Both independent reviewers audited the actual run and found no discrepancy;
see `evidence/runner-pilot-audit.json`.

| Case | Actual outcome | Score disposition |
|---|---|---|
| `guard.require-success-false` | killed by checked semantic witness | scored |
| `guard.require-revert-true` | killed by checked semantic witness | scored |
| `control.revert-diamond-true` | killed by independent checked witness | known-kill control, unscored |
| `control.guard-label-equivalent` | equivalent, universal certificate on both trees | equivalence control, unscored |
| `control.guard-invalid-syntax` | invalid compilation | invalid control, unscored |
| `control.guard-weak-oracle-survivor` | surviving; concrete witness and stronger regression checked | transparent duplicate runner self-test, unscored |

The pilot denominator is exactly the two scored guard IDs: 2 killed out of 2.
No unrun case is scored. The survivor remains visible; its stronger regression
passed normally and rejected the actual mutant without relabelling the primary
oracle outcome. These controls and exclusions were declared before execution.
`runner_cases_complete=true` and `scope_complete=false` distinguish pilot
execution from assignment acceptance. This is not the full H28 mutation score.

The peak recorded child RSS across the pilot was 1,454,092 KiB. No phase timed
out or OOMed, and every launched container has confirmed removal. The current
full-queue obligations above remain binding and unfinished.


## Unsigned overflow development checkpoint

Two further source-linked semantic witnesses pass12 fresh normal/mutant checks
in `evidence/overflow-checked-complete`: replacing the typed compound numeric
helper body with subtraction, and erasing the local-increment update. Both
start with a valid maximum uint256 stack local. The original checked addition
or increment reverts; the mutant has an explicit successful typed landing and
admits a true postcondition. Each `checked_kill` is an unconditional negation
of the existing Premise.Sound interface on that same input.

The helper edit preserves its original generic signature, compound-operator
premise and numeric premise. The local-increment edit is an additional negative
control. Separate finder/skeptic reviews replayed all12 validations, exact
source/diff/log identities, theorem signatures and permitted axiom sets without
Lean server use. They approved only these development cases.

The initially attempted fixed-minus schema defaulted to uint and failed generic
typing. It remains an invalid candidate in `overflow-schema-invalid.draft.json`
and `evidence/overflow-checked`; it is not counted as killed. The subsequent
helper witness compiled, but its missing #check typed_landing export caused a
validation refusal; that failure is retained too. The corrected witnesses now
include both axiom and type signatures for the concrete landing proof.

`inventory.py --with-term-helpers` reproduces
`inventory.extended.draft.json`:215 constructor rows plus all55 Tms term-helper
definitions. The original215-row pilot inventory remains byte-for-byte unchanged.
The binopC row identifies seven generic compound-update constructors and five
fixed push arithmetic constructors using it; size arithmetic is excluded by
schema pushArithmetic, and fixed subtraction remains unchanged by this mutant.
Full clause/operator and nine-family inventory acceptance remains pending.

`manifests/overflow-pilot.json` freezes these two selected cases plus the
independent revert known-kill control. Its committed runner execution is still
pending. This is not whole-overflow-family or whole-assignment acceptance.


## Adaptive bounded memory profiles

Two frozen overflow pilot attempts refused before launching Lean because the
6 GiB cap could not leave the required 4 GiB reserve. Their unchanged results
and checksums are retained in `evidence/resource-profiles`; all cases remain
unrun and neither attempt contributes a score. The launcher now chooses the
largest of 6, 4 or 2 GiB that preserves the same reserve, otherwise refuses.
Docker limits, in-container checks and inspection agree on the selected cap;
swap remains zero and OOM/timeouts remain errors. All 62 unit controls and four
actual backend controls pass; separate read-only finder and skeptic approve
this resource-policy change. This does not change semantic proof budgets.

The coordinator publication 89373e34cdfd6bb5db7054b1c204d01edffc5fa7 was
fetched and verified at origin/master. The assigned branch remains based on
6f3eedf0788ee1f8a3bcf230558c712ecdca04d5 without merging producer changes.


## Executed overflow pilot and inventory erratum

The frozen overflow pilot ran from 79041a2834070ad37c79fa0e68381207ce97a462.
All three cases were killed with checked semantic witnesses, including the
independent revert control. The selected denominator is two, both killed; no
case remains unrun. All 18 normal/mutant checks retain exact commands, exits,
timing, RSS, signatures, axiom output and confirmed cleanup in
`evidence/overflow-pilot-79041a28`. `scope_complete` remains false.

Both reviewers identified a draft-inventory omission: binopC is also used
transitively by binopI. The frozen inventory is preserved for reproducibility;
`inventory.extended.errata.json` explicitly marks its affected-use list partial
and records additional increment/decrement candidates. Fixed-sub changes add
increments while leaving sub decrements unchanged. This does not invalidate
the actual localOpAssign source link; full clause/operator coverage is pending.


## Division development checkpoint

A distinct conditional helper-body edit substitutes subtraction only for div,
preserving all numeric/compound typing premises. Six fresh normal/mutant
checks pass in `evidence/division-development-landing`. The Boolean family
uses signed minimum divided by -1 and 1 divided by zero. Both actual runs
revert; both mutant updates have explicit typed landings and unconditional
negations of Premise.Sound. The two inputs share one source-linked mutant ID
and count as one selected mutation, not two denominator entries.

Three earlier development refusals remain immutable: ill-typed literal, unused
binder warning, and an open local-valuation proof. No refusal is called a kill.
The final source-linked witness has no open obligations or placeholder axioms.
`manifests/division-pilot.json` freezes this case plus the independent revert
control; committed execution and full-family acceptance are still pending.


The frozen division pilot executed from
`a887c1a5f81ca572f81a5318f8365fdaad0c7363`: both cases killed in 12 checked
phases, including the independent known-kill. The selected denominator is one
mutation with two distinct boundary witnesses, killed; no case is unrun. The
byte-identical sealed evidence is `evidence/division-pilot-a887c1a5`. Scope
acceptance remains false; full family/operator and assignment gates are pending.

Separate read-only finder and skeptic audits pass for these 12 phases; see
`evidence/division-pilot-audit.json`. Peak child RSS was 1,454,904 KiB; all
checks used 4 GiB/no-swap profiles and preserved at least 4 GiB reserve.


## H35 VM build, axiom inventory and cache transport

H35 adds cache transport as a checkpoint acceptance requirement. Previous
pilot execution results remain valid, but H35 integration acceptance is pending
a transport receipt. A normal source-linked oracle and a mutant-only kill
witness must be compiled in their respective disposable trees; the latter
is intentionally rejected against normal source. No witness is weakened to
make all modules compile together against normal production.

The runner now produces and retains successful `.olean` outputs after exact
diagnostic, frozen signature and axiom validation. Files are isolated by case
and baseline/mutant phase, with source/output SHA256 and size. Missing, empty,
symlinked or overwritten artifacts refuse acceptance. Expected negative checks
retain no compiled artifact. These outputs are not represented as Lake cache
mappings or a transport receipt.

Every theorem in each owned oracle, including unselected helper theorems, must
now have exactly one #print axioms export and only the existing permitted
axioms. The shared restricted source scanner handles nested and line comments,
refuses string/quoted-identifier/quotation syntax and anonymous proofs, and is
used by both trust preflight and theorem inventory. Independent reviews found
and closed the string-comment hiding and anonymous-example gaps. All 65 unit
controls and four actual launcher controls pass in `evidence/h35-controls`.

The requested pinned `ship-cache.sh` was actually run twice. Its default
coordinator-only head check exited 2. With documented lane-head override and
the actual local Lake cache it exited 1 because the coordinator poll-state
catalog is absent; vmexec.py is absent too. It generated local shipment data
but transported nothing. `evidence/h35-shipping-preflight` retains commands,
exits and complete logs. Q-H35-TRANSPORT asks which VM-to-coordinator transport
to use. No receipt or H35 completion is claimed while that question is pending.


Fresh runs from `6b5d1fdb758a68d417b9ec92691099643f954933` pass all
65 phases across the three frozen pilot manifests. They retain 46 regular
compiled artifacts and 103 theorem axiom exports across 25 successful owned
source checks. Both independent final reviews pass. Every check used -j1,
4 GiB/no-swap, required reserve and confirmed cleanup; peak child RSS was
1,466,216 KiB. Dispositions and pilot denominators are unchanged.

`evidence/h35-vm-build` contains text receipts and a catalog referring to the
full external runs and 96,188,452-byte local export archive. The archive
includes the compiled proof worlds, all fourteen oracle source snapshots and
the exact pinned dependency cache. Its SHA256 is
`aeceb8036520bfa9df52a225053b8de6597747f8b3c46de299d630a22268c168`.
The renamed EXTERNAL-RUN-SHA256SUMS apply to the complete external directories,
not the text subset. Mutant Rules/witness artifacts must remain isolated from
normal production caches. This export is not a Lake mapping shipment.

The requested shipping script was also called after the fresh VM gates and
again refused the lane head. No cache transport receipt exists. All H35
integration checkpoint statuses remain partial pending that receipt, although
the recorded pilot executions and VM proof builds pass. Original full-queue
obligations remain unchanged.


### Q-H35-TRANSPORT

Sources: H35; pinned scripts/coord-tools/ship-cache.sh (coordinator relay).
The actual VM calls failed: default master-only check, then absent coordinator
poll-state catalog/transport after the documented lane-head override. Which
transport should this lane use for its completed local export?

1. Provide a VM-to-coordinator exporter and destination; run it here and retain
   its actual receipt before H35 acceptance.
2. Have the coordinator retrieve the sealed VM archive and issue a transport
   receipt; retain H35 status partial until that receipt arrives.

No option is assumed or recommended. The existing persistent full objective
remains unfinished; no goal has been created, reset or completed.


## H41 cache pull and continuation

H41 authorizes leaving VM cache packs with path and SHA256 for coordinator
pull. This resolves Q-H35-TRANSPORT without an invented transfer receipt. The
existing 96,188,452-byte archive was rehashed successfully on resume;
`evidence/h41-cache-pull.json` records its absolute path and hash. The 65 VM
checks, 46 artifacts and 103 axiom exports remain the accepted local gate
evidence. Coordinator pull has not been observed. Continue the original queue.

Published master 8bf8321873befa3f35ca31e97e5339a1baee93e6 was fetched and
its ancestry verified. The owned branch and immutable 6f3eedf0 base are
unchanged; no producer changes were merged.


## Index-bound development checkpoint

`bounds.array-read-skipped` changes only storageIndexReadArrayFind RHS from
find(storage, arr[ie]) to the target local v. It preserves every typed receiver,
array-kind and simplicity side condition while omitting the indexed read.
Six fresh normal/mutant phases pass in `evidence/bounds-skipped-checked`.
The actual generic source link covers dynamic and fixed array roots. The
concrete dynamic-empty read and fixed index equal to length both revert, while
the mutant has explicit inhabited identity landings. Both nonempty live-read
controls execute and store 7; the initial local and mutant result are 9.

The initial default-value DSL edit failed generic typing and remains an
invalid, unscored candidate in `bounds-default-schema-invalid.draft.json`.
Other development failures preserve a mismatched Out type, closed controls
requiring existing irreducible definitions unfolded, source-link attribution
format/implicit-side-condition errors, and an unfinished local landing read.
No failure was scored or relabelled as killed. The final statements retain
their original strength, explicit typed states, premises and proof budgets.

`manifests/bounds-pilot.json` freezes the reviewed selected edit, both boundary
witness exports, positive controls and an independent revert known-kill.
Committed execution, artifact build/axiom gate and H41 cache pack follow; this
is not complete index-clause or whole-assignment acceptance.

Separate read-only finder and skeptic reviews pass for the six development
phases and exact frozen inputs (`evidence/bounds-review.json`). Fresh runtime
gates on the resumed VM pass: Lean 4.24.0, Lake 5.0.0-src+797c613 and KeySort
exit 0; all 65 unit controls and four actual launcher controls pass. Their
commands, exits, timings and RSS are in `evidence/bounds-runtime-gate`.


The frozen bounds pilot executed from
`e852854de93f20e1529549db1be5b9a6d0811b79`: 12 checked build phases, eight
compiled artifacts and 27 theorem axiom exports pass. Both the selected mutant
and independent control are killed, denominator 1/1, no unrun cases. Separate
read-only finder and skeptic audits pass. Every check used -j1, 6 GiB/no-swap
and confirmed cleanup; peak child RSS was 1,456,132 KiB. Full scope stays false.

`evidence/bounds-pilot-e852854d` is an explicit text receipt subset; its H41
pack receipt identifies the complete external cache archive and SHA256. The
prior H35 pack provides the exact pinned dependency cache. Coordinator pull
has not been observed. These pilot outcomes do not complete the full queue.


## Pop/delete development checkpoint

Two distinct constructor RHS edits omit the storage update: storagePopSave
and storageIndexArrayDelete. The original simple-receiver and nonmapping
side conditions remain explicit. Twelve fresh development phases pass in
`evidence/pop-delete-development`, with no earlier rejected attempt. Empty
pop and an indexed delete at length zero really revert; each mutant has
inhabited successful identity landings on empty and populated typed states.
The live controls prove exact Out results: pop removes 7 and clears the shadow
slot to zero, whereas delete clears 7 without changing the live length.

`manifests/pop-delete-pilot.json` freezes these two cases plus the distinct
revert control. The pilot denominator is two, including the independently
declared delete negative control; development evidence remains score=null.
All 65 runner unit controls pass in `evidence/pop-delete-controls`. Committed
execution, all-theorem axiom inventory, compiled outputs and H41 pack follow;
full pop/delete constructor coverage and the original assignment remain open.


The committed pop/delete pilot ran from
`5b488a1159a149ca5f8950f9fcbf9de3008bf2c3`. All 18 phases pass, with
12 compiled artifacts and 34 theorem axiom exports. The two selected cases
and independent control are killed; denominator 2/2, no unrun, scope false.
Separate read-only finder/skeptic final audits pass. All checks used -j1,
6 GiB/no swap and confirmed cleanup; peak child RSS 1,466,808 KiB.
`evidence/pop-delete-pilot-5b488a11` holds text receipts and the H41 cache-pack
path/hash, referencing the unchanged pinned dependency pack. Coordinator pull
is not observed. Continue the original queue with push-tail/update ordering.


## Push recycled-tail and update-order development

`push.reference-tail-cleared` wraps the typed STerm.pushSlot helper result in
a deletion of the just-appended slot, leaving the original helper interface
and rule side conditions intact. On a concrete recycled reference slot the
actual push exposes an inner array of length 1 containing 7; the mutant has an
explicit typed landing with that inner array cleared to length 0. The clean
slot control is unchanged. The postcondition is evaluated through the actual
Theory term bridge, not a separate model of execution.

`push.compound-updates-swapped` reverses the two original updates of
storagePushAddAssign. On an empty array its first update fails ordinarily,
without exhaustion, so the mutant box premise admits false while the actual
compound push succeeds. On a populated array both mutant updates have actual
typed landings linked by the same intermediate state: [7] to [8] to [8,0],
while the actual statement returns [7,1]. This is not an always-failing or
empty update relation.

The selected six tail phases in `evidence/push-tail-order-development` and
six order phases in `evidence/push-order-checked` pass. The first tail attempt
retains a strict source-link formatting refusal; the first order attempt
retains an ill-typed intermediate heap declaration. That declaration was
replaced by the stronger explicit concrete-state landing conjunction. The
constructor diagnostic also records unavailable PairLands under the fixed
import boundary; it is diagnostic-only, not a passing proof gate. No failure
is scored, no theorem/premise weakened and no budget increased.

`manifests/push-pilot.json` freezes the two edits and the independent revert
control. All 65 unit controls pass in `evidence/push-controls`. Committed
artifact builds, complete axiom inventory and H41 pack follow; exhaustive
helper-callsite/operator and whole-assignment acceptance remain pending.


The committed combined push pilot ran from
`ea111ccfa14f9c7ad65691e4f2188c5488af2848`. All 18 phases pass, with
12 compiled outputs and 47 theorem axiom exports. Both selected cases and
the independent control are killed, denominator 2/2, no unrun, scope false.
Separate read-only finder/skeptic final audits pass. Every check used -j1,
6 GiB/no swap and confirmed cleanup; peak child RSS 1,451,232 KiB.
`evidence/push-pilot-ea111ccf` contains the explicit text receipt subset and
H41 pack path/hash with the separately pinned dependency cache. No observed
coordinator transfer or full-family/assignment completion is claimed.


## Authorized delivery rebase onto e6849d3b

The coordinator explicitly instructed rebasing onto
e6849d3bdf516099d20c33d3581d523449764018 before the next commit. Fetch and
ancestry checks pass; all 18 owned commits replayed without conflict. The old
head and alias WIP are preserved by a backup branch and retained stash, listed
in `evidence/rebase-e6849d3b/setup.json`. No work was reset or discarded.

The semantic source/cache base remains
6f3eedf0788ee1f8a3bcf230558c712ecdca04d5: all 68 cached dependency sources
and the pinned production inputs are byte-identical at the new delivery base.
The runner now checks exclusive writes relative to the explicitly authorized
delivery base, while retaining the original source/cache hashes, clean-tree,
committed-input, branch and runtime gates. A real-Git control rejects any new
producer edit after that base and any branch missing its ancestry. Historical
run heads remain factual; their original commits are retained by the backup.

Separate finder/skeptic rebase reviews pass after closing a rename-detection
blind spot: scope diff now uses --no-renames and a real-Git producer-to-owned
move control. All 66 unit controls pass. The alias WIP has an explicit
200000-heartbeat failure in its pure two-call control; its budget and statement
remain unchanged, no mutant run or kill is claimed. That proof will be split
compositionally after the provenance checkpoint is validated.


The fresh six-case pilot from
`f664b046340d0a43374d535ef2fb51654afdfccf` passes all 35 checks, 26 compiled
outputs and 53 theorem axiom exports after the authorized rebase. Separate
read-only finder/skeptic audits pass. Expected kills, equivalence, invalid
compilation and genuine survivor remain distinct; denominator 2/2 and scope
false. Every check used -j1, 6 GiB/no-swap and confirmed cleanup; peak RSS
1,459,724 KiB. `evidence/rebase-pilot-f664b046` provides text receipts and the
H41 pack path/hash with the unchanged dependency pack. This validates delivery
provenance, not completion of the remaining semantic-family queue.


## Alias receiver captured once development

`alias.receiver-getter-twice` evaluates the storage-returning getter twice,
then appends exactly once. The disposable rule uses an explicit typed premise
because the canonical source DSL deliberately accepts only a single capture.
All quantified constructor input types, names, LHS and defaultability premise
are identical before/after (both full signatures are printed in the logs);
only the semantic RHS changes. Production source remains read-only.

The effectful getter increments a storage counter: the actual statement ends
at 1, the mutant at 2, with one array element in both states. The pure getter
control has the same result after one or two calls. Actual call/append and
capture-pop frame executions provide inhabited typed intermediate/result
states. The first monolithic pure-control proof hit the existing 200000
heartbeat limit and remains unscored in `evidence/alias-development`. The same
control and budget now pass using small call/append lemmas composed with the
existing Prog.run_cons_ok. No budget, statement, input or side condition was
weakened. Six fresh phases pass in `evidence/alias-compositional-development`.

`manifests/alias-pilot.json` freezes this case plus the distinct revert control;
all 66 unit controls pass in `evidence/alias-controls`. Committed artifact/axiom
gates and H41 pack follow. Full alias/callsite inventory, rollback/payment,
callback frames and final original assignment gates remain pending.

The frozen alias pilot from64d7def6ef0a417ceb3a964450220930d6f1588c now passes all12 VM checks,8 retained compiled outputs and48 complete owned theorem axiom exports. The selected alias denominator is1/1; independent revert control passes, unrun=[] and scope_complete=false. Separate actual-run and H41 archive finder/skeptic reviews PASS. All checks used -j1,6GiB/no swap and confirmed cleanup; peakRSS1,467,752KiB. Evidence is `evidence/alias-pilot-64d7def6`; its cache-pack.json records the verified6,034,421byte H41 pack path/SHA, ready for coordinator pull with no transfer observed. Full family/assignment obligations above remain pending.

## Payment success flag development

`payment.success-flag-false` changes only the sendNoCallbackBox successful return flag from true to false. Both branches and the payment booking remain present. A funded accepted send books -5 at receiver9, leaves balance5 and returns true. A concrete recipient refusal returns false and preserves the full original state except that return local. The mutant admits a false-return postcondition contradicted by the actual accepted run. Actual typed landings of both mutant updates, with exact paid/unchanged ledger and balances, prevent vacuous box controls. Finder requested these explicit landings; added without changing statements or budgets.

Initial configuration, term notation and local-function conversion failures remain immutable and unscored in payment-development, payment-development-v2 and payment-inhabited-development. The earlier weaker development run passed but is superseded by the strengthened six-phase `payment-typed-development`; all six phases and all66 runner unit controls pass. `manifests/payment-pilot.json` freezes exact sources, edit, theorem signatures and independent revert control. Committed VM builds/complete axiom inventories and H41 pack remain pending; this is not full payment/callback or original-assignment acceptance.

The committed payment pilot from5b2317f359f9105050012ae6a249252357f0c3bb passes all12 VM phases,8retained compiled outputs and27full owned theorem axiom exports. Selecteddenominator1/1, independentcontrol killed, unrun=[], scope_complete=false. Separate finder/skeptic actualrun andH41 archive reviews PASS. Checks used -j1,6GiB/no swap/confirmedcleanup; peakRSS1,455,308KiB. `evidence/payment-pilot-5b2317f3` contains exactcommands/exits/timings/axioms/hashes and verified5,970,900byte pack receipt, readyforpull with noobservedtransfer. Original Work queue1 remains partial (candidate draft not exhaustive clause/operator/fixture acceptance); queue2 runner implementation and controls pass but assignment acceptance remains pending; queue3 selected pilot witnesses pass except callback-frame work remains open; queue4 wholecombinedmanifest/finalrepositorygates/finalreviews remain pending. No backfill or producer repair was substituted for those obligations.

## Coordinator automerge 32dd5bef provenance

The coordinator merged published master32dd5befce264eb9a5d1b622b9270e71c50a0f5a into owned headb5e2d9c97c1ef5c7d6f1512eac8357ad63b840ec, producing clean head9bd8e542c463b4dc08f42c2ab081f16f3139758d. Delivery/patch scope now anchors at32dd; immutable semantic/cache base6f3eedf0 is unchanged. All71unique pinned input files remain byteidentical. No production source was edited. The scope guard retains --no-renames and real-Git producer-edit, rename and missing-ancestry rejection controls; all66 tests pass. Exactsetup/unit receipts are in `evidence/automerge-32dd5bef`.

## Callback semantic cache and frame development

The original68-module cache remains unchanged. The authenticated extension adds exactly FirstOrder, Semantics.Callback and CallbackHolds from pinned6f3eedf0, with71source/output identities. Separate finder/skeptic reviews caught and closed mutable-receipt and output-validation gaps before execution: reuse now requires committed receipt bytes plus its fixed SHA, exact module inventories and regular nonempty artifacts; CLI acquires the writer lock. All70unitcontrols pass, including real-Git receipt forgeries, diagnostic fault cases and callback import requirements.

The first cache attempt stopped on the pinned producer's existing unused-simp warning atCallback.lean:1319 despite compilerexit0. Its incomplete evidence remains immutable. Fresh v2 builds all3modules serially, with exact warning JSON identity accepted only for that producer. Owned witness checks still reject every warning. The normal H41 delta receipt and verification are in callback-cache-bootstrap-v2; no transfer is claimed.

`callback.failed-send-flag-true` changes only the shared sendNoCallbackBox failed return flag from false to true; its successful payment remains unchanged. Besides an unconditional deterministic recipient-refusal kill, it checks funded actual ExecS.sendFailed and sendResume outcomes, changed callback ledger/balance with local13 preserved, inhabited capture-pop ExecF outcomes, universal frame preservation/drop landing, and a callback premise whose admitted postcondition actual execution with frames refutes. Both input states have concrete mutant update landings. This tests the shared Taclet under the real callback model; it does not mutate the separate CallbackTaclet table or discharge its additional producer obligations.

The initial oracle's four elaboration failures remain unscored in callback-development. All six strengthened phases pass in callback-typed-development with37owned theorem axiom exports and separate finder/skeptic PASS. callback-pilot.json freezes exact sources, signatures, edit, cache and distinct revert control. Committed pilot artifacts/axioms/H41pack follow. Exhaustive constructor/clause/operator/fixture coverage, combinedmanifest and original final repository gates remain open.

## H44 reviewable delivery split

H44 requires bulk evidence/fixtures out of Git. The exact pre-split snapshot atbe546c1dc41728361a687eeb979f3b9261a08d4a is preserved in a local backup ref and bundle. All1029data files (6,446,281bytes) are copied byte-for-byte under `/workspace/h28-h44-bulk-be546c1dc/files`, indexed in its files.json and sealed in its bulk-data.tar.gz (885,301bytes). The compact committed `tests/h28-sol/mutation-testing/bulk-data.json` records absolute paths, sizes and SHA256 identities. Existing repository paths remain ignored mirrors for unchanged commands. Prior evidence references in this document refer to these authenticated VM files, not tracked dumps.

Only Lean oracles, tools, docs and compact manifests remain in the reviewable increment, rebuilt on authorized delivery base32dd5bef. No theorem, observation, side condition, input, budget or gate changed. Tracked inputs still require exact HEAD bytes; off-Git frozen inputs require the committed bulk manifest, its hashed per-file index, exact external bytes and matching local mirrors. Mutable manifest/index, forged external/mirror bytes, unregistered files and symlinks are rejected by real-Git controls. The new lookup authenticates the same frozen input hashes rather than trusting ignored files. `python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py` checks every bulk file, archive and preserved bundle. Full assignment acceptance is still pending.

The sealed snapshot contains1029files:1012generated bulk files move offGit;9frozen pilot configuration manifests and8small verifier scripts remain tracked as reviewable support, with backup copies in the archive. The H44 pointer records this split. Local module registration remains tracked.

The fresh committed callback pilot at9863cd532396595cccd57ab021cbb8e398f9c0a2 passes12actualchecks,8compiledoutputs and45ownedtheoremaxiomexports, with separate finder/skeptic actualrun/archive PASS. Selecteddenominator1/1, independentcontrolkilled,unrun=[],scope_complete=false. A VMrestart interrupted the first run, retained explicitly unscored; the freshR2run is the accepted one. New proof/cache/validation archives stayoffGit; only their path/size/SHA receipts are appended to bulk-data.json. H44split andbulkverification pass, all71unitcontrols pass. Exhaustive fullinventory/coverage, combinedmanifest and originalfinalgates remain unfinished.

## Published master a6fa and archive verifier review note

The coordinator published this lane on mastera6fa01380efd373d85f7a8e6c13811e2d552ae7c. The inherited local mergefa649803 also contained11unrelated bookkeeping changes absent from that master. Both reviewers confirmed the exclusive-scope guard correctly rejected them. They remain byte-for-byte in `/home/agent/projects/solidity-lean-worktrees/h28-mutation-preserved-fa649803` on a preserved branch; all owned WIP hashes and its stash were retained. Because the lane-owned tree already matched published master exactly, the assigned branch now continues from that published base with only its verifier edits. No allowlist was widened and semantic/cache base6f3eedf0 remains immutable.

The eight retained evidence verifier entrypoints now authenticate every external receipt/catalog read through the committed H44 manifest and index, rather than trusting ignored local JSON. Explicit failure checks replace bare Python asserts, so optimization cannot remove the checks. The bulk verifier similarly keeps its checks active under -O. The initial tracked-support branch checked only HEAD bytes and was subsequently rejected by the coordinator. That relaxation is superseded below: tracked mirrors must also match indexed size and SHA; all1012off-Git bulk mirrors remain byte-exact. New real-Git and optimized-interpreter controls pass, alongside all prior controls (74tests total). Existing archive hashes, theorem statements, proof budgets and gate criteria are unchanged. Actual normal/-O archive runs and read-only reviews are recorded in the external checkpoint receipt; no logs or generated data are added to Git. Full original assignment inventory/acceptance obligations remain open.

At committed gate head `a310f670da30fbc0964477073fbf05829457e014`, all eight archive verifiers pass in both normal and optimized Python (16 executions). All 74 unit controls and full 1029-file bulk verification pass in both modes. Separate finder/skeptic actual evidence reviews PASS. Peak RSS is 23,528 KiB across 20 script gates. The first measurement launcher used a relative interpreter unsupported by execv and exited 127; it remains separate from accepted absolute-interpreter runs. The compact bulk-data.json archive_verifier_review pointer seals commands, exits, timings, RSS, source/log hashes and preservation provenance; no new bulk is tracked.

## Held strict-mirror check correction

The coordinator correctly rejected the HEAD-only tracked-mirror branch. `verify_snapshot_files` now retains the bytes returned by bulk_inputs.read and requires both their indexed byte count and SHA256, in addition to committed HEAD authentication. Regression controls reject same-length and different-length Git-committed replacements, plus uncommitted and external-copy tampering. Prior relaxed-check bulk gate results are historical and cannot establish the restored strict criterion.

The restored check first rejected the old snapshot in normal and optimized Python, as expected: its eight verifier source pins predated the reviewed authentication changes. The original 1029-file snapshot/index/archive remain untouched. A separate versioned snapshot refreshes exactly those eight source files from committed 61724cdf; all other 1021 files, including all 1012 off-Git data files and nine frozen pilot configurations, are byte-identical. Both versions and their hashes are explicitly linked in bulk-data.json. No proof artifact, semantic source, witness, case, log, statement or budget was changed to obtain a pass.

DELIVERY_BASE is the write-scope comparison anchor, not the semantic trust base. Earlier a6fa0138 was the then-published integration boundary; the coordinator now names published 86253aba9aad8b457190f9e5f14c77c7ad030318, already an ancestor of this checkout. Advancing that anchor attributes published upstream work to master while retaining the same exclusive-scope rejection for this lane's held/new changes. BASE remains 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5; all 71 cache-source hashes and every frozen input/proof budget remain unchanged. New strict normal/optimized gates and read-only reviews are recorded separately from the superseded results.

At strict gate head `34d40f376ee7b2ca228d84d2e8c74acf97b82a99`, all 20 actual normal/optimized archive, 74-test and full bulk gates pass. Separate finder/skeptic strict reviews PASS; peak RSS is 23,544 KiB. The active 1029-file snapshot totals 6,450,844 bytes, with exactly eight reviewed verifier revisions and 1021 unchanged entries. Every tracked mirror now matches HEAD plus indexed size/SHA. Original stale-index failures and superseded relaxed-policy results remain separate. The strict_mirror_validation pointer seals the new commands, exits, log hashes, timings, RSS and reviews outside Git.

## Complete named-declaration census and finite operator audit

After fetching and fast-forwarding to published `38d38d87e74376d6b95daf9b792fa884333f20b3`, the next original queue checkpoint adds a pinned source census. It enumerates all four constructor families (215 constructors), all 55 Tms definitions, all 17 other side-condition/call/summary helpers and three existing theorems in Rules/CallbackRules: 290 named entries and 308 textual premise/body units. It also enumerates all 30 tracked oracle fixtures, nine frozen manifests and 17 unique case variants, without treating fixture membership as a proof verdict.

The generated external Lean audit checks all 290 names, types and axiom inventories, independently prints the complete constructor families/enums, and proves four universal finite tables: 23 binary operators × 3 primitive types, 23 compound flags, 3 numeric flags and 4 increment mappings. A deliberately wrong add/uint cell must be rejected at the universal proof and leave no compiled artifact. These are declaration/finite-table facts; semantic rule soundness, whole compiler correctness, mutation scoring and full assignment acceptance remain separate obligations. Generated Lean, data, logs and objects stay outside Git; the tool supplies local artifact registration without shared-root changes.

Read-only finder/skeptic reviews closed a version-container cleanup gap before execution: the version probe now has a unique owned name, finally removal, confirmed cleanup and abort-on-uncertainty, with negative controls. The census was expanded to include previously omitted helpers, and pinned unqualified summary-helper references were recorded explicitly. This does not implement a general Lean resolver. All 83 unit controls pass. Committed actual Lean gates, axiom exports, source/kernel inventory comparison, H41 pack and final reviews follow. The semantic/oracle attribution and final whole-assignment acceptance obligations remain open.

At committed audit head `b85da7eb8f5cd1dc9cebeb19fd0a90f3613a2da9`, actual Lean 4.24.0/Lake 5.0.0-src+797c613, KeySort and the positive/known-bad-table gates pass with confirmed cleanup, -j1, 6 GiB/no swap and at least 7,200,382,976 bytes estimated reserve. All 290 declarations plus four universal facts have 294 checked signatures/axiom exports; the independent printed constructor/enum inventories match completely. Peak RSS is 1,088,904 KiB. The wrong table fails only at its universal rfl proof and produces no object. Separate finder/skeptic actual evidence reviews PASS. Printed/source helper attribution identifies 28 binopC constructor consumers, including previously omitted increment paths. The committed candidate_inventory_audit pointer identifies the isolated H41 proof-world archive, source, object and catalog hashes; generated data remains off Git. The census/table checkpoint is complete; semantic attribution, exhaustive candidate selection, combined execution and final whole-assignment acceptance remain separate and unfinished.

At final verifier head `c78b96cac48b23c75cfd75782f56c7f8e2021ff0`, all 83 unit controls, authenticated 294-export archive verification and strict 1029-file bulk verification pass in normal and optimized Python (six actual gates). Separate finder/skeptic reviews PASS; peak RSS is 23,492 KiB. Generation/audit sources and compiled Lean facts remain byte-identical to the proof-input commit. Validation receipts, logs and reviews are sealed separately in candidate_inventory_audit.validation; no generated bulk enters Git.

## Combined execution of the existing declared suite

combined-pilot.json copies exactly 17 unique previously frozen case payloads from nine original profiles, retaining original mutation, source, oracle and signature hashes. Its 13 scored program hashes are distinct; four controls remain outside that denominator. The active inventory is the existing 270-row extended superset: every used source/span/hash is identical to its original profile, including the older 215-row runner inventory. The existing authenticated 71-module callback cache supplies all oracle imports without changing production, runtime or budgets. This tenth configuration adds no mutant or fixture. The earlier census proof world records its nine original profiles at b85; current enumeration includes the combined configuration with the same 17 variants/30 fixtures. Combined execution alone does not grant semantic coverage of unselected candidates or whole-assignment acceptance.

The frozen combined manifest explicitly declares two **off-Git H44 pins, verifiable only on this VM** in input_storage. Their matching declarations are in bulk-data.json.frozen_manifest_inputs; the authenticated H44 index and ignored mirrors supply the actual bytes:

| Input | Bytes | SHA256 |
|---|---:|---|
| `tests/h28-sol/mutation-testing/inventory.extended.draft.json` | 106323 | `e7f8f223586b55837584f57385d46061e00d03377e160f2a25d8d23587002554` |
| `tests/h28-sol/mutation-testing/evidence/callback-cache-bootstrap-v2/manifest.json` | 36528 | `788c9e387fc7c03e803895521dee1389fc6f4843eb3290dc82f70754d892f63c` |

A Git-only checkout cannot execute that manifest without the indexed VM data. The input hashes, 17 case payloads, proof statements and budgets remain unchanged. The historical executed manifest in the proof-world archive remains pinned to its original run head; this delivery annotation does not rewrite that evidence. verify_bulk.py checks both explicit declarations against the authenticated index and actual bytes, and hashes all validation/review archives referenced by bulk-data.json, including nested audit validation. verify_combined.py also checks the archive member count against its committed receipt.

### Combined declared-suite VM execution (2026-11-06)

Input head `fb7ce29bc5305ca58bc4dd6264f4b30fc0fcbe56`, delivery base
`38d38d87e74376d6b95daf9b792fa884333f20b3`; semantic base remains
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. The exact frozen
`manifests/combined-pilot.json` ran all 17 IDs: 13 scored mutants killed,
independent known-kill killed, invalid control rejected during compilation,
label-equivalence certified, and weak-primary control surviving with its
stronger concrete regression checked separately. No unrun case entered the
denominator. Score 13/13 applies only to this declared suite.

Command: `python3 -B tests/h28-sol/mutation-testing/tools/runner.py tests/h28-sol/mutation-testing/manifests/combined-pilot.json /workspace/h28-combined-pilot-fb7ce29b` (exit 0).
Actual 101 phase checks, 70 isolated compiled outputs and 267 full owned
theorem axiom exports; summed check time 569.018 seconds; peak child RSS
1,466,012 KiB; minimum estimated reserve 6,469,640,192 bytes. Every Lean
check used -j1, hard 6 GiB/no swap, network disabled and confirmed cleanup.
Finder and skeptic independently replayed all saved checks and passed.
Their draft replay-verifier findings about missing phases, output attribution
and resource guarantees were fixed before using that verifier as a gate.

H41 pack: `/workspace/h28-combined-export-fb7ce29b/proof-worlds.tar.gz`,
49,560,922 bytes, SHA256
`d79ae154926399af25b2c0a598f0924c26da493bcb917efb2fb562bd2656b83a`.
`bulk-data.json` records the authenticated pointer and both dependency packs.
All generated data remains off Git; normal and mutant outputs must stay
isolated. Ready for coordinator pull; no transfer observed.

`tools/verify_combined.py` authenticates the committed pointer and archived
manifest, every regular member, required phase sets, source-linked failures,
positive signature/axiom certificates, output identities and runtime bounds.
The scope boundary remains false: unselected candidates in the 290-entry,
308-unit census have no general semantic validation, the final acceptance
scope question remains pending, and repository-wide final gates remain open.

Combined checkpoint gates at `3407707a3c8817ef72e5bd88211f41c712b2ef5c`:
83 controls, combined evidence replay, census proof-world replay and strict
bulk mirror verification all pass in normal Python and under `-O` (eight
effective gates). `gate.sh touched` passes with targets none. The first
optimized replay attempt was interrupted, retained as incomplete, and rerun
in a fresh directory; it is not counted as a pass. Exact commands, exits,
timings and process RSS are in the H44 validation archive referenced by
`bulk-data.json.combined_validation`; no source changed between attempts.
This receipt does not replace pending repository-wide final gates.

### Held delivery review correction (2026-11-06)

At `6f2390eecd3d62655f8a0042134e1e1307f78233`, all eight normal/optimized
Python gates pass: 85 controls per mode, explicit H44 inventory/cache pins,
five existing validation archives, strict 1029-file bulk verification, combined
101-check/70-output/267-export replay and 294-export census replay. Both
read-only finder and skeptic reviews PASS; peak gate RSS is 26,712 KiB.
The touched gate passes with targets none. Exact commands, exits, timings,
RSS, source hashes and reviews are in bulk-data.json.held_fix_validation.
The pre-commit census test refused uncommitted manifest bytes; that attempt
is explicitly excluded from passing gates. No Lean source, theorem, proof
budget or original evidence archive changed. This receipt adds a sixth
validation archive for subsequent bulk verification.

The delivery-only anchor is published `7d8a48cabffa81e7cea2a1e5a87013b0fca79db4`,
already included in coordinator-reviewed merge `54e50f69d`. The semantic base
remains `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. Repository-wide final gates
and broader original-assignment acceptance remain open.

### Repository gate on published c460 and return to updated master

The clean owned head `60a068ddf3d32e2a41244fe44f7ce5ed14eb5b82` had identical
tracked content to published `c460b20c15fd99d207a1297b49eb340608a129ee`. A detached
owned worktree ran `bash scripts/coord-tools/gate.sh full` with an untracked
resource-only alternate TOML, private serialized Lean -j1 wrapper, hard 10 GiB
limit, zero swap and 5,391,495,168 bytes estimated initial reserve. Actual
Lean 4.24.0 (797c613) and Lake 5.0.0-src+797c613 versions and a passing KeySort
check precede RUNTIME_GATE_PASS. Tracked sources, HEAD and configuration hashes
were checked before and after; owned container cleanup is confirmed.

The full gate exited 1 after 2917.871 seconds. Corpus passed (2865 seconds),
as did trust, layers, fragments, TestSuite audit and strict automatic
classification. Peak process RSS was 6,094,752 KiB; cgroup peak was
9,390,170,112 bytes. run-lean stopped before its default build because the
published root omitted CatchCoverage and CatchListCoverage; orphan and root
checks failed on those same modules. Axiom pins failed with zero errors and
4241 unrecorded changes. These failures remain failed, not accepted exclusions.

A separate documentation-path failure was a private-worktree preparation gap:
the primary checkout already held the cited Mathlib source. After linking that
dependency, a bounded 2 GiB/no-swap doc check passed with confirmed cleanup and
unchanged tracked sources. This establishes path availability, not a Bridge
proof build. The first launch's relative-shell execv failure (exit 127) and
the uncorrected full-gate log are retained separately. Finder and skeptic
confirmed the actual outcomes and source attribution without Lean-server use.

A fresh fetch then found published `812aeb301f27d70dad4acc3b3bd92d1c41d7c948`;
it was merged without resetting history, producing `d9687ad3f`. The fetched tree contains the Catch imports introduced by earlier integration
work (for example `9f49dbe41`); this records tree contents, not authorship. Fresh root/orphan checks pass (6334 reachable,
zero orphans); the axiom check still fails with zero errors and 4293 unrecorded
changes. Default-build validation on this newer source remains pending. The
delivery-only boundary now advances to that published commit; semantic/cache
base 6f3eedf0 and all frozen mutation inputs remain unchanged.

`bulk-data.json.repository_gate_validation` pins the immutable off-Git evidence
archive, commands, raw statuses, runtime identities, resource measurements and
reviews. The normal mutable build cache stays in the detached worktree; it is
not a sealed whole-repository passing cache. Existing H41 semantic proof-world
packs remain unchanged and ready for coordinator pull. Full assignment
acceptance, broader candidate scope and the shared axiom inventory remain open.

The c75 integration review nits are addressed separately from proof acceptance:
the H44 gate split now has a committed per-member manifest at
`tests/h28-sol/mutation-testing/evidence/repository-gate-60a068dd/manifest.json`.
It lists all 50 members with byte counts and SHA256, plus the absolute archive
path and archive SHA. Bulk verification authenticates that manifest from HEAD
and checks every actual archive member. The archive remains off Git.
`bulk-data.json.delivery_base` now matches the current engine write-scope
boundary; `snapshot_delivery_base` preserves the immutable older snapshot's
86253aba provenance. Neither field changes semantic base 6f3eedf0.

The acceptance review clarified that the original task authorizes bounded
selection (each selected family, whole declared manifest). Q-H28-FINAL-SCOPE
therefore needs no additional approval merely to retain explicit unselected
candidates. Remaining implementation work is an exhaustive selection/oracle
ledger and direct rollback-state and frame/capture-effect mutants; existing
send-flag witnesses keep their narrower claims until those additions pass.

At `4418c39a713a450a36353ef8523157528cf07af4`, 86 controls and strict bulk/member
verification pass in normal and optimized Python (four actual VM gates).
Both read-only reviews PASS; peak RSS is 24,532 KiB. The touched gate passes
with targets none and the write-scope guard passes.
`bulk-data.json.member_manifest_validation` identifies the off-Git gate/review
archive and its committed 11-member checksum manifest. No Lean source changed.
The coordinator published this fix in a91a6cca; the current delivery-only
anchor follows that published head while frozen snapshot provenance remains
86253aba and semantic inputs remain 6f3eedf0. Full assignment work continues.


### Direct rollback-state checkpoint (frozen input)

The rollback pilot adds `payment.failure-books-payment`: only the failed arm of
`Taclet.sendNoCallbackBox` books a payment. Its Boolean result remains false.
The normal funded/refused controls retain the real rollback behavior. The mutant
proof supplies inhabited typed update landings for both arms, proves the ledger
postcondition for every update landing, and proves that the real refused send
rejects it. `checked_kill` negates `Premise.Sound` without an added premise.
All 19 new theorem signatures and axiom inventories are pinned; the independent
revert control is unchanged. Development checks are not scored as a frozen run.

`DELIVERY_BASE` and the current bulk delivery anchor advance together to the
verified published `5c407a0ba004d8cf234c2600283f582a91789b76`. This only
accounts for upstream integration in the owned-write guard; semantic/cache base
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5` and the historical snapshot
delivery base remain unchanged. The new pilot explicitly declares its two
VM-only H44 inputs in its manifest and `bulk-data.json`. Current source census
now sees 32 fixtures, 11 profiles and 18 distinct case variants; historical
census receipts remain immutable. Frame-effect witnesses, final selection
ledger, expanded combined execution and final repository gates remain pending.
