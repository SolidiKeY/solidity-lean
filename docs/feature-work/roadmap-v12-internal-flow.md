# V12 internal calls, structured flow and transient execution

This is a **partial independent backfill checkpoint**, not completed V12,
G36, G37, G38 or G39. The full original queue, both backfills and final
validation remain open wherever the table below says so. No target runtime
frame emitter or general source-to-bytecode theorem is claimed.

Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v12-flow-calls`.
Repository: `/workspace/solidity-lean`.
Batch/task: `solidity-v12-v17-20261031` / `v12-flow-calls`.
The initial checkout was clean at the exact base on branch `work`; the
assigned branch was created there. No reset, fetch of worker branches,
cherry-pick, push, merge or PR was performed.

## Prerequisites and reproduced gap

The published intrinsic runtime is reused unchanged: `TEnv`, `State`,
`Out`, `CallRet.enterT`, `CallRet.leaveT`, `TRun.call` and `TLoop`.
The existing compiler is still value-argument/inline-body based.
`storage_argument_refused`, together with `memory_argument_refused`, `storage_result_refused`
and `recursive_call_refused`, it proves actual current refusals against
`Solidity/Evm/Compile.lean`, without changing or treating a refusal as admission.

The base has no published V11 backend namespace supplying the required
mixed heap/storage/shrink/allocation representation and transport interface.
`Solidity/Evm/MemoryCompile.lean` remains the restricted published memory
compiler; it does not supply a general runtime-call frame theorem.
`Solidity/Calculus/RunFrameMem.lean` explicitly excludes writes into older
objects from its `withinM` frame. Those old missing proofs stay reserved.

Unbounded recursion additionally needs the source/lowering owners:
`Solidity/Syntax/Scoped.lean` still defines `recDepth = 1024`, `recUnroll`
and an exhausted `Prog.recBase`; `Solidity/Syntax/Elab/Arms.lean` uses that
cutoff. Changing its number would not discharge the decided unbounded-source
obligation. Independent G01 Prefix algebra cannot discharge this premise.
Existing `Source/**`, function-reference repairs, memory loops/copies and
all V07–V11 owners remain read only. G38's published byte emitter and local
checkpoint are consumers' prerequisites, not reassigned implementation work.

## Every queue and backfill item

| Item | Current status and remaining obligation |
|---|---|
| 1 / G37.01 | Gap reproduced; intrinsic result/argument/frame laws and controls prepared. General target memory frames, typed argument/local/reference transport and operand-stack preservation still open, awaiting published representation/lowering prerequisites. |
| 2 / G37.02 | Independent finite-prefix concatenation and loop divergence laws prepared. Unbounded internal recursive return/prefix simulation and termination/divergence correspondence still open; the intrinsic source cutoff remains reserved. No recursion-depth admission is added. |
| 3 / G37.03 | Existing dependent result-renaming law consumed unchanged. Full-signature internal function-value target dispatch remains open, requiring the frame theorem and published frontend dispatch. The restricted function-ref-args job stays untouched. |
| 4 / G36.01 | Local unwind/reset law and a real intrinsic mixed-loop control prepared. General block/branch/break/continue/early-return target simulation with alias/frame transport remains open. |
| 4 / G36.02 | Actual intrinsic loop control combines storage push/pop, persistent/transient writes, allocation and scope exit. General mixed-loop backend simulation and old memory-loop prerequisite remain open. |
| 4 / G36.03 | Payment/call-loop consumer interface/final application remains open; no V14 proof is undertaken. |
| 5 / G38 | New adapter connects actual typed root projections to published exact-byte failure/return execution. It does not reconstruct a whole State or implement call/world rollback. Actual statement-to-target adapter and complete frame unwind/rollback remain open. V13/V15 callback composition remains external. |
| 6 / G39 | Intrinsic transaction idempotence/unwind/reset-restored-store laws prepared. New target TLOAD/TSTORE representation/reset/sharing/rollback adapter remains open. Logical roots remain distinct. Self-call/callback final applications await V13/V15. |
| Backfill A | Partial: actual result transport, two heap extensions, dependent renaming/noninterference reuse, intrinsic call equations and prefix algebra have controls. Target call-frame extension/composition and genuine unbounded recursion controls remain open. No algebraic wrapper closes a missing runtime theorem. |
| Backfill B | Partial: actual local-loop observed-prefix composition, mixed-location/shrink/allocation witness, reset laws and typed root-projection byte checkpoint adapters prepared. General target loop/unwind/transient composition remains open. |
| Reserved prerequisites | V11 integration and exact published runtime representation/transport exports; old memory-internal-call and memory-loop proofs; S03 unbounded recursion/lowering repair; frontend full-signature dispatch publication. No unmerged branch was imported. |

## Theorems and their exact boundaries

All names below are in `Solidity.Backend.InternalFlow` unless specified.

| Theorems | Premises and conclusion boundary |
|---|---|
| `storage_result`, `memory_result`, `tuple_result_tail` | Actual CallRet operation; typed caller/results, memory default/map-free certificates where required. Exact exported references and unchanged caller tail. No target state. |
| `scalar_result_other` | Distinct numeric destination/other positions; exact unchanged read at the other typed caller local. |
| `alias_heap_transport`, `memory_heap_identity` | Two real heap-prefix extensions; alias unchanged and memory identity unchanged. No heap mutation preservation hypothesis is assumed. |
| `call_return` | Actual `Args.evalT = ok arguments` and actual body execution `= ok out`; output uses both entry allocation and body extension, drops body locals, extracts results and weakens caller locals. These execution premises remain explicit. Body is the published TStep interface; this does not prove it is a compiled source function. |
| `call_body_failure` | Actual successful argument evaluation and body error; preserves exact THalt. TRes has no failed State, so no rollback follows. |
| `result_renaming` | Reuses `CallRet.leaveT_wk` exactly, including the existential background's `TEnv.off` equality. It is not dispatch compilation. |
| `loop_prefix_add`, `loop_prefix_continue` | Existing TLoop iterator, arbitrary body/condition/state and horizons; continuation needs the actual first-prefix running equation. No invariant is assumed. |
| `loop_observed_of_prefix` | Actual finite successful observed iterN equation; concludes the observation of the existing unbounded loop run. No target trace premise. |
| `loop_all_prefixes_running` | Every horizon has a running successor; concludes actual TLoop divergence. Does not assert recursive calls correspond. |
| `prefixContext`, `prefix_context_assoc`, `prefix_context_le`, `prefix_context_consistent`, `prefix_context_completes`, `prefix_context_diverges` | Observation adapter on the existing G01 Prefix type. Preserves event order, consistency, completion and divergence of an existing family; does not execute a callee or validate a compiler. |
| `root_failure`, `root_return` | Region-certified actual source root projections; actual Failure Slice machine; Fits(address, bytes), two free operand-stack slots. Exact original bytes and projected rollback/commit. Other roots, whole-state reconstruction, gas and world/callback rollback remain outside the theorem. |
| `root_write_noninterference`, `reset_root_pair` | Actual typed region roots; the region certificate supplies membership/disjointness. Persistent projection unchanged by transient write; reset preserves persistent and defaults transient. |
| `transaction_entry_idempotent`, `transaction_after_unwind`, `reset_restored_store` | Actual intrinsic State boundary operations; scope suffix for unwind. No statement or target failure semantics is defined. |

Controls include nonempty reference arguments, actual rebind/return and a
same-typed caller local; wrong reference/destination/root snapshots; two
really allocated arrays and a wrong identity; exact de-ad-00 source failure;
actual checked-slice RETURN versus REVERT on the same bytes; dirty store and
memory reset; nonzero loop prefix split; exact-byte loop failure; all-horizon
incrementing-loop divergence; nonempty event order and completed-prefix refusal.
`MixedLoopChecks.mixed_loop` executes the existing intrinsic loop, writes
persistent 7/transient 9, pushes/pops an array, allocates one object, and drops
the temporary local while retaining the heap. Zero live entries and one
shadow slot discriminate the shrink. `wrong_transient_reset` rejects losing
that transient write during internal unwind. These are kernel controls,
not bounded external EVM/compiler tests or general target simulations.

## Runtime, verification and reviews

Actual Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. The VM cgroup is 16 GiB with no configured swap;
Docker enforces `memory.max=12884901888`, `memory.swap.max=0`, leaving
headroom for the OS. Systemd/user-scope failures are retained; they were
replaced by the measured Docker cap, not relabeled passed.

RUNTIME_GATE_PASS: `lake -f .v12-runtime.lakefile.toml build Solidity.KeySort`
passed with explicit -j1 in weak Lean arguments and LEAN_NUM_THREADS=1:
`Build completed successfully (2 jobs).` Peak cgroup usage 26,050,560 bytes.
The temporary lakefile adds only -j1 and is not committed. Heavy checks use
`tests/internal-flow/run-capped.py`: writer lock, one compiler lock,
explicit -j1, offline Docker, cgroup peak, aggregate RSS samples and disk
measurements. No Lean MCP tools are exposed, so serial CLI diagnostics are
used. The tool catalog exposes stop_goal but not get_goal; no replacement
goal was created.

Raw failures are retained under `/workspace/scratch/v12-flow-calls/evidence`:
initial bind/renaming diagnostics; absent Contracts olean; wrapper shared-library
and standard-library discovery failures; concrete reference/type annotations;
missing finite-observation equality decisions and local-instance abstraction.
The final mixed-loop proof supplies a closed concrete decision to
`of_decide_eq_true`; the kernel checks it. There is no native_decide,
new implemented_by, axiom, sorry, weakened statement or increased proof budget.

The initial independent finder and skeptic reviews used no Lean server or
builds. Both found no defect in the stated partial frame/prefix laws and
required inhabited/negative/combination controls, axiom pins and exact scope
language. Those controls are now present. Skeptic's two-versus-arbitrarily-many
extension wording correction is applied. Final review and gate results are
to be recorded in the final handoff continuation and external HANDOFF when finalized.

Required full/import/final gates must pass before any lane-completion claim.
The root-projection adapter cannot close missing whole-state/world rollback;
loop divergence cannot close recursive-call divergence. The lane is blocked
until reserved prerequisites are published and integrated by the coordinator.

## Partial checkpoint handoff

The checkpoint is reviewable preparation with **full lane completion blocked**.
It is not a finished Work queue item or either complete backfill. The table
above accounts for every numbered item and both backfills. All remaining
premises must be discharged using published, coordinator-integrated interfaces.
The coordinator must publish/integrate V11's mixed-state representation and
allocation/shrink laws and the reserved internal-call/loop interfaces. The
source owner must replace the `recDepth`/`recUnroll` use in
`Solidity/Syntax/Elab/Arms.lean` with its unbounded recursive execution/lowering
interface, preserving the independent S03 prefix semantics; merely changing
1024 is not the requested patch. Full-signature dispatch must retain its
dependent signatures and default refusals. No such reserved patch is made here.

Proposed ledger reconciliation, **not a status upgrade**: record partial
preparation for G37.01–.03, G36.01–.03, G38 and G39. Exact relevant existing
feature IDs are `internalFunctionTypes`, `internalCalls`, `blocks`,
`whileStatement`, `forStatement`, `doWhileStatement`, `breakStatement`,
`continueStatement`, `returnStatement`, `revertStatement`, `assertBuiltin`,
`requireBuiltin`, `revertBuiltin`, `revertPayloads`, `transientState` and
`transientLayout`. Their full compilation/coverage verdicts remain unchanged.

| Gate | Actual outcome and evidence under `/workspace/scratch/v12-flow-calls/evidence` |
|---|---|
| Runtime KeySort | Pass, 2 jobs; `runtime-serial.log`, actual versions in `runtime.log`. |
| Published prerequisites plus FrameLaws | Pass, 63 jobs; `prerequisite-build-3.log`, cgroup peak 1,209,524,224 B. Earlier two wrapper failures remain raw failures. |
| Focused owned import closure | Pass, 71 jobs; `focused-reviewed.log/json`, 3.146s, sampled aggregate RSS 804,520 KiB, cgroup peak 369,004,544 B. |
| Fresh six-file CLI diagnostics | Pass; `files-reviewed.log/json`, individual `final-*-diagnostics.log`; 6.791s, RSS 777,424 KiB, cgroup peak 182,169,600 B. Guarded axiom pins pass. |
| Additional headline axiom audit | Pass; `added-axioms.log/json`; body failure, observed loop prefix, root return use only standard propext/Classical.choice/Quot.sound; reset pair uses propext. Final pins are guarded. |
| Required full `./run-lean.sh` | **Incomplete/fail**, exit124 at 300.499s; `full-bounded.log/json`. RSS 2,380,972 KiB; cgroup peak 2,744,991,744 B. The default build was incomplete; TestSuite and final sort checks were not reached. No source failure is waived as inherited and no full-gate pass is claimed. Do not repeat this unchanged failed heavy gate without new prerequisites or other justification. |
| Shared layers/orphans/trust | Pass: 172 core/0 reach elaborator; 1002 reachable/0 orphaned; 1017 sources/246 inventoried sites/0 findings. `final-layers.log`, `final-orphans.log`, `final-trust.log`. |
| Owned import/trust/budget closure | Pass, 6 modules/0 findings. Supplemental raw-import scanning handles edges filtered by the shared graph and nested comments/strings. `final-imports.log`. |
| Raw documentation checker, normal and strict | **Fail**, 46 missing references at exact base and head. Outputs byte-identical; separate no-new-findings gate **passes**. `base-docs*.log`, `final-docs*.log`, `final-static.json`. Exact-base snapshot/index were separate from the checkout and contained no build tree. |
| Runner lifecycle controls | Pass: `lifecycle-controls.json`. Name-collision launch exits125 without a created CID and preserves the existing canary. Interrupted monitor exits130, its own CID is stopped and fresh writer-lock acquisition succeeds. |

Post-pin final focused/CLI/static confirmations are retained as
`checkpoint-focused`, `checkpoint-files` and `checkpoint-static` evidence.
These confirm only the owned checkpoint; they do not repair the full gate.
The first RSS sampler omitted the required PID column and produced no valid
samples; those zero-sample records are retained, not treated as zero usage.
The corrected final sampler records nonzero aggregate RSS alongside cgroup peaks.
Branch creation preceded discovery of the canonical writer-lock directory;
all source edits and Lean checks thereafter used the lock, and no competing
writer was observed. The reviewed runner's container now retains the canonical
lock even if its monitor dies; cleanup only uses the CID it actually created.

Independent finder/skeptic review covered the actual diff, hypotheses, reference
witnesses, mixed loop, ownership, scripts and this partial status. Confirmed
findings were fixed: extension wording, populated/wrong-frame controls,
transient-only wrong rollback, raw import filtering, runner interruption and
wall-time bounds, and CID-only cleanup. `reviews.md` retains the rounds and
follow-ups; neither reviewer used a Lean server or builds. Final handoff audit
results are added to that external evidence record after exporting artifacts.

Original patch: `/workspace/scratch/v12-flow-calls/artifacts/original.patch`.
Bundle: `/workspace/scratch/v12-flow-calls/artifacts/v12-flow-calls.bundle`.
Handoff: `/workspace/scratch/v12-flow-calls/artifacts/HANDOFF.md`.
Checksums: `/workspace/scratch/v12-flow-calls/artifacts/SHA256SUMS`.
The external handoff records the full committed head after this document's
commit, exact theorem boundaries, open prerequisites and raw gate statuses.
No external EVM/compiler tests for a complete runtime-frame backend were
possible because that backend is not published; kernel controls are not a
substitute. No scope question is pending; no exclusion or premise is approved
or weakened by this checkpoint.

## Continuation checkpoint: allocating calls and nested projected emissions

The human-authorized continuation starts at clean committed checkpoint
`d0b7ff1075467a1582de5de3105b2498f586fda2` on the same branch, with the same
frozen base. The previous sections/evidence describe that preserved checkpoint.
This increment fills two investigated independent backfill gaps; it does not
complete either entire Backfill A/B or any general target Work queue theorem.
Original artifacts/checksums and raw failures remain untouched at their prior
absolute paths. New evidence/exports use
`/workspace/scratch/v12-flow-calls/continuation-1`.

### Backfill A: actual memory-result allocation and body growth

`MemoryCallTransport.lean` executes the published `TRun.call`, `CallRet.enterT`,
`Prog.runR` and `State.allocDefaultG`; it defines no new call evaluator.
The caller has an older allocated array reference and two same-typed scalar
locals (9,11). Actual nonempty memory arguments evaluate to the older reference.
The result-entry allocation grows the heap 1→2 and has identity1. The actual
body declares a temporary (heap2→3, identity2), binds that reference into its
result slot, and exits the temporary's scope. `actual_call` is an application
of `call_return` with proved `arguments_evaluate` and `body_evaluates`, not a
new simulation assumption. `returned.ext` is exactly
`entry.ext.trans bodyOut.ext` at the real dependent heap typing.

`returned_environment` and `exported_tail` retain the new result reference,
weaken the older caller reference along that composition, and keep both scalar
locals. `body_old_argument` directly reads the transported reference argument.
`old_reference_composition`, `entry_and_body_identities`, `growth_phases` and
`call_observation` pin composition, separate identities1/2, heap lengths1/2/3,
and the actual result2/old0/scalars9,11. `swapped_fresh_old_rejected` rejects
swapping result/caller references. A second actual scalar-result call allocates
in its body and writes7 into the first scalar destination while retaining11
and old reference0; `wrong_same_typed_destination` rejects writing the other
same-typed scalar slot.

Reusable `memory_call_caller_reads` is quantified over the actual dependent
`CallRet.mem` signatures, arbitrary caller context, result/parameter/body
contexts and body output. Its only execution premises are actual successful
argument evaluation and actual body execution. It proves the full exported
caller tail and every typed caller read weakened along the composed extension.
It makes no claim that older heap object contents were preserved by the body.
No target frame/operand-stack transport, recursive compilation or dispatch is
proved by these intrinsic laws.

### Backfill B: nested local emission consumer

`nestedRootEmission` sequences two actual `Failure.Local.execute` calls with
`save` on actual `rootJournal` projections, retaining the intermediate journal
and both observed outcomes. It neither calls nor restates the reserved generic
`Local.nested_failure`, and assumes no desired restoration/continuation equation.
`nested_root_return` proves the inner failure restores its prefix-entry snapshot
and the subsequent actual outer RETURN keeps those roots and updates the
restored middle machine's byte memory. `nested_root_failure` proves the same
intermediate restoration followed by a later outer failure restoring the
outer-entry roots and original caller machine. Both quantify over actual typed
region roots, three stores and three machines; their side conditions are only
`Fits a di`, `Fits b do'`, deep stack headroom and restored middle stack
headroom. Repeated snapshots/bytes are allowed by the general law; controls
instantiate all snapshots and inner/outer payloads distinctly.

The inhabited controls use persistent `uint` and transient `int` roots:
outer(1,-2), prefix(7,-9), deep(11,-13), constructed by actual typed store
updates. They use three different dirty memories and nonempty stacks, inner
bytes de-ad-00 and outer bytes be-ef-01-ff. `success_execution` and
`failure_execution` prove actual nonempty results. `success_roots_and_bytes`,
`success_memory_and_stack`, `failure_roots_and_bytes` and
`failure_memory_and_stack` check both snapshot stages, exact class/byte lists,
restored memory, precise outer write/exterior marker and retained stack tail.
Negatives `no_early_outer_restore`, `no_deep_transient_commit`,
`outer_failure_cannot_keep_prefix`, `return_is_not_revert` and
`inner_bytes_are_not_outer_bytes` reject the requested confusions.
These are local projected-root consumers, not source catch, whole-State
rollback, arbitrary callees, new world semantics or compiler simulation.

### Continuation gates, reviews and cache strategy

Fresh per-file CLI checks and guarded axiom checks pass for every new theorem;
only the standard propext/Classical.choice/Quot.sound subset occurs.
`cp2-memory-guarded.log` and `cp2-nested-guarded.log` retain clean outputs.
Focused import closure passes72jobs (`cp2-focused.log/json`):4.516s,
sampled aggregate RSS806196KiB, cgroup peak367263744B. Actual Lean4.24.0 and
Lake5.0.0-src+797c613 plus fresh KeySort2jobs pass are in `cp2-runtime.log`.
The existing canonical-lock/owned-CID runner still enforces actual-j1,
LEAN_NUM_THREADS=1,12GiB and swap.max0. No proof/fuel/node/test budget changed.
A syntax-only reserved-word failure is retained as `cp2-nested-1.log`; its
consequent error-generated axiom output is not a deliverable or a passing gate.

Both independent read-only source reviewers found no semantic/ownership issue.
Their confirmed signature/comment findings were fixed: explicit dependent
result types, direct theorem invocation instead of an untyped local have,
and an explicit body argument read. Final source/artifact follow-ups and static
checks are recorded in the continuation evidence and external handoff; neither
reviewer invokes Lean servers/builds. New paths and registrations remain owned.

`tests/internal-flow/cache-inventory.py` records the actual compiler/configuration
and transitive-source fingerprint plus owned artifact/trace hashes, without
rewriting/materializing caches or certifying compilation from those hashes.
The same existing `.lake` tree is reused; no duplicate build tree/cache is made.
The initial `cache-inventory.json` reports8owned modules/72source closure.
Skeptic detected a later docstring-only source SHA change; that initial report
is retained as historical. `cache-inventory-final.json` refreshes every source
and artifact hash after the final exact-source focused gate; it is checked
against the committed source before export. Read-only `lake --no-build build`
exits3 in1.415s and reports pending default dependencies (`cp2-cache-no-build.log`).
This is a cache-readiness inventory, not full validation. The initial artifact
report write was denied by the read-only shell sandbox; its failure is retained
and the authorized report write succeeds without changing any cache/source.

No new reserved prerequisite/interface was published here. The original full
`./run-lean.sh` exit124 at its fixed300-second bound remains **FAIL/incomplete**,
with TestSuite/sort not reached. It is not repeated, its budget is not extended,
and no targets are removed. A future integrated prerequisite may justify a
bounded named-target cache checkpoint followed by the unchanged full gate;
this inventory itself supplies no justification or missing premise.
Raw normal/strict documentation failures remain failures; exact-frozen-base
no-new-findings is still a separately checked gate.

All original Work1–6/G37/G36/G38/G39 obligations and remaining Backfills A/B
listed above stay open. The new requested independent memory-call and nested
emission constructions are implemented/proved/controlled, but the original lane
still needs its reserved general target/runtime/recursion/dispatch/loop owners
and mandatory full validation. No feature verdict, Fml.inTarget, refusal,
observation, invariant, exclusion, source tag or global ledger is changed.
The continuation handoff/patch/bundle and checksum manifest are exported under
`/workspace/scratch/v12-flow-calls/continuation-1/artifacts`; they record the
actual new committed head and retain links to the sealed original checkpoint.

### Continuation checkpoint handoff

The final exact-source focused command is
`lake build Solidity.Backend.InternalFlow.MemoryCallTransport Solidity.Backend.InternalFlow.NestedRootEmission`:
pass72jobs,3.044s,sampled RSS772088KiB,cgroup peak362106880B
(`cp2-final-focused.log/json`). The fresh eight-file serial sweep passes in
11.514s,RSS787864KiB,cgroup peak183005184B (`cp2-final-files.log/json`,
`final-*-diagnostics.log`). All28new theorem axiom checks are guarded and pass.
Static gates pass172core/0elaborator,8owned/0import-or-trust findings,
1004reachable/0orphans,1019sources/246trust sites/0findings. Normal and strict
raw docs checks still exit1 on the exact same46findings; both separate
exact-base no-new-findings comparisons pass (`static.json`). Original109
checksum entries verify and their manifest hash is unchanged.

Final source reviews cleared the mathematical/ownership/convention findings.
The cache fingerprint refresh addresses skeptic's last evidence finding;
all72recorded current-source hashes match. Source, review and hash evidence
are in the continuation directory, not overwriting original failures.
The exact frozen-base cumulative patch, this-checkpoint incremental patch,
verified bundle, owning document, external HANDOFF and SHA256SUMS are exported
only after these checks/reviews and the actual commit. External HANDOFF records
the final full head; no empty marker commit is needed. Full original lane/A/B
completion remains blocked as recorded above, not inferred from this checkpoint.


### Continuation 2: allocation-only content noninterference (partial Backfill A)

`Solidity.Backend.InternalFlow.memory_call_allocation_frame` consumes actual `Args.evalT`,
`Prog.runR` and `CallRet.mem.enterT`/`TRun.call`. Premises are the dependent
argument evaluation and body execution equations, `args.readsIn μ = true`,
`Prog.withinM μ body = true`, and the reference type's default/map-free guards.
It derives the body frame from published `Prog.run_frameM`, composes published
`CallRet.enterT_frameM` with it at exactly `entry.ext.trans out.ext`, and exports
`Heap.Keeps` for every caller object together with caller tail/result equations.
There is no assumed preservation equation. These are intrinsic local consumers,
not target runtime frames, arbitrary mutating callees or recursive compilation.
Heap content framing holds for each admitted μ; storage/net/selfBalance framing
is conditional on μ ≠ nonpayable in TGFrameM, while tx framing is unconditional.
Concrete controls use view and explicitly prove persistent/transient/tx framing.

`AllocationFrameChecks.actual_two_calls` executes two successive intrinsic
calls, each with result-entry and body allocation. The first copies stored
[13,17]; the second allocates [0,0,0]. Both use a true branch, block and temporary
local unwind. Initial caller object [7,11] has two aliases, with scalar locals
9/11, persistent/transient roots7/9 and nonzero transaction observations.
Initial, intermediate and final contents, scalar/global observations, fresh
identities2/4 and heap sizes1/2/3/4/5 are pinned. The frame proof derives Keeps
for all old objects, and the second frame includes the first returned object.
Countercontrols reject wrong old contents, swapped fresh identities and early
transient reset. An actual write through the old alias changes both aliases to
[99,11]; published withinM rejects that body even at nonpayable. The predicate
and all reserved sources remain unchanged. Existing scalar-destination controls
remain registered. Every new theorem has a guarded axiom pin.

Early per-file failures (dependent context annotations and redundant address
projection normalization) remain raw evidence. The stale published-import
artifact conflict is retained too: bounded Lake import-closure rebuilding in
the existing cache resolved it without reserved source edits. No generic memory
frame law was reimplemented or strengthened. No representation refactor occurred.
Separate read-only finder/skeptic reviews inspect actual source and final diff;
results and any corrections are recorded in the external continuation handoff.

Original Work1/G37.01 target frames, Work2/G37.02 unbounded recursion, Work3/
G37.03 dispatch, Work4/G36 structured/general mixed-loop simulation, Work5/G38
whole statement/frame failure composition and Work6/G39 callback/world transient
applications remain open against their reserved prerequisites. Backfill A remains
partial despite this content consumer; Backfill B remains partial with the prior
local projected-root consumer, not whole-State/world rollback. No theorem here
closes source recursion/cutoff, general target frames/dispatch or general loops.
Original full run-lean.sh exit124 at fixed300 seconds and no-build exit3 remain
failures/inventory, not rerun or relabeled; TestSuite/sort were not reached there.
Raw normal/strict docs failures remain separate from exact-base no-new findings.
There is no changed prerequisite justifying repeating the unchanged full gate.
New source checks and keyed cache inventory use the same existing cache and
budgets. Original sealed artifact sets are preserved. New exports are under
/workspace/scratch/v12-flow-calls/continuation-2/artifacts, with exact base/head,
command logs, source hashes, reviews, patch, bundle, handoff and checksums.


Continuation2 checkpoint gates: `lake build
Solidity.Backend.InternalFlow.AllocationFrame
Solidity.Backend.InternalFlow.AllocationFrameChecks` passes77jobs in10.553s,
sampled aggregate RSS863020KiB, cgroup peak427331584B. Final serial
`bash tests/internal-flow/check-files.sh <evidence>/guarded-files` passes all10
files in19.337s, RSS827388KiB, peak222924800B; its individual commands are
`lake env lean -j1 --tstack=131072 <owned-file>`. All29new guarded axiom pins
pass (only propext/Classical.choice/Quot.sound as printed, some smaller sets).
Per-file MCP is unavailable; these CLI diagnostics follow the repository
lean-verify workflow fallback. Both checks use the existing 120-second cap,
LEAN_NUM_THREADS=1, explicit -j1, enforced12884901888B memory/swap0 and writer
lock; no concurrent heavy checks. Lean4.24.0 commit797c613, Lake5.0.0-src+797c613
and `lake build Solidity.KeySort` pass2jobs in0.902s (runtime gate only).
`node scripts/check-layers.mjs`, `node tests/internal-flow/check-imports.mjs`,
`node scripts/check-orphans.mjs`, `bash scripts/check-trust.sh` and
`git diff --cached --check` pass:172core/0elaborator,10owned/0findings,
1006reachable/0orphans,1021sources/246trust sites/0findings.
`bash scripts/check-doc-paths.sh` and its `--strict` variant exit1;
complete outputs equal the frozen-base outputs byte-for-byte, separately
passing zero-new-findings. Original sealed manifests verify unchanged.
Evidence is /workspace/scratch/v12-flow-calls/continuation-2/evidence;
cp3-final-focused, cp3-final-files, cp3-runtime and static.json record exact
commands/outcomes. Finder and skeptic found no proof/control/ownership defect;
both identified the erroneous module-qualified theorem name in prose, now
corrected, and skeptic requested this explicit gate summary. No full gate
claim follows from these scoped passes.


### Continuation 3: inhabited finite recursive calls (partial Backfill A)

`Solidity.Backend.InternalFlow.finite_recursive_return` consumes published
`Stmt.run_callRec`, `recUnroll`, `Prog.withinM_recUnroll`, `Prog.run_frameM`,
`CallRet.enterT_frameM` and actual `TRun.call` return. For any finite unrolling
depth, its step hypothesis is syntactic withinM closure under the body thunk;
argument/body execution successes are explicit premises. Induction derives
body admission, then entry/body frames compose at exactly entry.ext.trans
out.ext. The conclusion includes actual recursive-call success, exact typed
result/caller export and Heap.Keeps for every older caller object. It contains
no assumed desired preservation equation. This generic theorem does not assert
an argument readsIn/call-admission certificate. Concrete `call_within` separately
discharges both readable arguments and body admission for view.

In `RecursiveUnroll`, n2 calls n1 which calls n0 through actual callRec nodes
and recUnroll depth3. Each frame allocates a one-element scratch array inside
a block and unwinds its local. The bottom returns13, recursive callers add1,
and the outer result15 overwrites caller slot2 while same-typed slot3 stays11.
The pre-existing nonempty [7,11] object has two caller aliases; the memory
parameter is forwarded at each recursive boundary. `nested_execution` proves
actual success; `body_execution` discharges the body premise of the reusable
consumer. `exact_recursive_export` binds the actual result to the exact composed
entry/body extension and typed caller/result export. `caller_aliases_transport`
uses the published local frame law, while `recursive_heap_contents` and
`recursive_globals` derive old-content and view-qualified storage/net/balance/
transaction preservation. Final observations pin both aliases, returned15,
untouched11 and heap size4. A separately executed inner boundary pins return14,
retained caller n2, old alias contents and heap size4; its arguments evaluate
to n1 with the transported alias.

The witness definitions extract outputs from the actual existing runs. Their
fallback states are ruled out by independent kernel-checked success proofs;
they are not an evaluator or successful default. Keeping these owned witness
definitions irreducible for elaborator inference avoids repeated whole-run
normalization; the kernel still checks their ordinary definitions. Initial
whole-State rfl normalization and subsequent inference reached the unchanged
200000-heartbeat bound. Those raw failures are retained; no proof limit was
raised. Final kernel success/observation proofs check within the same budgets.

Countercontrols reject returned14 instead of15, overwriting the wrong scalar
slot, a fresh scratch reference substituted for an old alias, and a lost caller
prefix. Depth0 and depth2 actually halt with THalt.exhausted. Further controls
reject interpreting depth2 as success or ordinary revert. recBase remains
assumeFalse/exhausted; the d metadata is not a runtime depth guard independently
of the supplied body thunk. No cutoff/refusal is removed or generalized away.
This is finite intrinsic unrolling backfill, not G37.02 unbounded source/target
recursion, termination/divergence correspondence or target runtime compilation.

All original Work1 target frames, Work2 unbounded recursion, Work3 dispatch,
Work4 structured/general mixed loops and G36.03 final applications, Work5 full
failure/return composition and Work6 transient callback/world applications stay
open against their reserved owners. Backfills A and B remain partial. No
source/compiler/semantics/RunFrameMem edit, new evaluator, new axiom or generated
G03/status change is made. The original full run-lean.sh exit124 at fixed300s
remains FAIL/incomplete (TestSuite/sort unreached), not repeated. Prior no-build
exit3 remains inventory only. Normal/strict raw docs exits1 remain failures;
exact-frozen-base zero additions is a separately compared gate. No new integrated
prerequisite justifies rerunning the unchanged failed full gate.

Continuation3 exports use /workspace/scratch/v12-flow-calls/continuation-3,
leaving all three prior sealed sets unchanged. External HANDOFF records exact
head/base/branch, every scoped command/exit and measurement, theorem premises,
full queue limitations, source hashes, reviews, patches, bundle and checksums.
Separate finder/skeptic source reviews found no semantic/ownership defect and
requested explicit types on inferred have bindings; corrected before checkpoint.
Final guarded/focused/static/doc comparisons and artifact reviews follow below
or in that exact-head external handoff. No integration/push/merge/PR authority.


Continuation3 scoped gate record: final `lake build
Solidity.Backend.InternalFlow.RecursiveUnroll` passes78jobs in5.184s,
sampled aggregate RSS943096KiB, cgroup peak492658688B (`cp4-final-focused`).
The eleven-file serial sweep `bash tests/internal-flow/check-files.sh
<evidence>/guarded-files` passes in22.886s, RSS902768KiB. Review then added only
an explicit dependent type on firstScratch; the changed file's final
`lake env lean -j1 --tstack=131072
Solidity/Backend/InternalFlow/RecursiveUnroll.lean` passes in4.560s,
RSS899864KiB (`cp4-final-rec`), followed by that final focused closure.
All23new theorem axiom guards pass, limited to propext/Classical.choice/
Quot.sound (some proper subsets). No Lean MCP is exposed; capped CLI diagnostics
follow the repository lean-verify fallback. All checks retain120s bounds,
LEAN_NUM_THREADS=1/explicit-j1, canonical writer lock,12GiB memory/swap0,
serial heavy execution and the same existing source/toolchain-keyed cache.
Initial default-heartbeat failures remain in cp4-rec-3/cp4-rec-4; budgets unchanged.
`lean --version; lake --version; lake build Solidity.KeySort` passes2jobs:
Lean4.24.0 commit797c613, Lake5.0.0-src+797c613 (`cp4-runtime`), runtime gate only.
Layer/import/orphan/trust/diff checks pass:172core/0elaborator,11owned/0findings,
1007reachable/0orphans,1022sources/246trust sites/0findings. Normal/strict raw
docs checks exit1; complete outputs are byte-identical to frozen-base outputs,
so both separate zero-new-findings comparisons pass. Evidence and exact commands
are in /workspace/scratch/v12-flow-calls/continuation-3/evidence.
Both read-only source reviewers clear the corrected have/firstScratch types,
actual recursive controls, guarded proofs, ownership and finite-scope wording.
Final actual diff/handoff/artifact reviews and committed hash bindings are
recorded in the external HANDOFF; full Work1–6/A/B completion remains open.


### Continuation 4: multi-iteration mixed-state prefixes (partial Backfill B/Work4)

Generic names below live in Solidity.Backend.InternalFlow; concrete control
names live in Solidity.Backend.InternalFlow.MixedLoopPrefixes.

`scopedLoopBody` is exactly the existing TRun.loop body lambda: execute actual
Prog.runR, drop body.ext locals and compose previous.ext.trans out.ext. It does
not evaluate loops or replace semantics. `scoped_body_frame` consumes one actual
successful body execution, syntactic withinM admission and the prior frame/local
agreement. `scoped_loop_prefix_frame` discharges that prior invariant from the
initial reflexive frame by induction over actual TLoop.iterN. Its only semantic
premise is a running or successfully completed finite prefix; body frames come
from published Prog.run_frameM, local/heap composition from published laws.
No desired preservation equation is a premise of the prefix theorem. The
condition's existing Val.evalT does not return a mutated state; no extra
condition-admission certificate is claimed. Heap framing holds for admitted μ;
TGFrameM storage/net/balance preservation is conditional on μ ≠ nonpayable.

The actual mixed body has two successful iterations: increment persistent p and
transient t, storage push followed by TWO pops, increment the caller counter,
allocate scratch[0,0], then let TRun.loop unwind that scratch local. Initial
caller has nonempty memory[7,11], TWO aliases to it, counter9, untouched17,
persistent7/transient9, live storage array[13,17] and nonzero transaction values.
Complete selected Observation projections at horizons0/1/2/3 are ordered and
pinned: heap sizes1/2/3/3; counter9/10/11/11; p7/8/9/9; t9/11/13/13; live storage
length2/1/0/0 and shadow length0/2/3/3, live/shadow contents, alias IDs/contents,
untouched scalar, sender/value/balance. Horizons0/1/2 are running, horizon3 is
successful completion. These are observations of actual runs, not a new G01
event semantics or an equality of the whole world. `horizon_split` uses the
existing loop_prefix_continue at the nonzero split1+2. `actual_loop` consumes
published run_of_iterN, not a bounded replacement of TLoop.run.

The existing predicate is narrower than this mixed body: published Stmt.within
in Calculus/Blocks assigns false to push/pop, and Stmt.withinM in RunFrameMem
also assigns false to both, EVEN at nonpayable. `mixed_body_rejected` preserves
that actual refusal. No generic frame theorem is instantiated with this false
premise, no reserved predicate is repaired and no assumption hides the gap.
The mixed witness's `concrete_old_heap` instead exhausts every typed reference
in its actual singleton initial heap and proves Heap.Keeps for all those old
objects; this is a concrete consequence, not a general mixed-loop frame law.
`mixed_alias_transport` proves both exact dependent references along second.ext.
`exact_second_extension_and_unwind` pins the composed extension and body-local
export. Fresh scratch identities1/2, transported first scratch and both surviving
scratch contents are proved. Canonical typed refs plus explicit congruence avoid
repeated whole-run dependent inference. Earlier unchanged200000-heartbeat
failures remain raw evidence; no proof budget was raised.

A SEPARATE actual two-iteration allocation/counter body is withinM-admitted.
`allocation_prefix` proves its actual finite execution, excluding extraction
fallback; `admitted_prefix_frame`, `admitted_old_heap`, `admitted_alias_transport`
and its complete selected observations instantiate the generic consumer without
an oracle. This admitted witness does not stand in for the mixed push/pop body.
Old-alias-write rejection controls remain in AllocationFrameChecks; no writes
through the old memory object are admitted or inferred noninterfering here.

The failing variant executes a successful first horizon with all first-state
observations, then the second body actually reverts after its mixed changes
with bytes de-ad-22-00. `second_body_failure` and `failure_second_horizon` retain
THalt.revertWith and those exact bytes. Ordered failing horizons0/1/2/3 and
`failure_absorbs` (every n≥2) use the existing semantics/iterN_done_le.
`actual_failing_loop` derives the mathematical loop result via run_of_iterN.
Wrong order, old content, fresh identity, premature transient reset and wrong
payload are rejected; failure is distinguished from exhaustion/divergence.
TRes.error carries NO successful State: no state rollback, source catch,
whole-world unwind or compiler-failure simulation is inferred. A real successful
State.glob.transactionEntry control keeps persistent9, resets transient13→0
and heap3→0, while internal iterations retain transient11/13 before that boundary.

#### Remaining producer/dependency map after this checkpoint

| Original obligation | Published obstruction/evidence | Required producer/application, still open |
|---|---|---|
| Work1/G37.01 | Existing Gap proofs keep Evm.argsIn memory/storage-argument refusals and CallRetIn reference-result refusal; Evm/Compile remains inline/value based. | V11 integrated mixed heap/storage representation, target runtime frame/stack transport and old internal-call owner's exports; no reserved edits here. |
| Work2/G37.02 | Syntax/Scoped still has recUnroll/recBase/recDepth1024; Syntax/Elab/Arms uses that cutoff; Evm.inFrag callRec is none. | Source/lowering owner's unbounded recursive execution interface plus target recursive-frame simulation; finite controls and prefix algebra do not discharge it. |
| Work3/G37.03 | Solidity.Source.Val.internalFn retains dependent ps/rs/m, while current core target lacks the needed general runtime frame theorem. | Published full-signature dispatch/lowering linked to that frame theorem; restricted function-ref-args owner remains untouched. |
| Work4/G36.01 | Intrinsic statements use existing blocks/branches and lowered loop flags; no break/continue/early-return semantics was invented. | Reserved source/structured lowering plus exact target alias/frame transport and final structured simulation. |
| Work4/G36.02 | Blocks.within/RunFrameMem.withinM reject push/pop; Evm/Compile.inFrag loop requires pushes=0 and no shrink. New mixed_target_refused proves this exact witness is refused for every Frag/LoopAnn. | Published old memory-loop/V11 mixed-state allocation/shrink representation and general target loop simulation; scoped admitted-only frame and concrete observations do not close it. |
| Work4/G36.03 | Existing TRun.loop/prefix consumers expose only intrinsic execution/frame observations here. | Payment/call-loop final interface/application remains open; V14 final proof is not undertaken. |
| Work5/G38 | Failure.Local execute/save/return/failure components are published, but TRes.error contains no failed State. Prior rootJournal consumers are projected roots only. | Actual statement/target-state-to-local-emission frame/unwind adapter and full rollback coupling; arbitrary callbacks/world composition stays V13/V15. |
| Work6/G39 | State.transactionEntry/resetTransient are consumed unchanged; no arbitrary target call-world coupling is supplied. | Target root/reset/local sharing/rollback representation and V13/V15 self-call/callback applications, retaining distinct persistent/transient roots. |
| Backfill A | Prior typed call/return/alias/content and finite recursion controls remain useful partial evidence. | Remaining target-frame extension/composition and full original coverage, not promoted to closure. |
| Backfill B | New admitted-prefix frame and concrete multi-iteration mixed/failure/reset controls add independent evidence. | General mixed-state local unwind/transient composition and missing target/world applications remain open. |

No prerequisite branch was fetched/imported/cherry-picked; all reserved sources
stay read only. These are missing producer obligations, not a human semantic
choice or a request to approve a premise/exclusion. No global G03/status or
Fml.inTarget/profile/refusal/SolKey change. Original full run-lean.sh exit124 at
fixed300s remains FAIL/incomplete, TestSuite/sort unreached, not repeated or
extended. Prior no-build exit3 stays inventory only. Normal/strict raw docs
failures remain visible separately from complete exact-base no-new comparisons.
No integrated prerequisite changed to justify rerunning the unchanged full gate.

Continuation4 evidence/artifacts use /workspace/scratch/v12-flow-calls/continuation-4;
all four prior sealed sets remain untouched. Existing goal remains independently
confirmed blocked (audit fcc30e9b-129f-4eb0-a1cd-596534287c3c); no goal write,
reset/reactivation/recreation or competing continuation is attempted this turn.
Separate read-only finder/skeptic source reviews found no mathematical/ownership
defect and requested precise admitted-only/concrete-only/selected-observation/
no-rollback wording, retained above. Guarded/focused/static/checksum outcomes,
actual versions/resources, final diff/artifact reviews and full committed hash
bindings are recorded below or in the exact-head external handoff.


Continuation4 checkpoint gates: `lake build
Solidity.Backend.InternalFlow.ScopedLoopFrame
Solidity.Backend.InternalFlow.MixedLoopPrefixes` passes79jobs in12.385s,
sampled aggregate RSS937128KiB, cgroup peak515620864B (`cp5-focused`).
Final `bash tests/internal-flow/check-files.sh <evidence>/guarded-files` passes
all13files in32.825s,RSS918276KiB,peak309661696B (`cp5-final-files`). Its exact
per-file commands are `lake env lean -j1 --tstack=131072 <owned-file>`; no Lean
MCP diagnostics are exposed, so the repository lean-verify CLI fallback is used.
All48new public theorem axiom pins are guarded and pass (only propext,
Classical.choice, Quot.sound or proper subsets). Tests retain120s bounds,
LEAN_NUM_THREADS=1 and explicit-j1, canonical writer lock, enforced aggregate
12884901888B memory/swap0, serial heavy work and the existing cache. Early typing
and default200000-heartbeat failures remain cp5-controls-* raw logs; no budget
increase. `lean --version; lake --version; lake build Solidity.KeySort` passes
2jobs in1.749s:Lean4.24.0 commit797c613 and Lake5.0.0-src+797c613 (`cp5-runtime`),
runtime gate only. Layer/import/orphan/trust/diff gates pass172core/0elaborator,
13owned/0findings,1009reachable/0orphans,1024sources/246trust sites/0findings.
Normal/strict docs raw exits1 persist; BOTH complete outputs equal exact frozen
base byte-for-byte, separately passing zero additions (static.json).
All prior109/84/91/86checksum entries verify unchanged. Stopped containers created
by cp5 were verified against exact owned CID/name records and removed by CID,
without force/prune or deleting old containers/caches/evidence. This reclaimed
3.64GB and restored about15.1GB available at that measurement; cleanup records
and each gate's disk/RSS/cgroup measurements are retained. No cold full build.
Read-only finder/skeptic source/diff reviews found no mathematical/ownership
defect. Skeptic corrected a module-as-namespace prose reference to the exact
Solidity.Source.Val.internalFn declaration. Both final artifact reviews and
exact committed source hashes are retained in the external continuation handoff.
Full Work1–6/A/B and mandatory full validation remain unfinished.


### Continuation 5: evaluated runtime payloads into checked emission (partial Work5/Backfill B)

Generic names below live in Solidity.Backend.InternalFlow, concrete control
names in Solidity.Backend.InternalFlow.EvaluatedRevertChecks.
`canonicalRevertInput` is a narrow THalt classifier into the EXISTING Input;
`checkedRuntimeRevert` consumes the actual TRes, selects that input and invokes
existing emit/checkedRun. `localRuntimeRevert` feeds the SAME runtime-derived
input to existing Local.execute. These are result-to-component adapters, not
another evaluator, codec, machine or source-to-target compiler. Unlike a
conjunction of unrelated source/emission facts, the actual runtime error's
bytes determine the instructions and output in the conclusion.

`evaluated_revert_execution` consumes actual ordered
parts.mapM (RevPart.evalT state)=ok chunks and derives TRun.revertData's exact
THalt.ofData chunks.flatten. `checked_evaluated_revert` wires this statement
result to checkedRun_emit_suffix, with Fits/headroom explicit.
`checked_call_evaluated_revert` additionally consumes actual Args.evalT success
and evaluates parts in ret.enterT(caller.withEnv arguments).st; call_body_failure
preserves that exact normalized halt. Those premises are execution equations,
not assumed simulation/preservation. `local_evaluated_revert` uses live root
projections FROM that actual known pre-revert State.storage; its saved snapshot
and caller/live slice machines remain explicit component representation hooks.
No failed whole-State is reconstructed. Storage/heap/stack/layout relations
between an intrinsic State and a slice Machine are not proved by these adapters.

The classifier accepts only bare revert and nonempty revertWith. It refuses
panic, exhausted, diverge and noncanonical revertWith [], though each can have
empty THalt.data. Actual revertData normalizes empty evaluated bytes to bare
revert via ofData, and nonempty bytes to revertWith. No panic code is guessed;
this adapter does not reuse inputOfResult's generic panic interpretation.
Assert/panic-code coupling needs its qualified published evidence and target
representation; the actual assert-false control here only proves panic and
refuses emission through this narrow byte-revert adapter. Require-false is an
actual bare-revert-to-checked-empty emission control. A successful actual nil
run is refused rather than converted to failure.

The inhabited source witness reuses the ACTUAL successful MixedLoopPrefixes
prefix (p7/t9→p8/t11, counter9→10, untouched17, populated caller aliases[7,11],
shrink/allocation/unwind), not a newly duplicated loop. successful_prefix ties
its statement run to the known prefix State; ordered_prefix_observations retain
the complete selected initial/prefix projections. Arguments/entered-frame/scoped
argument observations preserve BOTH old aliases and distinct scalars10/17 while
the outer scope declares a distinct55. Two nested ordinary calls and a block
execute the actual parts: literal de-00, word(counter10), raw heap alias[7,11],
empty chunk, word(other17), word(p8), word(t11), second raw alias[7,11].
parts_evaluate proves the complete eight ordered chunks using existing wordBytes
and heap evaluation; lengths2/32/2/0/32/32/32/2 flatten to134 bytes, with zero
padding/embedded zeros and multiple word-boundary crossings. nested_failure and
original_halt_class prove the actual full Prog.runR's revertWith134bytes.
checked_execution feeds THAT actual nested result into emission; checked_direct_call
also instantiates the generic dependent call theorem with both actual premises
discharged. Output-extraction fallback arguments are excluded by success proof.

The checked emitter runs at offset31 on a nonzero dirty byte memory with a
three-word protected stack and an unsupported suffix after the terminal opcode.
The complete output interval[31,165), immutable outcome bytes and exact stack
tail are proved via existing checkedRun_emit_suffix/getBytes_putBytes. The
outside_interval theorem covers EVERY address outside it; boundary markers at
30/165 and bytes31/32/164 are pinned. Source-derived live root projections8/11
and saved7/9 are distinct. Local execution restores the explicit saved journal
and its caller memory0x11, while returning the immutable evaluated134byte list
whose emitted first byte is0xde. This is local projected-journal restoration,
not source catch, whole-State/world rollback, gas/EVM agreement or G01 events.
RETURN of those same evaluated bytes is only an existing Local.execute_return
component contrast, preserving live roots/memory; no intrinsic ABI return
lowering is inferred.

Controls reject reordered chunks, wrong length133, shifted output offset,
transient-zero substituted into the payload, success instead of revert and
premature root reset. Empty parts actually evaluate empty and halt bare revert.
The current intrinsic division-by-zero evaluation returns bare revert (consumed
unchanged, NOT claimed source Panic correctness); an actual nonzero division
baseline returns word5. A failing part discards earlier de-ad partial chunks,
so only the original empty-revert result reaches emission. Stack baseline1022
succeeds with the same valid offset/empty payload;1023 is initially legal but
fails precisely the required two-word temporary headroom, and checked emission
returns none. No failure is replaced by success, no Fits is waived and no
heartbeat/recursion/fuel/node/test limit is increased. Early type/default-depth
failures remain raw evidence; final proofs use explicit types, memory-frame and
stack-boundary laws rather than larger budgets.

#### Remaining original producer map (no parent closure)

| Item | Exact remaining producer/boundary |
|---|---|
| Work1/G37.01 | Published core Evm.argsIn/CallRetIn still refuse general memory/reference call transport. V11 target heap/layout plus old internal-call frame/stack representation exports remain missing; the independent source result adapter is not such a representation. |
| Work2/G37.02 | Existing Syntax.Scoped recDepth/recUnroll/recBase and Elab.Arms cutoff are unchanged; core callRec refusal remains. Source/lowering owner's unbounded recursive execution and target-frame simulation remain open. |
| Work3/G37.03 | Solidity.Source.Val.internalFn retains dependent signatures; its target dispatch lowering must consume the unavailable general frame theorem. Restricted function-ref-args owner stays untouched. |
| Work4/G36.01–.03 | Structured source/flag lowering and target frame/alias proofs, general push/pop/shrink/allocation loop simulation and payment/call-loop interface/application stay open. Prior withinM push/pop and core mixed-loop refusals remain actual controls. |
| Work5/G38 | NEW actual evaluated statement/call payload→checked/local emitter coupling is proved. Still missing: an actual target-frame representation relating State C Γ to Slice.Machine and proving the chosen stack tail/byte-address layout/offset denote that State; target storage/root representation; statement lowering carrying that relation across the prefix/calls and qualified assert/panic-code/ABI-return applications. Existing TRes(Out C σ.H Γ) error returns only THalt, so no failed live State can be extracted to establish whole-State rollback. Such an enriched source/world rollback producer belongs to its existing owners, not a new premise silently discharged here. |
| Work6/G39 | Logical root projections/reset laws are unchanged; target transient/persistent root representation, sharing/rollback and arbitrary V13/V15 self-call/callback/world coupling remain open. |
| Backfill A | Prior frame/content/finite-recursion controls remain partial; general target-frame composition and full original coverage remain outstanding. |
| Backfill B | Evaluated payload bytes now drive actual projected emission after a successful scoped prefix; general target local-unwind/transient/world composition and full original coverage remain outstanding. |

The concrete machine hook is deliberately not identified with source heap or
locals: a representation relation of type State C Γ → Slice.Machine → Prop
is an open producer obligation, not a declared or assumed relation here.
The reserved producer must construct/prove that relation for actual lowering,
including stack/local encoding, heap byte layout and a noninterfering output
interval, and connect persistent/transient target roots. This is an explicit
open representation/transport obligation, NOT an assumed hypothesis in the
payload theorems. TRes.error's codomain obstruction additionally prevents
inventing a lost live State. No reserved source/predicate/semantic/component
implementation was edited, no unmerged branch imported and no global status/
G03/profile/refusal/Fml.inTarget/SolKey mapping changed. All Work1–6 and BOTH
full backfills remain unfinished. No semantic human choice is pending.

Original full run-lean.sh exit124 at fixed300s remains FAIL/incomplete with
TestSuite/final sort unreached, not repeated, extended or narrowed. Prior
no-build exit3 remains readiness inventory. Normal/strict docs raw exits1 stay
failures, separately compared COMPLETE exact-base findings for zero additions.
No new integrated prerequisite justifies rerunning that unchanged failed gate.
Continuation5 uses /workspace/scratch/v12-flow-calls/continuation-5, preserving
all five prior sealed sets and raw failures. Existing independently blocked goal
(audit ac446be6-6529-4285-a739-06bf368cfe30) stays untouched: no status write/retry,
reset/reactivation/recreation or competing continuation. Separate read-only
finder/skeptic source reviews clear actual coupling/non-vacuity/ownership and
require the qualified machine/projection/class boundaries retained above.
Exact scoped gates/resources/guarded sets, final diff/artifact reviews and full
committed source/base/head bindings follow below or in the external handoff.


Continuation5 checkpoint gates: `lake build
Solidity.Backend.InternalFlow.EvaluatedRevert
Solidity.Backend.InternalFlow.EvaluatedRevertChecks` passes81jobs in9.014s,
sampled aggregate RSS1040084KiB, cgroup peak598540288B (`cp6-focused`).
Final `bash tests/internal-flow/check-files.sh <evidence>/guarded-files` passes
all15files in40.084s,RSS995432KiB,peak386379776B (`cp6-final-files`). Each file
uses `lake env lean -j1 --tstack=131072 <owned-file>`; no Lean MCP is exposed,
so repository lean-verify's permitted CLI fallback is used. All55new public
axiom reports, INCLUDING axiom-free reports, are guarded and pass; dependency
sets are only propext/Classical.choice/Quot.sound or subsets/none. All gates
retain120s bounds, explicit-j1/LEAN_NUM_THREADS=1, canonical writer lock and
enforced aggregate12884901888B memory/swap0, with serial heavy work and OS/disk
headroom. Existing source/toolchain-keyed .lake cache remains1.9GB; no duplicate
tree/cache. Exact stopped cp6 CID/name records were checked before cleanup;
only those owned stopped containers were removed, without force/prune or touching
source/evidence/cache/older resources. Cleanup and per-gate disk/RSS/cgroup
measurements are saved. Early type/default recursion-depth failures remain raw
cp6-checks-* evidence; no limits changed. `lean --version; lake --version;
lake build Solidity.KeySort` passes2jobs in1.724s:Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613 (`cp6-runtime`), runtime gate only.
Layer/import/orphan/trust/diff gates pass172core/0elaborator,15owned/0findings,
1011reachable/0orphans,1026sources/246trust sites/0findings. Normal/strict docs
raw exits1 remain; BOTH complete outputs equal exact-frozen-base outputs
byte-for-byte, separately passing zero additions (static.json). All prior
109/84/91/86/114checksum entries verify unchanged. Source finder/skeptic reviews
found no defect; skeptic suggested the added actual-success rejection control.
Both clear source/hypotheses/non-vacuity/ownership and insist on the explicit
result-coupling, class, machine-hook and projected-restoration boundaries above.
Final staged diff/artifact review and actual full head/base/source hashes are
bound in the external continuation handoff. All original Work1–6/A/B and the
mandatory full gate remain unfinished; no whole-lane completion is claimed.


### Automatic continuation: producer reinspection and Work2 qualification

At clean implementation head86577b388a1a0d438a3454585a343608ad98e5c9,
read-only reinspection confirmed that Failure/Observe already publishes the
qualified assertion/require and encoded-result observation component laws.
Adding another wrapper would duplicate completed reserved work without producing
the missing target runtime/frame representation. No generic panic-code mapping
or whole-State rollback is added. Checked memory compiler StateRepr/AllocationInput
interfaces and limited compiler paths are acknowledged; their existence is not
denied by the core-fragment refusal controls.

Independent finder review corrected an overbroad Work2 blocker description:
the INDEPENDENT unbounded source semantics is ALREADY PUBLISHED in
`Solidity/Source/Eval.lean` (horizon family, including callInternal) and
`Solidity/Source/Semantics.lean` (sessionAt_consistent/sourceLang).
The horizon-zero timeout is not itself program behaviour, and that family has
no fixed loop/internal-recursion completion cutoff. External callAddr/envLoop
depth-limit failure branches remain unchanged. The still-missing V12 obligation
is its lowering/uncapped intrinsic-runtime interface and target recursive-frame
simulation. The separate scoped intrinsic recDepth/recUnroll use in
`Solidity/Syntax/Scoped.lean` and `Solidity/Syntax/Elab/Arms.lean` remains;
changing1024 or repackaging finite controls cannot prove that connection.
Earlier references to a missing source-recursion producer must be read with
this qualification: existing independent source semantics is reused read only,
not reassigned, absent or being recreated.

All original Work1–6 and Backfills A/B remain partial/blocked as mapped above.
No new Lean source, theorem, representation assumption, profile/refusal/verdict,
reserved implementation or proof budget is changed. No unchanged heavy gate is
repeated; the original full300s exit124 and readiness-only no-build exit3 remain.
This is a documentation correction with separate exact-base documentation
comparisons and independent finder/skeptic review, not an empty marker commit
or another proof/completion claim. Its versioned blocker audit is under
/workspace/scratch/v12-flow-calls/continuation-6-blocker-audit; all prior sealed
sets remain untouched. Stopping the existing goal as blocked is requested only through the automatic
continuation's goal context, without recreation/reset or a competing continuation;
the actual stop result is recorded in that audit.
