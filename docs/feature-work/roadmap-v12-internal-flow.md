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


### Published ordinary memory-call consumer (continuation 7)

This checkpoint supersedes earlier missing-memory-call-producer statements for
ordinary direct void, primitive-result and memory-result calls ONLY. Published
revision91e94ab57305ca055127934fd9e68fe9ea5e6be3 was incorporated as first-parent
published cherry-pick5db3bb36fa9f48a59630b6f9692424f50d4c68b4. All previous V12
commits and frozen-base ancestry are preserved. No unmerged worker revision or
manual reserved implementation repair was used. The historical core-only
argsIn/CallRetIn refusals remain true of their particular paths; they do NOT
refuse the new unified Compiler fallback.

`Backend/InternalFlow/PublishedDirectCalls.lean` consumes actual published
Calls.Statement.sound and Calls.Program.sound. statement_endpoint identifies
the producer endpoint with the supplied ACTUAL successful intrinsic Out;
program_endpoint does the same for finite program composition. call_endpoint
uses the existing call_return equation and actual Args.evalT/body.runR premises
to identify that endpoint's exact composed entry/body extension, exported
results and transported caller tail. Private argument/body locals are dropped
by the existing dependent CallRet.leaveT/TEnv.take/TEnv.drop execution equation,
not a new evaluator. Genuine StateRepr, expanded-frame need and reached-cost
AllocationInput premises remain explicit; none assumes the desired simulation.
The output carries StateRepr, the unchanged protected stack, BaseExtends for all
old typed identities and GrowsAllocator for the precise reached cost. Stable
addresses do NOT imply unchanged contents for arbitrary mutating callees.
statement_revert consumes only bare ordinary revert. Payload, panic, exhausted
and diverge distinctions are retained; no THalt.data=[] shortcut is used.

The standalone lane fixture tests/internal-flow/PublishedMemoryCalls.lean keeps
elaboration outside the owned core import closure. Its real source program has
scalar42, a length2 caller object containing7/11, two aliases and a callee-local
length2 object containing33. A parameter is privately rebound to another object
containing44. The returned local escapes; old caller references/scalar survive.
All generated frontend temporary locals remain in the ACTUAL typed context and
ordered endpoint observations; they are not silently discarded to fit an
invented frame. Source identities, exact cost9, target cursor265, protected
stack77/sentinel99 and complete ordered pointer/content observations are pinned.
The public Compiler.memoryCalls_input/Compilation.correct branch is instantiated,
with isMemoryCalls/usesMemory true and old isMemory false.

A SEPARATE nonempty_call_endpoint produces its intermediate StateRepr by running
a real prefix through Calls.Program.sound; no intermediate representation is
assumed. Its inhabited caller heap has one nonempty object, aliases0/0 and
scalar42. Prefix cost3 and call cost4 are discharged. The call's actual evaluated
argument is old identity0, and actual body execution allocates the escaping
identity2 while dropping private locals. AllocationInput is transferred using
GrowsAllocator.nextInput. The target and source export observations retain both
old aliases,7/11 contents and scalar42, with cursor263 and returned length2 zeros.
The whole-program endpoint starts with an empty heap, but this separate call-stage
BaseExtends ranges over an inhabited nonempty heap. The fixture tests private
rebinding isolation, not a general old-object-content-mutation frame theorem.
Existing AllocationFrameChecks retains its actual old-alias-write/withinM
rejection and noninterference controls unchanged.

Negative controls reject swapped old/fresh pointers and scalar destinations;
caller_frame_insufficient fails the theorem's expanded-frame input bound, NOT a
claimed runtime rejection. A successful prefix followed by actual bare revert
is compiled to target revert. A nonempty intrinsic payload [7] retains its
revertWith class and is REFUSED by the direct memory-call producer; existing
byte-emission consumers therefore cannot yet be composed through this path.

Independent finder and skeptic source reviews found no mathematical/ownership
issue and requested explicit fixture signatures and a nonempty represented
call-boundary control. Both are added. They verified that the representation
and next-allocation input are produced by real prefix execution, and required
precise distinctions between base-address stability/content preservation,
failed frame premises/runtime rejection and finite expansion/unbounded recursion.
Final skeptic review caught a temporary-local offset in the swap negative: it now
samples cells2/3/6, including the actual returned pointer, rather than three old
pointer cells. This confirmed control finding is fixed.
Final gate commands, guarded actual axiom reports, resource readings and artifact
review are recorded in the new continuation7 handoff/evidence, never over the
seven earlier sealed sets. Lane check-files now includes the standalone fixture;
cache keys additionally hash that fixture and its actual import closure.

Updated original queue accounting (all parents remain unfinished):

| Obligation | Newly available consumption and exact remaining boundary |
|---|---|
| Work1 / G37.01 | Ordinary direct memory-call representation is NOW published and consumed, with inhabited nonempty call-stage arguments, locals, escaping result, exact frame/cost/stack/address evidence. General storage/tuple/reference frame cases and runtime recursive frames remain unavailable: Calls.atHeight refuses storage/rets/callRec; preserve those producer refusals and reserved owners. |
| Work2 / G37.02 | Finite ordinary direct-call bridge now consumes actual producer soundness and exact Out. Structural finite embedded-body expansion has no public height search cutoff, but it is not arbitrary unbounded recursion. Missing source lowering/uncapped intrinsic runtime/target recursive-call simulation remains; independent unbounded Source semantics is already published and unchanged. |
| Work3 / G37.03 | Full dependent-signature function-value dispatch still needs its published lowering linked to general frame transport. Ordinary named direct calls do not supply that producer; restricted function-ref-args owner stays untouched. |
| Work4 / G36.01-.03 | New direct-call producer supports its existing blocks/branches. General mixed push/pop/shrink/allocation loop compilation, break/continue/early-return transport and V14 payment/call-loop application remain open; existing withinM restrictions and concrete mixed-loop controls are unchanged. |
| Work5 / G38 | Bare ordinary call failure now reaches actual target revert. Nonempty revertData is refused by this new compiler path. Still needed: a producer coupling Evm.Machine word memory/frame to Failure.Slice.Machine byte memory/protected interval, qualified panic/ABI-return lowering, actual root/frame unwind and world rollback. Existing evaluated/local byte proofs do not infer a lost State from TRes.error. |
| Work6 / G39 | Existing transient reset/root/local projected laws remain. New StateRepr includes its existing core store relation; no new transient transaction reset/callback/whole-world coupling follows from it. Distinct target transient/persistent root and boundary adapters plus V13/V15 applications remain open. |
| Backfill A | Additional real target producer consumer and nonempty call-stage controls pass; extension/prefix/result/finite-recursion work is partial evidence, not discharge of the entire original backfill or unbounded recursion. |
| Backfill B | Existing nested projected emissions/mixed finite loop/evaluated payload consumers remain partial. General unwind/rollback/mixed-location and final world applications are not newly discharged. |

The new source-keyed cache strategy retains one existing .lake tree. Bounded
cold import chunks refresh only declared prerequisites; original raw timeouts
remain visible. The first per-file test detected stale October24 Elab.olean
(join duplication, then obsolete Blk); Lake refreshed the declared Splice
closure without editing reserved sources or importing cached unmerged code.
The mandatory original full run-lean.sh exit124 at300s remains FAILED/incomplete,
TestSuite/sort unreached; old no-build exit3 remains inventory only. No full
rerun, target removal or budget increase is used. Normal/strict documentation
raw exit1 and complete exact-base no-new comparisons are separate gates. This
checkpoint is partial, does not close the persistent goal and requests no new
semantic premise, exclusion or human scope decision.


Continuation7 verified gate record: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613; dedicated lake build Solidity.KeySort reports successful2jobs.
The source-call prerequisite passed75jobs; adapter/public Compiler passed158jobs;
complete owned/published-control import closure passed197jobs in44.320s.
All16owned files plus standalone fixture passed per-file diagnostics in55.710s;
the review-corrected swap fixture passed again in15.925s. The separate Python
axiom guard accepts all27 exact observed sets (26 canonical three-axiom sets
and axiom-free noRef); altered/missing-report guard negatives reject as intended.
Layer/import/orphan/trust checks pass:172 core modules,16 owned,1014 reachable,
1029 sources/246 inventoried sites, zero findings. These are SCOPED gates, not
full validation. The largest sampled aggregate RSS among new gates was
1,788,260KiB and maximum recorded cgroup peak1,687,433,216B; each capped gate
records memory.max12884901888 and memory.swap.max0. No overlapping Lean builds,
new heartbeat limits, swap or duplicate build tree was used. Eighteen verified
stopped continuation7 containers only were removed, restoring about14GiB disk
headroom; caches, previous containers/evidence and all prior manifests remain.
The first cold import gates retain exits124 at120s, a missing-import fallback
exit1, stale elaboration-cache failure and fixture-development failures; later
passes do not relabel them green. All command arguments and decisive output,
source/toolchain hashes and bounded resource measurements are in continuation7
rather than overwriting any earlier evidence. Final exact-base docs comparisons,
review records, complete queue/handoff and artifact checksums accompany the head.

Normal and strict docs gates actually returned1 with46 missing references; BOTH
complete outputs are byte-identical to the exact frozen-base outputs, so the
SEPARATE no-new-findings comparisons pass. All seven previous checksum manifests
verify unchanged (109/84/91/86/114/90/34 entries). The original full300s failure,
no-build exit3, new cold gate failures and raw doc failures remain in evidence.


### Mutating older caller aliases (continuation 8)

This original Work1/G37.01 and Backfill A checkpoint extends the real published
ordinary memory-call consumer; it does not repeat the earlier private-rebinding
witness. Two scoped consequences are added to PublishedDirectCalls:
old_alias_at_entry_address combines a known transported caller local with the
actual post-StateRepr and BaseExtends to recover its unchanged entry address;
old_array_at_entry_address represents the ACTUAL output array contents at that
entry address. Neither assumes or proves general Heap.Keeps. The type retains
the original HRef and its actual Out.ext weakening. No source/type/state/target
representation or semantic predicate is changed.

The standalone tests/internal-flow/MutatingMemoryCalls.lean fixture has a real
prefix producing object0=[7,11], distinct object1=[23,29,31], two aliases of0
and scalar42. Its typed intrinsic callee writes19 through the evaluated old
reference, binds the result to that SAME reference, then privately rebinds its
parameter to object3=[99,101]. This is binding a return variable before the
later private writes, not inventing early-return execution. Return-entry object2
is the allocated empty default and stays in the real heap. Exported result0,
caller other1, both old aliases0/0 and scalar42 have the exact typed Final
context; only private binders are dropped. Dropping is not physical scrubbing:
private/scratch cells may retain values outside the live context.

The subsequent caller program writes37 to index1 THROUGH THE RETURNED ALIAS.
Actual Val.evalT reads through both original aliases and the returned alias see
19 after the call and37 after next use; the distinct old object reads23/29 and
retains its entire length3 contents[23,29,31]. All objects, including the empty
entry allocation and private allocation, have complete ordered source snapshots
at prefix/entry/body/export/next-use. Ordered actual target observations pin all
live pointer/scalar cells, lengths, contents, protected stack77, sentinel99,
private parameter cell5=264 before export, result cell6=256 before export and
live result cell5=256 after export. Prefix cursor263 becomes267 and stays267.
Source complete-program observations and actual public Compiler code are also
checked, rather than only a manually concatenated target endpoint.

represented_stages PRODUCES all three representations through actual prefix,
call and next-use execution. The prefix costs7, reached call costs4 and next
use costs0; exact need values are4/6/5 and public requiredFrame6. Public
Compiler.memoryCalls_input/Compilation.correct are instantiated on the whole
joined intrinsic program. The call's AllocationInput comes from the prefix's
actual GrowsAllocator.nextInput; no desired intermediate representation,
noninterference conclusion or simulation hypothesis is assumed. The actual
Args.evalT, body.runR and call-return equations are separately proved.

represented_old_objects instantiates the two scoped consequences for mutated
old0 and unrelated old1. Independent finder and skeptic both caught that its
first draft dropped the actual run equations from the existential conclusion.
The corrected theorem RETAINS actual prefix/call Evm.run equations and call
stack equality with the reached StateRepr/pointer/ArrayRepr facts. Both reviews
cleared the correction. The unrelated-content claim is established by the
actual source execution/observations; stable addresses alone do not imply it.

Positive baselines accompany wrong same-typed result1, missing mutation7,
unrelated-object mutation19, private-result escape3 and composed-cost12
negatives. Actual public target code separately rejects the corresponding
wrong return address259, old value7, unrelated value19, private address264 and
cursor268 observations. These are wrong observations of SUCCESSFUL executions,
not claims of runtime rejection from a failed input premise. The mutator's
withinM.view predicate is explicitly false, preserving the allocation-only
frame exclusion and all existing old-alias-write controls. No arbitrary mutator
is admitted into Heap.Keeps/withinM by this checkpoint.

Per-file fallback is used because no Lean MCP diagnostics is exposed. Initial
raw exit137 checks at the enforced12GiB peak and smaller failing probes remain
FAILURES. Diagnostic-only evidence probes isolated the dependent call-endpoint
application; no diagnostic IO is present in delivered source. Explicit actual
result arguments fixed unresolved source metavariables; explicit L/frame/state,
address maps and machines plus separately typed discharged room/capacity inputs
removed expensive endpoint inference. The final composition probe passed in
3.528s with231645184B cgroup peak, and the complete fixture/direct-read check
passed in18.721s. No memory, swap, heartbeat, depth, fuel, node or test limit was
raised. Existing large-certificate opacity conventions were inspected; opaque
runtime-state experimentation was removed after it obstructed dependent types.
Every raw failure is retained, not relabeled by subsequent scoped passes.

The42 actual new public fixture/helper axiom sets are pinned separately; the
previous27-report guard remains unchanged. The lane's complete per-file sweep
now includes both fixtures, and its single source/toolchain-keyed .lake cache
inventory already hashes both fixtures and their actual imports. No duplicate
build tree or external dependency cache is exported.

Read-only published-prerequisite reinspection continued beyond the mutation
checkpoint. The local tracking ref was91e94; fetching ONLY public origin/master
under the canonical writer lease found4165de133bafd522ab18099e18cad489bb1aa7d6,
with human-audited93920309f5c800c9ce4809bc74700ed4fde65fb2 its ancestor. No source
merge/import or worker-branch fetch occurred, and the own branch was preserved.
The three consumed Compiler/MemoryCalls/MemoryCallExamples files remain exactly
the91e94 published bytes even on that newer master. Additional published
Bridge ExternalEvm.MemoryRefinement.Represents is acknowledged: preallocated,
capacity-wide NUMERIC words, active physical EvmYul memory and explicit padding
allocator contract. It does not provide a core StateRepr-to-Failure.Slice frame,
byte/journal or transient-world coupling; Bridge is still forbidden in core.
The new TryPanicProducer explicitly labels producer36 an intrinsic GHOST, not
the original carried source callee; its raw ofData-computed bytes theorem is
not an arbitrary panic-code or target-call compiler theorem. Actual signatures
and source tags are retained in published-api-audit.log/ready-work-reinspection.json.
No conditional bridge/ghost result is counted as discharge of V12's missing
producer or recreated in another namespace.

Full original queue remains binding:

| Original item | Actual progress and remaining obligation |
|---|---|
| Work1/G37.01 | PARTIAL: real ordinary target memory-call mutation, old alias return, private rebinding, distinct-object observations and subsequent caller use now proved. General storage/tuple/runtime-recursive frames remain refused/missing in the unchanged producer. |
| Work2/G37.02 | PARTIAL/BLOCKED: finite direct calls, intrinsic finite recursion and prefixes remain evidence; no unbounded source-lowering/uncapped intrinsic runtime/target recursive simulation is supplied. Published independent Source semantics is acknowledged; existing cutoffs/exhaustion/refusals stay intact. |
| Work3/G37.03 | BLOCKED: full dependent-signature function-value dispatch needs its actual general runtime frame/lowering producer; restricted owner remains unchanged. |
| Work4/G36.01-.03 | PARTIAL/BLOCKED: ordinary supported blocks/branches and existing concrete mixed finite-loop evidence are retained. General mixed heap/storage push/pop/shrink/allocation loops and break/continue/early-return transport plus V14 application remain open. |
| Work5/G38 | PARTIAL/BLOCKED: actual evaluated byte/local projected consumers and ordinary bare target revert exist. Nonempty revertData remains refused by this memory-call compiler. New published byte/refinement/ghost components are not absent, but no actual core word-cell-to-Slice byte/frame/journal relation, qualified full panic/ABI return/unwind or whole-State/world rollback composition is discharged. TRes.error contains no live State. |
| Work6/G39 | PARTIAL/BLOCKED: existing intrinsic reset/projected-root/local laws remain, with no new transient/self-call/callback/world or general target root/boundary composition from this memory-only witness. |
| Backfill A | PARTIAL: new genuine mutating target-call/reference/array consequences supplement existing extension/result/prefix/finite-recursion controls; original coverage and mandatory final integration/validation remain open. |
| Backfill B | PARTIAL: existing nested projected emissions and mixed finite-loop/evaluated payload evidence remain; general unwind/rollback/root/world applications and full validation remain open. |

The original full run-lean.sh exit124 at fixed300s is still FAILED/incomplete;
TestSuite/sort were not reached. It was not repeated. Old no-build exit3 stays
inventory only; normal/strict docs raw exit1 and separate complete exact-base
comparisons are recorded separately. No new axioms, sorry, native_decide,
implemented_by, changed Fml.inTarget/profile/verdict/exclusion/SolKey mapping,
reserved source edit, goal write/reset/reactivation, push/merge/PR or whole-lane
completion claim is made. Prior sealed sets are preserved; a new continuation8
export binds the actual committed head, gates, reviews and outstanding queue.


Continuation8 decisive scoped gates: actual Lean4.24.0
(797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake5.0.0-src+797c613; dedicated
KeySort reports successful2jobs. Owned/published-control import closure197jobs
passes in1.407s using the existing validated cache. All16 owned modules and
BOTH standalone fixtures pass serial per-file checks in73.407s; the final new
fixture passes in18.721s. Separate host exact-axiom guards pass42 new and27 prior
sets. Wrong/missing/duplicated/error-bearing guard logs are all rejected by the
new guard, as intended. Layer/import/orphan/trust checks have zero findings.
All eight prior seals verify unchanged (109/84/91/86/114/90/34/7 entries).
Only24 verified stopped continuation8 containers were removed; cached sources,
.lake artifacts, previous evidence and unrelated containers were retained,
restoring about14GiB disk headroom. Raw exit137/cap-peak diagnostic failures and
all intermediate failed checks remain; final green gates do not rewrite them.
Final documentation exits and complete exact-base comparisons, exact source
hashes and independent artifact reviews are recorded with the new committed
checkpoint's handoff. Full300s/TestSuite/sort obligations remain incomplete.


### Direct primitive multi-result export (continuation 9)

This Work1/G37.01 and Backfill A checkpoint closes the LOCAL missing direct
CallRet.rets export consumer for the actual Binders interface. It does not
close the whole original assignment, change the reserved MemoryCalls producer,
or change public Compiler.compile admission. The initial public refusal is
reproduced by public_refusal/public_refusal_unchanged on an inhabited call.

Actual source-type boundary: Scope.Binders has only nil and snoc of PrimTy,
producing .val p :: rs. There is NO memory/storage-reference binder constructor.
Binders.defaultsT returns TEnv C H rs at FIXED H; CallRet.enterT.rets appends
those primitive defaults with identity heap extension. Tuple entry therefore
allocates ZERO objects. Single CallRet.mem remains a different constructor
whose default entry allocates a real object. no_memory_binder and
no_storage_binder prove the actual tuple type obstruction, rather than assuming
an uninhabited mixed-reference fixture. The exact reference-binder failed Lean
command and both type mismatches are retained in reference-binder-refusal.log
and unsupported-reference-binders.lean under continuation9 evidence.

A future reference-tuple producer needs reserved source Binders constructors
AND actual allocating default-entry transport, not uints pretending to be
references or a new AST. In particular fixed-H defaultsT cannot manufacture a
fresh HRef into an empty heap. An allocating interface would have to return an
actual Out C σ.H (rs ++ ps) from a State C ps, exposing the heap extension and
per-result default allocation order, then be linked to CallRet.enterT.rets and
its frame laws. Such a representation/profile change needs its actual source
owner and G0 handling. No such signature, exclusion or premise is assumed or
approved by this checkpoint. Storage/function-value tuple categories likewise
are not silently included in primitive Binders coverage.

Backend/InternalFlow/TupleCalls.lean implements:

* expand: actual Args.declsThen, Binders.declsThen and scoped weakened body,
  exactly as the published Stmt.runSt_callRets theorem. Args remain evaluated
  in their caller context and original order; defaults and private body/parameter
  removal are the existing intrinsic operations. expand_runSt consumes that
  theorem, and expand_runR recovers the exact Out extension/outcome, preserving
  every original error class and payload rather than only successful states.
* exportCode/resultFrag: arbitrary Binders arity and ALL current primitive kinds,
  with increasing-address mload/mstore result export. This is a real instruction
  list, not a replacement evaluator. compact is proved by Binders induction,
  including nil and ps=[]; it preserves reached StateRepr, caller tail/pointers,
  actual post-body heap, stack, every cell outside the export destination range
  and the published allocator representation. The reached local-frame bound
  provides space. Allocator framing retains the genuine 0<b condition.
* tupleReturn: a genuine Calls.Statement over the actual original Stmt.call.
  It consumes the published compiler's actual expanded-program Calls.Program
  and appends the proved export code. need/cost/allocates/zeroCost come from that
  real certificate; return copying allocates nothing. StateRepr, expanded room
  and reached AllocationInput remain real prerequisites, not desired simulation
  assumptions. Exact source equivalence identifies the actual original call's
  Out with the represented target endpoint. Failure uses run_append_revert,
  so export does not execute after bare failure.
* compileTuple: an owned direct-tuple entrypoint delegating the ENTIRE expansion
  to Calls.compile. It returns none for other statements or unsupported expanded
  bodies. It does not add automatic nested-tuple lowering, unbounded recursion
  or a new public Compiler branch. Both an admitted tuple and refused nonempty
  revertData body are checked. Public Compiler.compile still refuses the tuple;
  that earlier guard remains true and is not relabeled green.

The standalone tests/internal-flow/TupleMemoryCalls.lean witness executes a
REAL prefix with old0=[7,11], distinct old1=[23,29,31], aliases0/0 and scalar42.
Its evaluated parameters are memory0 then scalar42 (frame innermost order42/0).
The result binders are declared uint lo, uint hi, bool flag, with intrinsic
context [flag,hi,lo]. The callee writes19 through its evaluated old reference,
computes lo=seed-25=17, hi=lo+12=29 and flag=hi>lo=true, allocates scratch2=[99,101]
and privately rebinds its parameter to scratch2. All real binders are retained
in Input/BodyCtx; the explicit intrinsic driver does not claim frontend lowering
or discard hidden temporaries to fit a chosen frame.

Complete ordered snapshots pin prefix/entry/body/export/next-use objects,
lengths, contents, all result values and all caller aliases/scalar. Heap sizes
are2/2/3/3/3, explicitly showing no tuple entry allocation. Declared result order
is lo/hi/flag; context head order is flag/hi/lo; physical exported cells5/6/7 hold
17/29/1. Before export the source result cells are7/8/9; private parameter/seed
are5/6, private scratch10. Actual low-first export overwrites only5..7. Stack77,
sentinel99 and stale scratch/source cells outside the live context are pinned;
binder dropping is not physical zeroization. The caller then requires flag,
sets its scalar to100*lo+hi=1729 and writes lo through its old alias, yielding
old0=[19,17] while unrelated old1 remains[23,29,31]. Prefix cursor263 advances to266
and remains266. Needs are4/10/10/7; allocations7/3/0. An actual high-first bad
instruction control executes successfully but corrupts lo to1 via overlap,
producing [1,29,1], rather than relying on a failed Input premise.

represented_stages obtains ALL three reached representations and execution
witnesses from actual prefix/call/next code. GrowsAllocator.nextInput produces
the real call/checked-program capacity; no midpoint is supplied. The owned
Calls.Program is embedded in the existing checked Compilation.memoryCalls
constructor, with actual pushFree proof and public memoryCalls_input/correct.
This is explicitly NOT a claim that Compiler.compile returned that certificate.
Exact target code and actual source/target states pin both sorted result order
and caller-tail preservation. Wrong same-typed result order/destination, private
reference escape, old/unrelated content, composed cost and cursor all have
successful baselines and rejecting observations. withinM.view remains false
for the mutating body, preserving its old noninterference exclusion.

Ready original Work5 preparation continues through an ACTUAL tuple bare-failure
control with valid reached prefix representation. The body reverts before its
syntactically present allocation: exact reached cost0, source bare revert and
actual target revert are proved. No failed State or rollback is reconstructed.
A byte-payload variant retains actual revertWith[7] and is REFUSED by the owned
selector. expand_runR preserves arbitrary original errors, but the target
certificate only covers the actual compiled fragment; panic, exhausted,
diverge and nonempty byte paths are not collapsed into ordinary revert.

Independent finder/skeptic read-only source reviews found no mathematical,
hypothesis, coupling or ownership defect. Finder requested clearer copy-order
prose; that comment is corrected. No Lean/server/builds were used by reviewers.
48 final scoped reports are pinned by a NEW tuple guard. The existing27 and42
fixture guards remain unchanged; new guard growth preserves every earlier new
pin. Empty-tuple selector and zero-parameter copy controls pass. Additive root
import/module-map registration keeps the new core module below elaborators;
all fixture elaboration stays outside core. No producer/reserved source edit,
AST/evaluator, axiom/sorry/native_decide/implemented_by, raised heartbeat/depth,
changed profile/Fml.inTarget/verdict/exclusion/SolKey mapping or goal write.

Remaining ENTIRE original queue (not reset by this checkpoint):

| Item | Scoped progress and actual remaining producer/integration |
|---|---|
| Work1/G37.01 | PARTIAL: all actual primitive Binders arities now have a proved owned direct-call target adapter and real three-result endpoint. Public compiler tuple admission/integration remains with its owner; reference tuple syntax/default allocation is unrepresentable in current Binders; single storage/general recursive runtime frames remain open. |
| Work2/G37.02 | PARTIAL/BLOCKED: primitive result-count induction is not runtime recursion. Existing finite direct-call/unrolling/prefix proofs remain; uncapped intrinsic/runtime target recursive simulation and lowering remain absent/refused. Independent unbounded Source semantics is published and unchanged. |
| Work3/G37.03 | BLOCKED: ordinary direct tuples are not dependent full-signature function-value dispatch. Its actual frame/lowering producer and restricted existing owner remain untouched. |
| Work4/G36.01-.03 | PARTIAL/BLOCKED: ordinary supported blocks/branches and old finite mixed-loop controls remain; general mixed heap/storage push/pop/shrink/allocation loops, break/continue/early-return transport and V14 application remain open. |
| Work5/G38 | PARTIAL/BLOCKED: actual tuple bare failure now consumes the new frame adapter, with unreachable allocation cost0. Arbitrary bytes/panic/return/unwind and actual word-to-Slice byte/frame/journal/whole-world coupling are not discharged. |
| Work6/G39 | PARTIAL/BLOCKED: no new transaction reset/transient/persistent root/world/callback application is implied by memory-only tuple transport. Existing intrinsic and projected laws remain. |
| Backfill A | PARTIAL: new arbitrary primitive result export supplements actual alias/content/renaming/prefix/finite-recursion work. Full reference/signature/runtime coverage and mandatory integration/validation remain. |
| Backfill B | PARTIAL: existing projected/nested byte/finite-loop evidence plus actual tuple bare-failure preparation remain partial; full unwind/rollback/root/world coverage and validation remain. |

For integration, importing this module into MemoryCalls itself would be cyclic
because it consumes MemoryCalls; the reserved owner must arrange an appropriate
shared layer/registration or consume the owned selector from an acyclic compiler
entrypoint. No reserved import/branch is changed here. Global automatic tuple
admission is not silently claimed from the manually checked artifact.

Original full run-lean.sh exit124 at fixed300s and unreached TestSuite/sort remain
FAILED/incomplete; it is not repeated. No-build exit3 is inventory only. Raw docs
exit1 and COMPLETE exact-base no-new comparisons remain separate. All new raw
diagnostic failures and the expected reference-binder type-refusal command are
retained. Final per-file/import/runtime/guard/script/structural/doc outputs,
independent artifact reviews and exact committed bindings are recorded in NEW
continuation9; all nine earlier sealed checkpoint sets are preserved.


Continuation9 actual scoped gates: Lean4.24.0
(797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake5.0.0-src+797c613; dedicated
KeySort successful2jobs, RUNTIME_GATE_PASS only. Final owned/published-control
import closure198jobs passes. All17 owned modules and THREE fixtures pass the
serial20file sweep in92.642s, below its unchanged120s bound. Final tuple selector,
source/target and failure controls pass20.912s; separate exact guards pass48 new,
42 prior mutation and27 prior single-call reports. Altered/missing/duplicated/
error-bearing tuple guard controls reject as intended. Layer/import/orphan/trust
checks pass (17owned,1015reachable,1030sources/246sites, zero findings). All nine
prior seals verify unchanged109/84/91/86/114/90/34/7/7 entries. Only17 verified
stopped continuation9 CIDs were removed, retaining one cache and about14GiB disk
headroom. No OOM, time-bound or proof-budget increase was used this checkpoint;
intermediate syntax/type/proof errors and the intended binder type-refusal keep
their actual exit1 logs. Original full124/300s, no-build3 and raw docs1 failures
remain. Final complete docs comparisons, committed source/cache hashes,
independent source/artifact reviews and original/checkpoint patches/bundle/
checksums are bound in the new continuation9 handoff and evidence.


## Continuation10 — compositional finite direct tuple programs

Starting checkpoint02943b1857bff8fc1dd28702ee6f851697e9d83e retained on the assigned branch, frozen base unchanged. Root-only compileTuple delegated tuple bodies to published Calls.compile, so nested CallRet.rets remained refused. New owned `Solidity/Backend/InternalFlow/TuplePrograms.lean` composes actual public Calls.nil/cons/block/branch/plainStmt/equivalent/memoryReturn and TupleCalls.tupleReturn certificates. It first reuses Calls.compile if admitted. Otherwise its traversal uses the height derived from actual finite embedded call syntax; no caller-supplied call-depth budget or runtime recursion admission is introduced. Calls.Program.sound remains the actual target proof, including reached cost, expanded need, StateRepr, stack, BaseExtends and GrowsAllocator with genuine allocation-capacity premises. No desired simulation equation is supplied as an oracle. Global Compiler.compile/private producers remain unchanged.

Additive Composed controls in `tests/internal-flow/TupleMemoryCalls.lean` execute a primitive triple-result call inside another triple-result body, scoped within block/branch and followed by a real caller suffix. Arguments evaluate the populated outer parameter frame. Inner results [flag1,hi29,lo17] transfer to distinct outer results [flag1,hi30,lo17]; private parameter rebinding and two body allocations remain private. Existing real compiled prefix creates old0=[7,11], aliases to old0, distinct old1=[23,29,31] and scalar42. Nested body changes old0=[19,11], creates private2=[99,101] and private3=[55]. Export preserves aliases [other1,old0,old0] and scalar42; caller use after outer export writes old0=[19,17], scalar1730. Branch/block unwind drops results; outer suffix writes old0=[19,1735], scalar1735. Ordered source entry/body/export/transfer and target body/export/unwind/final snapshots pin all live contexts, lengths/contents/identities, private stale cells, stack77 and sentinel99. Heap sizes [2,2,2,3,3,4,4,4,4], allocator263→268 after prefix, expanded need15 and reached cost5; prefix costs7. StateRepr midpoints and allocation inputs follow real prefix and GrowsAllocator.nextInput, never an assumed desired midpoint. Manual Compiler.Compilation.memoryCalls and its Input/correct consume the actual owned certificate; public admission remains false.

Positive baselines and negatives distinguish same-typed result order, wrong private alias escape, missing/incorrect old writes, unrelated content corruption, wrong frame/cost/cursor and a successful wrong overlapping-copy instruction execution. Nested bare failure precedes inner/outer exports and syntactically present allocations/suffix: allocates=true but reached cost0 and exact THalt.revert/target revert. It does not produce a failed State or prove rollback. Byte-error, single storage-result and callRec controls remain refused; memory/storage tuple categories remain uninhabitable under the actual primitive-only Binders interface. No fabricated reference binder, source/frontend semantics, EVM machine, compilation admission or recursion evaluator was added. Existing withinM rejection remains intact.

Independent read-only finder and skeptic source/control reviews PASS, no findings, no Lean/server/builds/writes. Final diagnostics and committed artifact reviews are recorded in the versioned handoff/evidence after their actual outcomes. Actual source check passed at49.304s under unchanged120s cap; initial constructor/syntax/type/equality diagnostic failures retained. No new axioms/sorry/native_decide/implemented_by or heartbeat/fuel/time increase. Owned exact axiom guard extends original48 pins with37 actual reports, preserving the old sets.

Full original queue accounting remains: Work1/G37.01 PARTIAL (primitive tuple composition now present, single storage/general runtime frames open); Work2/G37.02 PARTIAL (finite direct expansion/intrinsic unrolling only, unbounded target recursive lowering open); Work3/G37.03 BLOCKED (dependent full-signature function-value dispatch/frame producer absent); Work4/G36 PARTIAL (scoped block/branch/suffix consumers, general mixed-loop compiler/break/continue/early-return applications open); Work5/G38 PARTIAL (bare target revert and local exact-byte consumers, byte/frame/journal/world coupling open); Work6/G39 PARTIAL (local transient root/reset consumers, full callback/world target composition open); Backfills A/B both PARTIAL, not parent closure. Published Source and Bridge/ghost-panic components acknowledged read-only; no unmerged imports or reserved repairs. Public tuple admission integration needs its reserved owner to arrange an acyclic shared layer; this owned consumer intentionally does not edit MemoryCalls or Compiler. Single-storage result support remains an implementation obligation, not claimed type-impossible.

Original ./run-lean.sh exit124 at fixed300s remains FAILED/incomplete, TestSuite/sort unreached; unchanged failed gate not repeated. Original no-build exit3 stays readiness inventory only. Raw normal/strict docs exit1 remain failures; complete frozen-base comparison is separately reported. Existing externally audited blocked goal preserved without writes/reset/reactivation. No human semantic choice requested. Fresh continuation10 evidence/artifacts preserve all ten earlier sealed sets; exact committed HEAD, commands, hashes and final review results live in its handoff/metadata.


Continuation10 final scoped evidence: core120jobs PASS and composed fixture PASS48.141s after generic program_revert factoring; actual guarded sets85 (original48 retained plus37). Dedicated runtime PASS: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613, KeySort2jobs. Initial runtime launch125 was a name collision with a preserved older container; uniquely named runtime passes. Aggregate21file sweep at unchanged120s FAIL/exit124 while checking final tuple fixture; all18core and earlier2fixtures completed, final changed fixture has its separate passing output. This aggregate failure is not relabeled a pass or retried unchanged. Direct concrete soundness projection in an attempted proof reuse hit enforced12GiB cap/exit137; its raw output remains. Generic program_revert preserves identical representation/room/capacity/exact-failure premises and proves failure through the existing certificate, avoiding that elaboration explosion. Negative controls reuse positive observations with unchanged statements. No cap, test, proof or time budget increased; no observations removed. Independent finder/skeptic reviewed these repairs PASS without Lean/builds/writes. Full mandatory and scoped aggregate failures remain visible, so validation is incomplete.

Final host/import results: focused import closure199jobs PASS; exact85/42/27 scoped guards PASS, wrong/missing/duplicate/error-report script controls reject exit1 as intended. Layer/import/orphan/trust PASS (18owned modules, 1031sources,246inventoried sites,0findings). Raw normal/strict docs BOTH exit1 and complete outputs equal frozen-base findings byte-for-byte; separate no-new comparison PASS. All ten previous seals109/84/91/86/114/90/34/7/7/7 verify unchanged. One existing source/toolchain-keyed .lake tree retained; cache inventory196sources is inventory only, not full validation. Source/control and final precommit reviews both PASS. Final committed-artifact review and exact head/checksum bindings are exported in the new continuation10 handoff/evidence; aggregate/full failures remain incomplete.


## Continuation11 — bounded cache validation without changing proofs

Starting clean committed checkpoint ea6538289e78bef622bc67df177979144a9dc3e1, same assigned branch/frozen base. The previous raw21file source sweep timed out at120s during its final tuple fixture; that failed gate remains unchanged and is not relabeled. A measured proof-reuse experiment moved identical cost observations and reused their numeric projections. Per-file49.367s did not improve prior48.141s. The exact experiment patch, intermediate failure and profiler49.29s output remain in continuation11 evidence; the original committed fixture was restored byte-for-byte. No delivered Lean statement/proof, observation, premise, profile, refusal or axiom pin changed.

New owned `tests/internal-flow/check-cached-files.sh` asks Lake to validate every owned module target through the existing source/toolchain-keyed .lake tree, explicitly includes all current standalone fixtures' Solidity imports, then directly checks every standalone fixture with lean-j1/tstack131072. It does not modify run-lean.sh/default targets, remove any owned module/fixture, substitute an inventory for a build, duplicate cache trees, or raise the external120s/12GiB/no-swap bounds. It must run through the established serial writer-lock/cgroup wrapper; the shell driver itself is not a standalone resource cap. This is a cached-target gate, not the original raw-source sweep or full repository validation.

Finder identified that version1 built only owned closures while fixtures could have unique imports. Fixed before final validation by adding all five current Solidity fixture imports as actual Lake targets. Final gate PASS81.846s,197jobs and all18owned modules/3fixtures; sampled aggregateRSS2071228KiB, actual enforced cgroup peak recorded in raw JSON/log. Version1 PASS79.105s is preliminary evidence with that limitation, not the final gate. `tests/internal-flow/check-cached-driver.py` uses no Lean: it checks exact owned/import target coverage, all three fixture invocations and fail-fast propagation of injected build61 and fixture62 exits. Initial mock-harness string escaping bug FAIL1 retained and fixed; final controls PASS. Mock output is not proof evidence.

Actual scoped axiom guards85/42/27 PASS with all prior names/sets unchanged; layer/import/orphan/trust PASS. Runtime PASS: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613, KeySort2jobs: RUNTIME_GATE_PASS only. Source/toolchain key remains8e76ebca74339c81dd154cd3a2857764d6d8c345193bacc43c78798db57d8ec5,196module sources plus3fixtures/configuration/toolchain inputs. This repair changes only lane validation scripts/docs and no default source; read-only full-gate readiness inventory is not validation and does not justify repeating unchanged full300s. One existing keyed cache retained. All eleven previous seals verify unchanged.

Separate independent finder/skeptic read-only source reviews performed without Lean/server/builds/writes. Finder's import-refresh finding fixed; final source/artifact review outcomes recorded in the exact-head handoff. Original full ./run-lean.sh exit124 at fixed300s with TestSuite/sort unreached, original no-build3 inventory, strict owned sweep124/120s, concrete projection137/12GiB and initial runtime125 remain raw failures in inherited evidence. Normal/strict docs raw exit1 remain global failures with a separate complete exact-frozen-base no-new-findings comparison. Passing cached scope does not discharge these failed gates.

Original Work1/G37.01 PARTIAL (memory/primitive-tuple finite transport; public admission/storage/general runtime frames open); Work2/G37.02 PARTIAL/BLOCKED (finite syntax/unroll/prefix consumers only; actual unbounded target recursion/lowering remains absent/refused); Work3/G37.03 BLOCKED (dependent full-signature dispatch/frame producer reserved); Work4/G36 PARTIAL/BLOCKED (scoped/finite mixed controls, general mixed-loop/break/continue/early-return compiler proof and V14 application open); Work5/G38 PARTIAL/BLOCKED (bare/local byte/projected-root consumers, actual byte/frame/journal/world coupling open); Work6/G39 PARTIAL/BLOCKED (local/reset/root laws, target callback/self-call/world composition open); Backfills A/B both PARTIAL. No new target runtime, world semantics, preservation assumption, source-owner repair or exclusion introduced. Full lane remains unfinished. Existing goal/objective preserved without reset/recreation/reactivation; no semantic choice requested.


## Continuation12 — actual plain storage-reference result frames

Starting clean98071d3e22fb6291cfaaecdb01198ba7ff72940e, same frozen base/branch. Read actual CallRet.storage and published Premise.sound_callStorage: entry creates an unset storage alias without allocation; expansion declares args, unset result, weakened scoped body, then keeps result while dropping private parameters. Public MemoryCalls.expandCall still refuses storage; MemoryCompile lacks declStorage/rebind clauses. This is an implementation gap, not a type impossibility. New owned StorageFrames/StorageCalls/StoragePrograms modules fill the plain-path finite consumer without editing those reserved files or any Source/runtime definition.

StorageFrames.pushDead/pushAlias/setAlias lift actual published Sim alias laws into full StateRepr, including pointer locals, separated heap/struct/ref-field representations and exact local frame bounds. declareUnset emits no code and keeps result dead; bindPath/declarePath consume actual spath_sim and PathSlot C true from evaluated q, writing Word.slot below frame and preserving allocator. Only spathIn F true paths admit; array-indexed fragile paths and unsupported RHS forms refuse. StorageCalls.expand_runSt/runR prove the published expansion's exact source outcome and actual Out.ext, not a simulation assumption. storageReturn consumes a genuinely compiled expansion plus its computed top-fragment.ok check, extracts actual SRef/slot from reached core.aliases, copies symbolic slot to caller result, preserves caller tail/stack/BaseExtends and exact GrowsAllocator. It does not cast storage slots into memory pointers. StoragePrograms uses public checked constructors plus these proved adapters and actual finite syntax height. Old public Compiler.compile/Calls.compile and existing TuplePrograms selectors remain unchanged. Unset/fragile result refusal is conservative admission, not a new source failure.

New StorageReturnCalls fixture compiles a real populated prefix: box.tag101, box.part.value41/other43, distinct spare.value17/other19, unrelated9, rows.length0; caller scalars x42/y5; old0=[7,11] with two aliases and distinct old1=[23]. Actual evaluated arguments are memoryold0 then seed42. Entry result is none with no allocation. Body binds result to the typed nontrivial box.part path, writes seed+31=73 through it, allocates private2=[99,101] and privately rebinds memory parameter a to it. Exported alias remains rootbox/path[part], old caller memory aliases and scalars preserved. Caller writes84 through returned storage alias, reads it into x84/y5, then writes old0[1]=84; spare/unrelated/box.tag/part.other/old1/private2 remain unchanged. Complete ordered source and target body/export/suffix snapshots include all7 storage root words, actual symbolic result slotroot1 versus spareslotroot3/private numeric pointer261, private shadow cells, stack77/sentinel99, heap sizes[2,2,3,3,3], frame need9, prefixcost5/bodycost3/suffixcost0 and cursor261→264. Canonical intrinsic struct name matches the actual elaborated Inner shape, no representation workaround.

represented derives prefix/call/suffix StateRepr and allocation inputs from real prefix execution and GrowsAllocator.nextInput. actual_program and whole_endpoint couple the actual selected whole-program producer.code to final.st, the true composed heap extension, actual address transport and cost, using generic public endpoint theorems; no desired midpoint is assumed. checked.Input/Compilation.correct consume the same real prefix. Positive baselines and negatives distinguish wrong same-typed spare root, wrong path, slot vs private memory pointer, scalar destination swap, missing/foreign-root mutation, old-memory corruption and wrong cost. Early failure before binding/allocation/export/suffix has exact bare revert, allocates=true but reachedcost0, and actual target revert proved through generic program_revert (no repeated concrete projection OOM). Byte payload[0,7,0] retains source revertWith and target refusal; unset source success with none, fragile array path, callRec and public/old-owned refusal controls remain explicit. No failed State, whole rollback/world, byte-slice conversion, gas/bytecode or frontend lowering claim follows.

Core focused build124jobs PASS; standalone complete fixture PASS31.342s, including whole endpoint and59 actual scoped axiom reports. Initial diagnostics retained: a broad simplifier reached default recursion depth, fixed by explicit typed pointer transport (no limit increase); canonical structural type and Lean identifier/index constructors corrected; no deliverable axiom/sorry/native_decide/implemented_by/heartbeat/fuel/node/test/time change. Separate independent finder/skeptic read-only semantic/control reviews PASS without Lean/server/builds. Final gates and exact-head artifact reviews recorded below/in the handoff.

Original queue remains Work1/G37.01 PARTIAL (plain single-storage result transport now implemented, public admission/fragile/general runtime frames open); Work2/G37.02 PARTIAL/BLOCKED (finite direct expansion only; unbounded target recursion/lowering remains); Work3/G37.03 BLOCKED (dependent function-value dispatch/restricted owner unchanged); Work4/G36 PARTIAL/BLOCKED (finite scoped composition, general mixed-loop/break/continue/early return and V14 final application open); Work5/G38 PARTIAL/BLOCKED (new actual bare failure, byte/frame/journal/world composition open); Work6/G39 PARTIAL/BLOCKED (local/root laws retained, full transaction/callback/world adapters open); both Backfills A/B PARTIAL. This closes a supported local frame case, not the entire parent. Proposed coordinator ledger reconciliation: G37.01 plain finite single-storage return adapter plus G36.01/G38 finite preparation; no generated G03/global status edits. Existing goal/objective preserved without reset/recreation/reactivation; no semantic choice authorized or needed.

Original full ./run-lean.sh exit124 at300s, strict source sweep124/120s, original no-build3 inventory and earlier137/125 failures stay retained; no unchanged failed heavy command repeated. Raw normal/strict docs1 stay global failures, complete frozen-base equality is a separate comparison. All previous seals/caches preserved; final scoped cache gate includes all owned modules/fixture imports and all fixtures under the original120s/12GiB/no-swap cap, never counted as full validation.

Final scoped evidence: cached gate PASS111.805s under unchanged120s,200jobs, all21owned modules/current fixture imports and all4fixtures. Sampled aggregateRSS2601568KiB; enforced cgroup peak2495815680B, memory.max12884901888 and swap.max0. Exact59/85/42/27 guards PASS; changed/missing/duplicate/error-report controls reject; driver coverage/fail-fast controls PASS. Layer/import/orphan/trust PASS1034sources/246inventoried sites/0findings. Raw normal/strict docs BOTH exit1 with COMPLETE exact-frozen-base byte equality, separate no-new comparison PASS. All twelve earlier seals109/84/91/86/114/90/34/7/7/7/7/7 verify unchanged. Cache key5a1f4fd5a2152abb55eb095ef07684f49b08817dec064849f01bc57a6bea28c5 includes199module sources/4fixtures/configuration/toolchain; inventory is not full validation. Independent final source/doc/guard finder/skeptic reviews PASS, no outstanding finding. Exact committed-artifact reviews and head/source/hash bindings are recorded in the fresh continuation12 handoff/evidence. Full original assignment remains partial/blocked and mandatory full validation incomplete.


## Continuation13 — live indexed storage-reference result frames

Starting clean502767b726cbae894d0d4749cf452328df69a242 on the same frozen branch/base. New owned FragileFrames lifts actual Sim.pushFragile/setFragileE into full StateRepr. Declaration/rebind use spathIn false and actual spath_sim path/findLive evidence. FragileCalls.storageReturnFragile extracts the reached slot, path and live reference from core.fragile; it retains .fragile rather than casting it to .ok. Actual source expansion and target slot copy preserve caller tail, memory/ref-field/struct separation, stack, BaseExtends and reached GrowsAllocator. Old StorageFrames/StoragePrograms/public selectors and their refusals remain unchanged. FragilePrograms composes finite actual syntax only, not unbounded recursive target calls.

FragilePop consumes published pop_sim/popCode_run/storeDrop/dropFragile for actual root-array pop. Stale result after pop has actual findLive=false and computed .dead: source return succeeds with the stale reference, while owned target export refuses. No new source failure or shrink exclusion is introduced. A positive pop-then-rebind program selects surviving row0 and compiles/executes successfully.

The complete FragileReturnCalls fixture uses a real core-compiled persistent prefix with two populated same-typed structs and rows.push twice. Actual Sim array bound1 grows to3 from two pushes; this is not falsely treated as a fixed-bound Calls certificate. StoragePrefixFrame proves the actual assign/push heap frame and no-memory-store target consequence. Existing Prog.within rejects push and remains explicitly false; the new proof is an operation consequence, not weakened within/withinM admission. Actual core endpoint plus that frame yields the genuine reached StateRepr and allocator; the subsequent memory prefix and GrowsAllocator.nextInput supply real inputs for the selected whole program. No desired intermediate state or body-liveness oracle is assumed.

Ordered storage snapshots include both seed structs, array length, both rows and unrelated root: prefix[11,13,21,23,2,11,13,21,23,9], body/export[11,13,21,23,2,11,13,73,23,9], final[11,13,21,23,2,11,13,84,23,9]. Evaluated arguments are index1/seed42/old0. Caller old0=[7,11] has two aliases, distinct old1=[23]; private2=[99,101] remains private after parameter rebinding. Returned alias is rows/index1 with the actual symbolic slot, not numeric memory pointer261 or row0. Caller writes84 through it and old0[1], preserves old1 and scalar y1, and exports x84. Complete source/target entry/body/export/suffix observations pin stack77, sentinel99, live/shadow locals, identities and heap sizes0/2/2/3/3/3. Prefix allocation cost5, call cost3, suffix0; cursor256→261→264; expanded/program need10. OOB index2 is actual bare revert before allocation, allocates=true but reached cost0; target also reverts. No lost State/rollback is inferred. Wrong element/root/slot/memory-pointer/lost-alias/cost controls retain positive baselines, plus unset/public/old-selector refusal.

Separate independent read-only finder/skeptic source/control reviews PASS without Lean/server/builds/writes. Only confirmed comment finding (plain versus fragile declaration) corrected. Full fixture and scoped axiom reports pass under unchanged120s/12GiB/no-swap; detailed raw commands/resources and final reviews are in the new continuation13 handoff. Intermediate diagnostics and default-heartbeat concrete-projection failure remain raw evidence; the source proof now uses actual generic frame laws without increasing any budget. No sorry/axiom/native_decide/implemented_by, predicate/profile/source-world change or reserved edit.

Original queue remains Work1/G37.01 PARTIAL (live indexed finite storage results now consumed, general runtime frames/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite direct/unroll only; unbounded target recursion/lowering missing); Work3/G37.03 BLOCKED (full dependent function-value dispatch/reserved producer); Work4/G36 PARTIAL/BLOCKED (finite scoped/root-pop consumers only; general mixed-loop/break/continue/early-return compilation/V14 application open); Work5/G38 PARTIAL/BLOCKED (bare/local bytes/projected roots only; byte/frame/journal/world coupling missing); Work6/G39 PARTIAL/BLOCKED (root/local/reset preparation only; transaction/callback/self-call/world adapters open); Backfills A/B both PARTIAL. No parent closure or desired preservation assumption. Proposed coordinator ledger reconciliation: G37.01 finite live indexed storage result plus G36.01 local pop/rebind preparation; no generated/global ledger edits. Existing blocked goal preserved; questions=[] (no semantic choice necessary).

Original full run-lean124/300s and raw source sweep124/120s remain FAILED, TestSuite/sort unreached; no unchanged failed heavy gate repeated. Raw normal/strict docs1 remain failures with a separate complete frozen-base comparison. Prior cached21-module/4-fixture111.805s pass is historical, not validation of the expanded26-module/5-fixture set. New focused closure and per-fixture checks are reported with their actual bounds and do not pass the full or raw-source gate. All13 prior seals/caches preserved.

Final coverage adds an actual indexed declaration selected through FragilePrograms: reached row1 alias/slot, caller tail, .fragile, unchanged cursor261 and cost0. Wrong scalar destination, missing old-object write and wrong cursor controls retain successful baselines. Independent finder/skeptic extension reviews PASS with no finding. Final complete new fixture PASS33.344s with68 actual scoped axiom reports, sampledRSS1820336KiB/cgrouppeak1519353856B, hard cap12884901888/swap0. All four retained fixtures pass serially14.036/19.204/47.517/29.693s, with exact27/42/85/59guards unchanged; new68guard and injected wrong/missing/duplicate/error reports pass/reject as intended. Full focused closure of26owned modules and all actual fixture imports PASS205jobs (actual target list/log retained); source/toolchain-keyed inventory is not a build certificate. Runtime Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS: RUNTIME_GATE_PASS only. Layer/import/orphan/trust PASS1039sources/246sites/0findings. Raw normal/strict docs BOTH1 with separate COMPLETE exact-base byte equality. Historical cached aggregate and full/raw-source failures are not relabeled by per-file success; expanded aggregate/full gates remain incomplete.

All13 prior seals verify unchanged. Only25 recorded stopped continuation13 CIDs removed after checking exact identity/state; raw metadata/logs preserved, disk restored to14GiB free and .lake2GiB retained. Missing python in container caused a new focused-launch127; actual installed-tool invocation subsequently passes, both raw outputs retained. Final exact-head handoff includes every attempted command/outcome, headline premises, producer/source hashes and queue dependency map; original and checkpoint patches/bundle/new checksums are separate from all earlier seals. No goal write/reset/reactivation, push/merge/PR or reserved edit.


## Continuation14 — expanded checked-fixture cache and late failure

Starting clean dbd40f1c3a0af2d379f96ee8993fdc4696f72abe, same frozen base/branch and blocked goal. Investigated prior timing/profiler and speed history: repeated concrete source checking of five fixtures exceeds120s; the earlier cost-projection refactor did not improve49s tuple elaboration. No broader/slower proof refactor, heartbeat/fuel/node increase or observation removal. Existing actual fixture sources/68/59/85/42/27guards remain, with four additional late-failure theorems checked separately.

Owned fixture-cache.mjs extends the single existing Lake tree to complete kernel-checked fixture modules. Explicit cold preparation uses actual lean-j1/tstack131072/-o, verifies all actual reports and records the produced object hash. The key binds the fixture source, complete transitive Solidity sources AND actual dependency objects, guard/registry/script/configuration hashes and the COMPLETE actual toolchain (all module objects, IR, compiler, Lake and shared runtime files). Before/after equality detects changes during checking. No cache/build/toolchain tree is exported. The aggregate refreshes every owned target and actual fixture import with Lake, rejects missing/stale/altered fixtures, then actually imports EACH of the five matching proof modules and prints/checks EVERY existing pinned axiom set. This is checked compiled-module reuse like the core cache, not an inventory or mock proof. Missing/stale caches fail closed and require a new bounded cold check; cold preparation is separate, never claimed to fit the aggregate bound. Full/raw-source gates are unchanged.

Independent finder/skeptic found an initial registry extraction omitted37tuple updates and shallow root-module toolchain hashes missed descendants/runtime. Both fixed before cold-all: complete85pins and full-toolchain contents now bound. A suspected newline problem was retracted after raw byte counts, successful real import, actual28line harness and executable sentinel controls. Initial parser comment false dependency and runtime-library name assertion failures retained. Source late failure initially lacked Decidable State equality; existing exact error_tag Boolean projection fixes it without semantic or budget changes.

check-cached-driver.py compares the complete registry to all existing guard definitions, verifies the exact26owned/actual-import/five-fixture target list and fail-fast at build AND EACH fixture position, without Lean. check-fixture-cache.mjs verifies missing/key/source-binding/object tamper rejection before Lean, restores task-owned manifest/object in finally, exercises the actual report parser against missing/duplicate/wrong/error reports and executes the mock sentinel itself. These controls do not prove semantic theorems. Actual five cold preparations PASS21.908/41.845/25.103/54.567/36.699s (published/fragile/mutating/tuple/storage); unchanged individual120s cap throughout. Actual aggregate run ONCE after repair PASS78.599s/120s:205job Lake closure, all26owned+actual imports and all5real fixture imports, exact68/59/85/42/27reports. Sampled aggregateRSS1137180KiB/cgrouppeak1042268160B, enforced memory.max12884901888/swap.max0, serial Lean-j1/LEAN_NUM_THREADS=1 with writer/compiler locks. This is a warm source/dependency/toolchain-keyed cached gate, not cold source or full validation.

Next original Work5/G38 regression: FragileReturnCalls.lateBody actually executes the existing populated body in a block (storage row1.value73 and private3-cell allocation/rebind), then bare revert before export and an unreachable newArr3. late_source proves exact THalt.revert through actual argument/body execution; late_cost pins allocates=true/reachedcost3/need10. late_target derives actual prefix representation and capacity with GrowsAllocator.nextInput, then existing program_revert proves actual target halt. late_no_skipped_cost rejects0 and7, distinguishing reached allocation from none or unreachable allocation. The pre-halt body's complete ordered observations remain earlier positive baselines; no failed State/live-memory reconstruction, successful export or rollback is inferred. All four extra actual axiom sets pass a separate exact guard; the old68guard remains byte-identical. No duplicate evaluator/AST/world, new axiom/sorry/native_decide/implemented_by or reserved edit.

Original full run-lean124/300s and raw-source124/120s remain FAILED, TestSuite/sort unreached; no unchanged failed heavy retry. Raw normal/strict docs1 remain failures with separately compared COMPLETE exact-frozen-base findings. Prior seals/caches/raw outputs preserved. Runtime Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS (RUNTIME_GATE_PASS only). Final structural/guard/doc/source/artifact reviews and exact-head hashes are recorded in the fresh continuation14 handoff.

Work1/G37.01 remains PARTIAL (finite plain/fragile/memory/primitive tuple consumers, general runtime frames/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite direct/unroll only, unbounded target call/lowering absent); Work3/G37.03 BLOCKED (dependent dispatch/restricted owner); Work4/G36 PARTIAL/BLOCKED (finite scopes/root-pop/actual intrinsic mixed-loop controls only, general loop/break/continue/early-return compiler/V14 application open); Work5/G38 PARTIAL/BLOCKED (new actual late bare target failure, full byte/frame/journal/world relation open); Work6/G39 PARTIAL/BLOCKED (root/reset preparation only, full transaction/self-call/callback/world producer missing); Backfills A/B both PARTIAL. Actual Failure.Local.execute still accepts an explicit byte-machine Journal; Evm.Machine word/slot memory is not identified with it, and TRes.error supplies no successful State. No target transient field, unbounded recursion or desired simulation premise invented. Proposed coordinator ledger addition is finite G38 late-call reached-cost preparation; no global/generated ledger changes or exclusion request. Existing blocked goal unchanged; questions=[].


## Continuation15 — published direct/scoped memory-loop consumers

Starting clean115e69660123e8d8a46ff4170f272815a152bb62 on the frozen branch/base. Fresh ls-remote/fetch confirmed origin/master exactly5f6a75b6038371a3917dbe08b660d5f2d1207c58 and reachability before consumption. Authorized isolated merge758383a8d619b94abd2c716af48da5be2e1ceceb preserves all47prior owned files. Compiler conflict resolved BYTE-EXACT published file, retaining memoryCalls, memoryLoops, memoryLoopScopes and every theorem/selector arm; module-map retains every incoming line plus26owned rows. Compiler/TrustAudit match publication; no reserved producer repair, unmerged import, push/merge into master or goal reset/reactivation. Separate independent read-only finder/skeptic merge reviews PASS.

New owned PublishedLoops consumes actual Loops.ProgCert.correct and LoopScopes.ProgCert.correct. Successful endpoints retain actual source Out, relational Cost, reached StateRepr, evaluation-stack tail, BaseExtends and GrowsAllocator. Exact bare revert and divergence-to-abstract-fault remain separate. block_endpoint derives local unwind through StateRepr.drop and exact env drop. after_allocating_prefix derives the actual target midpoint from Calls.Program, transfers real capacity through GrowsAllocator.nextInput and a genuine source Demand bound, then composes Cost/address/allocator/stack facts. Loop Room/Cost are NEVER replaced by legacy allocationCost; only the separately finite call prefix uses its own producer cost. old_alias transports typed old addresses without Heap.Keeps for mutated contents. No desired-simulation field or oracle.

New PublishedMemoryLoops fixture executes a real allocating prefix: persistent count9, marker42, old0=[7,11] with two aliases, cursor128→131 and cost3. A selected branch/block contains an actual two-turn loop mutating that old aliased array to[3,4] and persistent count11; its private index i0→1→2 is dropped at scope exit. Source exact horizons0/1/2/3 preserve complete ordered array/root/index observations and use existing loop_prefix_add at split1+2. A successful runF3 witness is lifted by published runF_approx to the ACTUAL unbounded run, not an admission cutoff. Caller suffix reads same[1]=4. whole_endpoint proves actual pre+scope+suffix target run, StateRepr, original stack77, target scalar cell4=4, BaseExtends, exact composed GrowsAllocator3 and derived cursor131. Old typed alias addresses are tied to the reached prefix map, not supplied as a desired midpoint. direct_reached independently instantiates the direct-loop success producer after a real prepared local.

The fixture reuses public published example proofs to infer their actual private programs and machines without accessing/recreating those declarations. Eight kernel proofs retain actual source array result4/record result3 for direct/scoped legacy/viaIR variants. Complete supplied target local-cell lists remain executable controls: arrays[131,128,128,2,4,2,3,4,99], legacy records[130,128,128,128,3,99], viaIR records[130,0,5,128,3,99]. They are not normalized together or claimed as kernel equalities. Main raw shadow/cell/root/cursor vectors are likewise bounded compiled-evaluation controls; mathematical typed endpoints, live result4/cursor131 and source values are separate kernel proofs. Mathematical spin proves every source prefix keeps running and then actual target abstract fault; no infinite #eval or EVM gas claim. Wrong tail/alias/cursor/selected branch and nested-body/withinM refusals retain successful baselines; .view withinM remains false for the actual old-alias writer.

Next original combination investigation: ordinary memory-return prefix allocates private default0 then returned1, followed by the same scoped loop. Three additional kernel SOURCE proofs pin actual call/run, both aliases1/scalar42, default object[0], returned[2,7,11]→[2,3,4], heap2 and count11. Two executable target/cost controls pin stack77/cursor132/returned pointer129/cost4 versus3. The stronger concrete combined TARGET StateRepr/allocator theorem remains RESOURCE-BLOCKED: three distinct full/isolated/opaque-state attempts exited137 at enforced12GiB. Prefix-only opaque source check passes2.515s. Failed target endpoint/cost projections are not delivered as proofs; exact source attempts/probes and raw failures are preserved in evidence. No increased cap/heartbeat, hidden stop, new premise or theorem weakening. This is not absence of the now-published loop producer.

Actual scoped gates: new fixture PASS24.095s before additional source controls; final complete source PASS25.508s, fresh final loop proof-cache preparation PASS31.277s.43new exact registered kernel reports plus7separately guarded reports (3new source-combination and4retained late-failure) pass; old68/59/85/42/27guards unchanged. All27owned/current-import closure PASS51.602s/223jobs. Complete six-fixture warm aggregate RUN ONCE PASS94.197s/120s,324registered reports, sampledRSS1155356KiB/cgrouppeak1101545472B, hard memory.max12884901888/swap.max0. All six source/dependency/toolchain/object provenances freshly prepared under original per-file120s bounds after publication and source changes. Runtime controls execute during cold checking; warm import authenticates those same checked modules and repeats exact axiom reports. Inventory/mocks are not proof/full-validation certificates. Single .lake tree retained.

New-publication cold preparation hit120s in three staged attempts; raw exits124 and partial progress retained, then distinct staged targets/current source checks pass. Original full run-lean124/300s and raw-source124/120s remain FAILED, TestSuite/sort unreached, unchanged failed commands not repeated. Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS (RUNTIME_GATE_PASS only). Raw normal/strict docs remain reported independently: complete frozen-base findings and exact-publication findings are both retained; incoming inline-assembly path debt is not authority to edit reserved documents/records. Exact comparisons, structural/guard/resource/review evidence and final head are in the new continuation15 handoff. All prior seals preserved.

Queue: Work1/G37.01 PARTIAL (finite call/ref frames, concrete call→loop target composition resource obligation remains); Work2/G37.02 PARTIAL/BLOCKED (finite direct/unroll consumers only, unbounded target recursive frames/lowering missing); Work3/G37.03 BLOCKED (dependent full-signature dispatch/reserved owner); Work4/G36 PARTIAL (specific memory-loop producer gap CLEAR and actual direct/scoped consumers now proved; finite-body restrictions, storage push/pop/general mutation-loop compiler combination, nested loops/break/continue/early-return and V14 effectful application remain open); Work5/G38 PARTIAL/BLOCKED (exact bare/local bytes/preparation, full byte/frame/journal/world coupling missing); Work6/G39 PARTIAL/BLOCKED (local root/reset laws, full target transient/transaction/self-call/callback/world producer missing); Backfills A/B both PARTIAL. No source/target state, profile, refusal, SolKey mapping or Fml.inTarget changed. Proposed coordinator reconciliation only G36.01/.02/.03 finite supported consumer/interface evidence, not parent closure; no global/generated ledger edit. Existing blocked goal untouched, no semantic choice requested.

Final host checks PASS: layers/import/orphans/trust (1113sources,258inventoried sites,0findings), exact six-fixture driver/fail-fast coverage and fail-closed cache/parser controls9.282s. Complete current normal/strict documentation logs both exit1 and equal exact-publication logs byte-for-byte (zero owned additions). They differ from the frozen baseline:48missing references versus46, including incoming reserved inline-assembly path debt; no reserved repair or global docs pass claimed.15previous seals verify unchanged. Independent finder/skeptic final source/doc/guard reviews PASS with no findings; exact committed-artifact reviews and all raw command/source/provenance hashes are recorded in the fresh handoff.


## Continuation16 — checked call-return-to-loop target endpoint

Resumed clean98b30a35138861d64556baa34cc993042140bced on the original frozen branch/base; the previously consumed published5f6a75b6038371a3917dbe08b660d5f2d1207c58 is unchanged. All16previous seals and the original blocked goal remain untouched. The existing PublishedMemoryLoops fixture and all reserved producers remain byte-identical. No merge, push, new goal, semantic/profile/predicate change or increased budget.

The four fresh one-proof imported diagnostics isolate actual call-prefix cost, call-prefix frame, loop frame and loop nonallocation: all PASS1.993/1.924/1.946/1.988s, below900MiB sampled aggregateRSS. None alone reaches the cap. A reached-only target theorem using the imported facts passes1.987s. This does not identify a unique internal normalization site in the old137failures; it establishes a different successful checked proof decomposition. The new tests/internal-flow/CallLoopFacts.lean proves the concrete checked certificate fields, typed alias/content observations and actual initial capacity, then instantiates PublishedLoops.after_allocating_prefix. No midpoint or desired simulation is supplied. The actual allocating call/source/loop definitions are imported unchanged, not redefined or replaced.

The new tests/internal-flow/CallLoopEndpoint.lean seals exact growth separately, then proves call_loop_endpoint with the SAME full original target claim: actual prefix and concatenated target execution, reached relational loopCost0, StateRepr, stack tail, totalGrowsAllocator4, both aliases to returned object1 at its reached prefix address, and cursor132. Explicit dependent alias state arguments avoid unnecessary inference through the opaque reached states. The first original-claim check passes2.425s/below900MiB. call_complete_endpoint strengthens this to a kernel-proved ordered target vector: both aliases, marker42, private object0 length0, returned object1 length2/content[3,4], persistent count11 and cursor132, with stack77 and actual reached allocator/representation. Content/root/local equations come from the actual StateRepr and independently checked source observations. Heap separation proves that the returned alias cannot name private default0. Wrong old content7, count9, cursor131, stack78 and prefix cost3 are rejected on the SAME successful target witness. This is actual permitted old-alias mutation, not Heap.Keeps or a weakened withinM predicate.

The concrete call-to-loop target resource obligation is now discharged; the three historical continuation15exit137attempts and their raw probes remain FAILED evidence, not erased or relabelled. Existing source and executable numeric vectors remain independently useful controls, but they are no longer the only evidence for this concrete target endpoint. This finite embedded-body composition does not prove uncapped recursive target execution. Reached loop Room/Cost remain the published relational interfaces; legacy allocationCost is used only by its actual separately finite producer.

A further ready original Work5/G38 regression proves actual false selected-branch bare failure after that same allocating call prefix. call_rejected_source retains THalt.revert, and call_rejected_target derives the reached representation from the real prefix, checks the actual scoped frame/nonallocating Room and proves target .revert. call_rejected_not_fault distinguishes it from abstract fault. No failed State, return payload, panic code, byte-memory identification, catch or world rollback is inferred.

Fixture reuse now admits only registered lane fixture imports, binding transitive sources, objects, guard files and prior checked dependency manifests. Every imported manifest self-key/object and complete source/toolchain/config input binding must match current inputs before reuse. The two-level endpoint→facts→PublishedMemoryLoops chain is authenticated; a matching arbitrary source/object pair alone is insufficient. New no-Lean controls reject missing provenance, changed dependency object, changed transitive source, changed provenance binding and unregistered import before invoking Lean, restore every task-owned mutation, and test the rejection sentinel itself. Existing cache/parser controls remain intact. Complete driver controls cover all27owned/current imports and all8fixtures, with failure at build and EACH fixture position. All prior six guard maps are unchanged;17facts+7endpoint reports are additive.

Actual runtime Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs PASS (RUNTIME_GATE_PASS only). Focused closure PASS1.468s/223jobs. All8fixtures were freshly kernel-checked/prepared after the driver/registry change under their unchanged individual120s bounds: published calls19.172s, mutating calls27.693s, tuple52.826s, storage35.974s, fragile40.890s, original loops30.661s, facts11.938s and endpoint9.760s. The expanded actual aggregate ran ONCE and PASS113.746s/120s:27owned modules/all actual imports/8real fixture imports/348exact registered reports. SampledRSS1140312KiB/cgrouppeak1058267136B; enforced memory.max12884901888/swap.max0, serial Lean-j1/LEAN_NUM_THREADS=1, writer/compiler locks. Separate actual7report audit PASS2.982s; existing cache controls PASS9.259s and dependency controls PASS12.415s without Lean. The single keyed Lake tree is reused; inventory and mock controls are not semantic/full-validation evidence.

Original full run-lean124/300s and raw-source124/120s remain FAILED, TestSuite/sort unreached. Neither unchanged failed command was repeated. Raw normal/strict docs remain exit1: COMPLETE current findings match exact publication48missing and differ from frozen46 by the two incoming reserved inline-assembly path findings. No reserved repair or global docs pass claimed. Source diagnostics from incremental type annotation fixes are retained. Scoped guards/structural/doc comparisons and exact source/artifact reviews are recorded in the continuation16 handoff; no new axiom/sorry/native_decide/implemented_by or heartbeat/fuel/node/test/time cap changes.

Full queue remains unfinished: Work1/G37.01 PARTIAL (this concrete call→loop target composition proved, general runtime frames/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite direct/unroll only, unbounded recursive target/lowering missing); Work3/G37.03 BLOCKED (dependent full-signature dispatch/reserved owner); Work4/G36 PARTIAL (supported actual direct/scoped loops and call-prefix composition, general mixed push/pop/shrink/iteration-allocation applications and nested loops/break/continue/early return/V14 application open); Work5/G38 PARTIAL/BLOCKED (new concrete target bare failure, full byte/frame/journal/world relation missing); Work6/G39 PARTIAL/BLOCKED (local root/reset laws, full target transient/transaction/self-call/callback producer missing); BackfillsA/B both PARTIAL. The published loop producer gap stays CLEAR; unsupported loop bodies still require actual finite Memory.ProgFrag certificates and a stable fragment. Owned Calls.Statement certificates do not manufacture a Memory.ProgFrag constructor. No general Heap.Keeps, target transient field, world semantics or missing producer theorem assumed. Proposed coordinator-only reconciliation is finite G37.01/G36.01/.02 composition and G38 bare-failure preparation, not parent closure or generated-ledger edit. No independent-work-exhaustion or full assignment completion claim; questions=[].

Final independent read-only finder/skeptic source/control/document reviews PASS with no findings, without Lean/server/builds. Host structural/import/orphan/trust checks PASS (1113sources/258inventoried sites/0findings); all8actual scoped guard checks and missing/duplicate/wrong/error report countercontrols PASS. Complete committed-artifact reviews, exact head hashes and prior-seal preservation are recorded in the new handoff.


## Continuation17 — allocating prefixes before scoped failure/divergence

Resumed clean5bb190d996eec4fff1603a8e97ba2ed5ebbe2437 on the original frozen branch/base, with previously consumed published5f6a75b6038371a3917dbe08b660d5f2d1207c58 unchanged. All17earlier seals, caches and raw failures are preserved. No goal writes/reset/reactivation, reserved producer edits, new integration, push/master merge/PR or profile/observation/predicate/budget change. Every prior theorem body and all8prior fixture/guard maps remain intact.

PublishedLoops now adds allocating_prefix_room, after_allocating_prefix_revert and after_allocating_prefix_diverge. Their genuine capacity is before.cost sigma + budget, with actual prefix execution/frame bounds and an actual source Demand bound. The real prefix endpoint supplies the reached machine/base/StateRepr/stack/BaseExtends/GrowsAllocator; nextInput transfers the remaining capacity to relational Room. The existing scoped_revert/scoped_diverge then prove exact bare revert versus divergence-to-abstract-fault. No failed suffix State, rollback, byte-memory or world relation is constructed. The old successful adapter is unchanged. Generic laws alone are preparation; the new closed fixture discharges their premises.

New tests/internal-flow/AllocatingLoopFacts.lean and tests/internal-flow/AllocatingLoopHalts.lean import the unchanged C16 allocating call prefix and its returned aliases. The prefix cost4/cursor132 leaves private default0 empty, returned object1=[7,11], both caller aliases1, scalar42 and persistentcount9. The new actual loop body allocates a two-element array and then explicitly reverts. Published checked Memory.compileProg and Loops/LoopScopes constructors provide its certificate. Its reached Demand3 is inhabited, all demand is bounded by3, and the real initial capacity4+3=7 derives the closed actual target revert. The body has no completed turn; no successful suffix Cost or failed State is invented. A zero budget is refuted. At full cursor, actual reached Room/Input3 refuses while skipped Room0 holds even though BOTH syntactic certificates allocate; this is premise refusal, not a runtime halt classification.

A distinct actual allocating suffix allocates3 then enters a nonallocating constant-true nil-body loop. Source all-prefix running proves mathematical divergence; genuine reached Demand3 includes the finite allocation. The new divergence adapter gives actual target abstract fault and rejects bare revert. No infinite evaluation or gas/bytecode adequacy claim. Published runF uses a .diverge horizon MARKER, not THalt.exhausted: a terminating skipped loop has the same runF0marker, while skipped_source proves its actual success. Actual assumeFalse exhaustion remains a separate intrinsic source control and is not newly admitted by the compiler. The initial incorrect marker expectation and incremental type diagnostics remain raw failures.

The successful allocation prefix BEFORE failure is also a closed kernel endpoint: actual call code and actual head-allocation code execute, StateRepr and BaseExtends reach heap3 with totalGrowsAllocator7/stack77/cursor135. Complete ordered source/target observations pin private0=[0], returned1=[2,7,11], fresh2=[2,0,0], both old aliases1, fresh pointer2, scalar42 and persistentcount9. Target body_code is derived from actual checked compilation construction equations and equals allocation-code++revert; its actual body execution therefore reverts after that observed prefix. This is a successful pre-failure state, not recovery from TRes.error or a completed successful allocating loop. Wrong same-typed fresh/old alias, omitted allocation/cursor132 and premature root reset are rejected on the same successful witness. A separate bounded numeric vector includes the protected sentinel99. Old C16 [3,4]/count11 observations are unchanged; they belong to its different successful loop.

Two new combined/dependent proof attempts exited137 at enforced12GiB (31.505/22.972s), retained with raw probes. Controls-only4.102s and allocation-facts3.043s isolate passing parts. An imported allocation_only boundary, explicit source types and shallow cost rewrites prove the SAME successful prefix endpoint1.956s; final Facts PASS10.305s and complete closed endpoints/controls PASS5.111s. No unique internal normalization site is claimed. No new axiom/sorry/native_decide/implemented_by, heartbeat/fuel/node/time increase or desired-simulation premise. Exact new guards40+5 are additive to the unchanged348reports; separate7report audit remains.

Measured old key-only profiling reads2.692GB/11922files in2.711s, including11574toolchain entries, twice per fixture. The reviewed owned batch repair shares ONLY a complete freshly content-hashed toolchain map, independently fully rehashed after the serial batch. Per-fixture before/after source/dependency/object/guard/provenance self-key checks and actual Lean import/report guards remain; standalone prepare/check still fully hash per file. Batch input must contain EVERY registered fixture once in sorted order. Production visitor fail-fast at EACH position, full-map changed/missing/extra checks, malformed actual batch lists and all existing no-Lean cache/parser/tamper controls pass. No mtime/version shortcut, persistent arbitrary shared hash or skipped fixture. Per-file batch evidence requires the final matching complete-toolchain batch record.

Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS (RUNTIME_GATE_PASS only); focused closure PASS1.450s/223jobs. Every10fixture source was freshly kernel-checked/prepared under the unchanged individual120s caps. Expanded actual aggregate ran ONCE and PASS91.436s/120s: all27owned modules/all actual imports/10real fixture imports/393exact reports, with complete before/after toolchain digest equality. Sampled aggregateRSS1187344KiB/cgrouppeak1062998016B; hard memory.max12884901888/swap.max0, serial Lean-j1/LEAN_NUM_THREADS1 and writer/compiler locks. Separate7actual axiom audit PASS2.997s. Existing no-Lean cache/parser controls PASS9.271s; dependency controls PASS11.885s. One existing source/toolchain-keyed Lake tree retained. Inventory/mocks are not semantic/full-gate evidence.

Full original run-lean124/300s and raw-source124/120s remain FAILED, TestSuite/sort unreached; neither unchanged failed command was repeated. Prior no-build3 remains inventory only. Raw normal/strict docs1 remain failures; complete current publication48versus frozen46findings comparisons are retained separately, including the two incoming reserved inline-assembly path findings. No reserved historical/vendor repair. Exact source/guard/structural/doc/resource/review/command evidence and final head are in the new handoff.

Full queue: Work1/G37.01 PARTIAL (finite frame/prefix consumers, general runtime/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite direct/unroll only, unbounded recursive target/source-lowering missing); Work3/G37.03 BLOCKED (dependent full-signature dispatch/reserved owner); Work4/G36 PARTIAL (new real reached allocating failure/divergence and successful allocation-prefix observations, general mixed shrink/push/pop/iteration-allocation applications and successful allocating-loop completion, nested loops/break/continue/early return/V14 remain); Work5/G38 PARTIAL/BLOCKED (new actual bare target failure, full byte/frame/journal/world coupling missing); Work6/G39 PARTIAL/BLOCKED (local root/reset laws only, target transient/transaction/self-call/callback producer missing); BackfillsA/B PARTIAL. Published allocation/loop producers EXIST and were consumed; a separate successful allocating-loop consumer remains ready work, not an absent-producer claim. Generic loop bodies still require actual Memory.ProgFrag and stable fragment; owned Calls.Statement does not supply its missing constructors. Failure.Local.execute needs an explicit byte-machine Journal, and Evm.Machine has no independent target transient/world field. No hidden premises, exclusions or parent closure; no claim independent work exhausted. Proposed coordinator-only reconciliation: finite G36/G37 prefix composition and G38 bare-failure preparation; no generated ledger/status edit. Existing blocked goal untouched; questions=[].

Final independent read-only finder/skeptic source/control/document reviews PASS with no findings, without Lean/server/builds. Host structural/import/orphan/trust checks PASS (1113sources/258inventoried sites/0findings), all10actual scoped guards and missing/duplicate/wrong/error report controls PASS. Raw normal/strict docs both exit1 and equal the COMPLETE publication output, not the frozen output. Exact committed-artifact reviews/head/source hashes and all17prior-seal checks are recorded in the new handoff.


## Continuation18 — completed successful allocating loop and caller alias use

Resumed clean9b9dc5789a659f20f6694e6f449a3e8d671524be on the original frozen branch/base. The same published5f6a75b6038371a3917dbe08b660d5f2d1207c58 producers and SAME callBefore/callMid are consumed read only. Original blocked goal, all previous checkpoints/seals, old fixtures/guards, judgments, observations, predicates and budgets remain unchanged; no publication, reserved edit or new goal.

New tests/internal-flow/SuccessfulLoopFacts.lean constructs an actual typed body which allocates a two-element uint array, resets the caller marker to0, then drops its private local at the loop boundary. Memory.compileProg and the published Loops/LoopScopes checked constructors supply the actual certificate. The guard reads the actual caller marker; body execution proves it false after one turn. Source runF2 success is lifted by the published approximation law to actual unbounded Prog.run success, not an admission cutoff. Every actual relational Demand is bounded by3, reached Demand3 is inhabited, and successful relational Cost is exactly3. The latter eliminates the EXISTING dependent Cost evidence through small one-layer views and excludes zero turns using actual heap growth2→3. These views are not new execution/cost semantics. Legacy finite allocationCost is used only for the actual finite body producer, never substituted for loop Demand/Room/Cost.

SuccessfulLoopEndpoint.reached discharges PublishedLoops.after_allocating_prefix with the actual source run, initial StateRepr, exact finite call cost4, genuine initial AllocationInput(4+3), actual frame bounds and source Demand bound. No desired midpoint, result representation or simulation is supplied. endpoint and complete_endpoint prove actual prefix/suffix/concatenated Evm.run success, actual Cost3, final StateRepr, BaseExtends from reached call heap, total GrowsAllocator7, stack77 and cursor135. The loop need is exactly4; a frame reserving only final caller locals is refuted.

Complete ordered kernel observations are NEW for this successful program: caller aliases both name returned object1 at its reached prefix address; marker0; private default0=[0]; returned1=[2,7,11]; fresh2=[2,0,0]; persistentcount9; cursor135; stack77. Local unwind removes the fresh local from the typed caller context, while its allocated object remains in the heap. It does not assert clearing a dead physical local cell. These are not C16's different [3,4]/count11 or C17's before-failure marker42 observations. Those old fixtures remain byte-identical.

Further original Work1/4 and BackfillA/B combination work is also discharged: actual checked caller code writes99 to returned[1], reads it through the OTHER old alias into a new scalar, and runs after the completed loop. next_use proves the actual concatenated target success, reached StateRepr, both alias effects, resultcell4=99, fresh[0]=0, unchanged total growth7/cursor135 and stack77. Source use_values pins every represented object and caller tail: old contents[2,7,99], fresh[2,0,0], private[0], both alias identities, marker0/count9 and result99. Bounded numeric vectors also observe sentinel99 and dead-slot reuse; they supplement kernel proofs, not replace them.

Same-success-witness negatives reject fresh/old alias confusion, omitted allocation/growth4/cursor132, wrong old element3, root11 and marker42; success rejects revert/fault. Actual reached Demand refutes budget0 and Room at full cursor, while the syntactically allocating but skipped variant has Demand0 and Room at that cursor. These are capacity PREMISE controls, not runtime rejection claims. Existing stale/export, OOB/pop-rebind, old-alias-write/withinM and failure-class controls are retained.

Published Prog.withinM deliberately refuses loop syntax: loop_guard_refused proves false. allocation_body_within proves the actual allocation/reset body admitted. scoped_body_frame uses actual body_run and the existing run_frameM/withEnv law to retain TGFrameM and Heap.Keeps through that body's local drop. It names that precise scoped body state, not a presumed equality to the independently packaged finalOut. The attempted whole-loop-guard and direct packaging proofs failed and remain raw failures. Complete finalOut content/target observations are independently proved. No Heap.Keeps claim covers the later alias-writing caller.

Final source checks PASS9.779s/6.710s under the unchanged per-file120s limits. New exact guards40facts+6endpoint reports are additive to the unchanged393; all sets contain only actual standard propext/Classical.choice/Quot.sound subsets. Every12fixture source was freshly prepared with complete source/dependency/object/guard/provenance/toolchain binding. Complete aggregate PASS103.321s/120s:27owned modules/all actual imports/12fixtures/439reports, full11575-entry toolchain map rehashed before AND after with identical digest617fd68210c0b46750ab92f863878665875839568f23d99320f79053956360f1. Cgrouppeak1060208640B/sampled aggregateRSS1188400KiB, hard12884901888B/no swap, serial explicit Lean-j1/LEAN_NUM_THREADS1 and writer/compiler locks. No fixture/report/guard/import removal or cache deletion. Runtime Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS0.940s; RUNTIME_GATE_PASS only. Focused closure PASS0.891s/223jobs; separate7report audit PASS3.763s; unchanged cache/parser controls10.059s and transitive dependency controls13.365s. Actual expanded driver/fail-fast/batch-coverage, all12exact guards and48missing/duplicate/wrong/error controls plus layer/import/orphan/trust checks PASS; trust1113sources/258sites/0findings.

A distinct investigated original mandatory-gate preparation found355missing top-level cached objects (inventory ONLY). Required RecursiveStorage/Termination/LexMetrics preparation PASS16.019s/40jobs. A separate actual77-target required semantics/calculus preparation timed out124/120s after further checked prerequisites (last completed RuleKit); raw command/log/resource output is retained. This is a FAILED preparation, not the full gate, and no repeat or increased budget follows. No unique internal cause, inherited waiver or base/full success is inferred. Original full ./run-lean.sh124/300s, raw-source124/120s and no-build3 inventory remain retained; original TestSuite/sort were not reached. No unchanged failed full/raw operation was repeated.

Normal/strict documentation raw1 remain failures. COMPLETE current outputs are compared separately with publication48findings and frozen46findings: two incoming reserved inline-assembly paths remain, no new owned paths and no global/frozen zero-addition pass. Pending reserved-owner path request is not permission to edit those records.

Full queue remains unfinished: Work1/G37.01 PARTIAL (finite calls/tuple/storage/fragile/reference and now successful allocating suffix/caller-use consumers; general runtime/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite unroll/direct expansion, no unbounded recursive target/source lowering); Work3/G37.03 BLOCKED (dependent dispatch/reserved function-ref-args producer); Work4/G36 PARTIAL (completed successful allocating-loop composition now PROVED, general mixed storage shrink/push/pop/nested loop bodies/break/continue/early return and V14 application open); Work5/G38 PARTIAL/BLOCKED (bare revert versus fault and existing byte consumers, full byte/frame/journal/world coupling missing); Work6/G39 PARTIAL/BLOCKED (local roots/reset only, independent target transient/transaction/callback-world producer missing); BackfillsA/B PARTIAL. Current loop constructor still requires actual Memory.ProgFrag body/stable fragment, which owned Calls.Statement is not. Failure.Local.execute requires an explicit BYTE-machine Journal; Evm.Machine has no independent transient/callback-world field. No desired preservation/world premise or replacement semantics is introduced. No independent-work-exhaustion or whole-lane completion claim; questions=[].

Independent read-only finder/skeptic final source/control reviews PASS with no findings and no Lean/server/builds/writes; their initial packaging wording is explicitly superseded by the precise scoped-body statement above. Final actual committed-artifact reviews, exact head/parent/base, command logs, producer/source hashes, original patch/incremental bundle and immutable checksums are recorded in continuation18's separate handoff. Proposed coordinator-only reconciliation remains finite G36/G37 frame composition, not parent closure; no generated ledger/status edit.


## Continuation19 — actual completed-loop source frame

Continued after the substantive C18 milestone from clean9a273224f4df98db27e83086b57d7261b15d2e1b, preserving its exact source and immutable seal and every earlier checkpoint. Original branch/frozen base and externally blocked goal remain unchanged; no goal writes, publication, reserved edits, new producer intake or budget/profile/predicate changes.

New Backend/InternalFlow/CompletedLoopFrame.lean proves scoped_loop_completed_frame for an ACTUAL successful Stmt.loop execution and the existing BODY Prog.withinM guard. It derives an existential successful finite horizon from the actual published TLoop.run definition, then consumes scoped_loop_prefix_frame. No horizon or call-depth cutoff is supplied, and neither desired frame nor target simulation appears as a premise. This is a source frame consequence of successful execution, not a termination theorem or unbounded recursive compiler proof. The existing conservative loop-syntax guard remains false; it is not edited or cast to true.

New tests/internal-flow/CompletedLoopFrameChecks.lean identifies the actual singleton loop statement with C18's unchanged successful program execution, then closes the generic theorem on the SAME independently packaged finalOut. This resolves C18's precise source-frame packaging gap through actual execution equations, instead of asking definitional unification to identify a body state's packaging. completed_frame gives full reached TGFrameM and the exact guarded TLocAgreeM; all_old_contents covers EVERY old object through finalOut.ext, not only selected element observations. roots_and_transaction preserves the intrinsic source storage/net/tx/selfBalance fields for this actual view body. It is not target transient/transaction reset, failed-State reconstruction, rollback or callback/world composition. C18's exact target endpoint remains byte-identical and shares this same source finalOut.

The concrete positive execution starts with C18's populated callMid: two aliases to nonempty returned1=[2,7,11], private default0=[0], marker42/count9. The actual successful loop allocates fresh2=[2,0,0], drops its local and resets marker0; all C18 ordered source/target/cost7/cursor135/stack77 observations remain unchanged. A real successful subsequent caller writer is NOT framed: writer_guard_refused proves its actual withinM guard false, and writer_not_kept disproves Heap.Keeps by the actual old element11 becoming99. The existing actual source/target caller-use success and other-alias read99 provide the positive baseline. Guard refusal is not runtime/compiler rejection. No unconditional noninterference claim is extended over that mutation.

Core source check PASS2.982s and concrete fixture PASS3.309s; initial two small proof/rewrite diagnostics remain failed raw output. Actual new7headline axiom sets contain only standard propext/Classical.choice/Quot.sound subsets and are additive to ALL439old reports. Registration is append-only in Solidity.lean, module-map and docs/README; no Bridge/Source/elaborator import enters core. Every13fixture source is freshly checked with complete source/dependency/object/guard/config/provenance/toolchain binding. Complete aggregate PASS105.960s/120s:28owned/all actual imports/13fixtures/446reports, complete11575entry toolchain before/after maps equal digest617fd68210c0b46750ab92f863878665875839568f23d99320f79053956360f1. Cgrouppeak1053032448B/sampledaggregateRSS1190760KiB, hard aggregate12884901888B/no swap, serial explicit Lean-j1/LEAN_NUM_THREADS1, canonical writer/compiler locks and existing keyed cache. Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS1.062s (RUNTIME_GATE_PASS only); focused closure PASS2.643s. Separate7report audit and unchanged cache/driver/tamper controls, all13actual axiom guards plus52missing/duplicate/wrong/error controls and layer/import/orphan/trust checks are recorded in the new handoff.

Original full124/300s, raw-source124/120s, no-build3 inventory, C15/C17resource failures and C18distinct77targetpreparation124/120s remain preserved; no unchanged failed command is repeated or widened. Original TestSuite/sort unreached. Raw normal/strict docs1 remain failures; COMPLETE current/publication48findings equality and frozen46plus2incoming reserved findings are compared separately, never called global/frozen no-new success. No cache deletion or unrelated cleanup; only recorded stopped task CIDs removed.

Independent read-only finder/skeptic source reviews PASS with no findings: actual execution-derived horizon, closed same-finalOut source frame, real writer counterexample and unchanged ownership/predicate boundaries. No reviewer Lean/server/builds/writes. Final staged/doc and exact committed-artifact reviews/head/hash/bundle/command/checksum evidence are recorded in the new handoff; C18 and all earlier seals remain unchanged.

All original queues remain unfinished: Work1/G37.01 PARTIAL (finite call/reference consumers only, general runtime frames/public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite intrinsic unroll/direct expansion, no unbounded recursive target/source lowering); Work3/G37.03 BLOCKED (dependent dispatch/reserved producer); Work4/G36 PARTIAL (C18 successful allocating target loop plus C19 actual completed-source frame now proved, general mixed shrink/push/pop/nested bodies/break/continue/early return and V14 effectful application open); Work5/G38 PARTIAL/BLOCKED (exact local bytes/bare halt consumers, missing byte/frame/journal/world producer); Work6/G39 PARTIAL/BLOCKED (local roots/reset and successful source frame only, missing independent target transient/transaction/callback world producer); BackfillsA/B PARTIAL. Existing Loops.StmtCert.loop still needs actual Memory.ProgFrag/stable body, which Calls.Statement does not supply; Failure.Local.execute still needs explicit live byte Journal, and Evm.Machine has no independent transient/callback-world field. No missing hypothesis is silently discharged, no generated ledger/status rewrite, no whole-lane completion or independent-work-exhaustion claim; questions=[].


## Continuation20 — finite dispatch frame and target consumers

Published prerequisite 099bfbe185731c354b12a40f28ccf5d98534c779 (including CF2 a9e12c55832d982db559fa6276f91fe6ee649424) was freshly fetched from normal origin/master, its ancestry checked, and incorporated by isolated-branch merge e2bfdacd7d86184fce9d9d5e828dd7a034a47037 after read-only integration reviews. All prior owned sources and seals were preserved. Incoming reserved documentation EOF whitespace is retained as a raw diff-check failure; no reserved producer repair or master publication occurred. Original externally blocked goal is untouched.

New Backend/InternalFlow/FiniteDispatch.lean composes actual DispatchArm.chain through public Calls.branch/cons/nil and actual compiled condition/body certificates. Checks is typed certificate data indexed by the EXISTING intrinsic arm list, not a replacement AST or evaluator. cons_frag and cons_need retain the exact restricted branch meet and maximum frame. select_run and none_run explicitly use Stmt.runR_eq/Prog.runR_eq before consuming the published runC selection facts; runC and target run are never identified by assertion. selected_endpoint and fallback_revert consume actual existing Calls soundness and reached execution. Their genuine representation/room/allocation inputs are discharged in the concrete consumers, not counted as closed by the generic theorem alone.

FiniteDispatchFacts and MemoryDispatchFacts connect ACTUAL frontend quotations to the published chain, including hidden argument-capture temporaries and complete program suffixes. Literal guard equations prove miss of tag1 then hit of tag2. Actual candidate body/run equations close each concrete direct-candidate link. Raw parameter types, locations and return flags are checked where claimed. A trial canonical-signature-string proof stops at the published partial Raw.canonFnTy; raw failure is retained, and string normalization is only an explicitly bounded runtime control. No generic frontend guard-generation/canonical-signature/global fnMemoryDispatch-chain theorem is claimed.

Scalar complete_endpoint derives actual prefix and selected target runs, reached StateRepr and AllocationInput through GrowsAllocator.nextInput. Caller holds marker42, aliases to old0=[7,11], unrelated1=[23,29], selector2 and captured arguments. The selected candidate mutates old[1] to16, allocates private2=[70,71], returns16 and changes count9 to10. The first allocating candidate is skipped. Actual frame need12, prefix cost6 and reached arm cost3 give total growth9/cursor137/protected stack77. Ordered source observations cover all caller locals and objects before/after; complete target observations include all represented cells, roots and cursor. Actual tag-clear execution after the SAME prefix reaches all-miss and exact target bare revert, separately refuted as fault. Wrong same-typed scalar destinations, fresh/old identity, missing mutation, first-candidate root and incorrectly summed candidate costs have successful same-witness baselines.

Memory complete_endpoint derives prefix/selected/post target success and all reached representations from actual execution. It starts with old0=[7,11], unrelated1=[23,29], shared default2=[] and caller aliases. Selected execution mutates old0 to[12,11], changes count9 to11, creates callee default3=[], then privately rebinds/allocates object4=[99,101]. The actual exported result and frontend post-declaration retain OLD0, not either default or private4. Complete ordered observations retain all five objects and final nine caller cells, scalar42, root11, stack77, reached cost4 plus prefix7, total growth11/cursor139. Actual heap separation rejects unrelated/default/private result escapes; missing mutation and missing default-allocation cost/cursor are rejected on this SAME successful endpoint. No general Heap.Keeps conclusion covers the intentional old-alias mutation.

Both complete numeric target vectors also execute on published Evm.run and observe the protected sentinel; these are supplementary runtime controls, not external EVM/gas agreement or kernel proof substitutes. Public producer refusals for byte payload errors, recursive constructors and storage result calls remain explicit. Existing withinM old-alias-write rejection and all prior fixtures/axiom pins remain unchanged. The original finite-signature/reference profile is not widened.

Independent read-only finder and skeptic source/control reviews PASS with no confirmed findings; neither ran Lean/server/builds or wrote sources. New exact actual axiom guards add 42 scalar/core +25 memory facts +12 endpoint reports to the unchanged446. Complete final cache/structural/driver/provenance checks, raw exits and exact committed-artifact reviews are recorded in the separate continuation20 handoff; no pending check is passed by this prose.

Full original queue: Work1/G37.01 PARTIAL (finite frame/alias/export consumers, general runtime/storage/full public admission open); Work2/G37.02 PARTIAL/BLOCKED (finite expansion/unroll, no unbounded recursive target/source lowering); Work3/G37.03 now PARTIAL (concrete finite frontend-linked scalar/memory dispatch target frames, no general dependent/full-signature dispatch/compiler closure); Work4/G36 PARTIAL (prior completed allocating loops/frame, general mixed/nested/effectful loops and break/continue/early return open); Work5/G38 PARTIAL/BLOCKED (exact local-byte and bare-halt consumers, missing word-frame/byte-journal/world coupling); Work6/G39 PARTIAL/BLOCKED (local roots/reset and source frame only, missing independent target transient/transaction/callback-world producer); BackfillsA/B PARTIAL. Loops.StmtCert.loop still requires Memory.ProgFrag/stable body rather than arbitrary Calls.Statement; Failure.Local.execute still needs an explicit live BYTE-machine Journal rather than Evm word-cell StateRepr; Evm.Machine has no independent transient/callback-world field. No absent producer/hypothesis is silently discharged, no failed State reconstructed and no source catch/world rollback invented.

Original full ./run-lean.sh124/300s, raw-source124/120s, distinct prerequisite timeouts, resource failures, no-build3 inventory and unreached original TestSuite/sort remain retained. No unchanged failed heavy command was repeated or budget increased. Raw normal/strict docs1 and incoming reserved findings stay failures; complete publication/frozen comparisons are separate. No global ledger/status/pin rewrite, goal reset/reactivation/completion or whole-lane completion claim; questions=[].

C20 measured aggregate repair: the initial expanded sixteen-fixture gate actually timed out124/120s after fifteen fixture results (121.429s including wrapper overhead); all raw output and first prepared bindings are retained separately. A distinct instrumented single-Tuple check measured actual Lean14.459s, fresh key checks0.488/0.442s and full toolchain2.438s. This is measured per-fixture overhead, not a unique explanation of every timeout. After inspecting speed history and warning about a larger imported environment, the OWNED cache driver now uses ONE actual Lean process to import every registered fixture and print every525report. All fixture prekeys, exact actual name/order/count/error checks, original per-fixture axiom-set guards, fresh postkeys/object hashes and complete before/after toolchain hashes remain. Per-file preparation/check mode is unchanged. Six new no-Lean report-split negatives supplement all original driver/coverage/tamper controls; they do not prove kernel statements. Independent read-only finder/skeptic driver reviews PASS, no findings. The changed script key requires actual fresh preparation of every16fixture again; no old manifest is relabelled. The revised aggregate must actually pass under the SAME120s/hard12GiB/no-swap limits; its outcome is in the handoff. The original failed aggregate stays failed regardless.

C20 final scoped validation: every16fixture source was actually freshly prepared under the changed driver key. Revised COMPLETE registered aggregate PASS112.636s/120s:29owned/all actual fixture imports/16fixtures/525reports; complete11575entry toolchain map rehashed before AND after with identical digest617fd68210c0b46750ab92f863878665875839568f23d99320f79053956360f1. Actual cgrouppeak1055911936B/sampledaggregateRSS1233256KiB, hard aggregate12884901888B/swap.max0, serial explicit Lean-j1/LEAN_NUM_THREADS1 and writer/compiler locks. All old13fixtures/446pins remain unchanged; new79 are additive. Separate7report audit PASS2.987s; cache controls9.240s/dependency controls12.435s; all16exactguards and64missing/duplicate/wrong/error negatives PASS. Final12027unique-content hash audit passes after tamper restoration and is labelled integrity inventory, not proof. Six additional report-split negatives plus original batch/driver coverage controls pass separately. Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS0.897s, RUNTIME_GATE_PASS only. Complete focused closure passed227jobs/5.347s after actual prerequisite refresh and1.615s before final preparation. Earlier focused/aggregate124s and all original mandatory failures remain preserved. Numeric vectors supplement kernel proofs. Final committed-artifact source/hypothesis/ownership/handoff reviews and exact-head checksum/bundle evidence are in the immutable continuation20 handoff; no whole-lane completion or independent-work-exhaustion claim.


## Continuation21 — structural successful-flow frames and raw-source investigation

Continued from clean8014ca2ab3c42f29bf659b341eef04ee4b7f2b5b on the same frozen branch/base. All21prior manifests (original plus C1–C20) verified unchanged. No goal writes/reset/reactivation/completion, upstream intake, reserved edits, semantic/profile/predicate/budget changes or publication.

NEW StructuredFrame.lean defines FrameStmt/FrameProg as typed PROOF derivations indexed by the existing intrinsic statement/program and a protected Idx. These are not a replacement syntax/evaluator or compiler admission. Leaves retain original withinM and exact unwritten-local premises. Completed loops retain condition readsIn, actual body withinM and its protected-local exclusion; their frame is derived from scoped_loop_completed_frame and actual success. Branch/block/sequence closure transports local indices through actual Ext and composes actual heap extensions. FrameStmt.sound/FrameProg.sound prove full TGFrameM plus the exact weakened protected caller value after dropping private locals. No desired frame/simulation equation is supplied as a field. Existing withinM remains false for loop syntax. No termination, new target compilation, arbitrary lifetime/mutation/world theorem or unsupported early-return/break/continue constructor is asserted.

StructuredFlowChecks starts from the same inhabited callMid with nonempty returned object1=[7,11], two aliases, private default0=[] and marker42/count9. An actual successful allocating loop sits inside a block and selected branch; a SECOND allocation follows before branch-local drop. Actual execution closes composition, yielding H4 with COMPLETE ordered objects[0],[2,7,11],[2,0,0],[2,0,0], aliases[1,1], marker0 and count9. Both protected aliases and ALL older contents are derived from the structural theorem, not assumed. False branch is exact bare revert. Wrong fresh alias/content/heap count controls have successful baselines. The actual successful caller writer is excluded by its existing concrete not-Heap.Keeps counterexample; the changed scalar cannot be protected either. All11actual headline axiom sets are standard subsets; original525pins/16fixtures and all old observations are unchanged.

Raw-source investigation preserves legacy check-files.sh and its124/120s, original full ./run-lean.sh124/300s and unreached TestSuite/sort. Original raw progress reached the three heavy call fixtures; full progress stopped at90/984. A distinct actual CLI profile checks all30current owned source bodies, taking60.278s (wrapper61.185s); slowest MixedLoopPrefixes8.180s, EvaluatedRevertChecks5.366s, StoragePrefixFrame5.165s. This diagnostic subset is NOT a narrowed mandatory source gate.

An evidence-only prototype (preserved with the continuation21 artifacts) invokes actual Lean4.24 Language.Lean.process for each entire fresh source buffer, with fresh options, header/context/main-module identity, oldSnapshot none and trust0, mirroring the no-output Shell/runFrontend path. It reports all snapshots and waits for final command state; no source main-module import replaces elaboration. It scopes snapshots instead of Runtime.forget, which the CLI frontend uses assuming imminent process exit. Its experimental driver keeps every30owned source and all3original call fixtures. This is a SEPARATE fresh-frontend experiment, not universal separate-process IO equivalence and not a relabelling of the legacy raw failure. Current source bodies contain no #eval/run_cmd/initializer commands. Real controls compare positive CLI logs byte-exactly and exercise fresh options/declarations/private names, header/syntax errors, fail-fast and rejection of changed bad source despite a valid old olean. Controls PASS9.454s; first Python-in-container attempt actually failed127 because Python was unavailable, retained before using the already available Node runtime. Full experiment outcome/resources and output comparison are in the new handoff.

Independent read-only finder/skeptic initial source and validation-design reviews PASS, no findings; no Lean/server/builds/writes by reviewers. Final fresh checks, full registered cache gate, exact guards/provenance, host checks and committed-artifact reviews are recorded separately with actual outcomes. No pending validation is passed by this prose. Proposed coordinator-only reconciliation: add PARTIAL G36.01/G36.02/BackfillA-B successful structural frame evidence; no parent closure or generated ledger edit.

All Work1–6 and BackfillsA/B remain PARTIAL: general runtime frames, unbounded recursion, generic dependent signature/source lowering, general mixed-loop body/lifetime and early control, full byte/frame/journal/world and independent target transient/transaction/callback producers remain open. Loops.LoopCert still requires actual Memory.ProgFrag plus stable restriction; Calls.Statement is not that inductive producer. Failure.Local.execute requires a live byte Journal, which existing Evm word StateRepr does not produce; TRes.error supplies no successful State. Evm.Machine has no independent transient/callback-world field. C20 finite source guard/candidate links remain closed, canonical-string controls remain runtime-only. Original mandatory failures and documentation/whitespace debt stay visible. No independent-work-exhaustion or full-assignment completion claim; questions=[].

C21 rejected validation experiments (superseding any pending-tool wording): the interpreted all33source fresh-frontend experiment hit the actual12884901888B cap and exited137/32.774s; the distinct native/exported/explicit-one-worker version also hit it, exit137/30.446s. The latter's symbol-export prerequisite first failed a small control, then matched Lake supportInterpreter's documented -rdynamic and passed all small controls3.542s; native bootstrap was explicitly constrained with public lean_init_task_manager_using(1). Neither bulk experiment completed. No unique retention cause is inferred; native execution did not establish a fix. All prototype tool/control/driver source bytes, exact generatedC/binary hashes, commands, raw failures and resource outputs are preserved in continuation21 evidence/rejected-fresh-frontend, not shipped as a production checker. The ONLY moved files were this turn's own new uncommitted prototypes. Existing check-files.sh is byte-identical to C20 and remains FAILED/incomplete; original full ./run-lean.sh is likewise retained FAILED, TestSuite/sort unreached. A source/cache inventory or paired small controls cannot relabel either gate. No third bulk retry, limit increase or stop hidden as success. Remaining validation engineering is concrete proof-elaboration cost reduction or a supported bounded fresh-session lifecycle; independent-work exhaustion is not claimed.

C21 scoped validation completed: actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs PASS1.109s (RUNTIME_GATE_PASS only); complete focused closure PASS1.511s. All17fixture sources freshly prepared with actual source/toolchain/dependency/object/guard binding. Complete registered cache gate PASS114.630s/120s:30owned/allactualimports/17fixtures/536reports, full11575toolchain hashes before/after equal617fd68210c0b46750ab92f863878665875839568f23d99320f79053956360f1. Actual cgrouppeak1088430080B/sampledaggregateRSS1249600KiB, hard12884901888B/swap0, serial-j1/LEAN_NUM_THREADS1 and writer/compiler locks. All525oldpins/16fixtures unchanged;11new additive. Separate7report audit, cache/dependency tamper controls, all17exactguards/68negative controls and post-tamper12033content integrity audit PASS; integrity is not proof. Extra-audit wrapper48.630s includes serial lock waiting behind the47.240s profiler; one compiler executes at a time, no time budget raised. Cached validation is not raw/full validation.

Further original validation work continued after the structural proof: actual CLI TupleMemoryCalls source profiling PASS47.240s/120s, with reported type checking28.1s, elaboration14.9s and import728ms. It preserves every original85report and source body; profiling flags are diagnostics, not raised proof limits. This identifies concrete remaining OWNED proof-elaboration work rather than an absent producer, and is not an equivalent raw-source repair. Full/raw gates remain FAILED. Current default-cache object presence is inventoried separately and proves neither freshness nor readiness; it does not justify an unchanged full300s retry. No independent-work-exhaustion claim.

## Continuation22 — shared tuple observations and structured call unwind

Partial original Work1/Work4 and BackfillA/B evidence only. The existing blocked
goal, full queue, source profile and mandatory gates remain unchanged. No new
publication or reserved implementation is incorporated in this checkpoint.

The owned TupleMemoryCalls fixture now derives result-entry observations from
its already checked prefix/argument observations, checked_target_next from the
actual checked-code equation and target_next, and five negative controls from
complete source snapshots/cost observations. All old theorem statements,
ordered vectors, 85 axiom reports and report order are unchanged. The named
profile passes in49.782s; the changed fixture passes in46.645s. These are separate
runs with different profiler flags, not an isolated causal speedup measurement.
Asynchronous named kernel trace spans overlap; their sum is not CPU cost.
The attempted shared caller-export simplification hit the existing recursion
limit and was reverted; the limit was not increased. Both original failures
are retained under unique C22 evidence names.

A materially changed complete raw-source attempt still exits124 at120.851s,
after reaching TupleMemoryCalls. Proof sharing is insufficient to pass that
mandatory gate. The original full300s timeout, raw-source timeout and all prior
resource failures remain failures; no unchanged full gate was repeated.
Repeated target-stage reductions remain concrete owned engineering work.

[StructuredFrame](../../Solidity/Backend/InternalFlow/StructuredFrame.lean)
adds structured_call_frame over actual Args.evalT, CallRet.enterT, a genuine
FrameProg derivation at a protected typed index and actual body.runR success.
It derives the real TRun.call return equation, exact composed entry/body heap
extension, TGFrameM and Heap.Keeps through actual result export. A FrameProg
plan is a restricted syntax derivation, not an assumed preservation equation.
This theorem does not assert arbitrary caller-local protection or change
withinM/compiler admission.

The inhabited StructuredFlowChecks void call evaluates the populated caller's
two non-null aliases and scalar as actual parameters, executes the existing
nested block/selected branch/completed allocating loop plus local allocation,
and drops the private body environment. Complete ordered objects remain
[0], [2,7,11], [2,0,0], [2,0,0]; caller aliases remain1/1, caller marker42 is
restored after the callee's marker0, and persistent count9 remains. Actual
argument evaluation derives non-nullness and its typed Unit tail; no desired
midpoint, simulation or heap-preservation premise is supplied. Wrong marker0
and fresh alias3 controls are rejected from the complete successful snapshot.
Six new exact standard-axiom pins are additive; all old536 reports remain.

Independent read-only finder and skeptic source reviews found no issue. Neither
review ran Lean/server/builds. Final command/resource, provenance, guard and
committed-artifact results are recorded in the new immutable C22 handoff.
All Work1–6/BackfillA–B remain partial: no unbounded target runtime/dependent
signature lowering, early-return/break/continue producer, general mixed-loop
body certificate, word-frame/live-byte-journal representation or target
transient/callback-world composition is added. No independent-work-exhaustion,
full validation or integration eligibility claim follows.

C22 scoped final gates: all30 owned import targets PASS2.079s; all17fixture
sources freshly prepared, then the COMPLETE registered cached gate
PASS112.706s/120s with542 ordered reports, plus the separate7-report audit,
all17actual guards/68 corruption controls and post-tamper input integrity.
The actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort2-job runtime gate passes.
The attempted broader root import check separately exits124/120.609s while
building uncached prerequisites; it remains FAILED, not a focused pass. No
original full300s retry follows. Raw normal/strict docs remain exit1; complete
output equals consumed publication, with two incoming reserved missing paths
and ambiguity relative to frozen base. None of these distinctions waives a
mandatory original source gate or establishes integration eligibility.

## Continuation23 — exact target observations and source-report traversal

Partial original Work1/BackfillA engineering and validation; no parent closure.
The original blocked goal and all prior seals remain unchanged. No new upstream
publication, reserved implementation edit or source-profile change is included.

[TargetObservation](../../Solidity/Backend/InternalFlow/TargetObservation.lean)
reconstructs the actual word list from a successful complete numeric observation.
Explicit cell/address lengths determine the ENTIRE protected stack, so its
subselection does not guess a stack prefix. Original wrong destination/cursor
controls in all three call fixtures now project the same complete observations.
All original theorem statements, ordered vectors, aliases, frame/cost/cursor,
private-object and failure/refusal controls are retained.

TupleCalls.compileTuple_success exposes the actual checked construction from a
real successful body compilation. The fixture closes that premise with the
existing compiled witness; actualSelectorResult links the shared certificate
back to the unchanged selector. The original certificate's full equality was
kernel-checked before replacing its duplicate construction. Actual prefix/Input,
need and cost facts derive the expanded body's real zero-skip endpoint. The same
full target export and wrong-order-copy control then execute their six actual
instructions via run_append_ok. The unchanged exact_frame_cost declaration is
earlier only to permit opaque proof reuse; its type, proof and report position
are unchanged. No new evaluator or assumed target simulation is used.

Whole-fixture timings did not establish a substantial improvement from these
proof changes alone. Isolated suffix arithmetic simplification hit the existing
recursion limit, and symbolic chunk probes hit the actual12GiB cap/exit137.
Separate direct certificate projection probes hit200000 heartbeats. These raw
failures remain under unique names; no limit was raised or failed probe shipped
as a passing proof. They do not establish a unique resource-retention cause.

A separate actual standard Lean collectAxioms run took92.362s for542 theorem
roots. The first conservative metadata memo comparison timed out at120s and is
retained FAIL. A distinct reverse-dependency implementation matches all542
actual standard sets and10 fresh cycle/duplicate/query-isolation controls in a
5.077s whole diagnostic. Its reported internal0ms is NOT a reliable CPU timer.

[AxiomReports](../../tests/internal-flow/AxiomReports.lean) is TEST-ONLY metadata
tooling, not a proof checker or a kernel theorem of equivalence. It forces the
same checked kernel environment, resolves actual root names with the builtin
resolver, discovers the standard collector's exact dependency edges once, and
propagates each actual axiom along reverse edges. Visited sets handle cycles;
each requested root is emitted in order, including duplicates/empty sets. It
uses no expected-pin allowlist, unchecked environment, Expr-node manipulation,
proof shortcut or builtin-command override. The independent cached gate keeps
UNMODIFIED standard #print axioms for every original542 root. Core guards are
unchanged. All mathematical proofs still undergo ordinary fresh Lean checking.

The three original source fixtures batch reporting only; their original27/42/85
reports exactly match the prior actual builtin reports and order. Fresh source
checks pass9.798s/11.909s/31.738s. The tool is an added18th registry module with
zero headline proof reports, explicit source/selftest/provenance coverage; it is
not counted as mathematical coverage. The raw driver retains every original
source/fixture and adds a fresh check of this metadata tool, under the SAME120s
aggregate bound. Original full/raw/root/docs failures remain recorded until an
actual justified repaired gate passes. No cached import is a raw-source pass.

Independent read-only finder/skeptic reviews confirm the structural observation
and metadata reachability arguments, subject to final source/artifact audits;
neither review runs Lean/server/builds. Exact command exits, full independent
builtin audit, type preservation, resources, driver controls and final reviews
are in the immutable C23 handoff. All Work1–6 and BackfillA–B remain partial:
unbounded runtime recursion/dependent dispatch, early-control/general mixed-loop
certificates, word-frame/live-byte-journal and transient/callback-world producers
remain open. No independent-work exhaustion or integration eligibility is claimed.

Actual final C23 gates: the COMPLETE fresh-source driver checks all35 sources
(31 owned core modules, added metadata tool, all three original call fixtures)
and passes119.502s/120s, exit0. Every original invocation/stack flag remains;
this is fresh elaboration, not a cached-import substitute or split timer. The
margin is narrow; no stable performance guarantee follows. All542 original
kernel-imported theorem types (including85 tuple types) are byte-identical to
the authenticated pre-change query. All original17 fixture pin maps/report
orders remain exact. Independent UNMODIFIED builtin542 cached audit passes
116.200s/120s with18 registered modules; helper0 is metadata coverage only.
Separate7 retained and6 new actual builtin axiom sets pass. All72 exact guard
corruption controls, real unknown-name/format/order reporter controls,
cache/dependency corruption and both drivers' coverage/fail-fast controls pass.

Runtime: Lean4.24.0, Lake5.0.0-src+797c613, actual KeySort successful2jobs.
All heavy checks stay serial explicit-j1/LEAN_NUM_THREADS1, hard12884901888B
aggregate and swap.max0, canonical writer/compiler locks. Raw sweep sampled
peak aggregateRSS1874012KiB and cgroup peak1251454976B are distinct measurements.
Verified stopped task-owned C23 containers alone were removed for disk headroom;
all caches, probes, raw failures and23 previous manifests remain unchanged.

The old full ./run-lean.sh124/300s, prior raw120 failures, broad-root124/120.609,
prerequisite124 and137 probes remain preserved FAIL. C23 raw pass repairs that
specific workload; it does not pass the full pipeline/TestSuite/sort. The last
broad-root failure still built only126/825 jobs; its unrelated uncached core
prerequisites and default executables are not repaired by a fixture-only
metadata change, so no unchanged broad/full rerun is claimed. Raw normal/strict
documentation exits remain1; complete current findings equal publication/C21,
while frozen base has46missing versus48current plus incoming Arms ambiguity.
Independent final source and exact helper0 driver reviews find no confirmed
semantic/trust/control flaw. Final committed-artifact reviews are recorded in
the handoff; no reviewer runs Lean/builds. All eight original queue items remain
partial and the original blocked goal remains unchanged.

## Continuation24 — actual nested tuple construction and target-stage reuse

Partial original Work1/Work4/BackfillA-B. The original blocked goal, frozen base,
all previous seals and semantic/profile/observation/proof budgets are unchanged.
No upstream intake, reserved implementation edit or compiler admission change.

The owned TuplePrograms.compile_tuple_nil_success proves the EXISTING selector's
actual tupleReturn-plus-nil construction from ordinary outer/expanded None,
actual owned expanded Some, and exact finite syntax-height equality. These are
compiler/syntax premises, never a desired simulation equation. The populated
Composed fixture discharges all premises, including undecidable certificate
None equality through actual decidable isNone observations. Its full
actualOuterConstruction identifies the genuine selected record, including code,
fragment, need, allocation cost and soundness fields. No new evaluator, AST,
call-depth admission cutoff or assumed certificate is introduced.

The original exact_cost_frame statement/proof is unchanged and merely earlier;
its original report position remains unchanged. Reached expanded cost5 now
follows from actualOuterConstruction and that actual outer-cost fact. Real
initial capacity7+5, prefix execution/StateRepr and GrowsAllocator.nextInput
supply the reached input to expandedProducer.sound. The successful zero-skip
endpoint is closed; its failure alternative contradicts the pre-existing,
independently checked target_body observation. There is no circular dependency
on the rewritten export or wrong-copy controls and no assumed midpoint.

The SAME complete target_export vector now follows from that actual endpoint,
full numeric stack/cell reconstruction, the selected certificate's exact code
and the six real export instructions via run_append_ok. The SAME wrong_overlap
vector [77,1,30,1] likewise executes only the six actual badHighFirst instructions.
Every old caller/private/heap cell, alias, result order, scalar, stack77,
sentinel99, cursor268 and cost/frame observation/refusal remains. target_body,
target_unwind and target_final still have their existing independently checked
proofs; broader staged-sharing work is not claimed complete. All542 original
kernel theorem types (85 tuple types included), original17 mathematical pin maps
and report orders are preserved. New generic+four fixture lemmas have separate
actual UNMODIFIED builtin axiom guards: propext/Classical.choice/Quot.sound.
Their fixture metadata reporting remains separate from ordinary kernel checking.

Actual fresh whole-fixture preparation passes39.198s/120s. The COMPLETE35-source
fresh sweep passes exit0/118.689s at the original120s command bound. The complete
18-module cached gate, including all original542 builtin reports, passes
exit0/116.950s after fresh rechecking of the two legitimately stale StorageReturn
and FragileReturn bindings. The stale rejection (exit1/20.263s) and an earlier
missing parser-log setup failure (exit1/9.260s) remain raw failures, not negative
control successes. All72 report-guard corruption controls, cache/dependency
corruption controls,7 older and6 retained separate axiom sets pass. Original
proof statements/vectors/pins were not narrowed to obtain these results.

The earlier C24 proof version also completed with exit0 under the unchanged120s
command timeout, but outer wrappers measured120.640s cached and120.313s fresh;
these are NOT sub120s end-to-end claims. No isolated performance improvement is
inferred from different whole-file timings. Failed generic match-splitter,
definitional-associativity and undecidable-certificate probes remain evidence
only, including their sorryAx diagnostics; no failed proof is delivered.
No heartbeat/recursion/fuel/node/time/resource bound was raised.

Runtime again records Lean4.24.0/Lake5.0.0-src+797c613 and actual KeySort2-job
success. All heavy processes remain serial-j1/LEAN_NUM_THREADS1 under hard12GiB,
swap.max0 and writer/compiler locks. Only verified own stopped C24 CID layers
are removed for headroom, preserving all caches and raw records. Read-only
finder/skeptic reviews find no circularity, hidden oracle, ownership or changed
control; exact committed-artifact reviews are recorded in the handoff.

Required-root preparation is separate from validation: an explicit local import
inventory found1103 resolvable source nodes and414 absent object files. Two small
actual frontier dependencies were prepared and source/object hashes checked.
Further authenticated current-source frontier preparation continues serially,
with individual120s bounds and retained outcomes, stopping for diagnosis on a
new timeout/OOM or concrete disk blocker. Neither inventory nor warm-cache
preparation passes the original full gate. Final handoff records its actual
extent, failures and any justified later full attempt. No unchanged failed
full/broad operation is repeated or renamed green.

All Work1–6/BackfillA-B remain partial. General runtime frames/unbounded recursive
source/target transport, dependent full-signature lowering, early controls and
general mixed-loop certificates, word-frame/live-byte-journal/world coupling,
and independent target transient/callback state remain actual producer holds.
The original full124/300s, broad-root124/120.609s, prior prerequisite/raw/137 and
budget failures remain preserved. Raw normal/strict docs remain exit1; complete
findings equal publication/C23, with frozen46missing versus48 plus incoming
Arms ambiguity. No source delivery/integration eligibility, full-lane closure,
new semantic choice or independent-work-exhaustion claim is made.

C24 preparation milestone record:212 bounded parent commands,200 exit0 and12
retained120s timeouts, plus separately recorded focused prerequisite checks.
These are Lake preparation results (including cache reuse), NOT212 fresh-source
checks. The actual remaining-object inventory is in the handoff and remains
inventory only. No full/broad gate has been repeated or passed. Preparation is
suspended at a completed-job checkpoint boundary, with its remaining frontier
preserved for the next original-work phase; no active build is interrupted.

Controller review found a warning-location classification error and two latent
authentication/history gaps. Raw exits/progress snapshots remain preserved;
warning locations were removed as false blockers. The corrected controller
tracks all nested diagnostics, verifies sources/compiler before and after both
parent and child, records successful child object hashes, preserves actual error
lines on timeout and excludes mandatory roots from diagnostic retries. Both
independent read-only reviews close these findings. Audits found no actual
repeated diagnostic; retrospective bindings are explicitly not represented as
hashes captured at original completion time. Two controller-only maintenance
exits143 follow normally completed bounded children; neither is a hidden build
stop or a passing proof gate. Their exact drain/recovery records are archived.

Additional original BackfillB preparation closes an unconditional source-state
identity for a scoped primitive-tuple call versus its published expanded body
with exact typed local dropping. Its scratch check passes2.622s with standard
axioms; initial metavariable-rewrite failure is retained. This is NOT yet an
integrated loop/compiler consumer or delivered lane closure. Integration with
inhabited controls remains ready assigned work. Published TryPanicProducer and
TryPanicCarrier were reinspected: source-link provenance and a ghost literal
carrier do not supply original carried-body construction, arbitrary word-frame
to byte-journal/world coupling, or an inference from THalt.data=[] to REVERT.


## Continuation25 — exact scoped tuple disposal and reached prefix frames (partial)

This is additional original G37.01/G36.01 and Backfill A/B work after C24,
not whole-lane closure. The original blocked goal is unchanged. All six Work
items and both Backfills remain partial; no independent-work exhaustion is
claimed. C24 and all twenty-five preceding sealed sets remain preserved.

### Intrinsic proof and actual target consumer

`TupleCalls.Scoped.scoped_tuple_expansion` proves, for every existing typed
`Args`, primitive `Binders`, body and caller state, equality of the complete
`runSt` outcomes of a block containing the tuple call and a block containing
its published intrinsic expansion. Private dependent environment/state lemmas
compose result-frame and parameter-frame removal using actual `TEnv.drop`,
`TEnv.thin`, and the unique intrinsic `Ext`. Success retains the actual entire
state; errors retain their original `THalt`. This is not `Heap.Keeps`, rollback,
a new evaluator, or an unbounded recursive compilation theorem.

`TupleCalls.Scoped.statement` consumes a real `Calls.Program` for that
expansion, then transfers the actual public `Calls.block` soundness through
proved intrinsic outcome equality. Its fragment is the reached fragment
restricted to the caller, and its code, need, reached cost, allocation flag and
zero-cost law are exactly the supplied checked expansion's fields. A whole
unused result frame requires no result-copy instructions. Ordinary result
export when results are used, public admission, and every unsupported refusal
remain unchanged.

`TupleCalls.Scoped.program_statement_endpoint` exposes an actual prefix and
following statement at a reusable abstract certificate boundary. Its premises
are the input `StateRepr`, both genuine frame bounds, capacity for
`before.cost initial + after.cost middle.st`, and the two actual successful
source executions. It derives the prefix machine/representation and the
following `AllocationInput` via `GrowsAllocator.nextInput`; it returns both
target executions, both reached representations, complete stack preservation,
old caller address preservation and the actual following allocator growth.
These are real execution/representation premises, not a desired simulation
assumption. The generic statement alone does not discharge arbitrary callees.

The appended `TupleCallChecks.Composed.ScopedDiscard` fixture discharges those
premises with the existing real allocating prefix and nested tuple-call body.
The caller contains two distinct populated old objects and two aliases to the
first, plus scalar42. The inner call mutates the first object's first element,
privately rebinds its reference and allocates; the outer body allocates another
private object. After the entire result/parameter frame drops, the complete
ordered heap is `[[2,19,11],[3,23,29,31],[2,99,101],[1,55]]`, caller aliases are
`[some 1,some 0,some 0]`, and caller scalar remains42. The output heap extension
is the actual exported call extension. No midpoint or content preservation is
assumed.

The complete target observation reuses the independently checked expanded-code
endpoint through actual code equality; it retains every old/private physical
cell, stack77, sentinel99, cursor268, frame15, body cost5 and prefix cost7.
Logical local dropping does not scrub physical private cells. Wrong same-typed
caller scalar17, a private object escaping as an old alias, missing mutation7
instead of19, and omitted cost0 each contradict a positive complete baseline.
The actual bare-failure scoped control retains `.error .revert`; it does not
recover a failed state, conflate empty halt projections, or establish byte,
world, catch, or rollback coupling.

### Kernel evidence, reporting and retained failures

All original mathematical theorem types, ordered observations,85 tuple reports
and the complete542-report registry remain unchanged. Reviewed later sharing
changes the selector-construction, scope-success and ordered-unwind proof bodies
without changing their statements, selected data or programs. Axiom metadata
scheduling is separate from these ordinary kernel proofs. Five metadata guard
batches (three old single queries, four C24 roots and twelve new roots) are now
one joint reporting traversal with the same nineteen names, order and exact
sets. This changes no kernel proof check or builtin command. All nineteen
roots remain independently covered by the actual unmodified builtin audits.
`tests/internal-flow/check-scoped-tuple-axioms.py` additionally guards all fifteen
new actual builtin reports (three generic and twelve concrete), in exact order,
with standard `propext`, `Classical.choice`, `Quot.sound` sets. Positive output
and missing/duplicate/reordered/wrong/error-bearing corruption cases are checked.
The concrete extension equality still depends on the actual computed witness
through its type; an initial empty-set expectation failed and was corrected
against actual output, without altering any original pin.

Actual C25 evidence is in
`/workspace/scratch/v12-flow-calls/continuation-25/evidence`:

- Lean4.24.0 and Lake5.0.0-src+797c613, successful KeySort2-job output;
  runtime command0/1.610s with cap12884901888B and swap0.
- Actual scoped source, complete observation, expansion and field projections
  checked separately in2.100/1.935/1.998/3.040s. The generic prefix boundary and
  SAME concrete target claim pass3.519s. Final core/import closure passes;
  all31 owned targets pass15.836s. The full tuple fixture is kernel checked and
  authenticated, final joint-report version0/43.508s, every old report retained.
- Current builtin15, retained6/5/7 and all542 actual imported kernel theorem
  types pass and match their exact baselines. Complete18-module/542-report
  aggregate initially0/118.300s; current joint-report version exits0 but outer
  elapsed120.632s, explicitly NOT a strict sub120 end-to-end result. Before and
  after full11575-entry toolchain binding matches. Original72 axiom corruption
  controls and new5 scoped controls pass, as do cache/driver corruption checks.
- COMPLETE35-source raw gates remain FAIL124/121.432s and, after material
  metadata rebatching, FAIL124/120.861s. Their last progress and partial outputs
  are retained. Focused checks and cached/import checks do not pass this gate.
  Joint metadata scheduling measured only a small fixture timing difference
  from45.085/44.642s to43.508s, not isolated kernel-proof speedup evidence.
- Two combined concrete target probes hit the actual enforced cap, exits137
  at44.332s and30.574s. Small source/field checks passed separately; abstract
  prefix composition resolved the SAME target claim. No unique resource cause
  or raised limit is claimed. Unknown-helper/qualification and map-syntax
  setup errors, the failed axiom expectation, and the first rebatch assertion
  failure are all retained. The assertion failed BEFORE source mutation; its
  redundant unchanged successful preparation44.642s is not repair evidence.
- Original full `./run-lean.sh` FAIL124/300s, broad-root124/120.609s,
  prerequisite/source/OOM/heartbeat/recursion failures and no-build3 inventory
  remain retained; TestSuite/sort were not reached by the full gate. No unchanged
  full or broad-root retry occurred. Normal/strict docs remain raw exit1;
  complete current findings equal publication/C24, with frozen46missing versus
  current48missing plus the incoming Arms ambiguity. No global docs pass.

All heavy work is serial explicit Lean-j1/LEAN_NUM_THREADS1 under the canonical
writer/compiler locks and hard aggregate12GiB/no-swap cap, with measured OS/disk
headroom. Only verified own stopped CIDs are cleaned; existing keyed caches,
other work and raw logs remain. No new axiom/sorry/native shortcut, heartbeat,
recursion-depth, fuel, node, test, stack or time increase is used. Independent
read-only finder and skeptic reviews of the actual proof/control and metadata
changes found no issue; final exact-head artifact review is a separate step.

### Further checked structural sharing and current validation

The actual selected branch/block now has an explicit `scope_run_state` theorem,
derived from the existing actual `source_outer` and `source_used` equations and
published sequence/block/branch semantics. Those two old statements and proof
bodies are unchanged, moved earlier only. `scope_has_output` derives success
presence, so `unwound` still uses the SAME `.toOption.get` result with its checked
proof shared instead of recomputed. An independent kernel example equates it to
the original literal `get (by decide +kernel)` expression. `scope_state_drop`
proves the complete typed state equality after result-local removal, then the
UNCHANGED `ordered_unwind` statement projects the independently checked complete
`ordered_used` observation. There is no circular state/endpoint assumption.
The small imported probe passes2.846s; full fixture source45.159s in the latest
authenticated preparation. New three builtin sets are checked separately; the
joint metadata guard retains the previous nineteen names/order/sets and appends
those three. The original15-report maintained guard and all original542 pins
remain unchanged. Timing43.508/43.639/45.159 does not prove a fixture speedup.

A separate core profiler found a long simplifier invocation. Replacing only the
`compileTuple_success` proof with the actual `Option.bind` construction plus
`rw [built]` preserves its exact statement, selector definition and axiom set.
Identical profile flags measured5.592s before and3.797s after; tactic execution
falls1.69s to389ms and the1.36s simplifier invocation disappears, while kernel
type-checking remains195ms. This is measured local proof elaboration, not a
claim that a full gate passed. Current complete owned closure passes20.411s
(168 jobs), and actual source/dependency-keyed preparations for fragile/storage/
tuple fixtures pass41.457/39.390/45.159s without dropping any control.

The current actual542-type query, original15 builtin sets, new3 source-state
sets, and retained6 sets all pass with unchanged exact outputs. Current complete
18-module/542 builtin aggregate exits0 with outer120.095s: child120 completed,
but this is NOT strictsub120 end-to-end evidence. Earlier source-sharing version
passes118.708s; it is retained as earlier-version evidence, not a substitute.
The current COMPLETE35-source sweep remains FAIL124/120.908s, after prior C25
failures121.432/120.861/120.494s. Every original invocation, fixture and report
is retained; no cached check is relabelled raw validation. No further unchanged
raw attempt is justified by the current evidence. Exact axiom/cache/driver
corruption checks continue independently. Source eligibility and full original
completion remain unresolved.

### Required-root preparation and remaining original obligations

Authenticated same-cache required-root preparation drained naturally, with
one actual target/120s per process. Source transitions from C24 permit ONLY the
actual owned TupleCalls implementation/proof edits; every other discovered
source/compiler hash must match. The original frontier excluded all twelve prior
timeout holds and the actual roots. After that frontier ended, eight parents had
demonstrably changed prerequisite objects, backed by actual successful bounded
dependency receipts and exact before/after source/compiler/object hashes. Their
separate one-time original120s checks passed seven; Derived20 timed out again.
Only actual exit0 released a CURRENT preparation hold. Every original timeout
remains historical failure evidence. PowerBounds/OpenLoops/Derived7/UnitExamples
were not retried unchanged.

C25 parent preparation totals145commands:142exit0 and3exit124, plus a separately
recorded Hashing prerequisite diagnostic exit124. Across C24/C25 the parent
history has357records342exit0/15exit124. The final inventory is34missing objects,
33 transitively held; the remaining unheld object is an excluded actual root.
New Horizon and DecisionHashes/Hashing timeouts are retained, with no source edit
or raised bound. The published source Horizon module supplies fuel monotonicity
and event-prefix facts, not an unbounded recursive target/lowering theorem; its
own per-file120s validation is now a distinct pending prerequisite. Actual root
build/native/TestSuite/sort validation is still separate. Receipts, exact source/
object hashes, resource peaks and held paths appear in the new handoff.
Preparation/inventory is never a full gate, reserved edit or budget waiver.

Work1 general runtime/storage/result frames, Work2 uncapped recursive
source/target compilation, Work3 full dependent-signature dispatch/lowering,
Work4 general mixed bodies and early-control lowering/V14 application, Work5
word-frame/live-byte-journal/world coupling, and Work6 target transient/reset/
callback representation remain open. Current `Machine` has no independent target
transient/callback-world field. The existing syntax has no early-return/break/
continue constructor. `Loops.LoopCert` requires actual `ValFrag` and `ProgFrag`
body/stability evidence; a `Calls.Program` alone is not that body certificate.
The ghost panic byte carrier does not supply the original general carried-source
body producer. No failed state follows from `TRes.error`.

Further READY owned proof engineering is not declared exhausted: construction/
code-sharing facts for `Composed.target_body`, `target_unwind`, and `target_final`
remain to reduce raw elaboration, alongside finite scoped-call/loop consumers
where actual `ProgFrag` and reached Demand/Room/Cost can be discharged. Public
selector/construction links must be derived from actual compiler results, never
supplied as a desired endpoint. This checkpoint does not waive those gaps or any
original Backfill A/B item. Proposed coordinator reconciliation is only partial
G37.01/G36.01/Backfill A-B evidence; no global G03/status/pin/refusal edit or
parent closure, no push/merge/PR, no goal change and no semantic choice.


### Final unchanged-budget full-gate investigation

The reviewed source/proof checkpoints are538cbcfe42929389c7594c02d28edcf94abf5257
and18f8d749e2eeeec29a593d90a2a130a7f83a03ea. After authenticated preparation,
three actual COMPLETE `./run-lean.sh` attempts preserved every default/native/
TestSuite/sort target and the original300s cap: exits124 at300.887,300.535 and
301.050s. None reached TestSuite/sort; no whole-pipeline pass is claimed.

The first attempt actually completed PowerBounds in256s, emitted the checked
`threshold_bounds` axiom report `[propext, Quot.sound]`, built executable root
modules and linked the Lean CLI. Its new completed dependency justified the
second complete attempt at the SAME300s bound. That attempt replayed PowerBounds
and completed UnitExamples in152s; this genuinely new dependency justified the
third. The third emitted no further completed source dependency, so no further
unchanged retry is justified. Source.Horizon was observed active in the second
attempt; the final incomplete command and all raw resources/progress are saved.
A post-full31-missing-object inventory is existence ONLY: partially emitted or
old objects never relabel an exit124 command as passed. All earlier cold120s
failures, the original full124/300s and every later full failure stay retained.

PowerBounds and its six-source import closure are byte-identical to the EXACT
frozen base, compared through Git. This is source-provenance comparison, not an
executed base gate or waiver. Reserved source/performance repair remains with
its owners; no file, theorem, matrix, trust pin or budget there was changed.
Actual full failure, native progress and sort/TestSuite readiness are distinct.
The single source/toolchain-keyed cache and all25 previous seals are preserved.

The current owned raw35 gate remains FAIL124/120.908, current complete cached
542-report command is exit0/120.095 outer (NOT strictsub120), and all original
542 imported kernel types plus actual15+3 new scoped sets remain exact. Original
72 and new5 axiom-guard corruption controls, cache corruption controls, source
header preservation and structural/ownership checks pass separately. Raw normal/
strict docs remain1 with complete publication/C24 findings equality; no new owned
finding and no global docs pass. There is no source eligibility, full-assignment
completion, independent-work exhaustion, publication or goal-state change.


## Continuation26 — actual constructor boundary and checked final suffix

Starting clean checkpoint: edb467aa0830b681ce03c3f707e288957794fd6f.
Frozen base/branch and publication099bfbe185731c354b12a40f28ccf5d98534c779
are unchanged. The original blocked goal is untouched. All26 preceding sealed
manifests and their seven payloads were verified; no publication intake,
reserved edit, source/profile/admission change, push/merge/PR or new goal.

The additive laws in `Solidity/Backend/InternalFlow/TuplePrograms.lean` expose
its existing private traversal at the actual enclosing syntax height. The
nil/cons/block/branch equations consume genuine compiler selections;
`compile_construction` retains positive syntax height and ordinary compiler
refusal; tuple construction retains actual expanded selection/refusal and
height equalities. These are finite structural construction laws, not an
execution oracle, new evaluator or uncapped recursive compiler.

In `tests/internal-flow/TupleMemoryCalls.lean`, the actual Composed selector is
proved equal to public block/cons certificates. The suffix is checked over an
abstract typed fragment and instantiated at the actual block output fragment;
no supplied midpoint or representation is introduced. Its exact instruction
list follows from that real construction. The SAME `Composed.target_final`
statement obtains a zero-skip prefix/scoped endpoint from `represented`,
recovers the full protected stack and all ordered cells from `target_unwind`,
then executes only the real suffix with `Evm.run_append_ok`. Physical private
cells are retained, not scrubbed: stack77/sentinel99/cursor268, both caller
aliases, scalar1735, old arrays and private arrays all retain the original full
ordered observation. Original programs, producer selection,85 tuple report
order,542 registry pins/types and every positive/negative/refusal are unchanged.
Six new generic and five concrete actual builtin axiom sets are guarded at the
standard `[propext, Classical.choice, Quot.sound]`; no trust shortcut.

### Measured boundary, including unsuccessful routes

Identical CLI flags and explicit checked-declaration timing give baseline
40.451s versus final41.930s. Body/unwind/final stages were1077/1275/1392ms and
1085/1284/1087ms respectively; the final construction interval costs1824ms.
The first sharing variant was40.349s with a1506ms construction interval.
The final stage avoids replay and checks faster locally, but NO net speedup is
established; a new complete raw/full retry is not justified. All measurements,
source copies and raw receipts are retained in the new continuation26 evidence.

A separate scoped-constructor/true-branch/continuation probe ties actual
export execution to local writes using public append/skip laws. Its first
full source-result equality route exited137 at48.116s. Isolated continuation
code projection passed6.407s; a changed soundness-based outer endpoint passed
6.657s. The final abstract-continuation probe checks13.657s, substantially more
than the original unwind stage, so it is NOT adopted as a performance repair.
Syntax/type/simplification/guard failures and diagnostic sorryAx outputs remain
failed evidence only. No unique unproved OOM cause is asserted. One new profile
receipt name was accidentally reused: the initial missing-file exit1/0.906s
survives in the tool transcript, while the overwritten receipt records Docker
collision exit125. The explicit collision note distinguishes this evidence
loss from original raw logs; no earlier seal was touched.

### Gates and remaining assignment

Runtime again reports Lean4.24.0, Lake5.0.0-src+797c613 and successful KeySort
(two cached jobs). Serial explicit-j1/LEAN_NUM_THREADS1, canonical writer and
compiler locks, hard12884901888-byte aggregate/swap0, OS/disk headroom and the
single keyed cache remain enforced. Only receipt-authenticated stopped own
containers were cleaned; no source/object cache or unrelated work was deleted.
Owned import closure passes15.088s. Actual stale bindings identify precisely
FragileReturnCalls, StorageReturnCalls and TupleMemoryCalls; fresh kernel cache
preparation passes42.754/36.558/48.863s separately. All542 imported original
types remain byte-identical to C25;11 new actual builtin sets and retained
7+6+5+15+3 separate sets are checked. Metadata/report parsing is not raw checking.
Final complete cached/host/control/review outcomes are recorded below and in
the exact-head handoff; no pending gate is inferred passed.

Original fresh35-source FAIL124/120.908, earlier raw failures, broad-root
FAIL124/120.609, original full FAIL124/300s and three later complete full
FAIL124/300.887,300.535,301.050 remain. TestSuite/sort were never reached.
No unchanged raw/full/root/held retry or increased budget was run. Raw normal/
strict documentation exits1 remain failures; complete current/publication/C25
comparison and frozen46-versus48 incoming findings are separate observations.

ALL original queues remain partial: Work1 general runtime/result/reference
frames beyond finite consumers; Work2 unbounded recursive source/target
transport; Work3 generic dependent/full-signature dispatch and lowering;
Work4 early-control/general mixed/call loop certificates and V14 application;
Work5 word-frame/live-byte-journal/world unwind; Work6 independent target
transient/transaction/self-call/callback composition; Backfills A/B retain
their general recursive/reference/mixed lifetime/reset/unwind obligations.
Read-only reinspection confirms Stmt has no return/break/continue constructor;
LoopCert requires actual ProgFrag plus restricted-fragment stability, not a
Calls.Program soundness substitution; Failure.Local.execute needs a live byte
Journal, not a word-cell Machine relation; Machine has no independent target
transient/callback-world field. Missing producers cannot be inserted as desired
simulation premises. Ready owned body/unwind sharing remains engineering work;
no independent-work exhaustion, integration eligibility or lane completion.


Final C26 bounded outcome: the complete registered cached command exits124 at
120.700s. All18 fixture results and542 unmodified builtin reports were emitted,
but the final complete post-toolchain binding receipt was NOT written. This is
FAIL, not a cached pass or strictsub120 evidence. Actual imported542 types and
per-fixture ordered reports/sets are separately verified. Original raw/full
failures are retained without retry. The added structural proof has not repaired
the validation budget. Ready owned body/unwind proof and audit-cost engineering
remain; no source eligibility or independent-work exhaustion is claimed.


Independent read-only finder and skeptic source/final-doc reviews both PASS,
without Lean/server/builds/writes and with no findings. Layer/import/orphan/trust,
complete no-Lean cached/raw driver coverage/fail-fast controls,72 original and
12 separate scoped/construction guard countercontrols pass. Cache and transitive
dependency corruption controls pass10.375/14.217s before Lean invocation.
A separate complete12049-input/toolchain/object integrity inventory passes
7.313s; it does NOT turn the timed incomplete cached command green. Its first
Python attempt exits127 because the container lacks Python; actual Node
implementation checks the same content hashes. Final committed-artifact review
and exact full HEAD/bundle/checksum details belong to the immutable handoff.
No source obligation, failed mandatory gate or original dependency is waived.


## Continuation27 — captured caller views through witnessed finite dispatch

Human scheduling authorization permits exact committed peer packages in private
dependency worktrees, without whole-lane/publication waiting. It changes no
semantic decision, theorem premise, profile, guard, budget or final gate.
The original VM/branch/base/goal identity is unchanged; no goal write or new
continuation was scheduled. The existing external blocked status is not an
independent-work-exhaustion claim: this manual recovery continues ready work.
No peer package has yet been supplied. Already integrated compiler/memory
producers remain exactly published099bfbe185731c354b12a40f28ccf5d98534c779;
no unmerged intake, reserved edit, master merge/push/PR or ABI/function-ref repair.

C26 is sealed at4f3050933dd482c1834dd7c0ac9e5f6ede6e38a7, seven-payload
manifest4d23d19eb917c6f6288b477dba408702e977bc18ebccd4b3b7acc486902bc4f7.
Its separately exported PARALLEL-INTERFACE contains31 committed owned modules,
actual dependent signature output and a Git bundle, with manifest
6bc23ad48aa4521273887668c4060ca3ec48ebf9ebed06001120831456b727d3.
Both independent read-only artifact reviews passed. All27 prior seals remain.
Peer staging is development only; final combined concrete-tree gates remain.

### New intrinsic and target consumer

`Solidity/Backend/InternalFlow/CallerFrame.lean` uses existing intrinsic
CallRet/Thin/TEnv/Out/TRun and public finite-dispatch target certificates.
`Disjoint` checks ONLY that a scalar destination is outside the selected typed
caller view; it is not a profile/admission change or preservation oracle.
`export_environment` handles every EXISTING CallRet constructor and exact
ret.ext drop. Primitive Binders remain primitive; no reference tuple invented.
`call_environment` inverts the actual successful argument/body binds and proves
whole selected-environment equality along the actual composed heap extension.
`single_call_environment` uses the published runR_eq bridge explicitly;
`single_call_alias` derives exact old-reference transport from caller capture.

`selected_target` consumes an actual public Calls.Statement plus genuine source
execution, earlier misses/selected hit, StateRepr, frame need and reached-cost
AllocationInput. It derives the exact successful target, stack preservation,
BaseExtends/GrowsAllocator, full caller-view equality and EVERY protected old
reference's target cell at its entry address. No output alias equality or
hypothetical simulation is a premise. Body mutation is permitted; this is
LOCAL capture/reference identity, deliberately not Heap.Keeps or global rollback.
Source storage aliases keep their value, not an asserted liveness property.
Memory/storage/tuple source return laws do not widen public compiler admission.

### Closed populated client and countercontrols

The new ProtectedCaller client in `tests/internal-flow/FiniteDispatchEndpoint.lean`
uses the existing real frontend-generated two-candidate program. The existing
kernel actual_frontend_link/first_guard/second_guard/candidate_names and
candidate_signatures close THIS raw declaration/candidate/guard link: memory
uint-array plus uint arguments, uint result. Canonical full-signature lowering
and arbitrary candidate profiles remain open, not assumed from printing.

The actual seed creates two distinct nonempty arrays and three aliases of the
older array, hidden evaluated arguments5/reference0, tag2 and caller marker42.
The first candidate misses; second mutates old[1]11→16, changes count9→10,
allocates private array[70,71] and returns16 into caller index2. A Thin selects
ALL seven other caller locals, including same-typed scalars and aliases. Its
static destination guard is discharged. Full caller environment and Heap.Keeps
are each proved FALSE for this very execution, while the captured view survives.
Wrong projection drops argument5 instead of the result and is statically
rejected; wrong private escape to fresh object2 and any successful fallback
output are rejected with their actual positive baselines.

The new closed target derives the reached machine/representation/capacity from
actual seed execution and GrowsAllocator.nextInput, then uses selected_target.
It retains the FULL original ordered19-word target observation, including
all caller cells, actual old/other/private heap contents, count10 and cursor137;
protected stack77, frame12 within64, prefix cost6 plus selected cost3 and
composed growth9 remain exact. Protected pointer transport is derived generally
from capture, not supplied as the desired reached representation. The witness
uses the same actual target output for all these facts.

### Checked evidence and remaining full assignment

No MCP Lean server is available; permitted per-file CLI fallback is serial
explicit-j1/LEAN_NUM_THREADS1 under hard12GiB/swap0, canonical writer/compiler
locks, OS/disk headroom and one keyed cache. New core checks3.572s, complete
fresh endpoint source/guards20.460s and source/toolchain-bound import11.478s
pass. All32 owned import targets pass2.302s. Actual new16 builtin sets have
precisely pinned propext-only, propext/Quot.sound or standard3 dependencies;
all542 original imported theorem types (including85 tuple types) remain
byte-identical to C26, and all7+6+5+15+3+11 previous separate builtin sets match.
Runtime again passes Lean4.24.0/Lake5.0.0-src+797c613/KeySort(two jobs).
The failed initial implicit runR reduction and two beta-rewrite probes are raw
failed evidence only; the corrected kernel proofs use no sorry/native shortcut
or raised proof/fuel/node/test/time/stack/resource budget.

The C26 complete cached FAIL124/120.700 remains FAILED with final post-toolchain
receipt absent, despite all542 reports. This new source consumer is no timing
repair. No unchanged aggregate/raw/full/root/held retry occurred. Current
expanded32-owned/36-fresh-source full confirmation remains pending; previous
35-source FAIL124/120.908, broad-root124/120.609 and all original/later full300s
failures remain. TestSuite/sort are unreached. Fresh per-file/cache preparation,
type/axiom checks and integrity inventory are not those mandatory full gates.
Normal/strict docs raw1 remain; complete current/publication/frozen findings are
compared separately, with incoming reserved historical findings not rewritten.

ALL original Work1–6 and Backfills A/B remain PARTIAL. This advances G37.01
caller/result/reference views, G37.03 finite witnessed dispatch and scoped local
unwind/Backfill A; it does not close general target/runtime/storage frames,
uncapped recursive simulation, dependent/full-signature lowering, arbitrary
multi-statement/ref-result candidate export, early-control/general mixed-loop
certificates, word-frame/live-byte-journal/world or transient/callback coupling.
Further owned post-call rebind/sequence and body/unwind proof-cost work is ready;
no independent-work exhaustion or full assignment/integration claim follows.
Exact module hashes, dependent signatures, client invariants, required producer
facts and a NEW committed parallel package belong to the final handoff.


Final source controls: layers/imports/orphans/trust and both exact dynamic driver
coverage/fail-fast scripts pass. All72 original guard negatives and six new
ordered16-report guard corruptions reject, with actual report provenance stated:
current fresh Endpoint12 reports, other17 unchanged checked objects and their
C26 actual builtin logs. This is not a new complete timed542 audit. New producer
source/object and client-object tamper controls reject before Lean10.524s and
restore exact bytes. The current full input integrity inventory is separate
from the unresolved complete aggregate gate. No affected failed workload was
rerun or relabelled. Independent read-only source finder/skeptic both PASS with
no findings; final exact committed-artifact reviews are recorded in the handoff.

## Continuation28 — caller views through memory-return rebind and suffix

Partial original Work1/G37.01, Work3/G37.03, Work4/G36.01 and Backfill A/B
progress. `CallerTail.program_environment` derives an entire captured caller
view from the published `Prog.run_frameM` local projection. `environment` and
`alias` invert actual call-plus-tail execution and compose the genuine entry,
body and tail heap extensions. Only the tail requires the unchanged
`withinM .nonpayable` guard and explicit static protected-index write exclusion.
The callee may mutate old heap contents. There is no `Heap.Keeps` conclusion.
`selected_target` consumes the actual public finite selected-arm certificate,
selection/execution equations, input `StateRepr`, frame room and reached-cost
`AllocationInput`; it derives real target execution, represented dropped frame,
stack, BaseExtends, GrowsAllocator and all protected old pointer cells. It does
not assume output alias preservation or change compiler admission.

The existing generated CF2 memory-return fixture now has a nonempty witnessed
client `MemoryDispatchChecks.ProtectedTail`. Its actual second candidate is
call/rebind/nil: return old object0, then rebind caller result destination0 from
private default2 to old0. The view excludes exactly that overwritten destination
and retains argument5, old object0, tag2, unrelated object1, two more aliases0
and marker42. The actual callee mutates old array[2,7,11] to[2,12,11], preserves
unrelated[2,23,29], leaves defaults2/3[0], and creates private4[2,99,101]; count
becomes11. The entire callee body fails the allocation-only `withinM` guard,
while its real rebind tail is admitted. Negative controls show the whole caller
environment changes and protecting the written destination is invalid. The
actual frontend suffix then exports the returned reference and the view theorem
uses the exact composed extension `chosen.ext.trans finished.ext`. Existing full
ordered22-cell target endpoint, cost7+4=11/cursor139/stack77 and every previous
fixture/negative remain unchanged and separately checked.

The generic target law is checked; a new combined concrete target/view theorem
is NOT delivered. Multiple distinct attempts reached the enforced12GiB cap
(exit137), including the final attempt reusing the old closed target endpoint.
Their source and raw receipts remain in continuation28 evidence. Broad rewrite
attempts for the new source suffix also hit137; the SAME source theorem checks
in2.998s using explicit equality composition and the checked local helper.
No claim of a uniquely proved OOM cause, no raised budget, and no failed probe
is a proof. This new source repair is not a measured repair of the older
complete validation workload and does not justify retrying its failed gates.

Actual14 new builtin axiom sets are separately pinned in
`tests/internal-flow/check-caller-tail-axioms.py`; original542 types/reports,
85 tuple types,18 registry entries/17 mathematical fixtures and previous
separate guards retain their exact statements/order. This is kernel evidence
for intrinsic/abstract Evm execution, not external compiler/bytecode/gas/world
agreement. Guard formatting initially mismatched actual line breaks (exit1),
then was corrected to exact builtin output. No new trust primitive.

CLI per-file/focused fallback is used because no Lean MCP diagnostics are
available. Final command/resource/source-preservation and independent source
and committed-artifact review results are bound in the immutable handoff.
The earlier complete cached124/120.700, raw124/120.908, full124/300s,
broad/prerequisite failures and raw normal/strict docs1 remain failures.
Current expanded33-owned/37-raw complete confirmation is pending. Documentation
comparison remains current=publication/previous complete logs, with frozen
historical46missing versus48current plus incoming reserved ambiguity: this is
not a green global gate or exact frozen equality.

PARALLEL-INTERFACE exports committed dependent signatures and the actual CF2
client for read-only consumption in private dependency worktrees. No peer
checkpoint was supplied or silently imported; public producer099bfbe185731c354b12a40f28ccf5d98534c779
remains unchanged. All28 preceding seals are preserved. No push/merge/PR or
goal reset/reactivation/completion. All six original Work items and both
Backfills remain partial. General unbounded runtime recursion/full dependent
dispatch, early-control/general mixed-loop body certificates, word-frame/live
byte-journal/world and target transient/callback producers remain open. Concrete
large target assembly and older proof/audit performance engineering also remain
owned ready work; independent work is NOT claimed exhausted.

Continuation28 validation/reviews: fresh guarded client23.636s;33-module import
closure2.539s; original542 imported kernel types2.992s; focused source/toolchain
bound import11.421s; new14 actual axiom query3.192s; original separate
7+6+5+15+3+11+16 reports rechecked. Driver/layer/import/orphan/trust checks,
72old and6new guard countercontrols, three source/object cache-tamper controls
(9.272s), final complete input integrity inventory(6.117s) and actual dependent
signature query(1.466s) pass. Inventory is not aggregate validation. Runtime
Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs passes1.640s under the same cap.
Independent read-only finder and skeptic source/final-source reviews both PASS,
no confirmed findings, neither using Lean/server/builds/writes. Final committed
artifact reviews and all actual resource receipts are in the handoff. All old
mandatory failed gates remain explicit; no new full validation claim.

## Continuation29 — actual reached target caller-view addresses

Partial original Work1/G37.01, Work3/G37.03 and Backfill A progress.
`CallerView.by_id` reconstructs the intrinsic optional typed reference from its
observed object ID (no axioms); `reference` eliminates a genuinely captured
caller view. `represented` derives every selected old-reference target cell
from that view, actual reached `StateRepr` and `BaseExtends`.
`different_array` derives distinct primitive-array target addresses from the
reached representation's actual heap separation, including empty default
objects whose length header still occupies a cell. These are typed elimination
laws, not another evaluator, assumed compiler simulation or content frame.
For generic use, the captured view and reached representation remain explicit.

The real generated memory-return client now discharges those inputs in
`ProtectedTail.middle_endpoint`. It obtains the actual prefix/candidate target
runs, reached representations and base extension from the existing closed
endpoint, and the view from C28's actual call/rebind execution. No desired
midpoint, alias equation or capacity is supplied. The endpoint quantifies ALL
protected old memory references. `old_inputs` reconstructs actual typed
references by projection of the COMPLETE existing prefix observation; it does
not rerun the prefix. `middle_snapshot` proves the ordered cells[6,4,3,2] are
[old0,other1,old0,old0] at their ENTRY addresses, and rejects confusing cell6
with reached private4, unrelated1 or default2. These negatives use the SAME
successful reached target witness and genuine heap separation; no missing
Input/frame premise is mislabeled runtime rejection. Existing full22-cell
post target observations/cost11/cursor139/stack77, all source/private-object
observations and previous controls remain exactly unchanged.

This narrow compiled middle theorem is not the larger original combined
22-cell/post-view/middle-pointer endpoint. That SAME larger statement remains
unproved: new small reference/representation boundaries checked, final-cell
consequence checked2.464s, endpoint elimination alone1.474s and type-only
checking1.926s. Three distinct conjunction assembly repairs still hit the
12GiB cap (exit137,24.104/25.305/26.683s), including explicit reached
base/machine arguments. They are retained failed probes, not substituted
proofs or evidence of a uniquely established cause. The actual narrow target
endpoint with explicit reached arguments checks2.637s; the populated snapshot
and new module check3.541s. No net speedup of older complete gates is claimed.
No unchanged failed heavy gate was retried.

Initial diagnostic reserved-token binders and attempts to use an absent
Decidable equality instance/rfl for typed runtime references failed (exit1).
The final inputs instead use the kernel-proved optional-reference identity
law and the existing complete prefix fact. Failed sources/diagnostics including
sorryAx generated by failed elaboration are evidence ONLY, never deliverables.
Actual8 new builtin axiom sets have strict independent guards; old542 reports
and imported types,85 tuple types,18 registry entries/17 mathematical fixtures,
prior separate7+6+5+15+3+11+16+14 guards and every expected vector/order remain.

No whole-lane or general function-dispatch closure: unbounded source/target
recursion, dependent signature lowering, early-control/general mixed-loop
body certificates, byte-journal/world and target transient/callback producers
remain open. Larger concrete assembly and old proof/audit performance work
also remain owned ready work; independent work is NOT declared exhausted.
The original goal identity/blocked status remains unchanged. No push/merge/PR
or reserved implementation/public admission changes. Published prerequisite
099bfbe185731c354b12a40f28ccf5d98534c779 remains the actual consumed source;
no peer bundle was provided or silently imported. A committed interface/bundle
will expose these actual narrow facts for private dependency-worktree staging.

CLI per-file fallback is used because no Lean MCP diagnostics are available.
All new Lean checks retain-j1/LEAN_NUM_THREADS1, canonical writer/compiler
locks, aggregate12884901888B/no-swap, OS/disk headroom and original proof/time
bounds. Only exact receipt-authenticated own stopped containers were cleaned.
All29 previous seals and old raw failures remain. Current34owned/38raw complete
confirmation is pending. Retained complete cached124/120.700, raw124/120.908,
full124/300s and broad/prerequisite failures remain failed; TestSuite/sort
unreached. Raw normal/strict docs1 remains failure; complete current equals
previous/publication, frozen46missing versus48plus incoming reserved ambiguity
remains distinct from zero new owned findings. Scoped passes do not waive them.

Continuation29 validation/reviews: actual Lean4.24.0/Lake5.0.0-src+797c613
and KeySort2jobs pass0.886s.34-module closure0.915s; complete current guarded
Endpoint source22.481s; old542 imported types2.976s; focused bound import10.853s;
actual new8axiom query2.458s. Prior separate7+6+5+15+3+11+16+14 queries rechecked.
Structural/layer/import/orphan/trust/driver checks,72old+6new guard negatives,
three cache source/object corruption controls11.254s and final full input
integrity inventory7.512s pass. Inventory is not complete aggregate validation.
Actual committed-signature query2.309s. A real diskErrno28 interrupted the host
script before control-directory creation; initial outputs/transcript retained.
Removing only receipt-authenticated stopped own containers restored5.6GB,
then affected host/control checks completed; no cache/evidence deletion.
Independent read-only finder and skeptic source/final-source reviews PASS,
no findings, neither running Lean/server/builds/writes. Final exact-commit
artifact reviews/checksums are in the handoff. No full-lane completion claim.

Continuation29 artifact finder correction: the original artifact review found
that handoff/metadata omitted bundle prerequisites. Final metadata/handoff now
explicitly mark the Git bundle incremental, NOT standalone, and enumerate all
six required commits:127c2ee59de16971e45b08a2def54f4e5fae8e2a,
f4dee4a29c2e208b36db4a4161a4723c735cd775,
040e59d30a6726fa4f9fee831695eeaa4027ede1,
204eb1545cbf57e436196e4cba346075515b7279,
2fe1f8932f96be15b00df03ba2cde46f64a87758,
443d1f614ebf92d5c553c014a07ee3553bb5058a. Consumers must possess those
commits; an archive/bundle alone does not establish combined-tree validation.
This correction changes documentation/artifacts only, preserving every checked
Lean source/type/report/observation and the original review-set/interface seals.

## Continuation30 — share actual tuple frame/cost proof inputs

Owned validation/proof-engineering progress; all original Work1–6/Backfills A/B
remain partial. The SAME tuple consumer programs, signatures, result order,
old/private objects, physical cells, protected stack/cursor/sentinel, frame/cost
values, refusal/negative cases and all85 mathematical types/reports remain.
Only `TupleMemoryCalls.Composed.represented` and `checked_input_endpoint` proofs
change: they project already kernel-proved `exact_frame_cost`/`exact_cost_frame`
values instead of repeatedly deciding concrete producer fields. The unchanged
`expandedProducer` definition and exact vector theorem move earlier, without
circular dependency. Actual prefix execution and `GrowsAllocator.nextInput`
still derive every reached representation/capacity; no desired midpoint or
simulation premise is supplied. The checked compilation's actual memoryCalls
constructor is unfolded for its isMemoryCalls/requiredFrame/allocationCost
fields. No public selector/admission or intrinsic semantics changes.

One valid same-flags profile pair (-j1,stack131072,profiler=true,threshold100)
checks42.005→38.840s; represented2617→1300ms, checked-input2785→1298ms.
Normal fresh fixture preparation separately checks45.528→41.819s with all85
actual original axiom reports. These are single measured pairs, not timing
or complete-gate guarantees. All542 imported kernel types remain exact.
All old theorem statement headers and all three ordered actual report
invocations are byte-identical; original pins and guards are unchanged.

The measured repair justified ONE new complete38-source attempt at unchanged
120s: FAIL124/120.796s, reached TupleMemoryCalls after all preceding targets.
ONE complete registered cached attempt at unchanged120s also FAIL124/122.079s:
all542 actual builtin reports were emitted, but only eight post-import fixture
checks completed and no final full-toolchain receipt exists. Neither failure
is green or inferred green from individual checks/report counts. Current-input
integrity, guard slicing or later untimed checks cannot waive those failures.
Original full300s, broad/default-root/prerequisite failures remain; this fixture
repair does not repair held default-root producers, so no unchanged full retry.
TestSuite/sort remain unreached. Existing raw normal/strict docs1 remains a
separate failure with previous/publication equality and frozen incoming debt.

Diagnostics retained: two broad marker copies failed parser/guard-docstring
formatting (exit1); the valid focused profile leaves all guards untouched.
Profiler stderr interleaves a builtin axiom report, so the strict85 parser
correctly rejects that diagnostic stream; it is NOT axiom-gate evidence.
Fresh normal preparation supplies the real85-report pass. An initial adoption
preservation check expected run_elab rather than print_checked_axioms and failed
before source write; the subsequent misleadingly named prepare checked the
UNMODIFIED original fixture (45.528s baseline). Its source/object binding and
clarification remain. Corrected adoption checks the actual three report commands
and uses a distinct output directory, preserving every earlier raw log.

Runtime Lean4.24.0/Lake5.0.0-src+797c613/KeySort2jobs pass under the existing
serial12GiB/no-swap cap/writer/compiler locks. No heartbeat/fuel/node/time/stack
budget increased; only authenticated stopped own containers cleaned, no cache
or prior evidence deletion. Both independent read-only source reviewers PASS,
no findings and no Lean/server/builds. Final checks/reviews/actual committed
artifact hashes are in the handoff; all30 preceding main seals are preserved.

All general unbounded source/target recursion, dependent dispatch/lowering,
early-control/general mixed-loop body certificates, byte-journal/world and
independent target transient/callback producers remain open. The larger C29
combined target theorem remains failed, not proved by this performance repair.
Actual repeated import/dependency-key scanning in the OWNED cache driver is
ready engineering work: the failed batch completed Lean's542 reports but timed
out during fresh per-fixture post-key checks. Any repair must retain actual
full source/object reads and complete before/after toolchain binding, all18
fixtures/all542 reports and unchanged120s; inventory alone is not a gate.
No independent-work exhaustion, full-lane completion, goal reset/reactivation,
push/merge/PR or reserved-source edit. Published099bfbe185731c354b12a40f28ccf5d98534c779
remains the consumed producer; no peer package supplied or silently imported.

Continuation30 final scoped evidence: standalone UNCHANGED original542 builtin
queries pass95.527s/120s; all names/order/sets and72corruption controls pass.
This independent mathematical audit does NOT pass the complete cached gate.
All542 imported kernel types pass2.983s. Prior separate7+6+5+15+3+11+16+14+8
axiom reports rechecked exact; actual normal85tuple reports pass. Three cache
source/producer-object/client-object corruption controls pass10.446s with exact
restoration; complete input integrity inventory passes6.985s (inventory only).
Structural/layer/import/orphan/trust and dynamic no-Lean raw/cached driver
coverage/fail-fast controls pass. Actual dependent signature query1.411s passes
after correcting two filename-as-namespace lookup errors; failed query retained.
Initial audit-harness byte comparison failed only on blank separators, before
execution; corrected comparison checks every original import/query line and
copies the actual unchanged harness byte-for-byte, omitting no report.
Independent finder/skeptic source reviews PASS, no findings; final committed
artifact reviews/checksums and complete actual gate receipts are in handoff.
No kernel proof, external compiler/EVM agreement or entire lane completion is
inferred from profiling, metadata, inventory, report counts or these scoped
passes. Every original failure/seal remains.

## Continuation31 — preserve fresh reads, memoize pure import parsing

Owned cache-validation implementation; no Lean production/test source, theorem,
program, observation, supported profile, refusal, pin or proof budget changes.
The existing fixture import scanner body is byte-identical, renamed/exported
`scanFixtureImports`. `imports` memoizes successful results by the ENTIRE exact
freshly-read source text (no digest/collision premise) and returns a fresh array
copy, because each traversal pops its root pending list. Failed parses remain
errors, changed text obtains a distinct entry, and caller mutations cannot
poison later traversals. No file bytes/hash/key/mtime or toolchain snapshot is
memoized. The complete source/object read, hash, dependency, key, guard, CLI,
batch and before/after toolchain code tail remains byte-identical.

Real Node CPU profiling of the previous actual fixture check identified key
work; the complete input-only diagnostic retained all18 real fixtures and two
passes of actual hashes/keys. Before21.956s versus candidate18.773s, every key
and input count identical both passes. This is inventory/performance evidence,
NOT Lean validation or a gate pass. `check-import-cache.mjs` separately passes
241 controls over231 actual project sources from all18 bindings, plus nested
comments/quotes, changed text, repeated parse errors and returned-array alias
mutation. These parser controls never substitute for source/kernel checking.

The checker file hash correctly invalidated old bindings. Actual checking
rejected before Lean at the stale AxiomReports dependency. An initial control
expected the later leaf rejection and failed its too-specific assertion;
corrected control checks the EXACT observed dependency rejection and confirms
no Lean invocation. Original raw failure/source retained; this is cache
provenance rejection, NOT runtime rejection. An initial attempt to save CPU
analysis without filesystem escalation failed read-only before writing; the
authorized evidence write then succeeded. No source or gate bypass.

Every registered fixture was then freshly checked from actual source in real
dependency order, each with the unchanged120s bound, serial-j1/LEAN_NUM_THREADS1
under hard12884901888B/no-swap and the canonical writer/compiler locks. All18
source preparations (17 mathematical fixtures plus metadata tool) and all542
original reports pass. Old metadata was NOT simply re-keyed; actual Lean
processes generated each checked object/binding. Exact old tuple85 and other
original68/59/42/27/... inventories retained. Only authenticated stopped own
containers were removed after receipts; caches and earlier evidence preserved.

COMPLETE registered cached gate now PASS: exit0,117.230s strictly below unchanged
120s, all18 fixtures/all542 actual builtin reports, complete before/after
11575-entry toolchain maps with identical SHA256
617fd68210c0b46750ab92f863878665875839568f23d99320f79053956360f1.
The final batch receipt exists. This resolves the current cached-gate blocker;
it does NOT turn C30's124/122.079 or older failures green. All1392 tracked Lean
sources are independently verified unchanged. All542 imported kernel types
pass3.516s; prior separate7+6+5+15+3+11+16+14+8 axiom reports rechecked exact.
Six precise source/import/object/checker/pin corruption controls reject before
Lean and restore all bytes (18.256s). Complete post-control input inventory
passes6.660s, separately from the real passing timed gate.

Actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs pass0.903s. Exact actual
owned/fixture import-refresh phase passes1.420s. No-Lean dynamic drivers retain
34owned targets,23fixture imports,18fixtures/all542pins and raw38targets with
failure at every required point; no target/report removed. Final structural,
report corruption, doc, source and artifact reviews/receipts are in handoff.
No Lean MCP diagnostics are available; no Lean source edited in this step.

The raw38-source gate remains C30 FAIL124/120.796s and the original full300s,
broad/default-root/prerequisite failures remain FAIL; TestSuite/sort unreached.
This cache-only change repairs neither, so no unchanged raw/full retry. Raw
normal/strict docs1 remains historical/incoming failure, with separate complete
previous/publication equality and frozen46missing versus48plus ambiguity; no
new owned findings is not global success. All six original Work items and both
Backfills remain partial. Unbounded recursion, dependent source lowering,
early-control/general mixed loops, word-frame/byte-journal/world and target
transient/callback producers remain open. Larger combined target conjunction
also remains resource-failed. Fresh raw CLI process/environment overhead is
ready owned engineering to investigate next, preserving separate fresh Lean
processes/all38 source checks; rejected persistent-frontend137 experiments are
not being resumed. No independent-work exhaustion or completion claim.

All31 preceding main seals remain immutable. No push/merge/PR, reserved edit,
new goal, reset/reactivation/completion or unmerged dependency intake. The
original blocked full-assignment goal remains unchanged. Published099bfbe185731c354b12a40f28ccf5d98534c779
is still the consumed producer; no peer package supplied. An exact committed
PARALLEL-INTERFACE source/signature/bundle checkpoint supports private peer
worktrees; final combined-tree validation remains mandatory. Both bundles
explicitly disclose their incremental prerequisites and are not standalone.

Continuation31 final scoped controls: all original542 exact guards/order and72
report corruption controls pass on the ACTUAL completed cached audit. Structural,
layer/import/orphan/trust and both dynamic driver coverage controls pass. All
1392 Lean sources, every original pin/guard and both complete target drivers
remain byte-identical after adversarial controls. Actual dependent-signature
query passes1.420s. Six source/import/object/checker/pin freshness countercontrols
pass with exact error-class assertions and byte restoration; no unexpected
Lean invocation. Complete post-control inventory passes6.660s separately from
the real117.230s gate. Original raw normal/strict documentation logs remain
exit1 and complete previous/publication-equal, with no new owned findings.
Both independent early protocol reviewers PASS, no freshness/array/error issues,
neither running Lean/server/builds/writes. Final source and committed-artifact
reviews and checksums are bound in the handoff; no whole-lane completion.


## Continuation32 — caller pointers after a real extended-context suffix

`CallerView.reference_drop` and `represented_drop` consume the actual context
extension, captured dropped caller environment, reached `StateRepr` and
`BaseExtends`. They expose the transported typed reference and its entry target
address while output result/local binders remain. They assert no heap-content
invariant. No syntax, evaluator, compiler admission or reserved producer changed.

The populated `FiniteDispatchEndpoint` client now proves
`ProtectedTail.final_alias_after_drop`, `final_other_is_not_old`, `final_pointers`,
`final_target_pointers` and `final_target_observed`. The closed target witness
comes from the real compiled allocating prefix, selected memory-result call and
allocating suffix. It exposes BOTH actual prefix/final representations, composed
base extension, growth11, stack77, cursor139, all protected final-context pointer
cells, the same complete ordered22-cell observation and captured final caller
view. The old object is actually mutated by the callee; unrelated/private/default
objects and all previous observations and controls remain distinct. The separate
stronger middle-machine-plus-final conjunction is not silently counted proved.

Finder and skeptic reviewed independently without Lean/builds. The skeptic
identified a missing exposed prefix representation; the theorem now includes it
and the composed `BaseExtends`. A genuine implicit-polymorphic type error in the
strengthened proof was retained, then fixed with an explicit dependent type.
Final actual fixture preparation passes24.130s/120; imported composition probe
passes3.186s. Actual seven new builtin axiom sets are pinned separately; all542
original imported kernel types (including85 tuple types), reports/order/pins and
retained7+6+5+15+3+11+16+14+8 scoped axiom queries remain unchanged.

Owned raw-driver engineering shares one genuine `lake env` setup but launches a
fresh separate `lean -j1 --tstack=131072 SOURCE` for every original34 owned files
and four original fixtures, with inherited stdin, shared output/error log fd,
unchanged source order and failfast. No cached main-source import or persistent
frontend is used. Before/after source/config hashes and target membership are
checked. No-Lean controls cover every failure position, setup/spawn/signals,
environment/log bytes and private-tree membership mutation. Actual fresh-source
controls reject invalid current source despite a valid previous object and
retain separate private scopes. The four-file diagnostic comparison does NOT
establish an end-to-end speedup (outer4.905s versus4.950s).

The changed COMPLETE raw gate still FAILS124/121.214 at TupleMemoryCalls.
The COMPLETE current cached command returns0 with18fixtures/542actual builtin
reports and complete11575-entry before/after toolchain equality, BUT outer
121.091s exceeds the unchanged120s bound: its strict bounded gate is FAILED.
The prior C31 genuine117.230s pass remains historical, not a pass of this tree.
No unchanged retry follows. Original full124/300, broad/raw/prerequisite137/124
and documentation normal/strict1 remain retained failures; TestSuite/sort are
unreached. Current complete docs findings remain previous/publication-equal,
not frozen-equal/global success. Runtime Lean4.24.0/Lake5.0.0-src+797c613 and
actual KeySort two-job output pass independently.

All Work1–6 and BackfillsA/B remain partial. Unbounded target/source recursion,
general/dependent dispatch lowering, early-control/general mixed loops,
word-frame/live-byte-journal/world and target transient/callback applications
remain genuine producer obligations. The original blocked goal stays unchanged;
no independent-work exhaustion or whole-lane closure is claimed. Exact committed
module hashes, dependent signatures, witnessed clients and incremental bundle
prerequisites are exported in a new PARALLEL-INTERFACE checkpoint for private
V13/V14/V16/Yul worktrees. No peer package was supplied or imported, no reserved
edit or push/merge/PR occurred, and every previous seal remains immutable.


## Continuation33 — protected primitive locals through the reached frame

Continuing original Work1/Work4/BackfillA after C32, `CallerView.value_drop`
projects every protected intrinsic primitive from the actual captured dropped
caller environment. `represented_value_drop` consumes the real reached
`StateRepr.core.vals` and derives the existing `ReprV` relation to that ENTRY
caller value. No arithmetic uniqueness, new evaluator, simulation oracle or
heap-content invariant is introduced; all primitive types stay intrinsic.

`ProtectedTail.final_target_values` retains the SAME C32 actual prefix/final
representations, complete ordered22 cells, composed `BaseExtends`, growth11,
stack77/cursor139, captured final caller view and every protected reference,
and adds every protected primitive encoding on that same reached machine.
The inhabited `final_wrong_scalar_destination` uses that complete endpoint,
not another replay: protected uint cells7=5 and5=2 are distinct and cannot be
swapped. The original reference, allocation, private/default-object, mutation,
refusal and other countercontrols and all542 original reports remain intact.
This is typed finite local-frame transport, not full-signature admission or
unbounded target recursion, early-control, world or transient correctness.

Actual generic prototype passes2.713s; core build3.581s and complete changed
fixture source preparation27.810s pass at the original120s per-process bound.
Four actual new builtin axiom reports are pinned separately: source value law
uses propext; represented value law uses propext/Quot.sound; the two inhabited
clients use the existing propext/Classical.choice/Quot.sound set. All original
542 imported kernel types (including85 tuple types), C32's seven types/axioms,
and retained scoped sets are checked without changing pins or report order.
Actual runtime/import/structural/guard evidence and independent read-only
finder/skeptic source/artifact reviews are bound in the new handoff.

No demonstrated performance repair or new upstream prerequisite justifies
repeating a failed aggregate. Therefore raw/full/current-cached timing gates
are NOT rerun or claimed passed. C32 complete cached command0/121.091 exceeds
strict120 despite all18/542/11575-entry final binding; C32 raw124/121.214,
original full124/300 and all earlier failures remain retained. Current complete
aggregate validation remains unfinished; focused checks or input inventory
cannot replace it. Normal/strict docs raw1 and separate publication/previous
findings equality remain distinct from frozen/global success. No target, fixture,
report, budget, profile, predicate, observation or source refusal was removed.

All original Work1–6 and BackfillsA/B remain partial, with the same exact missing
unbounded/dependent/early-control/general-loop/byte-world/target-transient
producers and remaining stronger middle-plus-final assembly obligation. No
independent-work exhaustion, full closure, goal reset/reactivation/completion,
reserved edit, unmerged intake or push/merge/PR. C32 and every earlier seal stay
immutable. A fresh exact-committed PARALLEL-INTERFACE exports these narrow typed
contracts and populated clients for private peer staging; final combined-tree
checks remain required and open.


## Continuation34 — storage result paths and reached fragile liveness

`CallerView.storage_alias_drop` transports exact typed storage roots/paths
through a genuinely captured extended-context view. `represented_storage_drop`
requires the actual reached .ok flag and derives `PathSlot C true`;
`represented_fragile_drop` requires the actual reached .fragile flag and derives
BOTH `PathSlot C false` and `out.st.storage.findLive r = some sv` from the real
reached representation. No liveness premise, cast to .ok, new evaluator or
reserved predicate is added. `dead_not_fragile` shows that a retained reference
with actual findLive=None cannot acquire a fragile flag under those same real
representation/capture facts. It does not invent dead-code admission.

The populated `FragileReturnChecks.CapturedResult` client removes the actual
private memory binder with `returned_reference`, then couples that exact callee
reference to the actual compiled call's .slot word, typed indexed path, source
rows/index1 observation and DERIVED reached liveness. All prefix/call/suffix
executions, reached representations, base extensions and final protected stack
come from existing checked stages. `result_view` is reflexive at the reached
RESULT boundary: this concrete client does NOT prove general pre-call caller
storage-alias preservation or alias invariance through an arbitrary suffix.
The word-kind countercontrol rules out every memory .val pointer on the same
successful call witness. The actual shrink countercontrol keeps a syntactic
Some reference while findLive=None, the existing fragment is .dead and the
existing selector refuses export. All prior pop/rebind/OOB/refusal observations
and complete ordered vectors remain unchanged; no runtime rejection is inferred
from a failed compiler/input premise.

The first prototype's whole-suffix rfl proof failed and remains evidence only;
it is NOT a proof of inequality or a missing-producer claim. The precise private
result-export identity passes2.011s. The first fixture check failed on missing
Inhabited Fl and branch-rewritten equalities; raw source/logs are retained.
The fix uses optional list lookup and the actual rewritten equalities, with no
flag-instance/semantic change. Corrected actual fixture preparation passes
41.919s/120, affected dispatch preparation26.108s, core2.551s, per-file2.498s
and focused all-owned/fixture import closure1.669s. Nine actual new axiom reports
are pinned separately; all542 old kernel types and C32/C33 scoped sets remain
exact. Lean4.24.0/Lake5.0.0-src+797c613 and actual KeySort two-job output pass.

Current aggregate/full validation remains pending with C32 strictcached
command0/121.091>120 FAIL, raw124/121.214, originalfull124/300 and all previous
raw/prerequisite/OOM/docs failures retained. No unchanged failed heavy command
is rerun; new semantic facts are not a performance repair or global gate pass.
Normal/strict docs remain raw1 with separate complete previous/publication
findings equality, not frozen/global success. All original Work1–6 and
BackfillsA/B remain partial; general/unbounded/dependent/early-loop/byte-world/
target-transient producers and remaining frame assembly/validation work stay
explicit. No independent-work exhaustion, goal write, reserved edit, unmerged
intake or push/merge/PR. All earlier seals remain immutable; exact committed
source/signatures/witness/bundle are supplied for private parallel consumers,
which still require actual combined-tree validation. Independent read-only
finder/skeptic source and committed-artifact reviews are bound in the handoff.


## Continuation35 — heap mutation frames locals, not old contents

New `Backend/InternalFlow/MemoryStoreLocalFrame.lean` proves `CallerView.memory_store_environment`
by inverting ACTUAL successful intrinsic assignMem execution and consuming the
published typed weakening law. Every local is retained up to the real returned
heap extension; no withinM relaxation or Heap.Keeps statement is made. Core,
module-map and docs registration are append-only.

The populated `FragileReturnChecks.MemoryLocalFrame` client starts at the real
completed storage-prefix/memory-call/caller-suffix state. A genuinely compiled
public Memory.compileStmt/Calls.plainStmt store writes OLD object0 element0=91.
The actual endpoint exposes both target INPUT and OUTPUT representations,
protected stack, BaseExtends, reached GrowsAllocator0, every old memory-reference
address and every primitive encoding. The input is derived from the existing
whole_endpoint, not supplied as a desired midpoint. Complete source contents
change from [[2,7,84],[1,23],[2,99,101]] to [[2,91,84],[1,23],[2,99,101]];
wrong_content_frame rejects unchanged contents while original_guard_rejects
retains withinM.nonpayable=false. This demonstrates local noninterference under
real old-object mutation without claiming arbitrary callee/whole-state framing.
These are source observations plus a relational StateRepr target endpoint;
no new complete numeric target-cell snapshot or external EVM test is asserted.

The imported prototype passes2.465s after retained namespace/product-projection
errors; failed sorryAx reports are FAILED evidence only, never proof coverage.
Generic core build passes2.149s; actual changed source preparation44.103s and
strengthened pointer/value preparation41.865s pass at unchanged120s bounds.
Seven new actual axiom sets are pinned separately (existing standard axioms).
All old542 kernel types and C32/C33/C34 scoped type/axiom sets remain unchanged.
Actual per-file/import/runtime/guard/resource evidence and independent read-only
finder/skeptic source/artifact reviews are bound in the handoff.

No performance repair or changed held prerequisite justifies an aggregate retry.
Current raw/cached/full validation stays unfinished with all C32 strictcached
0/121.091>120, raw124/121.214, originalfull124/300 and prior failures retained.
All original targets remain; the raw driver now also discovers the added owned
module. Focused source checks/input inventory never substitute for complete
aggregate/full gates. Raw docs normal/strict1 and separate complete previous/
publication comparison remain explicit, not frozen/global success.

All Work1–6 and BackfillsA/B remain partial. General/unbounded/dependent/
early-control/general-loop/byte-world/target-transient obligations, stronger
frame assembly and validation work remain. In particular, this standalone
successful store is NOT a proof of the earlier entire caller-suffix storage-
alias equation. No independent-work exhaustion, goal write, unmerged intake,
reserved edit or push/merge/PR. All previous seals remain immutable; exact
committed source/signature/witness bundles support private parallel consumers,
which still require actual combined-tree validation.


## Continuation36 — actual mixed-store suffix alias transport (partial)

`Backend/InternalFlow/MixedStoreAliasFrame.lean` proves operational storage-alias
preservation through actual persistent assignment, a distinct typed primitive
assignment and heap assignment. The proof inverts the real three statement
executions; its sole execution premise is their actual successful composed run.
It neither requires nor proves heap-content preservation or alias liveness.
The existing withinM exclusions are unchanged.

The existing populated indexed-return fixture now proves MixedSuffix.alias_frame
through its SAME original suffix, exact_body_result after private local removal,
and final_slot on the SAME actual compiled whole endpoint. Its final computed
fragile classification and reached StateRepr supply the real slot, path and
findLive witness. Wrong-element rejection is transported from the existing
successful result baseline. Original complete observations, all542 original
kernel theorem types/85 tuple types, all18 fixture entries/report order and prior
C32–C35 scoped axiom sets are preserved. New eight actual axiom reports have a
separate exact guard, including missing/duplicate/order/error corruption controls.

The first new target-slot assembly hit the unchanged200000 heartbeat limit;
that failure remains raw evidence. Direct elimination of actual reached
Sim.fragile replaced only the costly thin/drop packaging and passes the SAME
statement at41.042s for the complete actual fixture, peak sampled RSS1992168KiB.
The generic composition probe passed1.973s. Per-file2.727s, focused import
closure2.316s, new actual axiom query2.520s, exact old scoped sets and all542
kernel type preservation pass. A missing output-directory setup invocation
failed exit2 and is retained separately from its corrected focused pass.
Actual Lean4.24.0/Lake5.0.0-src+797c613/KeySort output passed under serial-j1,
LEAN_NUM_THREADS1, hard12GiB/no-swap and writer/compiler locks.

Independent read-only finder/skeptic source reviews passed without builds.
Artifact reviews and exact committed identities are recorded in the NEW immutable
continuation-36 handoff/evidence/checksum set under /workspace/scratch/v12-flow-calls.
All36 earlier main seals are preserved. All original Work1–6/BackfillsA–B remain
partial: finite ordinary frame consumers are not general runtime/unbounded
recursion/dependent dispatch/general early-control loops/byte-world/transient
closure. Mandatory full124/300s, raw124/121.214s, strict cached121.091s despite
exit0, prerequisite/broad/OOM failures and raw docs1 remain failed evidence.
Current complete aggregate is pending: this semantic proof is not a demonstrated
performance repair and does not authorize an unchanged failed heavy retry.
Complete current docs equal the previous/publication findings, with historical
frozen46/current48 debt separate. Original goal identity/status is unchanged.


### C37 — local-only structured store frames and a real reached target client

`Solidity/Backend/InternalFlow/LocalStoreFlow.lean` adds typed proof derivations indexed by the
existing intrinsic Stmt/Prog. Existing leaves retain BOTH the published withinM
premise and the exact `(t,i.toNat)` writes exclusion. Store leaves consume
actual storage/memory environment laws; sequence, block and branch proofs
compose real successful executions and dependent heap weakening/drop. The
conclusion preserves only the selected local binding, not old heap contents,
mutability, persistent roots or storage-reference liveness. Plain/fragile slot
consequences consume actual reached StateRepr; fragile findLive evidence is
extracted from Sim.fragile rather than assumed from source identity.

`LocalStoreTarget.program_statement_frames` retains both actual target frames,
BaseExtends, genuine GrowsAllocator and the reached AllocationInput of two
finite checked certificates. Its real premises are source success, initial
representation, frame bounds and summed initial capacity. It does not implement
another compiler or assume a simulation conclusion. The populated ScopedAlias
client begins at the existing real call/suffix state, mutates indexed persistent
storage and an older heap object, reads the mutation into caller scalar x,
allocates a private array, writes55, then drops its memory/scalar binders through
a selected branch and block. The actual source result has storage value91,
heap [[2,7,91],[1,23],[2,99,101],[1,55]], scalars[91,1], memory identities[1,0,0]
and result path rows[1]. No earlier fixture observation is changed.

The actual target client derives the populated prefix frame and capacity5,
executes the existing checked cost3 program, derives remaining capacity2 by
GrowsAllocator.nextInput, then executes the real new compiled branch/block.
The compiler-derived suffix need is8/cost2/fragile. The closed endpoint retains
all three executions, prefix and both reached StateRepr, BaseExtends, growth2,
stack equality, actual checked Input/Agrees, every protected memory address and
primitive representation. It does not claim a new complete numeric target
snapshot, a fixed numeric final cursor, or an unconditional final live alias.
Actual false-branch bare revert, private-marker nonescape, wrong fresh alias,
old content/persistent-write negatives and the rejected written-scalar guard
have explicit positive baselines. withinM remains false for this mutating body.

Both independent read-only reviewers caught one initial generalization error:
the existing-leaf exclusion still named an alias type instead of the actual t.
It was corrected before the generic proof passed; confirmed-review-fix.json
retains the finding. Failed helper applications hit unchanged heartbeat limits;
the successful proof uses separate checked endpoint boundaries and scalar cost
facts. A decomposed proof then exposed missing opaque checked cost/need
projections; named kernel-proved equations fixed those type mismatches. The
failed output containing sorryAx is failed evidence only, never a deliverable.
A distinct stronger old C29 joint endpoint attempt exited137/12GiB and remains
open; its conditional observation preparation is not target closure. The
false-branch test's initial incorrect literal constructor failed and was fixed
to the existing Simple.bool constructor. All raw failures remain preserved.

C37 uses new immutable continuation-37 artifacts and separate exact axiom guards
without removing any previous report/type/fixture. Original Work1–6 and both
Backfills remain partial. General frames/uncapped recursion/full-signature
lowering/general early control and mixed loops/byte-journal-world/target
transient-callback producers remain open. No goal write, publication or reserved
producer edit occurs. Complete current raw/cached/full validation is pending
with previous failed exits retained: this semantic checkpoint is not a measured
repair authorizing an unchanged heavy retry. Raw docs normal/strict1 remain
failures; complete previous/publication equality and frozen historical debt are
separate findings. Runtime, scoped checks, exact identities, reviews and resource
receipts are recorded in the checkpoint handoff, not inferred from this prose.


### C38 — source local-only loop frames from actual typed body plans

`Solidity/Backend/InternalFlow/LocalStoreLoop.lean` consumes C37 ProgPlan without
changing C37 constructors, proofs, withinM or observations. `scoped_step` applies
the typed body plan to actual scopedLoopBody execution, drops iteration locals
and composes genuine heap extensions. `loop_prefix` inducts the existing iterN
for every finite horizon, including running and successful termination. It does
not identify an error with a state. `loop_success` builds the protected-binding
invariant internally from the body plan and applies published TLoop.run_induct:
condition false returns the current binding, condition/body failure remains an
error and divergence has no output state. `loop_statement` connects the same
law to the actual Stmt.loop constructor. No whole-loop preservation equation is
a premise, and no fresh evaluator, loop cutoff, global Heap.Keeps or fragile
alias liveness theorem is introduced. Existing ScopedLoopFrame/CompletedLoopFrame
require withinM and assert stronger heap framing; they cannot discharge this
old-object-writing client's guard, so their laws are reused unchanged elsewhere.

The actual new LoopLocalFrameChecks client starts from the published owned
nonempty caller with two aliases to object0 and protected scalar17. Two true
turns increment persistent/transient values (7,9)→(8,11)→(9,13), write old object0
[7,11]→[9,11]→[10,11], increment counter9→10→11, allocate private objects1/2
containing [10]/[11], and create private scalar77. Every turn drops both private
binders. Exact complete ordered observations pin heap sizes1/2/3, both aliases0,
the counter and protected scalar, storage array[13,17], caller transaction and
balance. The false third test terminates. Both prefix and completed-loop local
frames are derived from actual body plans, including the full thinned protected
environment and actual source statement execution. The same client proves
withinM is false and Heap.Keeps is false: reference identity is preserved while
old contents actually change. A plan protecting the written scalar yields the
false actual10=9 equation and is rejected. Wrong alias/private marker/old-content
controls have the complete positive observations as baselines. Unconditional
storage-reference liveness is rejected using the existing actual shrink/dead
export witness read only, not by duplicating that producer or changing refusals.

A second actual body asserts after allocation/local creation: its first turn
succeeds and has the exact first observation; turn two halts with THalt.panic.
Ordered horizons retain the original class and failure absorption uses existing
iterN_done_le. Panic is distinguished from bare revert, exhaustion and divergence.
An actual out-of-bounds memory-read condition has the model's bare-revert class
before any turn. A false initial condition succeeds without allocation; a real
nil-body true-condition loop has every horizon running and the published prefix
law yields divergence. No failed State is reconstructed, no panic code/bytes
are inferred from an empty data projection, and no rollback/world conclusion is
claimed. The failing variant's first Out is obtained from its own real execution,
not assumed equal to another program's Out. An attempted definitional equality
failed and is retained as raw evidence; ordinary typed-index/beta-rewrite and
closed-condition proof errors were corrected without any budget change.

All C37 files/declarations/542 original pins and its32 new reports remain
preserved; the new fixture and exact scoped reports are additive. Runtime,
per-file/import checks, actual axiom guards, controls, source preservation and
separate independent finder/skeptic reviews are recorded in continuation-38.
All Work1–6 and BackfillsA/B remain partial. This is source/kernel local framing,
not a target loop certificate/Room/Cost/StateRepr endpoint, general mixed-loop
compilation, early return/break/continue, unbounded recursive target execution,
full dependent dispatch or byte/journal/transient/callback/world transport.
No assertion is made that independently ready target/client work is exhausted.
Current complete aggregate/raw/full validation remains pending with the actual
old strict cached/raw/full/prerequisite failures and raw docs1 retained. New
semantic progress alone does not authorize an unchanged heavy retry. Goal
identity/status and all original resource/proof/test bounds remain unchanged.


### C39 — actual represented mixed allocating loop after a real prefix

`Solidity/Backend/InternalFlow/LoopLocalTarget.lean` consumes published
LoopCert.correct unchanged. Its outcome/endpoint retain actual LoopPrefix cost,
StateRepr, stack, BaseExtends and GrowsAllocator, adding the protected thinned
environment and target pointer/primitive facts DERIVED from C38 typed body plans.
Real certificate, initial representation, frame and source-prefix LoopRoom are
explicit generic premises; there is no desired simulation/frame equation field.
The actual producer's bare revert and divergence→abstract fault cases stay
distinct, with no failed State. Two-turn prefix classification derives Room and
exact reached cost from actual body executions, actual stopping condition and
summed allocation input. It does not impose a loop admission/unrolling cutoff.
Storage-only prefix/zero-growth and public compiler-construction helpers reuse
actual compile_exact, source frame and target memory laws; they are proof
boundaries, not replacement compiler/machine semantics.

Both public admission probes for the unchanged C38 body and loop are true.
The new client starts with an empty heap and concrete nonzero transaction and
balance matching C38, runs REAL compiled storage assignments/two pushes, then
REAL checked memory prefix code that creates old[7,11], two aliases and caller
scalars9/17. Its derived input runs the same C38 body/condition twice. Exact
ordered source observations equal C38's zero/one/two vectors. No equality with
C38's separately hand-built entire State is assumed or claimed: a definitional
State-equality probe failed and is retained; that is not a counterexample or a
missing-producer assertion. All representations and input ownership are derived
from actual prefix execution, not supplied as a populated midpoint premise.

The public Loops statement/program selector/code equations are closed using
actual Memory.compileVal/compileProg results and real fragment stability.
Compiler.Compilation.memoryLoops Input/Agrees is derived via memoryLoops_input
and correct, separately from actual Evm.run; no runC/run identification or global
Compiler.compile admission repair is asserted. LoopRoom comes from real nextInput
and all reached LoopPrefixes. Per-turn finite cost2 accumulates to exact loop4,
not the legacy whole-loop allocationCost0. The SAME represented endpoint composes
storage0+prefix3+loop4=total7, with capacity4 at loop entry, need6/frame128,
StateRepr at entry/end, BaseExtends, protected locals and stack[77].

Actual target finite horizons are projections of existing exec/loopIterN; their
success tags rule out every fallback. loopRun_of_iterN connects the observed
finish to the original unbounded target run. Determinism identifies these SAME
machines with the producer's represented endpoint. Full ordered word/root
snapshots cover prefix/turn1/final, caller and private physical cells, sentinel99,
all three objects and roots. Cursor259→261→263; old aliases stay256; private
object pointers259/261 and scalar77 remain physical but are dropped from source
locals; old contents[7,11]→[9,11]→[10,11], fresh contents[10]/[11], roots(p,t)
(7,9)→(8,11)→(9,13), unrelated root/array data preserved in the snapshots.
Negative cursor/alias/destination/fresh order/private frame/old mutation/word-kind
and early-reset observations follow from these complete positive snapshots.

Actual compiled bounds-condition failure yields bare revert. A nonallocating
true nil loop yields source divergence/target fault. A false guard skips the
allocating body successfully and has no reached allocation demand. Wrong frame
and capacity are STATIC premise failures, not runtime rejections. Actual source
panic and nonempty de-00-ad payload baselines remain compiler refusals; they are
not reinterpreted as supported target panic/payload preservation. Root1's word
update is the published abstract word-store relation, not a separate target
transient/transaction/callback world or EIP1153/bytecode/gas adequacy theorem.
No Heap.Keeps, unconditional alias liveness, rollback or general loop closure is
claimed. General early-control, nested/call/recursive loop bodies and full
runtime/dispatch/world/byte/transient producers remain original obligations.

Concrete dependent elimination initially hit unchanged heartbeat limits (one
failed check sampled about10GiB); raw failures remain. Checked abstract result,
cost and construction boundaries fixed those proof obligations without raised
budgets. Exact compiler result projections fixed a separate Input type mismatch.
The failed definitional State equality, parser/type setup failures, all old137/
124/heartbeat/recursion receipts and all previous seals remain preserved. No
unique cause for historical failures or whole-gate performance repair is claimed.

New exact85 builtin reports are additive: old21 fixture entries/618 pins,
including original542 types/85 tuple types and C32–C38 inventories, stay intact.
Current inventory is25 fixtures/703 reports. Scoped/per-file/import/guard/runtime
and independent read-only source/artifact reviews are recorded in continuation-39;
complete current aggregate/raw/full validation remains pending with retained
strict cached121.091/120, raw124 and full124/300 failures. Raw docs normal/strict1
stay failures, with complete prior/publication comparison separate. All eight
original Work/Backfill items remain partial; no independent-work-exhaustion,
goal reactivation/reset/completion or publication claim follows.


## C40 — concrete caller preservation at every reached horizon (partial)

`LoopCallerPrefix.captured` consumes C38's typed per-binding plans and the
actual running/successful source horizon to preserve the complete protected
thinned environment. `represented` eliminates a genuinely reached StateRepr
and BaseExtends into old memory-address and primitive ReprV observations; it
does not produce target execution or representation. Public condition/body
error eliminators preserve ordinary bare revert only.

The new CallerPrefixFacts fixture executes the unchanged C38 mixed body from
C39's REAL compiled prefix/caller (not the older hand-built initial State).
`first_reached` executes the actual public compiled body, drops iteration
locals using StateRepr.drop and real fragment stability, and identifies its
machine with C39's checked horizon1. `second_reached` derives remaining input2
from first growth2 and actual input4, executes the same body again, and uses
the actual false condition/checked horizon3 to identify the second machine.
No desired midpoint, target run, allocation cursor or heap preservation is a
hypothesis. The SAME entry base transports through both steps.

`reached_all` quantifies EVERY Nat horizon: 0/1/2 are running at source/target
start/first/final, cost0/2/4; horizon3 and every later horizon are completed at
the same final source/target state. The existing public stopped-horizon laws
supply absorption, not a new admission cutoff. `protected_all` strengthens
these SAME reached pairs with complete caller environment, old alias addresses
and primitive word observations. All C39 complete ordered vectors, old
contents[7,11]→[9,11]→[10,11], private allocations/markers, roots and protected
stack remain unchanged. No Heap.Keeps or unconditional fragile liveness follows.

CallerPrefixControls includes an actual always-running true/nil source/target
loop on the populated represented caller for EVERY horizon. Actual condition
failure and an admitted mixed mutating/allocating body followed by bare revert
are absorbed at every positive horizon, using real checked body cost2/frame
and actual reached input4. Neither error exposes a successful State or rollback.
Horizon2 completion, horizon1 final-state/cursor, old-alias/private-reference,
protected scalar and old-content countercontrols derive from full positive
snapshots. Existing panic/payload/exhaustion/refusal distinctions are untouched.

Finder confirmed an initial generic target-turn/iterator draft overlapped the
reserved producer. It is removed from deliverables and retained as failed scope
review evidence. The replacement contains no generic iterator reconstruction.
For a GENERAL represented-prefix consumer the precise read-only producer
boundary remains: MemoryLoop's MemoryTurn, loopBody and memory_loop_iter are
private. A public supported paired-horizon eliminator (or public relation plus
iterator theorem) preserving that exact LoopPrefix/StateRepr/stack/BaseExtends/
GrowsAllocator contract would permit composition with captured/represented.
The request is additive API exposure by that owner, NOT a semantic exclusion
or assumed future theorem. The concrete all-N consumer above is discharged
without it; it is not general target-prefix simulation.

New36 exact builtin reports are additive to all25 old fixture entries/703pins;
current inventory is27fixtures/739reports. Original542 mathematical types,
85tuple types and C32–C39 inventories remain intact. Failed C40 generic-scope,
type/definitional/projection/heartbeat probes and wrong object output path are
retained. Sealing the checked failing-body object BEFORE shallow code projection
fixes demonstrated repeated normalization; no budget is raised and no whole-gate
speed improvement is claimed. Source and final artifact finder/skeptic reviews
and actual per-file/import/axiom/resource outputs accompany the sealed handoff.

All Work1–6 and Backfills A/B stay partial. Original full124/300s (TestSuite/sort
unreached), raw124, strict cached121.091/120 and docs normal/strict1 remain
failures; expanded raw/cached/full validation is pending. Semantic progress is
not a repair authorizing unchanged failed heavy retries. Complete previous/
publication doc equality is separate from frozen historical +2 findings and
global failure. General runtime/unbounded recursion/full-signature dispatch,
early-control/general-loop producers and word-frame/live-byte-journal/world/
transient/callback transport remain open. No goal write/reactivation/completion,
publication, peer transfer or independent-work-exhaustion claim follows.


## C41 — invocation-local source I/O in fixture authentication (partial)

The owned fixture-cache driver now reads each root/transitive source once per
key invocation, hashes that fresh raw Buffer and parses imports from the same
bytes. Only a local digest map survives the traversal; the next key invocation
starts empty and reads all sources again. Existing pure text parse memoization
is unchanged and is NOT claimed as this repair. Input insertion order, complete
actual toolchain hashing before/after, all guards/configs/objects/dependency
receipts, imported-fixture authentication and batch/report checks are unchanged.
This is coherent per-file byte binding, not an atomic filesystem snapshot;
the writer lease and fresh pre/post checks remain essential.

The no-Lean key controls compare actual old/new key bodies with identical input
bytes and exact serialized key/input order. They cover invalid UTF8 raw hashing,
changed import-closure rebuilding, root/transitive source/object/guard/config/
driver/manifest mutations between calls, missing dependencies, valid-JSON receipt
corruption, mutation after a source read, and missing/reordered/duplicate/wrong/
error reports using the actual parser/batch splitter. Controlled test receipts
are NOT production authentication or Lean proof evidence.

The first telemetry run retained a negative whole-key result (median10.440→
10.575seconds). Its read wrapper normalized legacy UTF8 reads to Buffers;
corrected telemetry preserves actual production read modes. Over the same27
fixtures, source reads fall10130→5065 and median source-read time571→62ms.
Corrected whole-key medians10.560→10.544seconds are essentially flat: no broad
or statistically established whole-key/kernel speedup is claimed. Both raw
profiles are retained, with complete real toolchain comparisons and identical
complete old/new key outputs. Benchmark dependency receipts exist only in memory
and do not authenticate actual objects.

The changed driver hash intentionally invalidates existing production fixture
manifests even though key serialization is compatible for identical inputs.
Fresh source-bound preparation is required for every affected fixture, under
its existing per-process bound. It is not a split raw/full/aggregate gate.
Exactly one complete registered cached attempt may follow this measured source
I/O repair and successful authentication, at the SAME strict outer120s bound
with every27fixture/739orderedreport and complete toolchain before/after check.
Its actual outcome is recorded in the C41 handoff; earlier failures are never
rewritten. No unchanged raw-source/full300s retry is justified by this change.

All intrinsic and fixture Lean sources, all739 registry pins/order (including
original542types/85tupletypes and prior703pins), observations, proof budgets,
profiles/refusals and reserved producers remain byte-preserved. The exact
public MemoryTurn/loopBody/memory_loop_iter owner request remains unresolved;
no withdrawn generic iterator proof is recreated. All original Work1–6 and
Backfills A/B stay partial. The blocked goal is untouched. No publication,
peer transfer, general source/target/world closure or independent-work-exhaustion
claim follows from this validation-code checkpoint.


C41 actual outcome: all27 source-bound preparations and739 exact ordered
standalone report guards PASS. The one complete cached attempt FAILS with
exit124,120.820seconds outer elapsed at unchanged120s. The owned/import build
completed239jobs and the complete792-line combined harness (27fixture imports,
739reports and separators) was written. Its child diagnostics file was not
written before timeout: existing run() buffers spawnSync output and writes it
only on return. This does not locate a particular slow declaration or establish
that all combined reports completed. Raw wrapper/cgroup/RSS/timeout output is
retained; no output is invented and no unchanged retry follows. Future narrow
profiling/diagnostic-retention work is independently ready; source read sharing
alone does not establish sufficient aggregate headroom. All old raw/full/docs
failures and every semantic queue remain partial.


## C42 — durable diagnostics and observed stage lifecycle (partial)

The owned validation runner now awaits an asynchronous child and fsyncs received
stdout/stderr chunks into separate raw files. A successful child produces the
same legacy stdout-then-stderr completed log used by the unchanged report
parser. Failed, over-bound or interrupted children never return partial text to
guards/cache writers. The installed Node24.19 legacy spawnSync probe rejects
600stdout+600stderr bytes at maxBuffer1024; this VM's combined64MiB bound is
preserved, not doubled from an unverified per-stream interpretation.

An append-only flushed JSONL stage journal records actual starts as unfinished,
observed ends/failures, signals and owned child-group cleanup/close. Key before/
after, report validation, both full batch toolchain snapshots/comparison,
harness creation and the combined child have named stages. Key/authentication,
input ordering, parser/count/order, toolchain and guard functions remain
byte-identical. All async callers are awaited; batch prechecks are serial.
Diagnostic records never authorize a cache or gate pass. Stage durations exclude
their own start/end journal flush, but parent/child durations include nested
logging/lifecycle overhead. No kernel CPU-time or performance gain is inferred.

The child gets a private process group. Catchable cancellation forwards TERM,
then escalates after1second within the original outer10second cleanup grace;
this timer exists only after cancellation/failure, not during normal validation.
All post-spawn setup/error paths kill that owned group and await actual close.
Handlers/fds are restored and closed. SIGKILL cannot be handled: the existing
container/external supervisor must stop the recorded group. Fully written raw
received chunks and flushed start records survive; unreceived pipe bytes and
an interrupted JSONL tail are not claimed complete. A missing terminal record
remains unfinished, never reconstructed as success. These are diagnostic records,
not source/world rollback journals or semantic execution evidence.

Host-only fake-lake controls cover exact legacy completed text/UTF8/arguments,
nonzero/signal/spawn/output-bound failures, all report corruptions, serial
await/fail-fast, parentTERM/KILL, descendants, actual outer timeout, handler
restoration and protected stage fields. Real /dev/full journal-after-spawn and
output I/O failures test close/reap and no success-marker behavior. Test-only
/dev/full symlinks are failure fixtures, not readable output payloads.
The first host suite timed out because its fake background child was not unref'd;
that raw120.947s failure is preserved. The repaired final19-case suite passes
in5.201s under the same120s/hard12GiB/no-swap cap. No Lean process was run.

Finder/skeptic identified a real post-spawn journaling-before-close-listener gap;
tracking/consumers now precede journaling and cleanup awaits even setup failures.
The suggested per-stream buffer interpretation was checked against actual
Node24.19, refuted and withdrawn; no output budget was increased. Successful
later tests are separate from the retained original failure.

A real read-only stale-fixture rejection (with a sentinel forbidding any child)
records actual key-before work3.386seconds, then expected stale driver binding
failure, with no child launched. It includes a fresh full per-file toolchain
hash and is not a batch or kernel cost measurement. Existing C41 source-read
I/O measurements/flat whole-key timings and buffered timeout artifacts locate
no particular slow theorem. Actual combined-child/closing stage costs remain
pending a separately justified future check. Instrumentation/fsync adds overhead
and is NOT an optimization or authority to retry an unchanged failed gate.

All Lean sources,27fixtures/739pins/observations and original Work1–6/Backfills
A/B remain unchanged and partial. Changing the driver invalidates its old cache
bindings; no redundant Lean re-preparation is performed just for logging.
Original cached124/120.820s, raw124, full124/300s/TestSuite-sort unreached and
normal/strict docs1 failures are retained. Current full validation is pending;
complete publication-doc equality remains separate from frozen additions.
The private MemoryLoop prefix API request, general recursion/dispatch/early-
control/frame/byte-journal/transient/world obligations remain open. No goal
administration, publication, peer transfer or independent-work-exhaustion claim.


## C43 — actual key-phase attribution and argument-prefix failure (partial)

The new host-only key profiler executes the exact committed955 key body against
all27 actual source/object/guard/config/dependency-manifest closures. It adds
only dependency wrappers and a nonmutating observer before binding validation;
no synthetic binding, substituted object or bypassed validation is supplied.
The baseline bytes are SHA-bound to955 in evidence. A fresh complete shared
batch-style toolchain snapshot before/after is the EXISTING behavior, not a new
sharing proposal. Fresh read/crypto/import/JSON timing and byte counts reset
per invocation; output references are comparison assertions, not read caches.
The22 stale dependency failures and5 returned keys are not cache authentication
(the root caller's saved-binding check is outside key()). VM/wrapper/GC costs
and partial validation paths are explicit limitations, not kernel timings.

One baseline sweep measured10.686seconds of key work:5038 object reads/hash
consume9.35GB and about9.1seconds (read3.339/hash.update5.733). Manifest reads
consume188.307MB in122 calls/~92ms; parsing61 manifests takes~325ms. Source
reads are~69ms. Thus source/manifest reads are not the dominant measured key
work. Per-path attribution identifies large read-only producer objects, e.g.
Semantics.Callback, Calculus.SoundSummary/Lands and syntax elaborators. No
reserved object, authenticated input or required freshness check is removed.

A prospective same-invocation manifest Buffer variant was tested ONLY in the
experiment. It halves manifest-read bytes188.307→94.154MB (122→61 reads), with
median read time~90→16ms, but whole-key pairs are mixed: before10.636/11.170/
11.113s; after10.674/11.139/10.681s. The small affected phase and VM/GC variance
do not establish a material gate repair or causal whole-key speedup. Production
fixture-cache.mjs remains byte-identical to955. Controls verify stable serialized
inputs/order/results or actual stale errors, fresh between-call changes,
self-consistent manifest corruption and report-order failures. They also expose
the interleaving difference: the candidate parses its first hashed bytes while
legacy may parse a later version; no universal mutation-interleaving equivalence
is claimed or silently installed. No Lean preparation or gate follows profiling.

A DIFFERENT ready original Work1/Backfill A source leaf is completed in
CallArgumentPrefix. Three typed Args suffix laws propagate an actual failed
prefix through scalar/storage/memory arguments. call_failure consumes the real
args.evalT error and unfolds published TRun.call: default-result entry, private
body and export are not reached. It introduces no evaluator/AST or assumed
simulation. The generic implication preserves its supplied halt; its inhabited
argument evaluator control is actual bare revert, not panic/bytes/divergence.

The populated typed caller has an allocated old memory reference and distinct
scalar locals9/11. Its actual argument prefix reads the reference and9; an empty
array index0 then fails. A successful argument variant uses the SAME allocating
body and proves real entry/private heap growth1→2→3, ordered argument environment
11/9/ref0, exported default result identity1, caller identity0 and retained9/11.
A private object2 is dropped. Wrong scalar/result/private identity and false
success/panic controls have this nonempty successful baseline. Failed execution
returns no State: no failed heap, old-content invariant, rollback, target frame,
allocation-cost or byte/world theorem is reconstructed. No restricted function-
reference job or compiler admission/refusal is altered.

Focused/per-file/import checks and actual17 scoped signature/axiom reports pass;
these are separate additive core reports, not replacements for the original
27fixture/739pin inventory, which is unchanged. Early identifier/bind/rfl proof
failures are retained and fixed without raised proof limits. Runtime versions/
KeySort are checked for this genuine source implementation, not to profile.
Independent read-only finder/skeptic source/artifact reviews accompany the seal.
All original Work1–6/Backfills A/B stay partial. Cached124/120.820, raw124,
full124/300/TestSuite-sort unreached and normal/strict docs1 remain failed.
No unchanged heavy retry, goal administration, publication, peer transfer,
exclusion/premise change or independent-work-exhaustion claim follows.


### C44 — invocation-scoped exact-byte digest experiment (partial)

Production `fixture-cache.mjs` is unchanged. New host-only
`tests/internal-flow/profile-byte-digests.mjs` runs the exact committed key body
for all 27 actual closures, using `exact-byte-digest.mjs` only in its candidate
hash wrapper. Every original object read remains. A hit requires exact fresh
Buffer equality with a private copy. The final candidate bounds retained payload
to 512 MiB and entries to 4096; these are not a total RSS guarantee. Cache lifetime
is one experiment sweep, never persisted or used by production or Lean.

One paired instrumented run preserved complete ordered inputs and exact outcomes
(22 stale errors and five returned helpers each, neither cache authentication).
Both variants read 5038 objects / 9,349,966,680 bytes. Key totals were
10.929s versus 6.837s; measured candidate hashed 399,039,856 bytes, compared
8,950,926,824 bytes, and retained 399,039,856 bytes. Whole experiment24.779s,
sampled peak914068 KiB. Warm order/GC/instrumentation limit attribution; this is
not combined Lean/report/postcheck timing or proof of aggregate headroom.
The measured helper preceded the metadata entry cap; its exact bytes are retained
in evidence. No affected gate was retried and no candidate was installed.

Host controls cover private-copy mutation, same-size/same-mtime real-file changes,
changes between reads/calls/owners, oversized bypass, eviction/zero-byte entry
bounds, malformed bytes, original two-read manifest interleaving, source/object/
guard/config/manifest mutations and report corruption/order. Existing27fixtures,
739pins, all mathematical types/observations and production authentication remain
unchanged. Finder/skeptic require authenticating the helper and explicitly
clearing lifetime before any future production adoption; both remain adoption
requirements, not discharged runtime claims. All Work1–6/BackfillA–B remain
partial. Cached124/120.820s, raw124, full124/300s (TestSuite/sort unreached),
and docs1 remain failures. No Lean/cache preparation or aggregate/raw/full gate
was run in C44. The original blocked goal is untouched.


### C45 — authenticated exact-byte digest phases (partial, validation pending)

The validator now requires and hashes `tests/internal-flow/exact-byte-digest.mjs`
in every fixture key, including dependency bindings. All existing source/config/
guard/object/manifest/toolchain inputs remain in their original relative order.
Only project object digests may be reused, after the original complete fresh read
and exact comparison against a private copy; all other hashes and manifest's two
reads remain unchanged. Preflight and postflight own separate bounded maps.
Both close and clear in `finally`, then synchronously major-collect released
buffers before returning, including on error. No map is live during the actual
Lean child; late owner use fails. Ordinary Node launch is supported; a private VM
collector is acquired through temporary V8 GC exposure, without changing CLI or
Lean child arguments. This is host lifecycle behavior, not kernel evidence or a
claim that RSS returns to its initial value.

The FINAL 512 MiB/4096-entry helper was measured with exact actual inputs in two
reverse-order paired sweeps INCLUDING cleanup: ordinary9.591/9.378s versus
bounded4.883/5.131s. Each sweep retains5038 fresh object reads/9,349,966,680bytes,
4790hits/248misses. Actual complete ordered keys/outcomes match (22stale dependency
errors and five returned helpers are not authenticated successes). Full toolchain
hashes match before/after. Process34.639s, sampled peak806888KiB; after collection
live arrayBuffers209323B, remaining RSS650–680MB. This demonstrates changed host
work, not aggregate headroom. Actual CLI stale-preflight cleanup passed3.528s,
no child; controlled key/read-boundary/helper/manifest/report mutations and
exception/owner cleanup pass. Original542types/85tupletypes/27fixtures/739pins and
all Lean sources are unchanged. Source finder/skeptic PASS; genuine bounded
fixture preparation and at most one complete120s aggregate are still required.

The first combined host-control invocation retained exit127 because Python is
absent inside the container, after its Node controls passed. Unchanged Python
cached/raw driver mocks passed separately in the host under the original120s
bound, no Lean. This does not repair cached124/120.820s, raw124, full124/300s,
TestSuite/sort unreached or docsnormal/strict1. All Work1–6/BackfillsA–B remain
partial; original blocked goal untouched. No unchanged raw/full retry or broader
semantic admission is authorized by this host repair.


C45 validation outcome (supersedes the pending validation above): all 27 genuine
kernel source preparations and exact guards passed, 739 registered reports total,
helper included in every binding. Longest preparation51.362s outer at unchanged
120s. Runtime Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs pass; focused current
owned/fixture imports pass. Exactly ONE complete cached attempt then FAILED124,
strict outer121.001s at unchanged120s. Actual27authenticated preflight keys
completed in5.578s. The unchanged792-line/27-import/739-builtin-report harness was
byte-identical to C41. Child spawn and later SIGTERM are recorded, with111.111s
wall interval; no child-close/complete report/postcheck/final toolchain receipt.
Available child stdout/stderr are empty. This does not identify lock/import/
report/CPU root cause; no completed stage is invented. Resource peak sampled
1592692KiB; hard cap/no-swap retained. No retry, raw/full rerun or deadline change.

Thus the authenticated, reviewed code repair and genuine individual preparations
are partial progress; complete cached validation STILL FAILS. Actual postflight
is not reached by this failed aggregate (its invariants have host controls only).
Original raw/full/TestSuite/sort/docs obligations and all eight original queues
remain partial. All Lean/fixture sources and739pins are byte unchanged; earlier
542/85 type inventories retained, not a new separate type audit. Exact committed
artifact reviews accompany the seal. Original blocked goal is untouched.


### C46 — actual argument failure to compiled bare revert (partial)

`ArgumentFailureTarget.call_revert` combines actual `Args.evalT = .error .revert`
with a published `Calls.Statement`, real `StateRepr`, exact expanded frame room
and reached `AllocationInput`. `after_prefix` derives that representation and
remaining capacity from actual successful prefix execution using
`program_endpoint` and `GrowsAllocator.nextInput`. No target simulation, midpoint
representation, failed State or desired preservation equation is postulated.

The new ArgumentFailureFacts/ArgumentFailureEndpoint clients reuse the checked
PublishedMemoryCalls prefix READ ONLY: nonempty array object0 contains[7,11], two
caller aliases name it, scalar42, stack[77], sentinel99 at127, allocation starts256.
The actual typed argument prefix evaluates the old reference and42; last index2
fails with bare revert, whereas index1 gives11. Both actual expanded programs
and public root direct-call selectors admit; checked `Calls.memoryReturn`
constructs their genuine target statement certificates. The same memory-return
body allocates privately and rebinds its result. Actual success has caller/entry/
body heap counts1/2/3, argument order(11,42,ref0), default object1 not returned,
exported private object2, old aliases0 and caller scalar42. Source lengths and
all old/new element observations are checked; no generic Heap.Keeps is asserted.

Closed failed_endpoint/failed_composition prove the real prefix reaches its
represented caller and the compiled bad call/composition returns exactly target
bare revert. The successful_endpoint also derives its midpoint and genuine
capacity. Prefix cost3, bad reached cost0 and good cost4; both call frames need8.
The complete successful target observation is
[77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0]
at addresses[0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262]
following the protected stack. Thus cursor263, old pointers256, default object at259
and escaping private result at260 are distinct. Private physical cells are retained
in the observation even though their binders are dropped logically. Negative
controls reject success/fault, source panic/exhausted/payload, wrong argument
order/result/default alias, wrong target alias/cursor and insufficient frame
premise (the latter is NOT a runtime rejection).

Boundary: source non-entry follows the existing TRun.call argument bind. Target
Out.revert has no returned State/frontier/bytes/world journal. Bad producer cost0
is reached-cost metadata, NOT proof of failed-target cursor, rollback or absence
of body effects. A separately compiled actual Args.declsThen.nil program also
reverts at the same represented caller; existing run_append_revert absorbs any
suffix. Its equality with an instruction prefix of the full call is NOT assumed
or claimed. That extra closed code decomposition was investigated: opaque rfl
failed, and explicit certificate normalization (including an isolated fragment
rewrite) reached the ORIGINAL200000-heartbeat limit. Raw failures are retained;
no limits were increased and the unproved equation was removed. Exact instruction
construction sharing remains ready proof engineering, not an unavailable semantic
producer or an approved premise. The actual full-call revert endpoint is proved
independently through the public checked producer.

All39 new headline builtin axiom reports are pinned (23facts/core,16endpoint).
The original27fixtures/739pins remain exactly unchanged after removing additions;
expanded29fixtures/778reports are registered, aggregate PENDING. Adding the registry
entries intentionally stales earlier manifest bindings; none are rebound or
relabelled green. CLI per-file/focused checks are used because Lean MCP is not
available. No unchanged cached/raw/full attempt is run. Retain C45cached124 at
121.001s/120s, earliercached124/120.820s, raw124, full124/300s with TestSuite/sort
unreached, docsnormal/strict1. All six original Work items and both Backfills
remain partial: general frames/unbounded recursion/dependent dispatch, early-control/
general mixed loops, live word-frame/byte-journal and transient/world coupling are
not closed. This intrinsic finite-call client is not frontend name-resolution,
source lowering, bytecode/gas agreement, recursive compilation or whole-lane closure.
The original blocked goal is untouched; no administration, push, merge or peer transfer.


### C47 — compiler-selected shared argument prefix (partial)

The C46 instruction-prefix gap is now closed for its SAME inhabited bad/good pair.
New `SharedCallPrefix.attach` packages existing `Memory.CompiledStmt`/`CompiledProg`
with the existing `ProgFrag.cons` constructor. `compile_attach` proves the public
`Memory.compileProg` head/tail equation; `attach_prefix` lifts an already proved
tail decomposition through the SAME compiled head, even with differently typed
continuations. Concrete proofs bottom out at the actual nil certificate, not a
hypothetical prefix/simulation premise. No syntax, evaluator or machine is added.

SharedArgumentFacts compiles the three actual argument declarations separately,
then uses the same head certificates for the argument-only program and the full
result-entry/body continuation. Exact source constructor shapes and each public
compileStmt/compileProg selection are proved. Named small equations connect those
shared certificates to `Calls.compile` for the expansions AND the public root
call selectors, and to the original C46 getters/Statements. This is actual emitted
code, not merely an alternative sound certificate. No private producer is edited
or imported under a new name. The literal C46 drop-form equation is recovered by
constructor decomposition plus `List.drop_left`, not deep normalization. Historical
C46 heartbeat failures stay sealed; the original200000 limit is unchanged.

`actual_bad_prefix` and `emitted_bad_prefix` prove the original/full public call
code equals the actual old argument code followed by the compiled continuation
and return-pointer code. The good pair has the corresponding proved decomposition.
`emitted_argument_failure` consumes the SAME genuinely reached C46 caller and its
actual argument-program revert, then existing `run_append_revert` proves failure
absorption for this actual emitted prefix and prefix/call composition. Public good
code/fragment equality transports the original represented successful endpoint and
EXACT complete ordered vector, not a recomputed smaller witness:
[77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0].
Stack77, sentinel99, old aliases256, source scalar42, private/default separation,
result object2 at260 and cursor263 are unchanged. A new negative proves the bad
and successful public emitted programs cannot be substituted for one another;
wrong-cursor uses the retained full vector. None yields a failed output State,
frontier, rollback, absence of effects, payload bytes, target trace or world theorem.

All51 new actual builtin axiom reports are pinned (42facts/core,9endpoint), with
strict corruption/order controls. Removing additions preserves EXACT old29fixture/
778report entries/order, including all39 C46 pins. Expanded31/829 aggregate remains
PENDING; source/config bindings intentionally stale, no rebind or cached/raw/full
retry. No semantic progress is relabeled performance repair. General runtime frames,
recursion/divergence, dependent dispatch, mixed/early-control loops and byte-journal/
transient/world composition remain OPEN; all Work1–6/BackfillsA–B remain partial.

A real disk guard observed zero free after stopped task containers accumulated.
Further checks paused, only stopped C47 containers verified by saved CID/name
receipts were removed, restoring2.7GiB. No cache, old seal, other container or
unrelated work was deleted; later checks use explicit admission and immediate own
cleanup. Initial constructor monad/dependent-source rewrite failures are retained
and fixed with public Option equations/definitional source shapes, no budget change.
Existing layers/trust/profile/observations are unchanged. Original blocked goal
untouched; no goal administration, push/merge/PR, peer transfer or new VM/thread.

C47 also closes the directly available metadata consequence: public bad/good root
cost equals its original call cost for EVERY typed caller state (nil short-circuits
without evaluating an unreachable suffix). At the actual caller costs are0/4 and
both selected public roots have need8. The represented successful endpoint states
GrowsAllocator with the actual public program cost. This is constructor-derived
metadata, not a failed-state frontier or a global frame/recursion theorem.


### C48 — shared reached prefix capacity; validation investigation remains open

`SharedPrefixCapacity.fork` consumes one actual `Calls.Program`, entry
`StateRepr`, frame bound, successful intrinsic prefix execution, and initial
`AllocationInput (prefix.cost + max left right)`. It produces ONE actual target
prefix endpoint with reached representation, unchanged stack, `BaseExtends`,
`GrowsAllocator`, and both alternative continuation capacity premises. The
maximum supports choosing either continuation, not sequentially running both.
`SharedArgumentEndpoint.shared_capacity` discharges these premises for the SAME
populated C46/C47 prefix and actual public bad/good costs 0/4. No desired
midpoint, target continuation simulation or failed State is supplied. Existing
successful 20-element vector, private/old/result addresses, bad-index failure,
frame/cursor/alias negatives and every old theorem/pin remain unchanged.
Two additive actual builtin axiom reports retain precisely Classical.choice,
Quot.sound and propext. All 31 fixtures remain registered; 829 old ordered
reports remain unchanged, with two additive reports (831 total).

C48 source-only diagnostics reject proof re-elaboration as a demonstrated
cached-harness cause: all 31 imported fixtures plus immediate dependency
inspection of 829 roots passed in 3.374s (0.076s direct inspection). A 30-root
sample of the UNMODIFIED standard transitive axiom collector took 6.363s inside
9.133s process time. These are diagnostic samples, not authentication, aggregate
measurements or a performance repair. The collector follows checked types AND
values without certificate normalization. C47 head types already transitively
reach the compiler; opacity alone cannot cut that dependency. A certificate
value repair for the older prefix remains investigated, not implemented or
measured. NO cached/raw/full aggregate was retried. Their historical failures,
documentation raw failures and all original Work1–6/BackfillA–B obligations remain
open. This independent finite-prefix consequence is not general frame, recursion,
dispatch, loop, rollback, byte/world or transient closure; the original blocked
goal remains unchanged.

C48 independent read-only finder and skeptic source reviews PASS with no confirmed
finding; neither runs Lean/server/builds. They explicitly confirm that both
capacities refer to ONE actual reached machine and address map and that max is
an alternative budget. The changed source/client and focused import/KeySort
checks pass; driver coverage/fail-fast and actual report corruption checks pass.
Documentation normal/strict raw exits remain 1, complete outputs byte-identical
to C47; frozen comparison retains two incoming missing paths and one incoming
ambiguity (48 missing versus 46, 86 total findings versus 83). No owned addition.


### C49 — explicit populated prefix certificate and public selector bridge

The owned PublishedMemoryCalls fixture now supplies `prefixConstructed` from the
five existing intrinsic statement certificates (scalar declaration, array
allocation, two actual writes and alias declaration). Each head has its actual
public `Memory.compileStmt` equation. `compile_attach` composes these equations
into `selected_constructed`; `selected_public` connects the SAME certificate to
actual `Calls.compile`. `prefix_constructor_eq`, `prefix_getter` and
`prefix_public_fields` retain exact original compiler admission, code, fragment,
frame need and cost FUNCTION, including arbitrary actual getter witnesses.
The original `prefixProducer` getter body and irreducible attribute are RESTORED
UNCHANGED. Existing public client types/statements/observations are byte-exact
after excluding additions in memory; all831 prior ordered pins remain unchanged.

`constructed_endpoint` transports the genuinely populated old prefix/call/export
endpoint including StateRepr, stack, BaseExtends and GrowsAllocator, not a desired
midpoint premise. `constructed_ordered` covers EVERY address list. The separate
argument-call client retains the SAME complete20-element successful vector and
wrong-alias control through actual public-prefix equality. No new evaluator,
representation, admission, unsupported category, failed State, rollback, byte,
absence-of-effects or world theorem is inferred. Nine new actual scoped reports
are pinned additively:31fixtures/840reports; selected_constructed uses precisely
propext/Quot.sound, the other eight use Classical.choice/propext/Quot.sound.

The measured production-replacement candidate is REJECTED as a performance fix.
UNMODIFIED Lean.collectAxioms on SAME5actual public roots x3 repetitions, with
identical root/order/axiom outputs, took4.394313039s before versus4.647849077s
candidate (process6.952s versus7.489s). This is one measured pair, not proof of a
unique bottleneck or an aggregate/headroom prediction. Explicit data was checked,
but adopting it as prefixProducer did not improve the actual affected root sample.
No aggregate/raw/full retry or fixture-manifest rebind/preparation occurred.
The failed whole-rfl200000-heartbeat probe (including compiler-inserted sorryAx)
is INVALID failure evidence only; no such proof/axiom is in committed deliverables.
Per-head constructor equations solve the link without increasing any budget.

A DIFFERENT owned correctness repair closes the published-call standalone guard's
order gap: its ORIGINAL complete27reports reordered are accepted by the old guard
(exit0), while the strengthened guard now rejects reordering with all34 current
reports present. Missing/duplicate/altered-axiom/diagnostic controls also reject;
all original report order is retained. This is authentication/control correctness,
not performance or cache/kernel/full-gate evidence. Independent READ-ONLY finder
and skeptic source reviews PASS without builds, no confirmed finding.

All original Work1–6/BackfillA–B remain partial. The aggregate is PENDING31/840
with intentionally stale source/config bindings; cached124/121.0013827s against
120s, raw124, full124/300s/TestSuite-sort unreached and normal/strictdocs1 remain
failures. No optimization/gate success or independent-work-exhaustion claim.
General runtime frames/unbounded recursion/full-signature dispatch, general mixed
or early-control loop compilation, live byte-journal/transient/world producers
remain open/reserved. Original blocked goal unchanged, no administration/reset/
reactivation, push/merge/PR/peer transfer/new VM/thread/model or budget change.


### C50 — general typed runtime and ordinary-world caller-phase interfaces

Coordinator-directed implementation resumes in Work1/G37.01 without treating
mandatory validation overruns as implementation blockers. RuntimeCalls.success_iff
and failure_iff invert ACTUAL TRun.call for EVERY current CallRet constructor:
none, val (including a particular destination), primitive tuple binders, memory
and storage alias results. The exact evaluated TEnv, result-entry Out, body Out,
composed heap extension and private-local removal/export are retained. No noMem,
inlining depth, target simulation oracle or desired output equation is assumed.
This is the existing intrinsic call semantics, not general target call frames or
uncapped recursive source/target simulation. Alias identity is not liveness.

RuntimeWorld.concat constructs only existing typed Prog constructors and its
runR law uses actual TRun.seq associativity. RuntimeWorld.callFrame_success
extracts installed typed storage, actual paid initial state, actual nonempty
caller prefix, evaluated arguments/body and exported state from a REAL
World.callFrame success. It retains exact finish/settlement and derives other
account STORAGE preservation through the published finish_other theorem (not
arbitrary balance preservation). RuntimeWorld.call_success_iff separates actual
World.call success into frame execution AND caller-side decoder execution.
decode_failure retains the exact halt after a successful frame, with no catch,
failed State or rollback inference. The Entry.result decoder is NOT run by
callFrame itself. These consume existing source-world APIs unchanged; they are
not external CALL/gas/bytecode or general callback/world correspondence.

RuntimeGuardedFrame.success combines the SAME actual call decomposition with
the published syntax-derived TGFrameM and TLocAgreeM theorems. Genuine readsIn
and withinM premises remain. In particular val-result destinations may change,
and local transport excludes actual writesAt destinations; other typed locals
are weakened along the exact extension. No unconditional Heap.Keeps or fragile
alias liveness is asserted for arbitrary mutating bodies. Readonly consumers
can use this guarded interface independently of the ordinary-world adapter.

The inhabited RuntimeFrameChecks world prefix constructs old[7,11], two aliases
and protected9/11 locals. Memory result entry and private allocation grow H1→H3;
returned reference2 contains[13,17], old aliases0 retain[7,11], and the body writes
persistent23/transient29 in the ACTUAL local Storage model. This is not EIP1153
or transaction-reset/world-journal correspondence. The ordinary zero-value world
client derives its runtime frame from actual execution and preserves a distinct
installed account. It pins all these ordered observations, wrong alias/scalar,
static refusal and rejected mutating withinM. A SEPARATE admitted allocation-only
readonly client consumes RuntimeGuardedFrame. Body failure keeps DE/00/AD bytes;
a separate99/00 decoder failure occurs AFTER an actual successful frame. No
failed-world state, absence of side effects or rollback follows from error values.

The local published World.callFrame conservatively REFUSES all these nonempty
entries in static mode; RuntimeWorld.static_refused preserves that exact rule.
The V13 effect-certified StaticInvocation.Frame.static producer is not locally
published here and is not recreated. This interface supplies ordinary caller
phase and guarded intrinsic-call facts; it does not claim that V13/G22 parent
obligations or computed static admission are discharged. Installed bodies and
external response tables retain their existing explicit model obligations.

All23 new actual builtin axiom reports are pinned; all840 old ordered pins and31
fixture sources remain unchanged, giving32fixtures/863reports. Independent
read-only finder/skeptic generic and populated-client source reviews PASS with
no findings; final registration/guard/artifact reviews are separate. Per-file
CLI fallback is used because Lean MCP diagnostics are unavailable. No proof,
fuel, node, heartbeat, stack, memory or test budget increase. Three new core
modules are append-only registered; no reserved producer/source file is edited.
Old cached/raw/full/docs failures remain failed and are HELD until end-of-lane
validation under coordinator scheduling, not rerun or relabeled here. All
original Work1–6/BackfillsA–B remain partial. No push/merge/PR, peer transfer,
new VM/thread/model or goal administration/reset/reactivation/completion.


### C51 — actual callee and caller-result failures to checked byte emission

WorldResultEmission consumes a remaining ready Work5/BackfillB composition.
`rejectingEntry` retains the existing method body/payable flag and uses the
EXISTING TRun.revertData evaluator as its caller-side rejecting result handler.
`same_frame` proves actual frame execution is unchanged. `world_rejection`
uses the REAL successful frame state and actual typed RevPart evaluation to
produce the exact World.call halt; checked_rejection/local_rejection feed THAT
SAME actual runtime error into the published checked emitter/local journal.
This is result-to-component coupling, not an unrelated conjunction, new payload
evaluator/codec, world semantics or desired simulation premise. It is a
model-level rejecting handler, not proved frontend ABI decoder lowering.

The inhabited client reuses C50's actual nonempty ordinary-world frame. Payload
parts read returned memory13, protected caller local9, actual persistent23 and
transient29 roots, then literal DE/00/AD. Complete ordered chunks are four
32-byte published word encodings plus3bytes:131total with embedded zero bytes.
Full checked emission bytes, immutable outcome, protected3-element stack and
outside memory4/136 are pinned at nonzero offset5, with a halting ignored suffix.
Saved7/9 and live23/29 roots are explicitly from the separately witnessed source
states (saved source installed storage is checked). The failed world result
itself supplies NO State. Local projected restoration proves no world rollback,
StateRepr, byte/word memory coupling, source catch or post-error effect absence.
A failed Fits premise is distinguished from actual over-stack checked rejection.
Wrong order, ordinary successful World.call versus error adapter, normalized
empty revert, and separately executed panic rejecting handler retain classes;
THalt.data=[] is never used to invent a REVERT or panic code.

All41 actual builtin reports are pinned additively:33fixtures/904reports, all
old32/863pins/source bytes unchanged. The genuinely missing C50 fixture object
was created by checking its exact unchanged committed source to permit import;
all23 prior report sets pass. NO saved cache manifest was rebound or promoted.
Initial typed-lambda/syntax and naive stack recursion failures are retained;
stack rejection now uses the original exact length/stack guard structurally,
with no recursion/heartbeat/fuel/time increase. Source/core/client checks pass;
independent read-only source/artifact reviews are required. Held aggregate/raw/
full/docs final gates remain failed/pending, not retried or implementation stops.

Remaining queue review: general target runtime frames and unbounded intrinsic callRec
runtime/target bridge remain missing (the intrinsic Stmt.callRec elaboration path
still quotes finite recUnroll with recBase/exhaustion). Published
Solidity.Source.callInternal/sourceLang unbounded semantics already exist; their
bridge to this intrinsic/runtime target is a SEPARATE obligation. Full dependent dispatch still lacks the general generated
guard/direct-candidate agreement noted in finite-dispatch, beyond existing
concrete controls. General mixed/early-control loop and exact finite-horizon
transport need supported body certificates/public MemoryTurn/loopBody/iter API;
private producer implementation is not copied. Callee ABI RETURN bytes cannot
be manufactured by substituting a byte-returning Entry.result, which is a
CALLER decoder: a real return-lowering/representation producer is required.
Word-frame/live byte-journal/world and target transient/transaction/callback
correspondence remain open; logical source root projection is not EIP1153.
All original Work1–6/BackfillsA–B remain partial. No reserved edit, new axiom,
sorry/native trust shortcut, profile/refusal change, push/merge/PR/peer transfer,
new VM/thread/model, goal reset/reactivation/completion or budget increase.

C51 review identified and completed a SECOND ready Work5/BackfillB path rather
than prematurely stopping: `callee_rejection` evaluates typed parts INSIDE the
callee after a successful mutating/allocating prefix. `frame_failure` retains
exact original world admission/storage/entry/body equations; world_callee_rejection
composes actual caller prefix, argument evaluation, callee prefix, typed revert
and ordinary world failure. The caller decoder is unchanged and not substituted.
The inhabited InsideCallee client checks default entry H2/ref1, body H3 with
private/result/old identities2/2/0, contents13/17 versus7/11, roots23/29. Typed
parts read private17, result13, old argument11 and roots23/29, giving163bytes.
Complete machine/output/journal observations and a131-versus163 wrong-phase
payload control distinguish caller-result and in-callee scopes. Prefix state is
known from ACTUAL successful prefix execution, not reconstructed from failure.
Protected stack and outside-memory facts use shallow published byte frame laws;
no recursion limit was raised after a deep concrete projection failed.

Confirmed review correction: finite recUnroll concerns the INTRINSIC
Stmt.callRec elaboration/runtime path, not all source semantics. Existing
Solidity.Source.callInternal (Source/Eval.lean) and sourceLang
(Source/Semantics.lean) provide unbounded source semantics. The source-to-intrinsic/
runtime/TARGET bridge is the missing separate producer; it is not repaired by
reimplementing reserved source semantics. A further ready BackfillA target
composition candidate is whole-program prefix/certificate joining (public
Calls.Program currently supplies statement-cons composition); inspect and consume
published Prog.join/DeferredSource.join_run instead of duplicating an evaluator.
No general independent-work-exhaustion or lane-completion conclusion follows.


## C52 — whole-program target frames and actual world-body endpoints

Owned `ProgramComposition.join` constructs a real Calls.Program for existing
Prog.join from two genuinely checked program certificates. It derives, rather
than assumes, actual intermediate StateRepr, next AllocationInput, complete stack,
composed BaseExtends and GrowsAllocator. Need is max of the actual constituent
frame needs. Cost is first cost plus second cost at the ACTUAL successful source
prefix output, or zero suffix cost after a first failure. Published
DeferredSource.join_run supplies execution algebra; no evaluator/syntax, private
producer access, public selector change or source judgment is introduced.

The populated ProgramCompositionChecks client uses the unchanged published-style
prefix and actual public bad/good memory-result call selectors. Initial capacity
is discharged, not supplied at an arbitrary midpoint. Good total cost7 reaches
cursor263; bad total cost3 reverts. Complete original20-element ordered target
observation remains `[77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0]`,
including protected stack/sentinel, old object and both aliases, scalar42/argument11,
private default object and returned object2. Wrong alias/cursor and included-cost
controls retain successful baselines. Independent read-only review requested an
actual failing FIRST constituent with nonempty allocating suffix: the admitted
suffix has real cost2 at the separate successful baseline; actual source/target
failure absorbs it, joined cost remains3 rather than5. This metadata comparison
is not a failed-state/frontier or absence-of-side-effects claim.

`WorldProgramTarget.frame_endpoint` extracts actual body execution and settlement
from successful World.callFrame, identifies the represented initial state by
actual lookup/entry determinism, then consumes the real checked body certificate.
Only the BODY has target execution/StateRepr/stack/BaseExtends/GrowsAllocator;
world entry and settlement do not thereby have target implementations. The
fixture discharges every premise at an actual ordinary zero-payment world entry
and successful settlement, retaining the same complete populated endpoint.
`frame_revert` uses the SAME actual bare body error to derive ordinary world
failure and checked body revert; it consumes C51 frame_failure unchanged. Its
concrete bad client is inhabited. Arbitrary world errors cannot be inverted to
body errors; panic, payload failures, exhaustion and divergence are not collapsed
to bare revert. Error-valued results contain no failed state. There is no ABI,
gas/physical EVM, byte/journal/world rollback, callback, target transient/EIP1153
or general source-lowering claim.

Source reviews pass after the requested first-failure control. Failed syntax and
dependent-rewrite probes are retained; no proof/recursion/time/resource bound was
raised. New imports are checked through bounded focused closure and actual
builtin axiom guards. Original fixture source/type/axiom order is preserved;
registry additions are additive. Final counts and exact command outcomes are in
the immutable handoff and raw evidence, not inferred from cache inventory.
All original Work1–6/BackfillsA–B remain PARTIAL, and mandatory cached/raw/full/docs
failures remain held to lane end under coordinator scheduling, not relabeled.
General target runtime/uncapped recursion/full-signature dispatch, mixed nested
and early-control loops, live byte-journal and transient/world applications
still require the precise original producers. The source unbounded recursion
semantics already exists; its faithful runtime/target lowering is still separate.
Goal identity/status is unchanged. No publication/peer transfer is authorized.


## C53 — three actual programs, shared frame and reached cost

After C52, independent review identified an available original BackfillA prefix
composition leaf rather than a reason to stop at whole-program binary joining.
ProgramAssociation proves exact structural equality over existing Prog.join and
code/final-fragment/max-frame/reached-cost association for THREE genuine checked
Calls.Program certificates. Actual first/middle success and failure are split
using published join_run. No source cutoff, new syntax/evaluator or desired
simulation premise is introduced; no public compiler selector is changed.

The new ProgramAssociationChecks client keeps C52 untouched and adds a real
publicly memory-compiled third stage: allocate length1 then write19. Its actual
source endpoint has heap4, new reference3[19], returned reference2[0,0], both old
aliases0[7,11] and caller scalar42. Both intrinsic association orders succeed.
Exact frame/capacity are derived; both target code associations yield the SAME
reached represented state and stack/BaseExtends/GrowsAllocator with totalcost9.
The complete22-value target observation includes cursor265, private/default and
old physical cells, new pointer263 and object words1/19. The earlier C52
20-element observation is not changed: this is a different subsequent program.
Wrong new/returned identity, cursor and included failed cost reject. A failed
middle stage, reassociated with the admitted allocating continuation, still
reverts and has cost3 rather than5; errors provide no failed State/frontier or
absence-of-side-effects conclusion. No Heap.Keeps is inferred from address
preservation; only the actual observed contents of this real client are pinned.

Deep cost rewriting hit the unchanged200000-heartbeat ceiling in a retained
failed probe. Small typed equality composition fixes the proof without changing
statements, observations or limits. No speedup claim follows. A contract-specific
old contents observer could not be used at this client's C; the new fixture
reads its existing intrinsic typed heap directly, not a substitute semantics.
Final fixture exit0/9.418s, sampledRSS1048480KiB;18 actual builtin axiom reports
strictly guarded with missing/duplicate/reorder/axiom/diagnostic controls.
Previous34fixtures/937maps/order/sourcebytes remain unchanged; now35/955.
The genuinely required C52 fixture import was kernel checked unchanged with its
33 original guards, not rebound from metadata. Focused import/structural/runtime
outcomes and exact source/axiom/resource evidence are in the immutable handoff.
Independent source finder/skeptic reviews pass; committed artifacts are reviewed
separately. All original Work1–6/BackfillsA–B and held aggregate/raw/full/docs
gates remain PARTIAL/failed or pending as recorded. This association component
is not general recursive frame execution, full dispatch, early-control/world/
byte-journal/transient correctness or a validation performance repair.
