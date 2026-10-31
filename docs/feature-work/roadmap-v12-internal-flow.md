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
