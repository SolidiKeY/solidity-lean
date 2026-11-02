# P8a finite dispatch coverage

Partial P8a checkpoint, not complete G15 admission or SourceSpec/Failures.
Frozen H12 signatures remain unchanged. Revision is this document's commit;
the sealed handoff records the full revision and cumulative artifacts.

## Published prerequisite and interfaces

The lane fetched published `19bf3ba677c45d35acc1907b8e35a866dd3bb02a`, including
P9 publication `9e7a9f119`. This checkpoint consumes
`Solidity.Lowering.P9.WholeProgram.dispatch_mem` without re-proving or changing
P9. The private helper branch was rebased, retaining upstream P9/preservation/
progress imports and module-map additions. Old sealed checkpoint
`5e6cc7df95938e80fa829268183bb1f38d4a8043` and its artifacts remain preserved
under `refs/recovery/p8a/program-5e6cc7df`.

`Solidity.Lowering.P8.DispatchCoverage` adds:

- `dispatchMod_mem`: actual `Glob.dispatchMod` selects an environment
  declaration or its original input; if the input is in `E.decls`, so is the
  selected declaration. Intrinsic declaration identity is retained.
- `checkFunctionTarget`/`checkModifierTarget`, and their soundness theorems:
  executable actual roster membership and selected body existence.
- `check`: all carried contract/call/modifier-target combinations, without a
  manual allowlist or recursively unfolding calls.
- `internal_body_covered`, `external_body_covered`, `modifier_body_covered`:
  successful check, actual scanned site/target and contract membership imply
  a selected body and inclusion of all its observations in the existing scan.

The function branch uses the published P9 theorem. The modifier proof follows
actual source selection/filtering and leaves all source definitions unchanged.
No new executable representation, semantic premise, exclusion or profile is
introduced. These are finite coverage checks, not public compiler admission.

## Boundaries

`check` can pass on an empty contract/site roster. The exported coverage
conclusions require actual contract and site/target membership, so they do not
conclude arbitrary executed calls are covered. Missing bodies may erase their
own call sites; retained-caller negatives explicitly prevent that vacuity.

No completeness theorem (`InProfile` implies check) is claimed. Checking all
contract/target combinations can be stronger than actual receiver-specific
reachability. The external theorem concerns dispatch at the supplied contract
`c`, not the actual external receiver lookup or the behavior of outside-system
accounts. Function/modifier kind, parameter/return/frame agreement, successful
execution, base-name resolution and operational receiver/roster closure are
separate. This check must not be promoted to an approved-profile exclusion or
substitute for those proofs.

## Controls and checks

The actual published P9 elaborated function passes the local target check;
its original source-machine observation is reused as
`inherited_source_execution`, parametric in all fixed inputs and source state.
This is a kernel source observation, not external solc/EVM evidence.

Synthetic typed carriers separately exercise a populated recursive internal
call and a genuine `.modifier` declaration/invocation with a timestamp body.
Modifier fallback dispatch has positive local/global checks and nonempty body
observation coverage. Missing function/modifier bodies are refused while a
constructor call/invocation remains in the scan. Foreign intrinsic identity
and the actual published abstract-interface target are refused. No claim that
these synthetic carriers are Elaborated or executed source programs is made.
Modifier override selection is not exercised by these controls.

`timeout 300 lake build Solidity.Lowering.P8.DispatchCoverageControls` passed
40 jobs, 2.565 seconds, peak aggregate RSS 501112832 bytes; no OOM/resource
stop. The base module checked in 0.605 seconds; the final control build reported
2.3 seconds (separate checks, not a controlled benchmark). All printed headlines use propext, Classical.choice and Quot.sound
only. Missing-import/elaboration/control failures remain failed in exclusive
receipts; no sorry or new axiom is committed.

Lean 4.24.0 / Lake 5.0.0-src+797c613; LEAN_NUM_THREADS=1, explicit -j1, hard
whole-group 12 GiB, zero swap and authorized 4 GiB host reserve. No proof,
time, test or resource budget increased. No full end-of-lane build is inferred
from these touched modules. H12 full/root/import, combined TrustAudit,
TestSuite, corpus, strict/docs/sort gates remain required; prior failures and
interrupted full run stay nonpassing. Per-file MCP was unavailable.

Independent finder and skeptic reviewed read-only without Lean/server/builds.
Control gaps fixed: populated modifier branch and nonvacuous global missing
body tests. They approve checkpoint accuracy, not source completion.
Evidence: `${VM_WORKSPACE}/p8a-implementation-20261102-evidence`.

## Remaining P8a work

Actual executed-target/receiver closure; complete feature/type/spec extraction
and independent frozen-root-model coverage; full settings/resolution and
public frontend routing or solc-JSON correspondence; operational failure
hooks/rollback/resource consistency, hash/slot preimages and SourceSpec
realization; final mandatory gates. P8b/G01 remains V16-owned. S02-IMMUT,
SS-CP5-HASHED and SS-NEW remain queued. Persistent goal unchanged; no worker
push, default branch edit or controller integration claim.
