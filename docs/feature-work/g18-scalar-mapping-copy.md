# Integer-valued mapping copy

[The mapping consumer](../../Solidity/Backend/Aggregates/G18ScalarMapping.lean)
composes existing Source storage cells, intrinsic `SVal` mappings, the published
whole-value symbolic storage representation, and the structured target's
SLOAD/SSTORE driver. It adds no execution semantics.

`Cells` relates **every** typed mapping key. `write` requires injective Source
paths, the initial relation, a source-width range proof and the initial whole
mapping representation. It derives the actual intrinsic save, all-key Source
agreement after the real storage write, and whole-value representation after
the published symbolic word write. The path injectivity premise prevents one
Source cell from accidentally representing distinct target keys.

`copy` captures the actual Source read. The initial whole-value representation
and target-store agreement identify the word read by the current target SLOAD.
The emitted copy code contains captured source/destination slots, not the
Source payload. Its result includes the exact target machine (all other fields
retained) and target-store agreement at every mapping key. It does not require
a desired target run or final simulation as a premise.

[The controls](../../Solidity/Backend/Aggregates/G18ScalarMappingControls.lean)
resolve actual `mapping(bool => integer)` declarations and use the Boolean key
bytes produced by `Source.keyStep`. All input premises are inhabited. The
unsigned sample copies 7 over 11; the signed sample copies -1 over 11 and
retains the exact padded word. Both have a nonempty value/slot stack, populated
memory, account/sender/value/time fields and distinct balance/ghost functions.
The ordered vectors retain both Source cells, both intrinsic values, both
symbolic and target words, and an untouched storage sentinel, before and after.
`complete_target_frame` retains the entire non-storage frame, including functions.

Reversed code, changed current target contents, wrong outcome tags, signed
normalization and width countercontrols are checked on actual definitions.
A collapsed-path example starts with equal 7/7 observations but produces Source
8/8 versus intrinsic 7/8, exhibiting the injectivity requirement. `wrong_frame`
uses the new certificate itself to reject an entire result with a lost stack.
The actual Source key helper and zero-horizon expression timeout are separate:
helper success does not establish enclosing-expression progress or divergence.
Fifteen generated guards pin the scoped standard axiom dependencies.

This is a captured-key **full-word symbolic** operation result. The fixtures
are not admitted Source compilation units. Computed source-address lowering,
packing, physical hash/address realization, fetched bytes/Osaka, resources,
general source-expression/statement execution, failure correspondence, rollback,
transactions and full aggregate/compiler coverage remain separate obligations.

Independent read-only finder and skeptic reviews found no semantic defect.
They checked the actual premises, inhabited controls, full frame and symbolic
scope; neither review ran Lean or a build.

## Actual Source storage phases

[The machine consumer](../../Solidity/Backend/Aggregates/G18SourceMapping.lean)
uses the actual `Env.cellTy` and published Source Hoare bind law. `read` derives
`readAt` success from the initial persistent account cell, preserving the
entire locals/state pair. `write` derives the real `writeAt` success under the
nonstatic premise, including the existing account operation's journal entry.
`copy_phases` derives these two results and the structured target certificate
from the all-key initial relation and representation. The read leaves the
state unchanged, so the write's initial state is the actual read endpoint.
No desired execution is an input.

[The machine controls](../../Solidity/Backend/Aggregates/G18SourceMappingControls.lean)
use populated account storage at the actual total Source cell layout. This
layout differs from the earlier storage-only fixture at invalid paths; no
coercion between them is assumed. Both integer samples have nonempty locals,
heap, logs and a prior journal entry. `state_cells` ties the all-key output
relation to the actual account after the journaled write. `complete_frame`
preserves every non-`ex` field, and `rollback` consumes the published
`undo_apply` law to restore the complete state after exactly one added entry.
It does not model whole-transaction rollback.

The ordered Source observations retain both cells, journal length, heap cursor
and logs before/after. `wrong_phase` rejects a successful write paired with the
old state using the actual certificate. A populated foreign account retains
its old cell. Most importantly, `static_control` proves an actual Source empty
revert with unchanged state while the structured target copy still succeeds.
It is a counterexample to dropping the nonstatic input, not a failure-agreement
theorem. Empty revert remains distinct from timeout and stuck; no divergence
or enclosing-expression progress follows from these finite helpers.

The Source and symbolic target frames are not physically related by this
component. The phases are the actual storage helper executions at captured
paths, not a lowering theorem for an elaborated assignment or compilation unit.

Independent read-only finder and skeptic reviews also found no semantic defect
in the machine-phase consumer and controls. Thirteen generated guards pin its
scoped theorem dependencies to the observed standard axiom sets.

## Resolved mapping assignment execution

[The expression client](../../Solidity/Backend/Aggregates/G18MappingExpression.lean)
builds actual typed `RExpr.state`, Boolean-key `indexMapping`, `RLVal.indexMapping`
and assignment constructors. `reference_program`, `read_program` and
`location_program` describe their actual evaluator computations for arbitrary
frames. `assignment_run` derives exact success at every horizon `fuel + 3`,
returning the integer read from the populated Source account and preserving
the complete locals/state endpoint of the actual journaled write. It consumes
the checked phase results; source success is not a premise. `static_run`
executes the same resolved assignment with a static frame and proves exact
empty revert with the whole state unchanged.

[The expression controls](../../Solidity/Backend/Aggregates/G18MappingExpressionControls.lean)
construct actual `Source.Program` and `Source.Glob` values. They reuse the G07
fixed-parameter control, not another evaluator. The expression invokes no hash,
precompile, ledger, external call or creation operation. Both signed and unsigned
samples run under either pipeline. Horizons zero, one and two time out with
unchanged state; timeout is not divergence. Wrong returned-value and stale-state
controls derive their rejection from actual successful expression execution.
Nine generated guards pin these dependencies to the observed axiom sets.

These are manually constructed resolved expressions, not frontend elaboration
outputs. The fixture's program has no contracts and no proof connecting its
stored account code index to a contract; no accepted or reachable compilation
unit, SourceSpec, failure-plan realization or physical frame follows. The target
copy driver's storage effect is already checked, but it discards the assignment
value and preserves its input stack. Consequently these results do **not**
assert that it implements an expression result on the target stack. A consumer
that discards the result must use the actual Source expression-statement phase;
a value-producing expression adapter needs its own result representation.
General admission/lowering, aggregate coverage and runtime correspondence remain
open.

Independent read-only finder and skeptic reviews found no semantic defect in
the resolved expression producer or controls. They checked the complete success
and static-failure endpoints, resource boundary and result-discard distinction.
