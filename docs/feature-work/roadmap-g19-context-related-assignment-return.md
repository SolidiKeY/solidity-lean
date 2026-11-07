# G19: context-related Boolean assignment-return control

The target program is hand-written. Context mapping relates its locals to Source locals; it does not establish a generated lowering endpoint.

One Source statement shape is covered: `if (x = y) return;` for Boolean locals,
with a bare return. This is not whole-function/control-flow/modifier lowering.
The new Lowering/G19 modules consume V07 read-only and add no source AST,
evaluator, state carrier or second lowering relation.

[AssignmentReturnFlag](../../Solidity/Lowering/G19/AssignmentReturnFlag.lean)
derives both target positions from V07 ContextMap using typed Boolean slot
proofs. Its code is exactly assignLocalOperand.code. The existing fresh capture
is used as this statement's return-control flag.

`correct` takes initial ContextMap.Related, independent Boolean reflection,
slot-type facts and two explicit slot equations. It derives actual Source.execS,
actual target prefix execution, reached heterogeneous-local alignment, captured
control Boolean and preserved target globals. No desired-run/preservation
premise is supplied. The routine universal slot-projection lemma remains a
Terra obligation; concrete clients close both equations by reflexivity.
No P8 producer or whole-world relation is assumed.

`source_run` proves the actual equations at fuel+3. `source_zero` retains timeout
at resource0. This is not an input-profile unrolling bound or arbitrary-horizon
positive theorem. Continuation suppression, return values, general conditions,
loops/modifiers/constructors and whole Source/EVM correspondence remain open.

[Controls](../../Solidity/Lowering/G19/AssignmentReturnFlagControls.lean)
reuse V07's six-binding fixture: two Booleans, two integers, live memory and
storage references. True assignment changes false to true and returns; false
assignment changes true to false and completes normally. Both pipelines,
every fuel offset and both checked modes are quantified. The yes/no controls
explicitly retain reached Related alignment. Separate repeated-index alias,
stale-initial-guard and wrong-map controls test runs, values and positions.
These are kernel Source/intrinsic facts, not solc/EVM differential observations.

Validation: shared per-file checks, complete type AND value/dependency/axiom
extraction of16 declarations under100000-node/512-depth limits, independent
live replay, generated local axiom guards and independent read-only reviews.
Exact final commands/exits/resource receipts are in the checkpoint handoff.
No global pin/ledger/profile/verdict/budget/core registration is edited.
Coordinator registers the two new modules. All457 release rows remain open.
