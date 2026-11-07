# G21 typed boolean-literal custom-error statement adapter

Checkpoint `09a73f5bd7f66f07567aa70a7b106ba4caf82738` adds only
`Solidity.Lowering.V08.BoolErrorStatement` and its Controls module. Published
base is `629abfd551730581f077e6701a04d78405c9a69b`; original V13 frozen base
remains `2fe1f8932f96be15b00df03ba2cde46f64a87758`.

`literalArgs` and `statementView` select the actual intrinsic typed statement.
Their dependent views certify syntax identity, including parameter types and
unchanged output context. `emitStatement` is a partial adapter for existing
custom-error statements whose boolean arguments are literals. It refuses live
local arguments and other statements; this does not alter source admission.

`selected_witness` derives the declaration and literal list from actual option
selection. `selected_correct` proves the existing source execution at horizon
`bits.length + extra + 4` and the existing Failure.Slice emitted execution.
It retains `Fits` and the two-stack-slot capacity condition. The source state
uses the same published L0/state convention. This is not unknown-value ABI
encoding, a new source evaluator, or general lowering/runtime/world coverage.

Controls use the populated published caller, old heap alias and state through
`client`. `concrete_target` executes the code extracted from actual selection,
with architectural conditions discharged by the published fixture. Empty
selection, supported nonempty selection, valid-source local refusal and skip
refusal are kernel checks. No previous payload or complete byte observation
was changed; selection equals the existing emitter exactly. There are no new
compiler/native/EVM vectors or pipeline-agreement claims.

Automation attempts preceded hard proof steps. The initial syntax/continuation
errors and fixture context-name error are retained in raw evidence. Final
per-file diagnostics are complete with no errors. Toolkit per-file checks
pass both modules; eight scoped axiom outputs contain only propext,
Classical.choice and Quot.sound. No limits or semantics changed.

Independent read-only finder and skeptic inspected the syntax views and
soundness hypotheses. Both requested a populated application of the selector
soundness theorem; this was added as client and concrete_target. Final source
and immutable artifact reviews accompany the seal separately. No reviewer ran
Lean or builds.

All original G40/G41/G42 and Backfills A/B remain partial. P1-REVERT is now
published and its prerequisite closure has passed; approved-profile provenance
and general source/runtime frames remain distinct. G21 all-profile calldata,
nested/reference/catch lowering remains open. Published P2/P3/P6 supply real
conditional interfaces, not automatic execution linkage. Unknown-memory ABI
encoding, general CALL/RETURNDATA source origin, arbitrary callee/world/resource
composition and mandatory whole-lane gates remain open. G42.03 and P3 belong
to readonly-external; no work here modifies those owners. Historical Suite124,
full1, cold124, bodyexport1, MCP failures and docs1/frozen-comparison1 remain
failed. Prior/publication finding equality is a separate comparison. No
unchanged failed full gate was rerun. Goal identity and blocked status are
unchanged. Coordinator registers new modules; Solidity.lean is untouched.
