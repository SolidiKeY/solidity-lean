# Diamond try H8: bounded source model

Core and example modules of the next10/diamond-try H8 checkpoint: the pinned
try/panic source and its finite-memory model, generic in the local length.

- `Evm/TryPanicSourcePlan.lean`: the fixed mstore0/mstore4/revert `ThreeOp`
  plan; `BodyCompletedAt` finite-memory completion, with the length taken from
  the local.
- `Evm/TryPanicSourceFrame.lean`: `FiniteEntry` (the prologue frame `entryK`),
  `dataK`, and the reduction to `computed36` at local 36.
- `Evm/TryPanicSourceDeterminism.lean`: completion inversion and uniqueness;
  capacity and range refusals.
- `Frontend/SolcJson/TryPanicSource{Data,Plan,Caller}.lean`: the quoted pinned
  AST and input; `DerivesWholeF`/`DerivesWholeC36` structural derivations with
  inversion soundness.
- `Examples/Tactics/TryPanicSource{Plan,Determinism,Whole}.lean`: length
  controls, refusals and JSON-mutation refusals.

Not on master yet: the Bridge relative closure (`ExternalEvm/TryPanicRelative`,
`TryPanicSourcePadding`, `TryPanicSourceScanner`), which needs the H7 padding
and scanner supplier and the vendor overlay. In that theorem the P1/P3
conjuncts restate supplied premise fields; P1/P3 provenance stays open.

Generic Panic body (sched 2026-11-03), core only:

- `Evm/TryPanicSource{Control,Bytes,Body,BodyImage,Execution}.lean`: normalized
  bounded Panic caller/return control; the generic Panic bytes; a proof-only
  body (allocation, six guarded byte writes, raw-memory revert) over the
  existing `Stmt`/`Prog`; its byte image and its execution. Two single-step
  glue facts (`TryPanicSourceBody.PutThen`, `AllocateRun`) are parameters, not
  proved. This is not an association with the compiled code.
- Still not on master: the Bridge `TryPanicOperational` adapter, which imports
  the relative closure above.

