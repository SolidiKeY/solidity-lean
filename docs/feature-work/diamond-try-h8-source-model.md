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

Earlier core-only checkpoints omitted the Bridge relative closure while H7
was unpublished. The published-H7 consumers below now close that dependency.
Their P1/P3 conjuncts still consume supplied premise fields; original-site
provenance stays open.

Generic Panic body (sched 2026-11-03), core only:

- `Evm/TryPanicSource{Control,Bytes,Body,BodyImage,Execution}.lean`: normalized
  bounded Panic caller/return control; the generic Panic bytes; a proof-only
  body (allocation, six guarded byte writes, raw-memory revert) over the
  existing `Stmt`/`Prog`; its byte image and its execution. The execution
  module parameterizes the two single-step glue facts
  (`TryPanicSourceBody.PutThen`, `AllocateRun`); their owned proofs are in
  `Backend/TryCall/PanicNormalization.lean` below. This is not an association
  with the compiled code.

## Checked try-call producer checkpoint

`Backend/TryCall/ProducerInterface.lean` states the intrinsic try-call site and the
checked emitter duties over the existing runtime-frame relations. It is a
signature, not a producer instance: both successful and bare-reverting source
runs must have actual represented entries for the same emitted plan. No
approved-profile coverage or original-site provenance follows from it.

The first intended producer is the bounded H8 known-self-Panic normalization.
Its branch must be derived from the generic body execution, not supplied as a
chosen reply. Core `CALL` currently models a payment flag and has no returndata
or child execution; this checkpoint does not claim a general unknown-call
implementation or the G42 world-call producer. Any specialization must prove
its all-outcome source normalization and actual emitted core instructions.
Original compiled-site provenance remains the readonly-external P3 premise.

### Inhabited bounded producer

`Backend/TryCall/PanicNormalization.lean` proves the two primitive glue steps
without editing the source modules. It derives
both outcomes of the generic known-self Panic body at every caller state.
`PanicEmitter.lean` proves its conditional/store/revert expansion equivalent
to that intrinsic `tryCall`, then supplies the V1 `ReturnClaim` and
`BareRevertClaim` through existing checked compiler and footprint laws.
`PanicControls.lean` constructs represented zero/nonzero receiver entries for
that SAME statement and plan, and inhabits `Producer`.

This is compile-time known-body specialization in the core model. It emits
no synthetic CALL and supplies no unknown-call implementation. Success and
bare revert are real core executions; original solc bytecode, deployment,
installation and original-site/P3 association are not derived. The scope is
not V3 profile coverage. Finder and skeptic read all three modules without
running Lean and found no confirmed defect; kernel diagnostics separately
check the statements. Failed drafts and resource measurements remain in the
worker evidence, including the repaired missing-contract-index elaboration
failure, with no changed proof limit.

### Published H7 consumers

The optional modules `ExternalEvm/TryPanicSourcePadding` and
`ExternalEvm/TryPanicSourceScanner` consume the published H7 word padding and
bounded scanner laws for the retained full runtimes. `TryPanicRelative`
collects their conditional consequences; it does not establish an EvmYul run.
`TryPanicOperational.operational_checked` discharges the independent core
return claim for structurally normalized sites whose emission equals the
checked known-self plan. Original-site `Normalized` and emission association
remain separate unproved adapter inputs; installation and same-invocation
frame provenance remain explicit P3 premises. No original-site
instance, native provider correctness or complete compiled-EVM correspondence
is asserted.
