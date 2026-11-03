# G21 closed failure lowering

Source failure expressions with constant payloads, lowered through the
published terminal emitter (`Lowering/V08/`). From the v13-abi-world lane.

## Proved

- `LiteralFailureLowering.lean`: `literalInput` is a syntactic compiler for
  closed `assert(false)`, `revert()`, `revert("…")`, `require(false[, "…"])`
  and literal panics; `emitLiteral` emits the terminal code. `*_source`
  theorems run the actual `evalE`/`execS`; `literalInput_sound` and
  `literal_lowered` (with `assert_lowered`, `reason_lowered`,
  `require_lowered`) give the target terminal bytes. Effectful or non-literal
  arguments are refused.
- `BoolErrorLowering.lean`: custom errors with a closed list of boolean
  arguments. `encoded`/`payload` compute the ABI payload, `source_run` runs the
  source statement, `emitted_run` the target. `emit` takes the boolean list as
  a meta-level input (a constant-payload emitter, not a function of the
  statement); `lowered` pairs the two facts through the shared payload.
- `SliceFailureLowering.lean`: calldata-slice evaluation in the existing
  evaluator (`accepted`, `reversed`, `beyond`, `exhausted`, `accepted_toEnd`).
  `lowered_reversed` pairs the source revert with the empty terminal emitter;
  the target side does not depend on the slice expression, so this is a
  source-side slice result plus an empty terminal, not a lowered bounds check.
- `*Controls.lean`: concrete clients, old-memory and low-horizon controls,
  wrong order/length/byte-order negatives.

## Open

Runtime-value encoders, reading unknown memory or calldata, emitted bounds
checks, catch semantics, source-world simulation.

## Source ABI failure consumers (sched 2026-11-03)

`Lowering/V08/` modules from the V13 help branch, each with a `*Controls`
module. They consume existing Source definitions, ABI codecs and decoder arms;
none adds an AST, evaluator, decoder or admission rule.

- `BoolErrorAbi`, `BoolErrorStatement`, `BoolErrorCompleteness`: closed Boolean
  custom-error payloads agree with the indexed ABI codec; an executable
  selector on existing typed statements; completeness for the supported
  literal family only. `LiteralFailureBoolStatement` adds typed Boolean error
  statement selection with exact error-span bounds.
- `LiteralFailureCalldataDecode`, `LiteralFailureSliceDecode`,
  `LiteralFailureChoiceDecode`, `LiteralFailureEffectDecode`: progress and
  preservation through the calldata `abi.decode` arm, calldata slices,
  conditional data selection, and local-assignment effects surviving a decode
  failure.
- `LiteralFailureStorageDecode`, `LiteralFailureStorageSuccessControls`: storage
  byte copies and typed local decoding; the canonical success case with the
  exact caller state.
- `LiteralFailureDynamicError`, `LiteralFailureDynamicListError`: heap-backed
  custom-error encoding, mixed and arbitrary-length typed reference lists.
- `LiteralFailurePackedBytes`, `LiteralFailureSignatureBytes`,
  `LiteralFailureSelectorBytes`, `LiteralFailureEncodedRethrow`: packed bytes
  reads with fresh allocation, signature encoding with alias preservation,
  selector-local expression execution, rethrow of allocated ABI payloads.

Not on master: `LiteralFailureBytesReadback{,Controls}` (they import
`Solidity.Backend.AbiWorld.ErrorRoundtrip`, which does not exist). No runtime
target encoder, source/target simulation or admission theorem is claimed.


### Tuple-return argument failure

`LiteralFailureTupleAbort` consumes an actual failed `evalConvArgs` execution and derives the exact failed tuple-return statement. Its subcomputation locals are discarded while its actual Source state is retained; this is not transaction rollback. Controls discharge the premise with an assignment followed by division by zero and distinguish a skipped later assignment from a positive divisor-one tuple return. Return-slot extraction, older aliases, timeout and nonempty Panic payload remain explicit. These statement components do not establish complete function admission, target lowering or unknown-memory result encoding.
