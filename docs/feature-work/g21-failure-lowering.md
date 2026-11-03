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
