# Labelled runtime control edges

`Backend/LabelExec/` gives byte-PC execution of the numeric control-flow slice
(from the revert-outcome-specs lane, G45.03). It reuses `Creation.fetch`,
`Scalar.step`, the assembler widths and layout and `validJumpdest`.

`step` fetches at the byte PC in the actual code. JUMP/JUMPI pop typed 256-bit
operands, and an untaken JUMPI skips destination validation. `advance n` means
exactly n supported steps; zero is the identity, not termination or fuel
exhaustion. `none` combines unsupported instructions or fetch refusal, underflow
and a bad target; it is never an EVM error or revert verdict.

- `Packets.lean`: `jump_packet`, `jumpi_packet`, `test_packet` for
  PUSH/JUMP, PUSH/JUMPI and ISZERO/PUSH/JUMPI.
- `Assembly.lean`: `resolved_layout` derives packet bytes, bounded immediate
  readback and scanner validity from `assemble … = some out`;
  `assembled_jump`, `assembled_jumpi`, `assembled_test` need no supplied step.
- `Loops.lean`: `loop_header`, `loop_backedge` for a top-level loop at base 0:
  zero goes to the exit label, nonzero enters the body, the backedge targets
  byte zero. They do not prove body reachability, termination or whole
  structured execution.
- `ScalarTransfer.lean`: `effect_of_scalar` lifts `Scalar.step` results.

Scope: gasless numeric/stack control. No storage, memory, world, gas, account,
terminal result, stack cap, divergence or pinned-EVM correspondence. The
reused fetch refuses a truncated PUSH, unlike full EVM padding. No instance or
negative control is on master yet (the lane's controls depend on unmerged
`Backend/Executable` modules).
