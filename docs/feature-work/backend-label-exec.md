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

- `Placement.lean`: `loop_header_at`, `loop_backedge_at` generalize the local
  control packets to arbitrary preceding/following assembler items. The whole
  runtime still assembles at base zero; this is not external section relocation.
- `Fragment.lean` / `FragmentSound.lean`: intrinsically indexed refinements of
  existing `Block` and numeric code, with exact arities and prefix capacity.
  `InstrShape.fetched_step` derives an actual successor vector from physical
  operand availability, not a selected run premise. Structured tests reserve
  two temporary words. These single-step facts do not yet prove whole-block
  simulation or loop termination.
- `FragmentControls.lean`: underflow/capacity controls and an admitted condition
  that changes a lower word. Height preservation is not value-frame preservation.
- `Checks.lean`: a standalone assembled loop witness after a nonempty prefix
  reaches byte offset 3, plus retained invalid-target, underflow, truncated-PUSH
  and PUSH-data controls. It imports no unmerged `Backend/Executable` modules.

- `LiteralLoops.lean`: `literal_loop_header_at` starts before the actual emitted
  loop-head JUMPDEST, executes it and the condition PUSH, and derives both test
  outcomes from `Scalar.immediate imm.toList`. This eliminates the independent
  reached-test/condition premise for literal conditions, with arbitrary placement,
  body and physical tail. The five-step cut ends at the exit label or body entry;
  it does not execute that label/body or establish whole-loop termination.
- `LiteralChecks.lean`: actual assembly-existence clients for zero and nonzero
  literals, retaining the emitted target/continuation PCs. These controls need no
  V14 Executable modules or separately selected destination table.

- `Boundaries.lean`: `fetch_at` derives both instruction and suffix from an
  actual program index; `step_at` retains its exact effect/refusal, and
  `assembled_tag_step` executes a resolved tag at its emitted byte offset.
  `step_at_end` records EOF refusal of this slice, not an EVM halt verdict.
- `LoopExit.lean`: `zero_loop_complete` consumes the zero-literal loop's actual
  head, test and exit JUMPDEST in six steps. It reaches the byte immediately
  after the loop with the original tail, without any body-run premise.
- `LoopExitControls.lean`: actual assembly of a zero loop with unsupported STOP
  in its body still executes past that unfetched body to EOF in six steps. Its
  seventh step refuses. This makes the boundary/termination distinction concrete.

Scope: gasless numeric/stack control. No storage, memory, world, gas, account,
terminal result, divergence or pinned-EVM correspondence. Static capacity is
checked for the complete declared input height; adding a protected tail needs
its own capacity check. The reused fetch refuses a truncated PUSH, unlike full
EVM padding. A local assembled packet witness does not prove entry reachability.

The omitted peer Executable modules are not restored. No original Revert
source/native completion is claimed.
