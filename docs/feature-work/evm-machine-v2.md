# Core EVM revert and return data (machine version 2, H115 item 1)

Lane `core-p1` (batch p1core-20261107). User decisions H114/H115: the core EVM
model gains revert and return data as an H57 versioned pair, so that an
emitted-code language can observe revert data (V13 P1-REVERT payload bridge,
V15 item 1 `CallReturndataLaw`, RO v2 G42.02 CALL input/returndata).

## What changed

Nothing in `Solidity/Evm/Machine.lean`: `Out`, `Machine`, `Instr`, `exec`,
`run` and every frozen statement are unchanged, and no existing module imports
the new one. Two new modules:

| Declaration | Meaning |
|---|---|
| `Evm.OutV2` | `ok m skip`, `ret m data` (EVM `RETURN`), `revert data`, `fault`. |
| `Evm.MachineV2` | `base : Machine`, `returndata` (return buffer), `reply` (callee oracle: output bytes of a call by callee, value and input), `calls` (ghost journal of `CallRec`). |
| `Evm.InstrV2` | `base i` (frozen instruction, frozen meaning), `revertData`, `ret`, `returndatasize`, `returndatacopy`, `callIn` (CALL with input bytes), `loop` over V2 code. |
| `Evm.runV2`, `execV2`, `loopRunV2` | The V2 interpreter (same structure as the frozen one). |
| `Evm.wordBytes`, `bytesWord`, `readBytes`, `writeBytes` | Byte windows over the word-addressed memory: a window starts at a cell and covers `⌈len/32⌉` cells, big-endian; a slot cell faults. |
| `Evm.OutV2.forget` | V2 → frozen outcome, forgetting data (`ret` forgets to end-of-code success). |
| `Evm.OutV2.exit` | The frame exit as a caller sees it: `some (success?, data)` or `none`. |
| `Evm.lift` | Frozen code as V2 code (`map .base`). |

## Migration and laws

- `execV2_lift`, `run_lift`: lifted frozen code runs as the frozen code on
  `base`, leaving buffer, oracle and journal unchanged (outcome
  `OutV2.ofOut m (run c m.base)`).
- `forget_run_lift`, `forget_run_lift_ofBase`: forgetting a lifted run's data
  is the frozen run. `run_lift_revert`, `run_lift_ok` specialize it.
- `callIn_forget`: `CALLIN`'s balance and stack effect forgets to the frozen
  `CALL` once the input operands are dropped (`accepts` decides acceptance in
  both).
- `callIn_returndata`: the core counterpart of V15's
  `CallReturndataLaw.call_returnData`: an entered call (value covered) leaves
  `reply callee value input` in the buffer and one journal entry with the
  exact input bytes; a call not entered empties the buffer and journals
  nothing. Depth and gas are not modelled (the frozen machine has neither).
- `revertData_forget`: the data-carrying `REVERT` forgets to the frozen one.
- `OutV2.eq_revert_of_exit`, `OutV2.eq_fault`, `OutV2.okView`: decidable
  views so concrete runs are checked with `decide +kernel`.

## Witnesses and controls (`Evm/MachineV2Controls.lean`)

Joint satisfiability: `joint_witness` runs `CALLIN` (callee 7, 4 input bytes),
`RETURNDATACOPY` and `REVERT` with the copied 4 bytes in one run and ends in
`.revert [1, 2, 3, 4]`; `call_journal`, `returndatasize_after_call`,
`return_exit` (RETURN with data, later code not run), `prefix_forget`.
Negative controls: `reply_observed` (another reply, other revert data),
`forget_blind` (the frozen projection cannot tell them apart),
`slot_window_faults`, `copy_past_buffer_faults`, `unentered_empty`,
`refused_entered`, `partial_cell_keeps`. Axioms pinned with `#guard_msgs`.

## Coordination with V15 and RO v2

- V15 (`Bridge/.../P10/CallReturndataLaw.lean`): its buffer is a
  `ByteArray`, set to the callee's `Θ` output when `entered` (balance and
  depth) and emptied otherwise. The core buffer is `List UInt8`
  (= `Roadmap.Bytes`), set by the same disjunction minus depth. A reference
  relation maps `MachineV2.returndata` to `ByteArray.data.toList` and the
  oracle `reply` to the `Θ` output.
- RO v2 G42.02: `CALLIN` reads the input bytes from memory and journals them,
  so an emission can transport `captured.input`; `ReturndataDuty` can be
  pinned to `callIn_returndata`.

## Limits

- The callee's code is not run: `reply` is an oracle and `accepts` still
  decides success, as in the frozen model. There is no depth limit or gas.
- `base .call` keeps the frozen meaning and does not touch the buffer; code
  that needs the buffer uses `callIn`.
- Windows start at a cell (solc's aligned free pointer); unaligned byte
  offsets in memory are not modelled. `RETURNDATACOPY`'s source offset is a
  byte offset.
- No compiler emits V2 code yet; the public compiler and all frozen
  theorems stay on the frozen machine.

## Check-time impact

`Evm/Machine.lean` is unchanged, so none of its dependents rebuilds. The two
new modules are leaves (imported only by the generated root). Elaboration:
`MachineV2.lean` and `MachineV2Controls.lean` each check in seconds per file
in the Lean server.
