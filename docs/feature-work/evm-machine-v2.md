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
| `Evm.OutV2` | `ok m skip`, `ret m data` (EVM `RETURN`), `revert calls data` (EVM `REVERT`, keeping the journal of calls made before it), `fault`. |
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
  is the frozen run. `run_lift_revert`, `run_lift_ok` are corollaries of `run_lift`.
- `callIn_forget`: `CALLIN`'s balance and stack effect forgets to the frozen
  `CALL` once the input operands are dropped (`accepts` decides acceptance in
  both).
- `callIn_returndata`: the core counterpart of V15's
  `CallReturndataLaw.call_returnData`: an entered call (value covered) leaves
  `reply callee value input` in the buffer and one journal entry with the
  exact input bytes; a call not entered empties the buffer and journals
  nothing. Depth and gas are not modelled (the frozen machine has neither).
- `callIn_step`: the `CALLIN` step runs `callInStep` on exactly the bytes of
  its memory window, or faults on a slot cell.
- `revertData_forget`: a data-carrying `REVERT` whose window reads forgets to
  the frozen `REVERT` (the V2 one can also fault: underflow, slot window).
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
`refused_entered`, `self_call_entered`, `input_observed` (a nonzero input
cell and an input-echoing callee: the journal and buffer hold the window's
bytes, another cell gives other bytes), `partial_cell_keeps`. Axioms pinned with `#guard_msgs`.

## Coordination with V15 and RO v2

The V15 law, RO v2's `ReturndataDuty` and the reference relation below are
on those lanes' unmerged branches; nothing on master states them yet, and no
lemma here backs the reference relation (it is the planned shape).

- V15 (`CallReturndataLaw`, P10 module on its branch): its buffer is a
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
- `base .call` keeps the frozen meaning and does not touch the buffer, so
  `RETURNDATASIZE`/`RETURNDATACOPY` after it read a stale buffer, which the
  EVM never does. Data-aware code must use `callIn`; nothing enforces it.
- `accepts` does not see the input while `reply` does, so a callee that
  succeeds for some calldata and reverts for other calldata is not
  expressible, and `reply` is not tied to running any callee's V2 code
  (no frame-composition lemma). V15's `Θ` gives both from one run.
- `forget` sends `ret m _` to `ok m.base 0`: meaningful for a whole frame's
  outcome only (it does not commute with sequencing after a `RETURN`).
  The migration lemmas cover fully lifted code; mixed code and
  `InstrV2.loop (lift c) (lift b)` vs `base (.loop c b)` are not related.
- `CALLIN`'s operands are value, callee, input cell, input length (the
  frozen `CALL` order plus the input window), not the EVM's gas, address,
  value, args, ret window. It has no output window; callee output reaches memory only through
  `RETURNDATACOPY`. A cell-aligned window can fault (slot cell) where the
  EVM would not; `revertData_forget` assumes the window reads.
- Windows start at a cell (solc's aligned free pointer); unaligned byte
  offsets in memory are not modelled. `RETURNDATACOPY`'s source offset is a
  byte offset.
- No compiler emits V2 code yet; the public compiler and all frozen
  theorems stay on the frozen machine.

## Check-time impact

`Evm/Machine.lean` is unchanged, so none of its dependents rebuilds. The two
new modules are leaves imported only by the generated root `Solidity.lean`,
which (with whatever imports the whole library, e.g. the axiom audit) is
re-elaborated. Elaboration:
`MachineV2.lean` and `MachineV2Controls.lean` each check in seconds per file
in the Lean server.

## Reviews (item 1)

Read-only finder and skeptic reviews (no Lean server). Confirmed: frozen
`Machine.lean` untouched; `forget_run_lift` genuine; `callIn_returndata`
exhaustive and non-vacuous; REVERT/RETURN/RETURNDATACOPY operand order and
bounds as in EIP-211. Fixed findings: input transport was uncontrolled (all-zero
input, input-blind reply) → `input_observed`; no self-call control →
`self_call_entered`; `CALLIN` input not tied to its window at step level →
`callIn_step`; doc overclaimed "no rebuild" (the root `Solidity.lean` changes)
and left out the `CALLIN` operand/output-window, `accepts`/`reply`, stale
buffer after `base .call`, `ret` forgetting and conditional `revertData_forget`
caveats → now under Limits; external V15/RO v2 names marked as on their
branches.
