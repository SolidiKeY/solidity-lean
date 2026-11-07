import Solidity.Evm.MachineV2

/-!
# Version-2 EVM machine: witnesses and negative controls

Concrete runs of `Evm/MachineV2.lean`, checked by the kernel (`rfl`):

* `joint_witness` — one run uses every new instruction together: `CALLIN`
  with input bytes, `RETURNDATASIZE`, `RETURNDATACOPY` and `REVERT` with the
  copied data; its frozen projection is the frozen `REVERT`, and the lifted
  frozen prefix agrees with the frozen run (`prefix_forget`).
* `return_witness` — `RETURN` with data: a completed success that is not
  the end of the code.
* Negative controls: the revert data depends on the callee's reply
  (`reply_observed`, so it is not a constant), while the frozen projection
  cannot tell the two apart (`forget_blind`); a window over a storage slot
  faults (`slot_window_faults`); copying past the buffer faults
  (`copy_past_buffer_faults`); a call that is not entered empties the
  buffer and is not journaled (`unentered_empty`); a part-written cell
  keeps its other bytes (`partial_cell_keeps`).
-/

namespace Solidity
namespace Evm
namespace MachineV2Controls

/-- The fixture's code, `CALLIN` to account `7` with value `0` and the
4 input bytes of cell `0`, then copy 4 bytes of the buffer to cell `10`
and revert with them. -/
def callThenRevert : List InstrV2 :=
  [.base (.push w[4]), .base (.push w[0]), .base (.push w[7]), .base (.push w[0]), .callIn,
   .base .pop,
   .base (.push w[4]), .base (.push w[0]), .base (.push w[10]), .returndatacopy,
   .base (.push w[4]), .base (.push w[10]), .revertData]

/-- A fresh machine whose callees answer `out`. -/
def machineWith (out : List UInt8) : MachineV2 :=
  { base := Machine.init, reply := fun _ _ _ => out }

/-- The one journal entry of the fixture: callee `7`, value `0`, the four
input bytes of cell `0`, accepted, answering `out`. -/
def entry (out : List UInt8) : CallRec :=
  ⟨⟨7, by unfold W; decide⟩, ⟨0, W_pos⟩, [0, 0, 0, 0], true, out⟩

/-- **Joint satisfiability**: call, buffer, copy and data-carrying revert in
one run; the revert keeps the journal of the call made before it. -/
theorem joint_witness :
    runV2 callThenRevert (machineWith [1, 2, 3, 4]) = .revert [entry [1, 2, 3, 4]] [1, 2, 3, 4] :=
  OutV2.eq_revertView (by decide +kernel)

/-- Its frozen projection is a bare frozen revert. -/
theorem joint_forget : (runV2 callThenRevert (machineWith [1, 2, 3, 4])).forget = .revert := by
  rw [joint_witness]; rfl

/-- The call itself: entered, flag `1` on the stack, buffer set to the
reply, one journal entry with the exact input bytes. -/
theorem call_journal :
    (runV2 (callThenRevert.take 5) (machineWith [1, 2, 3, 4])).okView =
      some ([w[1]], [1, 2, 3, 4], [entry [1, 2, 3, 4]]) := by
  decide +kernel

/-- `RETURNDATASIZE` after the call reads the buffer's length. -/
theorem returndatasize_after_call :
    ((runV2 (callThenRevert.take 6 ++ [.returndatasize]) (machineWith [1, 2, 3, 4, 5])).okView.map
      (·.1)) = some [w[5]] := by
  decide +kernel

/-- A lifted frozen prefix runs as the frozen code. -/
theorem prefix_forget :
    (runV2 (lift [.push w[4], .push w[0]]) (machineWith [])).forget =
      run [.push w[4], .push w[0]] Machine.init :=
  forget_run_lift _ _

/-- `RETURN` with the 2 leading bytes of cell `3` (`0xABCD…`): success with
data, and the `REVERT` after it does not run. -/
def returnCode : List InstrV2 :=
  [.base (.push w[0xABCD * 2 ^ 240]), .base (.mstore 3),
   .base (.push w[2]), .base (.push w[3]), .ret, .base .revert]

theorem return_exit :
    (runV2 returnCode (machineWith [])).exit = some (true, [0xAB, 0xCD]) := by
  decide +kernel

/-! ## Negative controls -/

/-- **Revert data is observed**: another reply gives other revert data. -/
theorem reply_observed :
    runV2 callThenRevert (machineWith [5, 6, 7, 8]) = .revert [entry [5, 6, 7, 8]] [5, 6, 7, 8] ∧
      (runV2 callThenRevert (machineWith [5, 6, 7, 8])).exit ≠
        (runV2 callThenRevert (machineWith [1, 2, 3, 4])).exit := by
  have h : runV2 callThenRevert (machineWith [5, 6, 7, 8]) =
      .revert [entry [5, 6, 7, 8]] [5, 6, 7, 8] :=
    OutV2.eq_revertView (by decide +kernel)
  refine ⟨h, ?_⟩
  rw [h, joint_witness]
  decide

/-- **The frozen projection is blind to it**: both runs forget to the same
frozen revert. -/
theorem forget_blind :
    (runV2 callThenRevert (machineWith [5, 6, 7, 8])).forget =
      (runV2 callThenRevert (machineWith [1, 2, 3, 4])).forget := by
  rw [reply_observed.1, joint_witness]; rfl

/-- A byte window over a storage slot faults. -/
theorem slot_window_faults :
    runV2 [.base (.push (.slot (.root 0))), .base (.mstore 0),
      .base (.push w[1]), .base (.push w[0]), .revertData] (machineWith []) = .fault :=
  OutV2.eq_fault (by decide +kernel)

/-- Copying past the end of the buffer faults. -/
theorem copy_past_buffer_faults :
    runV2 (callThenRevert.take 6 ++
      [.base (.push w[5]), .base (.push w[0]), .base (.push w[10]), .returndatacopy])
      (machineWith [1, 2, 3, 4]) = .fault :=
  OutV2.eq_fault (by decide +kernel)

/-- A call the contract cannot cover is not entered: flag `0`, empty
buffer (even after an earlier one), nothing journaled. -/
theorem unentered_empty :
    (runV2 [.base (.push w[0]), .base (.push w[0]), .base (.push w[7]), .base (.push w[1]),
        .callIn] { machineWith [9] with returndata := [1] }).okView = some ([w[0]], [], []) := by
  decide +kernel

/-- A refused call is entered: flag `0`, the reply is the revert data in the
buffer, and the journal records the refusal. -/
theorem refused_entered :
    ((runV2 [.base (.push w[0]), .base (.push w[0]), .base (.push w[7]), .base (.push w[0]),
        .callIn] { machineWith [9] with base := { Machine.init with accepts := fun _ _ => false } }
      ).okView.map fun v => (v.1, v.2.1, v.2.2.map (·.success))) =
      some ([w[0]], [9], [false]) := by
  decide +kernel

/-- **The input window is read**: with `0xBEEF…` in cell `0` and a callee
echoing its input, the journal and the buffer hold the window's 2 bytes;
another input cell gives other bytes. -/
def echo : MachineV2 :=
  { base := { Machine.init with mem := upd (fun _ => w[0]) 0 w[0xBEEF * 2 ^ 240] },
    reply := fun _ _ input => input ++ input }

def echoCall (cell : Nat) : List InstrV2 :=
  [.base (.push w[2]), .base (.push (.val ⟨cell % W, Nat.mod_lt _ W_pos⟩)), .base (.push w[7]),
   .base (.push w[0]), .callIn]

theorem input_observed :
    ((runV2 (echoCall 0) echo).okView.map fun v => (v.2.1, v.2.2.map (·.input))) =
      some ([0xBE, 0xEF, 0xBE, 0xEF], [[0xBE, 0xEF]]) ∧
    ((runV2 (echoCall 1) echo).okView.map fun v => (v.2.1, v.2.2.map (·.input))) =
      some ([0, 0, 0, 0], [[0, 0]]) := by
  decide +kernel

/-- A self-call (callee `self = 0`) is entered: flag `1`, the reply in the
buffer, journaled, no balance moved. -/
theorem self_call_entered :
    ((runV2 [.base (.push w[0]), .base (.push w[0]), .base (.push w[0]), .base (.push w[0]),
        .callIn] (machineWith [3])).okView.map fun v => (v.1, v.2.1, v.2.2.length)) =
      some ([w[1]], [3], 1) := by
  decide +kernel

/-- Writing two bytes into a cell keeps its other thirty. -/
theorem partial_cell_keeps :
    (writeBytes (fun _ => w[2 ^ 256 - 1]) 0 [0, 0]).map (fun mem => mem 0) =
      some w[2 ^ 240 - 1] := by
  decide +kernel

end MachineV2Controls
end Evm
end Solidity

/-- info: 'Solidity.Evm.forget_run_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.forget_run_lift
/-- info: 'Solidity.Evm.MachineV2Controls.joint_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.MachineV2Controls.joint_witness
/-- info: 'Solidity.Evm.callIn_returndata' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.callIn_returndata
