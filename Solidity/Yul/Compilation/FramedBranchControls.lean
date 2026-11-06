import Solidity.Yul.Compilation.FramedBranch
import Solidity.Yul.Compilation.SignedClosedExecutionControls
/-! Concrete branch-tail controls. An untaken genuinely faulting arm is allowed;
zero selects that failure, while a dirty nonzero word selects a real literal
producer. Full numeric input/caller contents and all machine fields remain. -/
namespace Solidity.Yul.Compilation.FramedBranch.Controls
open Backend Scalar Selection MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def yesCode : Backend.Program := [pushWord dirty]
def yesModel : List Evm.Instr := [.push (coreWord dirty)]
def noCode : Backend.Program := [.op .SDIV]
def noModel : List Evm.Instr := [.sdiv]
def left : FramedLoweringCertificate yesModel (.code yesCode) :=
 FramedWordLowering.lowering yesCode yesModel (by rfl)
def right : FramedLoweringCertificate noModel (.code noCode) :=
 FramedWordLowering.lowering noCode noModel (by rfl)

/-- Nontrivial successful chosen arm for every numeric caller, even though
SDIV in the untaken arm faults on empty/singleton inputs. -/
theorem chosen_literal (input : Stack) (m : Evm.Machine) :
 Evm.run (MachineControl.branchTail yesModel noModel)
  {m with stack := coreWord dirty::irStack input} =
 .ok {m with stack := irStack (dirty::input)} 0 := by
 have trace : StructuredExec (.code yesCode) input (dirty::input) := .code (by rfl)
 have nonzero : dirty ≠ 0 := by decide
 have taken : (if dirty = 0 then StructuredExec (.code noCode) input (dirty::input)
   else StructuredExec (.code yesCode) input (dirty::input)) := by
  simpa only [if_neg nonzero] using trace
 simpa only [] using tail_forward left right dirty input (dirty::input)
  {m with stack := irStack input} rfl taken

theorem empty_untaken_fault (m : Evm.Machine) :
 Evm.run noModel {m with stack := []} = .fault := rfl

theorem zero_takes_fault (m : Evm.Machine) :
 Evm.run (MachineControl.branchTail yesModel noModel)
  {m with stack := [coreWord 0]} = .fault := rfl

/-- Reflection still recovers the exact numeric frame, not merely a preferred
output chosen by the forward witness. -/
theorem reflected (input : Stack) (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run (MachineControl.branchTail yesModel noModel)
   {m with stack := coreWord dirty::irStack input} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {m with stack := irStack output} ∧
 StructuredExec (.code yesCode) input output := by
 have nonzero : dirty ≠ 0 := by decide
 have actual := tail_reflect left right dirty input {m with stack := irStack input} final skip rfl ran
 simpa only [if_neg nonzero] using actual

/-- The other arm also has genuine successful inputs, not a fabricated
always-faulting certificate: signed division of6by2 yields3. -/
theorem zero_division (m : Evm.Machine) :
 Evm.run (MachineControl.branchTail yesModel noModel)
  {m with stack := coreWord 0::irStack [6,2]} =
 .ok {m with stack := irStack [3]} 0 := by
 have trace : StructuredExec (.code noCode) [6,2] [3] := .code (by decide)
 have taken : (if (0 : Scalar.Word) = 0 then StructuredExec (.code noCode) [6,2] [3]
   else StructuredExec (.code yesCode) [6,2] [3]) := by simpa only [if_pos rfl] using trace
 simpa only [] using tail_forward left right 0 [6,2] [3] {m with stack := irStack [6,2]} rfl taken

#guard Scalar.run noCode [] = none
#guard Scalar.run noCode [dirty] = none
#guard dirty.toNat > 2^200
#guard Scalar.run yesCode [1,2,3] = some [dirty,1,2,3]
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms left
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms right
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.chosen_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chosen_literal
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.empty_untaken_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_untaken_fault
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.zero_takes_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_takes_fault
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.zero_division' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_division

/-- A nonzero guard whose low byte is zero still selects the successful arm;
truncating the guard would instead choose the demonstrated SDIV fault. -/
theorem high_only_guard (m : Evm.Machine) :
 Evm.run (MachineControl.branchTail yesModel noModel)
  {m with stack := [coreWord (BitVec.ofNat 256 (2^200))]} =
 .ok {m with stack := irStack [dirty]} 0 := by
 have nonzero : (BitVec.ofNat 256 (2^200)) ≠ 0 := by decide
 have trace : StructuredExec (.code yesCode) [] [dirty] := .code (by rfl)
 have taken : (if (BitVec.ofNat 256 (2^200)) = 0 then StructuredExec (.code noCode) [] [dirty]
   else StructuredExec (.code yesCode) [] [dirty]) := by simpa only [if_neg nonzero] using trace
 simpa only [] using tail_forward left right (BitVec.ofNat 256 (2^200)) [] [dirty]
  {m with stack := []} rfl taken

#guard (BitVec.ofNat 256 (2^200)).toNat % 256 = 0
/-- info: 'Solidity.Yul.Compilation.FramedBranch.Controls.high_only_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_only_guard
end Solidity.Yul.Compilation.FramedBranch.Controls
