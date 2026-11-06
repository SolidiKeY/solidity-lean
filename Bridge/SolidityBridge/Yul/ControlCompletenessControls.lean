import SolidityBridge.Yul.ControlCompleteness
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.ControlCompleteness.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
open ControlRealization
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
#check branch_lowering
#check sequence_lowering
#check nested_lowering
#check prefixed_lowering
-- Constructive source-derived model witness through the whole iff certificate.
def prefixed_witness := (prefixed_lowering.success
  (#v[dirty,99].toList ++ (#v[highOnly,17].toList ++ [77]))
  (#v[dirty,99].toList ++ ((StructuredSource.compiled.update #v[highOnly,17]).toList ++ [77]))
  (machine [dirty,99,highOnly,17,77]) rfl).mpr
  (StructuredSource.prefixed_execution #v[highOnly,17] #v[dirty,99] [77])
#check prefixed_witness
#guard observe (Evm.run prefixedSelected.ir (machine [dirty,99,highOnly,17,77])) ==
  some ([some dirty.toNat,some 99,some highOnly.toNat,some 18,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run nestedSelected.ir (machine [highOnly,maximum,77]))).map (fun s => s.1) == some [some highOnly.toNat,some 0,some 77]
#guard (observe (Evm.run nestedSelected.ir (machine [highOnly,0,77]))).map (fun s => s.1) == some [some highOnly.toNat,some 0,some 77]
#guard (observe (Evm.run sequenceSelected.ir (machine [dirty,0,77]))).map (fun s => s.1) == some [some 0,some 0,some 77]
#guard (observe (Evm.run sequenceSelected.ir (machine [0,dirty,77]))).map (fun s => s.1) == some [some dirty.toNat,some (dirty+1).toNat,some 77]
-- Untaken underflow is allowed, taken underflow has no StructuredExec result.
def inactiveBlock : Backend.Block := .ite [pushWord 0] (.code [.op .ADD]) (.code [])
def activeBlock : Backend.Block := .ite [pushWord 1] (.code [.op .ADD]) (.code [])
def inactive := (selectBlock inactiveBlock).get (by rfl)
def active := (selectBlock activeBlock).get (by rfl)
def inactive_lowering := selected_lowering inactive (by rfl)
def inactive_witness := (inactive_lowering.success [] [] (machine []) rfl).mpr
  (StructuredExec.iteFalse (by rfl) (StructuredExec.code (by rfl)))
def active_no_success := (fault_iff active (by rfl) [] (machine []) rfl).mp (by rfl)
#check inactive_witness
#check active_no_success
-- Both classifier failure paths for sequences and a successful empty condition
-- result which faults at JUMPI because it supplies no condition operand.
def leftFaultBlock : Backend.Block := .seq (.code [.op .ADD]) (.code [])
def rightFaultBlock : Backend.Block := .seq (.code []) (.code [.op .ADD])
def emptyTestBlock : Backend.Block := .ite [] (.code []) (.code [])
def faultTestBlock : Backend.Block := .ite [.op .ADD] (.code []) (.code [])
def leftFault := (selectBlock leftFaultBlock).get (by rfl)
def rightFault := (selectBlock rightFaultBlock).get (by rfl)
def emptyTest := (selectBlock emptyTestBlock).get (by rfl)
def faultTest := (selectBlock faultTestBlock).get (by rfl)
def left_no_success := (fault_iff leftFault (by rfl) [dirty] (machine [dirty]) rfl).mp (by rfl)
def right_no_success := (fault_iff rightFault (by rfl) [] (machine []) rfl).mp (by rfl)
def empty_no_success := (fault_iff emptyTest (by rfl) [] (machine []) rfl).mp (by rfl)
def test_no_success := (fault_iff faultTest (by rfl) [dirty] (machine [dirty]) rfl).mp (by rfl)
#check left_no_success
#check right_no_success
#check empty_no_success
#check test_no_success
#check fault_iff nestedSelected (by rfl) [1] (machine [1]) rfl
#guard (selectBlock (.loop [] (.code []))).isNone
#guard (selectSlice [.op .SUB]).isNone
#guard (selectSlice [.push 1 #v[1]]).isNone
#guard (LiteralSelection.select (.dup 17)).isNone
#guard (LiteralSelection.select (.swap 17)).isNone
#guard (LiteralSelection.select (.dup 0)).isNone
#guard (LiteralSelection.select (.swap 0)).isNone
#guard !(Scalar.stackBound [pushWord dirty] 1024)
-- Total outcome classification is about the unchanged uncapped model, not
-- physical validity of an oversized EVM stack or expanded native join jumps.
#guard (observe (Evm.run nestedSelected.ir (machine (highOnly::17::List.replicate 1021 77)))).isSome

-- Generated from the scoped kernel axiom report; each report is enforced.
/-- info: 'SolidityBridge.Yul.ControlCompleteness.append_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.append_fault
/-- info: 'SolidityBridge.Yul.ControlCompleteness.true_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.true_out
/-- info: 'SolidityBridge.Yul.ControlCompleteness.false_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.false_fault
/-- info: 'SolidityBridge.Yul.ControlCompleteness.scalar_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.scalar_classified
/-- info: 'SolidityBridge.Yul.ControlCompleteness.sequence_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.sequence_classified
/-- info: 'SolidityBridge.Yul.ControlCompleteness.conditional_classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.conditional_classified
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_classified
/-- info: 'SolidityBridge.Yul.ControlCompleteness.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.fault_iff
/-- info: 'SolidityBridge.Yul.ControlCompleteness.branch_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.branch_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.sequence_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.sequence_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.nested_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.nested_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.prefixed_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.prefixed_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.prefixed_witness
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.inactive_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.inactive_witness
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.active_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.active_no_success
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.left_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.left_no_success
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.right_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.right_no_success
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.empty_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.empty_no_success
/-- info: 'SolidityBridge.Yul.ControlCompleteness.Controls.test_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.Controls.test_no_success
end SolidityBridge.Yul.ControlCompleteness.Controls
