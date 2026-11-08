import Solidity.Backend.AbiEntry.HeadGate
import Solidity.Backend.AbiEntry.HeadCheckControls

/-! Actual public-compiler guard execution, not numeric predicates alone.
Huge metadata heads do not allocate buffers or wrap into small immediates. -/
namespace Solidity.Backend.AbiEntry.HeadGateControls
open Solidity.Evm
open Interface (headGateOutcome)
private def C : Contract := {vars := []}
private def one : List Solidity.AbiEntry.Param := [{shape := .word .bool,loc := .value}]
private def mixed : List Solidity.AbiEntry.Param :=
  [{shape := .tuple [.fixed (.word (.uint 8)) 2,.word .bool],loc := .memory},
   {shape := .array (.word (.uint 256)),loc := .calldata}]
private def huge : List Solidity.AbiEntry.Param :=
  [{shape := .fixed (.word (.uint 256)) (2^256),loc := .memory}]
private def label : Fin W := wmod 99
private def compiled (parameters : List Solidity.AbiEntry.Param) := HeadGate.compiled C 7 parameters label
private def machine (size : Fin W) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=8 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (size : Fin W) : Machine :=
  {machine size with mem := upd (machine size).mem 8 (.val label)}
private theorem actual (parameters : List Solidity.AbiEntry.Param) (size : Fin W) :
    run (compiled parameters).code (machine size)=headGateOutcome 7 parameters label size (machine size) :=
  HeadGate.executed C 7 parameters label (compiled parameters) (HeadGate.selected C 7 parameters label)
    (machine size) size rfl

private theorem reject (parameters : List Solidity.AbiEntry.Param) (size : Fin W)
    (short : size.val<HeadCheck.need parameters) : run (compiled parameters).code (machine size)=.revert := by
  simpa only [headGateOutcome,ite_eq_left short] using actual parameters size
private theorem accept (parameters : List Solidity.AbiEntry.Param) (size : Fin W)
    (full : ¬size.val<HeadCheck.need parameters) : run (compiled parameters).code (machine size)=.ok (written size) 0 := by
  simpa only [written,headGateOutcome,ite_eq_right full] using actual parameters size

theorem empty_boundary :
    run (compiled []).code (machine (wmod 3))=.revert ∧
    run (compiled []).code (machine (wmod 4))=.ok (written (wmod 4)) 0 :=
  ⟨reject [] _ (by decide),accept [] _ (by decide)⟩
theorem bool_boundary :
    run (compiled one).code (machine (wmod 35))=.revert ∧
    run (compiled one).code (machine (wmod 36))=.ok (written (wmod 36)) 0 :=
  ⟨reject one _ (by decide),accept one _ (by decide)⟩
theorem aggregate_boundary :
    HeadCheck.need mixed=132 ∧
    run (compiled mixed).code (machine (wmod 131))=.revert ∧
    run (compiled mixed).code (machine (wmod 132))=.ok (written (wmod 132)) 0 :=
  ⟨rfl,reject mixed _ (by decide),accept mixed _ (by decide)⟩

theorem huge_all_sizes (size : Fin W) : run (compiled huge).code (machine size)=.revert := by
  have bound : W≤HeadCheck.need huge := by decide
  exact reject huge size (Nat.lt_of_lt_of_le size.isLt bound)

theorem huge_no_wrap : HeadCheck.need huge%W=4 ∧ run (compiled huge).code (machine (wmod 4))=.revert :=
  ⟨by decide,huge_all_sizes _⟩

private def shortInput : Solidity.AbiEntry.Input := {data := List.replicate 35 0,free := 0}
theorem short_before_fuel : Solidity.AbiEntry.entry shortInput 0 one=.error .revert :=
  HeadGate.semantic_rejection C 7 one label (compiled one) (HeadGate.selected C 7 one label)
    (machine (wmod 35)) (wmod 35) rfl shortInput (by decide) 0 bool_boundary.1

private def dirty : Solidity.AbiEntry.Input := {data := List.replicate 35 0++[2],free := 0}
theorem passed_head_not_decoded :
    run (compiled one).code (machine (wmod 36))=.ok (written (wmod 36)) 0 ∧
    Solidity.AbiEntry.entry dirty 2 one=.error .revert :=
  ⟨bool_boundary.2,HeadCheckControls.passed_head_not_entry.2⟩

theorem malformed_size_fault :
    run (compiled one).code {machine (wmod 36) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (size : Fin W) :
    (written size).mem 7=.val (wmod 71) ∧ (written size).mem 9=.val (wmod 71) ∧
    (written size).stack=[.val (wmod 258),.val (wmod 513)] ∧ (written size).callvalue=wmod 17 := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.empty_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.bool_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.aggregate_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aggregate_boundary
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.huge_all_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms huge_all_sizes
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.huge_no_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms huge_no_wrap
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.short_before_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_fuel
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.passed_head_not_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms passed_head_not_decoded
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.malformed_size_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_size_fault
/-- info: 'Solidity.Backend.AbiEntry.HeadGateControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.HeadGateControls
