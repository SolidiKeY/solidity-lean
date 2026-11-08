import Solidity.Backend.AbiEntry.UIntBindingBody

/-! Actual one-artifact body execution and failures, distinguished from raw
entry rejection. No body result is supplied to the composition certificate. -/
namespace Solidity.Backend.AbiEntry.UIntBindingBodyControls
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx rawArgumentWord singleWordParams uintBoundMachine)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def BodyCtx : Ctx := .val .uint :: UIntBoundCtx
private def body : Prog C UIntBoundCtx BodyCtx :=
  .cons (.declLocal .uint (.user "observed") (some
    (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 (by decide)))))) .nil
private theorem bodyCore : inFragP (Frag.init UIntBoundCtx) body=some (Frag.init BodyCtx) := by rfl
private def whole := UIntBindingBody.selectedWhole 7 8 label body (Frag.init BodyCtx) bodyCore
private def back := UIntBindingBody.selectedBody 7 body (Frag.init BodyCtx) bodyCore
private def good : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[255,0x77,0x88],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 30 0++[1,0],free := 71}
private def machine (input : Solidity.AbiEntry.Input) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) : Machine :=
  uintBoundMachine 7 label (rawArgumentWord input) (machine input)
private def finished : Machine := {bound good with mem := upd (bound good).mem 10 (.val (wmod 256))}
private theorem actual (input : Solidity.AbiEntry.Input) :
    run whole.code (machine input)=if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord input).val then run back.code (bound input) else .revert :=
  UIntBindingBody.executed 7 8 label body (Frag.init BodyCtx) bodyCore whole back
    (UIntBindingBody.whole_selected 7 8 label body _ bodyCore)
    (UIntBindingBody.body_selected 7 body _ bodyCore) (machine input) _ _ rfl rfl

private theorem body_run : run back.code (bound good)=.ok finished 0 := by
  have bodyCode : back.code=[.mload 9,.push (.val (wmod 1))]++uTail .add++[.mstore 10] := by rfl
  have argument : (bound good).mem 9=.val (wmod 255) := by decide
  have loaded : run [.mload 9,.push (.val (wmod 1))] (bound good)=
      .ok {bound good with stack := w[1]::w[255]::(bound good).stack} 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,argument]
    rfl
  have added := add_tail (bound good) (bound good).stack (a := 255) (b := 1) (by decide) (by decide)
  rw [dite_eq_left (by decide : 255+1<W)] at added
  rw [bodyCode,List.append_assoc,run_append_ok loaded,run_append_ok added]
  rfl

theorem selected_and_changes :
    Compiler.compile 7 (Frag.init RouteCtx) (UIntBindingBody.program 8 label body)=some whole ∧
    Compiler.compile 7 (Frag.init UIntBoundCtx) body=some back ∧
    run whole.code (machine good)=.ok finished 0 := by
  refine ⟨UIntBindingBody.whole_selected 7 8 label body _ bodyCore,
    UIntBindingBody.body_selected 7 body _ bodyCore,?_⟩
  have full : ¬(wmod good.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord good).val=true := by decide
  rw [actual,ite_eq_right full,ite_eq_left valid,body_run]

theorem decoded_argument (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.uint 8),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams (.uint 8))=
        .ok (.cons (.val (.word value)) .nil) ∧
      (bound good).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run whole.code (machine good)=run back.code (bound good) :=
  UIntBindingBody.decoded_body 7 8 label body (Frag.init BodyCtx) bodyCore whole back
    (UIntBindingBody.whole_selected 7 8 label body _ bodyCore)
    (UIntBindingBody.body_selected 7 body _ bodyCore) good fuel (machine good) (wmod good.size)
    rfl rfl (by decide) (by decide) (by decide)

theorem invalid_prevents_body (fuel : Nat) :
    run whole.code (machine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.uint 8))=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬(Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord dirty).val=true := by decide
  constructor
  · rw [actual,ite_eq_right full,ite_eq_right invalid]
  · rw [SingleWordGate.entry_form]
    have size : ¬dirty.size<36 := by decide
    rw [ite_eq_right size]
    exact dite_eq_right invalid

theorem short_prevents_word_and_body :
    run whole.code {machine good with
      mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert :=
  UIntBindingBody.short_before_body 7 8 label body _ bodyCore _ (wmod 35) rfl (by decide)

private def rejecting : Prog C UIntBoundCtx UIntBoundCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init UIntBoundCtx) rejecting=some (Frag.init UIntBoundCtx) := by rfl
private def rejectWhole := UIntBindingBody.selectedWhole 7 8 label rejecting _ rejectingCore
private def rejectBack := UIntBindingBody.selectedBody 7 rejecting _ rejectingCore

theorem body_failure_not_decoder_failure (fuel : Nat) :
    run rejectWhole.code (machine good)=.revert ∧
    ∃ value : Solidity.AbiEntry.Word (.uint 8),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams (.uint 8))=.ok (.cons (.val (.word value)) .nil) := by
  constructor
  · have actualReject := UIntBindingBody.executed 7 8 label rejecting _ rejectingCore rejectWhole rejectBack
      (UIntBindingBody.whole_selected 7 8 label rejecting _ rejectingCore)
      (UIntBindingBody.body_selected 7 rejecting _ rejectingCore) (machine good) (rawArgumentWord good) (wmod good.size) rfl rfl
    have full : ¬(wmod good.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord good).val=true := by decide
    rw [actualReject,ite_eq_right full,ite_eq_left valid]
    rfl
  · exact ⟨_,SingleWordGate.entry_success good fuel (.uint 8) (by decide) (by decide)⟩

theorem fuel_boundary :
    run whole.code (machine good)=.ok finished 0 ∧
    Solidity.AbiEntry.entry good 0 (singleWordParams (.uint 8))=.error .fuel ∧
    Solidity.AbiEntry.entry good 1 (singleWordParams (.uint 8))=.error .fuel :=
  ⟨selected_and_changes.2.2,SingleWordGate.insufficient_fuel good (.uint 8) (by decide)⟩

theorem protected_and_saved :
    finished.mem 7=.val (rawArgumentWord good) ∧ finished.mem 8=.val label ∧
    finished.mem 9=.val (wmod 255) ∧ finished.mem 10=.val (wmod 256) ∧ finished.mem 11=.val (wmod 71) ∧
    finished.stack=[.val (wmod 258),.val (wmod 513)] ∧ finished.callvalue=wmod 17 ∧
    finished.store=(machine good).store ∧ finished.bal=(machine good).bal :=
  ⟨rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.selected_and_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_and_changes
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.decoded_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_argument
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.invalid_prevents_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_prevents_body
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.short_prevents_word_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_prevents_word_and_body
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.body_failure_not_decoder_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_failure_not_decoder_failure
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBodyControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.UIntBindingBodyControls
