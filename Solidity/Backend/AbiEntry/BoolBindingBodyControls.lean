import Solidity.Backend.AbiEntry.BoolBindingBody

/-! Actual one-artifact body execution and failures, distinguished from raw
entry rejection. No body result is supplied to the composition certificate. -/
namespace Solidity.Backend.AbiEntry.BoolBindingBodyControls
open Solidity.Evm
open Interface (RouteCtx BoolBoundCtx rawArgumentWord singleWordParams boolBoundMachine)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def BodyCtx : Ctx := .val .bool :: BoolBoundCtx
private def body : Prog C BoolBoundCtx BodyCtx :=
  .cons (.declLocal .bool (.user "observed") (some
    (.unop .not rfl rfl (.simple (.local .here))))) .nil
private theorem bodyCore : inFragP (Frag.init BoolBoundCtx) body=some (Frag.init BodyCtx) := by rfl
private def whole := BoolBindingBody.selectedWhole 7 label body (Frag.init BodyCtx) bodyCore
private def back := BoolBindingBody.selectedBody 7 body (Frag.init BodyCtx) bodyCore
private def good : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[1,0x77,0x88],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[2],free := 71}
private def machine (input : Solidity.AbiEntry.Input) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) : Machine :=
  boolBoundMachine 7 label (rawArgumentWord input) (machine input)
private def finished : Machine := {bound good with mem := upd (bound good).mem 10 (.val (wmod 0))}
private theorem actual (input : Solidity.AbiEntry.Input) :
    run whole.code (machine input)=if (wmod input.size).val<36 then .revert else
      if Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord input).val then run back.code (bound input) else .revert :=
  BoolBindingBody.executed 7 label body (Frag.init BodyCtx) bodyCore whole back
    (BoolBindingBody.whole_selected 7 label body _ bodyCore)
    (BoolBindingBody.body_selected 7 body _ bodyCore) (machine input) _ _ rfl rfl

private theorem body_run : run back.code (bound good)=.ok finished 0 := by rfl

theorem selected_and_changes :
    Compiler.compile 7 (Frag.init RouteCtx) (BoolBindingBody.program label body)=some whole ∧
    Compiler.compile 7 (Frag.init BoolBoundCtx) body=some back ∧
    run whole.code (machine good)=.ok finished 0 := by
  refine ⟨BoolBindingBody.whole_selected 7 label body _ bodyCore,
    BoolBindingBody.body_selected 7 body _ bodyCore,?_⟩
  have full : ¬(wmod good.size).val<36 := by decide
  have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord good).val=true := by decide
  rw [actual,if_neg full,if_pos valid,body_run]

theorem decoded_argument (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams .bool)=
        .ok (.cons (.val (.word value)) .nil) ∧
      (bound good).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run whole.code (machine good)=run back.code (bound good) :=
  BoolBindingBody.decoded_body 7 label body (Frag.init BodyCtx) bodyCore whole back
    (BoolBindingBody.whole_selected 7 label body _ bodyCore)
    (BoolBindingBody.body_selected 7 body _ bodyCore) good fuel (machine good) (wmod good.size)
    rfl rfl (by decide) (by decide) (by decide)

theorem invalid_prevents_body (fuel : Nat) :
    run whole.code (machine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams .bool)=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord dirty).val=true := by decide
  constructor
  · rw [actual,if_neg full,if_neg invalid]
  · rw [SingleWordGate.entry_form]
    have size : ¬dirty.size<36 := by decide
    rw [if_neg size]
    exact dif_neg invalid

theorem short_prevents_word_and_body :
    run whole.code {machine good with
      mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert :=
  BoolBindingBody.short_before_body 7 label body _ bodyCore _ (wmod 35) rfl (by decide)

private def rejecting : Prog C BoolBoundCtx BoolBoundCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init BoolBoundCtx) rejecting=some (Frag.init BoolBoundCtx) := by rfl
private def rejectWhole := BoolBindingBody.selectedWhole 7 label rejecting _ rejectingCore
private def rejectBack := BoolBindingBody.selectedBody 7 rejecting _ rejectingCore

theorem body_failure_not_decoder_failure (fuel : Nat) :
    run rejectWhole.code (machine good)=.revert ∧
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams .bool)=.ok (.cons (.val (.word value)) .nil) := by
  constructor
  · have actualReject : run rejectWhole.code (machine good)=
        (if (wmod good.size).val<36 then .revert else
          if Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord good).val then run rejectBack.code (bound good) else .revert) :=
      BoolBindingBody.executed 7 label rejecting _ rejectingCore rejectWhole rejectBack
      (BoolBindingBody.whole_selected 7 label rejecting _ rejectingCore)
      (BoolBindingBody.body_selected 7 rejecting _ rejectingCore) (machine good) (rawArgumentWord good) (wmod good.size) rfl rfl
    have full : ¬(wmod good.size).val<36 := by decide
    have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord good).val=true := by decide
    rw [actualReject,if_neg full,if_pos valid]
    rfl
  · exact ⟨_,SingleWordGate.entry_success good fuel .bool (by decide) (by decide)⟩

theorem fuel_boundary :
    run whole.code (machine good)=.ok finished 0 ∧
    Solidity.AbiEntry.entry good 0 (singleWordParams .bool)=.error .fuel ∧
    Solidity.AbiEntry.entry good 1 (singleWordParams .bool)=.error .fuel :=
  ⟨selected_and_changes.2.2,SingleWordGate.insufficient_fuel good .bool (by decide)⟩

private def falseInput : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 32 0++[0x77],free := 71}
theorem false_argument_body :
    run whole.code (machine falseInput)=
      .ok {bound falseInput with mem := upd (bound falseInput).mem 10 (.val (bword true))} 0 := by
  have full : ¬(wmod falseInput.size).val<36 := by decide
  have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord falseInput).val=true := by decide
  rw [actual,if_neg full,if_pos valid]
  rfl

theorem protected_and_saved :
    finished.mem 7=.val (rawArgumentWord good) ∧ finished.mem 8=.val label ∧
    finished.mem 9=.val (wmod 1) ∧ finished.mem 10=.val (wmod 0) ∧ finished.mem 11=.val (wmod 71) ∧
    finished.stack=[.val (wmod 258),.val (wmod 513)] ∧ finished.callvalue=wmod 17 ∧
    finished.store=(machine good).store ∧ finished.bal=(machine good).bal :=
  ⟨rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.selected_and_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_and_changes
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.decoded_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_argument
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.invalid_prevents_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_prevents_body
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.short_prevents_word_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_prevents_word_and_body
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.body_failure_not_decoder_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_failure_not_decoder_failure
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.false_argument_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms false_argument_body
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBodyControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.BoolBindingBodyControls
