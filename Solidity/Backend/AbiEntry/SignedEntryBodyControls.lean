import Solidity.Backend.AbiEntry.SignedEntryBody

/-! Actual whole programs execute signed bodies after ordered value/ABI checks.
Source declaration association and native loading remain separate. -/
namespace Solidity.Backend.AbiEntry.SignedEntryBodyControls
open Solidity.Evm
open Interface
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def BodyCtx : Ctx := .val .bool :: SignedBoundCtx
private def body : Prog C SignedBoundCtx BodyCtx :=
  .cons (.declLocal .bool (.user "negative") (some
    (.binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 0 (by decide)))))) .nil
private theorem bodyCore : inFragP (Frag.init SignedBoundCtx) body=some (Frag.init BodyCtx) := by rfl
private def whole (payable : Bool) := SignedEntryBody.compiled 7 8 payable label body _ bodyCore
private def back := SignedEntryBody.Binding.selectedBody 7 body _ bodyCore
private def negative : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 255++[128,0x77,0x88],free := 71}
private def positive : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[127,0x77],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[128],free := 71}
private def machine (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  signedBoundMachine 7 label (rawArgumentWord input) (machine input value)
private def finished (input : Solidity.AbiEntry.Input) (value : Fin W) (result : Bool) : Machine :=
  {bound input value with mem := upd (bound input value).mem 10 (.val (bword result))}
private theorem actual (payable : Bool) (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run (whole payable).code (machine input value)=if payable || decide (value.val=0) then
      if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord input).val then run back.code (bound input value) else .revert else .revert :=
  SignedEntryBody.executed 7 8 payable label body _ bodyCore (whole payable) back
    (SignedEntryBody.selected 7 8 payable label body _ bodyCore)
    (SignedEntryBody.Binding.body_selected 7 body _ bodyCore) (machine input value) _ _ rfl rfl

theorem payable_signed_body (value : Fin W) :
    run (whole true).code (machine negative value)=.ok (finished negative value true) 0 ∧
    run (whole true).code (machine positive value)=.ok (finished positive value false) 0 := by
  constructor
  · have full : ¬(wmod negative.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord negative).val=true := by decide
    rw [actual,Bool.true_or,ite_eq_left (rfl : true=true),ite_eq_right full,ite_eq_left valid]
    rfl
  · have full : ¬(wmod positive.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord positive).val=true := by decide
    rw [actual,Bool.true_or,ite_eq_left (rfl : true=true),ite_eq_right full,ite_eq_left valid]
    rfl

theorem zero_nonpayable :
    run (whole false).code (machine negative (wmod 0))=.ok (finished negative (wmod 0) true) 0 := by
  have full : ¬(wmod negative.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord negative).val=true := by decide
  rw [actual,ite_eq_right full,ite_eq_left valid]
  rfl

theorem nonpayable_before_any_local (value : Fin W) (nonzero : value.val≠0) :
    run (whole false).code {machine negative value with mem := fun _ => .slot (.root 0)}=.revert :=
  SignedEntryBody.early_rejection 7 8 false label body _ bodyCore (whole false)
    (SignedEntryBody.selected 7 8 false label body _ bodyCore) _ (by
      change (false || decide (value.val=0))=false
      simp only [Bool.false_or,decide_eq_false nonzero])

theorem dirty_still_rejected (fuel : Nat) :
    run (whole false).code (machine dirty (wmod 0))=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.int 8))=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬(Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord dirty).val=true := by decide
  constructor
  · rw [actual,ite_eq_right full,ite_eq_right invalid]
    rfl
  · rw [SingleWordGate.entry_form]
    have size : ¬dirty.size<36 := by decide
    rw [ite_eq_right size]
    exact dite_eq_right invalid

theorem raw_signed_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.int 8),
      Solidity.AbiEntry.entry negative (fuel+2) (singleWordParams (.int 8))=.ok (.cons (.val (.word value)) .nil) ∧
      (bound negative (wmod 0)).mem 9=.val ⟨value.val,value.lt⟩ ∧
      sgn value.val=Solidity.AbiEntry.toInt (Solidity.AbiEntry.load negative.data 4) ∧
      run (whole false).code (machine negative (wmod 0))=run back.code (bound negative (wmod 0)) :=
  SignedEntryBody.decoded_body 7 8 false label body _ bodyCore (whole false) back
    (SignedEntryBody.selected 7 8 false label body _ bodyCore) (SignedEntryBody.Binding.body_selected 7 body _ bodyCore)
    negative fuel (machine negative (wmod 0)) (wmod negative.size)
    rfl rfl (by decide) (by decide) (by decide) (by decide)

private def rejecting : Prog C SignedBoundCtx SignedBoundCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init SignedBoundCtx) rejecting=some (Frag.init SignedBoundCtx) := by rfl
private def rejectWhole := SignedEntryBody.compiled 7 8 false label rejecting _ rejectingCore
private def rejectBack := SignedEntryBody.Binding.selectedBody 7 rejecting _ rejectingCore

theorem body_failure_not_decoder_failure (fuel : Nat) :
    run rejectWhole.code (machine negative (wmod 0))=.revert ∧
    ∃ value : Solidity.AbiEntry.Word (.int 8),
      Solidity.AbiEntry.entry negative (fuel+2) (singleWordParams (.int 8))=.ok (.cons (.val (.word value)) .nil) := by
  have ordered : run rejectWhole.code (machine negative (wmod 0))=
      (if false || decide ((wmod 0).val=0) then
        if (wmod negative.size).val<36 then .revert else
        if (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord negative).val then
          run rejectBack.code (bound negative (wmod 0)) else .revert else .revert) :=
    SignedEntryBody.executed 7 8 false label rejecting _ rejectingCore rejectWhole rejectBack
      (SignedEntryBody.selected 7 8 false label rejecting _ rejectingCore)
      (SignedEntryBody.Binding.body_selected 7 rejecting _ rejectingCore) (machine negative (wmod 0)) _ _ rfl rfl
  constructor
  · have allowed : (false || decide ((wmod 0).val=0))=true := by decide
    have full : ¬(wmod negative.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord negative).val=true := by decide
    rw [ordered,ite_eq_left allowed,ite_eq_right full,ite_eq_left valid]
    rfl
  · exact ⟨_,SingleWordGate.entry_success negative fuel (.int 8) (by decide) (by decide)⟩

theorem short_before_word_and_body :
    run (whole false).code
      {machine negative (wmod 0) with mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert := by
  rw [SignedEntryBody.gated 7 8 false label body _ bodyCore (whole false)
    (SignedEntryBody.selected 7 8 false label body _ bodyCore)]
  change (if false || decide ((wmod 0).val=0) then
    run (SignedEntryBody.Binding.selectedWhole 7 8 label body _ bodyCore).code
      {machine negative (wmod 0) with mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}
    else .revert)=.revert
  rw [ite_eq_left (by decide : (false || decide ((wmod 0).val=0))=true)]
  exact SignedEntryBody.Binding.short_before_body 7 8 label body _ bodyCore _ (wmod 35) rfl (by decide)

theorem fuel_boundary :
    run (whole true).code (machine negative (wmod 17))=.ok (finished negative (wmod 17) true) 0 ∧
    Solidity.AbiEntry.entry negative 0 (singleWordParams (.int 8))=.error .fuel ∧
    Solidity.AbiEntry.entry negative 1 (singleWordParams (.int 8))=.error .fuel :=
  ⟨(payable_signed_body (wmod 17)).1,SingleWordGate.insufficient_fuel negative (.int 8) (by decide)⟩

theorem protected_and_saved (value : Fin W) :
    (finished negative value true).mem 7=.val (rawArgumentWord negative) ∧
    (finished negative value true).mem 8=.val label ∧
    (finished negative value true).mem 9=.val (rawArgumentWord negative) ∧
    (finished negative value true).mem 11=.val (wmod 71) ∧
    (finished negative value true).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (finished negative value true).callvalue=value ∧
    (finished negative value true).store=(machine negative value).store ∧
    (finished negative value true).bal=(machine negative value).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.payable_signed_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_signed_body
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.zero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.nonpayable_before_any_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonpayable_before_any_local
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.dirty_still_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_still_rejected
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.raw_signed_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_signed_body
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.body_failure_not_decoder_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_failure_not_decoder_failure
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.short_before_word_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word_and_body
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBodyControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SignedEntryBodyControls
