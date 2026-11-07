import Solidity.Backend.AbiEntry.WordCarrierEntryBody

/-! Actual enum and fixed-bytes carrier bodies after ordered value/ABI checks.
Source declaration association and native loading remain separate. -/
namespace Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls
open Solidity.Evm
open Interface
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def BodyCtx : Ctx := .val .bool :: UIntBoundCtx
private def body : Prog C UIntBoundCtx BodyCtx :=
  .cons (.declLocal .bool (.user "matchesTwo") (some
    (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit 2 (by decide)))))) .nil
private theorem bodyCore : inFragP (Frag.init UIntBoundCtx) body=some (Frag.init BodyCtx) := by rfl
private def whole (payable : Bool) := WordCarrierEntryBody.compiled 7 (.enumBelow 3) payable label body _ bodyCore
private def back := WordCarrierEntryBody.Binding.selectedBody 7 body _ bodyCore
private def enumGood : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[2,0x77,0x88],free := 71}
private def positive : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[1,0x77],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[3],free := 71}
private def machine (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  uintBoundMachine 7 label (rawArgumentWord input) (machine input value)
private def finished (input : Solidity.AbiEntry.Input) (value : Fin W) (result : Bool) : Machine :=
  {bound input value with mem := upd (bound input value).mem 10 (.val (bword result))}
private theorem actual (payable : Bool) (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run (whole payable).code (machine input value)=if payable || decide (value.val=0) then
      if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord input).val then run back.code (bound input value) else .revert else .revert :=
  WordCarrierEntryBody.executed 7 (.enumBelow 3) payable label body _ bodyCore (whole payable) back
    (WordCarrierEntryBody.selected 7 (.enumBelow 3) payable label body _ bodyCore)
    (WordCarrierEntryBody.Binding.body_selected 7 body _ bodyCore) (machine input value) _ _ rfl rfl

theorem payable_enum_body (value : Fin W) :
    run (whole true).code (machine enumGood value)=.ok (finished enumGood value true) 0 ∧
    run (whole true).code (machine positive value)=.ok (finished positive value false) 0 := by
  constructor
  · have full : ¬(wmod enumGood.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord enumGood).val=true := by decide
    rw [actual,Bool.true_or,if_pos (rfl : true=true),if_neg full,if_pos valid]
    rfl
  · have full : ¬(wmod positive.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord positive).val=true := by decide
    rw [actual,Bool.true_or,if_pos (rfl : true=true),if_neg full,if_pos valid]
    rfl

theorem zero_nonpayable :
    run (whole false).code (machine enumGood (wmod 0))=.ok (finished enumGood (wmod 0) true) 0 := by
  have full : ¬(wmod enumGood.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord enumGood).val=true := by decide
  rw [actual,if_neg full,if_pos valid]
  rfl

theorem nonpayable_before_any_local (value : Fin W) (nonzero : value.val≠0) :
    run (whole false).code {machine enumGood value with mem := fun _ => .slot (.root 0)}=.revert :=
  WordCarrierEntryBody.early_rejection 7 (.enumBelow 3) false label body _ bodyCore (whole false)
    (WordCarrierEntryBody.selected 7 (.enumBelow 3) false label body _ bodyCore) _ (by
      change (false || decide (value.val=0))=false
      simp only [Bool.false_or,decide_eq_false nonzero])

theorem dirty_still_rejected (fuel : Nat) :
    run (whole false).code (machine dirty (wmod 0))=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.enumBelow 3))=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬(Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord dirty).val=true := by decide
  constructor
  · rw [actual,if_neg full,if_neg invalid]
    rfl
  · rw [SingleWordGate.entry_form]
    have size : ¬dirty.size<36 := by decide
    rw [if_neg size]
    exact dif_neg invalid

theorem raw_enum_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.enumBelow 3),
      Solidity.AbiEntry.entry enumGood (fuel+2) (singleWordParams (.enumBelow 3))=.ok (.cons (.val (.word value)) .nil) ∧
      (bound enumGood (wmod 0)).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run (whole false).code (machine enumGood (wmod 0))=run back.code (bound enumGood (wmod 0)) :=
  WordCarrierEntryBody.decoded_body 7 (.enumBelow 3) false label body _ bodyCore (whole false) back
    (WordCarrierEntryBody.selected 7 (.enumBelow 3) false label body _ bodyCore) (WordCarrierEntryBody.Binding.body_selected 7 body _ bodyCore)
    enumGood fuel (machine enumGood (wmod 0)) (wmod enumGood.size)
    rfl rfl (by decide) (by decide) (by decide) (by decide)

private def rejecting : Prog C UIntBoundCtx UIntBoundCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init UIntBoundCtx) rejecting=some (Frag.init UIntBoundCtx) := by rfl
private def rejectWhole := WordCarrierEntryBody.compiled 7 (.enumBelow 3) false label rejecting _ rejectingCore
private def rejectBack := WordCarrierEntryBody.Binding.selectedBody 7 rejecting _ rejectingCore

theorem body_failure_not_decoder_failure (fuel : Nat) :
    run rejectWhole.code (machine enumGood (wmod 0))=.revert ∧
    ∃ value : Solidity.AbiEntry.Word (.enumBelow 3),
      Solidity.AbiEntry.entry enumGood (fuel+2) (singleWordParams (.enumBelow 3))=.ok (.cons (.val (.word value)) .nil) := by
  have ordered : run rejectWhole.code (machine enumGood (wmod 0))=
      (if false || decide ((wmod 0).val=0) then
        if (wmod enumGood.size).val<36 then .revert else
        if (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord enumGood).val then
          run rejectBack.code (bound enumGood (wmod 0)) else .revert else .revert) :=
    WordCarrierEntryBody.executed 7 (.enumBelow 3) false label rejecting _ rejectingCore rejectWhole rejectBack
      (WordCarrierEntryBody.selected 7 (.enumBelow 3) false label rejecting _ rejectingCore)
      (WordCarrierEntryBody.Binding.body_selected 7 rejecting _ rejectingCore) (machine enumGood (wmod 0)) _ _ rfl rfl
  constructor
  · have allowed : (false || decide ((wmod 0).val=0))=true := by decide
    have full : ¬(wmod enumGood.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord enumGood).val=true := by decide
    rw [ordered,if_pos allowed,if_neg full,if_pos valid]
    rfl
  · exact ⟨_,SingleWordGate.entry_success enumGood fuel (.enumBelow 3) (by decide) (by decide)⟩

theorem short_before_word_and_body :
    run (whole false).code
      {machine enumGood (wmod 0) with mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert := by
  rw [WordCarrierEntryBody.gated 7 (.enumBelow 3) false label body _ bodyCore (whole false)
    (WordCarrierEntryBody.selected 7 (.enumBelow 3) false label body _ bodyCore)]
  change (if false || decide ((wmod 0).val=0) then
    run (WordCarrierEntryBody.Binding.selectedWhole 7 (.enumBelow 3) label body _ bodyCore).code
      {machine enumGood (wmod 0) with mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}
    else .revert)=.revert
  rw [if_pos (by decide : (false || decide ((wmod 0).val=0))=true)]
  exact WordCarrierEntryBody.Binding.short_before_body 7 (.enumBelow 3) label body _ bodyCore _ (wmod 35) rfl (by decide)

theorem fuel_boundary :
    run (whole true).code (machine enumGood (wmod 17))=.ok (finished enumGood (wmod 17) true) 0 ∧
    Solidity.AbiEntry.entry enumGood 0 (singleWordParams (.enumBelow 3))=.error .fuel ∧
    Solidity.AbiEntry.entry enumGood 1 (singleWordParams (.enumBelow 3))=.error .fuel :=
  ⟨(payable_enum_body (wmod 17)).1,SingleWordGate.insufficient_fuel enumGood (.enumBelow 3) (by decide)⟩

theorem protected_and_saved (value : Fin W) :
    (finished enumGood value true).mem 7=.val (rawArgumentWord enumGood) ∧
    (finished enumGood value true).mem 8=.val label ∧
    (finished enumGood value true).mem 9=.val (rawArgumentWord enumGood) ∧
    (finished enumGood value true).mem 11=.val (wmod 71) ∧
    (finished enumGood value true).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (finished enumGood value true).callvalue=value ∧
    (finished enumGood value true).store=(machine enumGood value).store ∧
    (finished enumGood value true).bal=(machine enumGood value).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


private def bytesGood : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12,0xab]++List.replicate 31 0++[0x77,0x88],free := 71}
private def bytesDirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12,0xab]++List.replicate 30 0++[1],free := 71}
private def bytesWhole (payable : Bool) := WordCarrierEntryBody.compiled 7 (.fixedBytes 1) payable label body _ bodyCore
private theorem bytes_actual (payable : Bool) (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run (bytesWhole payable).code (machine input value)=if payable || decide (value.val=0) then
      if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.fixedBytes 1).valid (rawArgumentWord input).val then
        run back.code (bound input value) else .revert else .revert :=
  WordCarrierEntryBody.executed 7 (.fixedBytes 1) payable label body _ bodyCore (bytesWhole payable) back
    (WordCarrierEntryBody.selected 7 (.fixedBytes 1) payable label body _ bodyCore)
    (WordCarrierEntryBody.Binding.body_selected 7 body _ bodyCore) (machine input value) _ _ rfl rfl

theorem payable_bytes_body (value : Fin W) :
    run (bytesWhole true).code (machine bytesGood value)=.ok (finished bytesGood value false) 0 := by
  have full : ¬(wmod bytesGood.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.fixedBytes 1).valid (rawArgumentWord bytesGood).val=true := by decide
  rw [bytes_actual,Bool.true_or,if_pos (rfl : true=true),if_neg full,if_pos valid]
  rfl

theorem dirty_padding_prevents_body (fuel : Nat) :
    run (bytesWhole false).code (machine bytesDirty (wmod 0))=.revert ∧
    Solidity.AbiEntry.entry bytesDirty (fuel+2) (singleWordParams (.fixedBytes 1))=.error .revert := by
  have full : ¬(wmod bytesDirty.size).val<36 := by decide
  have invalid : ¬(Solidity.AbiEntry.Kind.fixedBytes 1).valid (rawArgumentWord bytesDirty).val=true := by decide
  constructor
  · rw [bytes_actual,if_neg full,if_neg invalid]
    rfl
  · rw [SingleWordGate.entry_form]
    have size : ¬bytesDirty.size<36 := by decide
    rw [if_neg size]
    exact dif_neg invalid

theorem raw_bytes_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.fixedBytes 1),
      Solidity.AbiEntry.entry bytesGood (fuel+2) (singleWordParams (.fixedBytes 1))=.ok (.cons (.val (.word value)) .nil) ∧
      (bound bytesGood (wmod 0)).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run (bytesWhole false).code (machine bytesGood (wmod 0))=run back.code (bound bytesGood (wmod 0)) :=
  WordCarrierEntryBody.decoded_body 7 (.fixedBytes 1) false label body _ bodyCore (bytesWhole false) back
    (WordCarrierEntryBody.selected 7 (.fixedBytes 1) false label body _ bodyCore)
    (WordCarrierEntryBody.Binding.body_selected 7 body _ bodyCore)
    bytesGood fuel (machine bytesGood (wmod 0)) (wmod bytesGood.size)
    rfl rfl (by decide) (by decide) (by decide) (by decide)

/-- Value rejection precedes every kind's head/word representation and body. -/
theorem all_kinds_early_rejection (kind : Solidity.AbiEntry.Kind) (initial : Machine)
    (nonzero : initial.callvalue.val≠0) :
    run (WordCarrierEntryBody.compiled 7 kind false label body _ bodyCore).code initial=.revert :=
  WordCarrierEntryBody.early_rejection 7 kind false label body _ bodyCore _
    (WordCarrierEntryBody.selected 7 kind false label body _ bodyCore) initial (by
      simp only [Bool.false_or,decide_eq_false nonzero])

/-- Wider semantic metadata keeps accepted raw bytes and still executes the body. -/
theorem wide_bytes_body (value : Fin W) :
    run (WordCarrierEntryBody.compiled 7 (.fixedBytes 33) true label body _ bodyCore).code
      (machine bytesDirty value)=.ok (finished bytesDirty value false) 0 := by
  have ordered : run (WordCarrierEntryBody.compiled 7 (.fixedBytes 33) true label body _ bodyCore).code
      (machine bytesDirty value)=if true || decide (value.val=0) then
        if (wmod bytesDirty.size).val<36 then .revert else
        if (Solidity.AbiEntry.Kind.fixedBytes 33).valid (rawArgumentWord bytesDirty).val then
          run back.code (bound bytesDirty value) else .revert else .revert :=
    WordCarrierEntryBody.executed 7 (.fixedBytes 33) true label body _ bodyCore _ back
      (WordCarrierEntryBody.selected 7 (.fixedBytes 33) true label body _ bodyCore)
      (WordCarrierEntryBody.Binding.body_selected 7 body _ bodyCore) (machine bytesDirty value) _ _ rfl rfl
  have full : ¬(wmod bytesDirty.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.fixedBytes 33).valid (rawArgumentWord bytesDirty).val=true := by decide
  rw [ordered,Bool.true_or,if_pos (rfl : true=true),if_neg full,if_pos valid]
  rfl

/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.wide_bytes_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_bytes_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.payable_enum_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_enum_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.zero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.nonpayable_before_any_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonpayable_before_any_local
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.dirty_still_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_still_rejected
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.raw_enum_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_enum_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.body_failure_not_decoder_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_failure_not_decoder_failure
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.short_before_word_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word_and_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.payable_bytes_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_bytes_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.dirty_padding_prevents_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_padding_prevents_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.raw_bytes_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bytes_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls.all_kinds_early_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_kinds_early_rejection
end Solidity.Backend.AbiEntry.WordCarrierEntryBodyControls
