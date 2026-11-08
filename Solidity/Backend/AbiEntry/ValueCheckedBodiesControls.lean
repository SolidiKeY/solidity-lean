import Solidity.Backend.AbiEntry.ValueCheckedBodies

/-! Actual combined artifacts exercise value/head/validation/body ordering.
No desired body run or decoded payload is supplied to the certificates. -/
namespace Solidity.Backend.AbiEntry.ValueCheckedBodiesControls
open Solidity.Evm
open Interface
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def input (byte : UInt8) : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[byte,0x77,0x88],free := 71}
private def dirtyUint : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 30 0++[1,0],free := 71}
private def machine (raw : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawArgumentWord raw)
      else if address=8 then .val (wmod raw.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def uBody : Prog C UIntBoundCtx UIntBoundCtx :=
  .cons (.assignLocal (.there .here) (.simple (.local .here))) .nil
private theorem uCore : inFragP (Frag.init UIntBoundCtx) uBody=some (Frag.init UIntBoundCtx) := by rfl
private def uWhole (payable : Bool) := ValueCheckedBodies.UInt.compiled 7 8 payable label uBody _ uCore
private def uBack := UIntBindingBody.selectedBody 7 uBody _ uCore
private def uBound (raw : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  uintBoundMachine 7 label (rawArgumentWord raw) (machine raw value)
private def uDone (raw : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {uBound raw value with mem := upd (uBound raw value).mem 8 (.val (rawArgumentWord raw))}
private theorem uActual (payable : Bool) (raw : Solidity.AbiEntry.Input) (value : Fin W) :
    run (uWhole payable).code (machine raw value)=if payable || decide (value.val=0) then
      if (wmod raw.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord raw).val then run uBack.code (uBound raw value) else .revert else .revert :=
  ValueCheckedBodies.UInt.executed 7 8 payable label uBody _ uCore (uWhole payable) uBack
    (ValueCheckedBodies.UInt.selected 7 8 payable label uBody _ uCore) (UIntBindingBody.body_selected 7 uBody _ uCore)
    (machine raw value) _ _ rfl rfl

private def bBody : Prog C BoolBoundCtx BoolBoundCtx :=
  .cons (.ite (.simple (.local .here))
    (.cons (.assignLocal (.there .here) (.simple (.lit 11 (by decide)))) .nil)
    (.cons (.assignLocal (.there .here) (.simple (.lit 22 (by decide)))) .nil)) .nil
private theorem bCore : inFragP (Frag.init BoolBoundCtx) bBody=some (Frag.init BoolBoundCtx) := by rfl
private def bWhole (payable : Bool) := ValueCheckedBodies.Bool.compiled 7 payable label bBody _ bCore
private def bBack := BoolBindingBody.selectedBody 7 bBody _ bCore
private def bBound (raw : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  boolBoundMachine 7 label (rawArgumentWord raw) (machine raw value)
private def bDone (raw : Solidity.AbiEntry.Input) (value result : Fin W) : Machine :=
  {bBound raw value with mem := upd (bBound raw value).mem 8 (.val result)}
private theorem bActual (payable : Bool) (raw : Solidity.AbiEntry.Input) (value : Fin W) :
    run (bWhole payable).code (machine raw value)=if payable || decide (value.val=0) then
      if (wmod raw.size).val<36 then .revert else
      if Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord raw).val then run bBack.code (bBound raw value) else .revert else .revert :=
  ValueCheckedBodies.Bool.executed 7 payable label bBody _ bCore (bWhole payable) bBack
    (ValueCheckedBodies.Bool.selected 7 payable label bBody _ bCore) (BoolBindingBody.body_selected 7 bBody _ bCore)
    (machine raw value) _ _ rfl rfl

theorem uint_payable_all_values (value : Fin W) :
    run (uWhole true).code (machine (input 255) value)=.ok (uDone (input 255) value) 0 := by
  have full : ¬(wmod (input 255).size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord (input 255)).val=true := by decide
  rw [uActual,Bool.true_or,ite_eq_left (rfl : true=true),ite_eq_right full,ite_eq_left valid]
  rfl

theorem bool_payable_all_values (value : Fin W) :
    run (bWhole true).code (machine (input 1) value)=.ok (bDone (input 1) value (wmod 11)) 0 := by
  have full : ¬(wmod (input 1).size).val<36 := by decide
  have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord (input 1)).val=true := by decide
  rw [bActual,Bool.true_or,ite_eq_left (rfl : true=true),ite_eq_right full,ite_eq_left valid]
  rfl

theorem zero_nonpayable :
    run (uWhole false).code (machine (input 255) (wmod 0))=.ok (uDone (input 255) (wmod 0)) 0 ∧
    run (bWhole false).code (machine (input 0) (wmod 0))=.ok (bDone (input 0) (wmod 0) (wmod 22)) 0 := by
  constructor
  · have actual : run (uWhole false).code (machine (input 255) (wmod 0))=
        if false || decide ((wmod 0).val=0) then run uBack.code (uBound (input 255) (wmod 0)) else .revert := by
      have full : ¬(wmod (input 255).size).val<36 := by decide
      have valid : (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord (input 255)).val=true := by decide
      simpa only [ite_eq_right full,ite_eq_left valid] using uActual false (input 255) (wmod 0)
    rw [actual]
    rfl
  · have full : ¬(wmod (input 0).size).val<36 := by decide
    have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord (input 0)).val=true := by decide
    rw [bActual,ite_eq_right full,ite_eq_left valid]
    rfl

theorem value_before_any_local (value : Fin W) (nonzero : value.val≠0) :
    run (uWhole false).code {machine (input 255) value with mem := fun _ => .slot (.root 0)}=.revert ∧
    run (bWhole false).code {machine (input 1) value with mem := fun _ => .slot (.root 0)}=.revert := by
  constructor
  · exact ValueCheckedBodies.UInt.early_rejection 7 8 false label uBody _ uCore (uWhole false)
      (ValueCheckedBodies.UInt.selected 7 8 false label uBody _ uCore) _
      (by
        change (false || decide (value.val=0))=false
        simp only [Bool.false_or,decide_eq_false nonzero])
  · exact ValueCheckedBodies.Bool.early_rejection 7 false label bBody _ bCore (bWhole false)
      (ValueCheckedBodies.Bool.selected 7 false label bBody _ bCore) _
      (by
        change (false || decide (value.val=0))=false
        simp only [Bool.false_or,decide_eq_false nonzero])

theorem zero_value_still_validates :
    run (uWhole false).code (machine dirtyUint (wmod 0))=.revert ∧
    run (bWhole false).code (machine (input 2) (wmod 0))=.revert := by
  constructor
  · have full : ¬(wmod dirtyUint.size).val<36 := by decide
    have invalid : ¬(Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord dirtyUint).val=true := by decide
    rw [uActual,ite_eq_right full,ite_eq_right invalid]
    rfl
  · have full : ¬(wmod (input 2).size).val<36 := by decide
    have invalid : ¬Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord (input 2)).val=true := by decide
    rw [bActual,ite_eq_right full,ite_eq_right invalid]
    rfl

theorem uint_raw_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.uint 8),
      Solidity.AbiEntry.entry (input 255) (fuel+2) (singleWordParams (.uint 8))=.ok (.cons (.val (.word value)) .nil) ∧
      (uBound (input 255) (wmod 0)).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run (uWhole false).code (machine (input 255) (wmod 0))=run uBack.code (uBound (input 255) (wmod 0)) :=
  ValueCheckedBodies.UInt.decoded_body 7 8 false label uBody _ uCore (uWhole false) uBack
    (ValueCheckedBodies.UInt.selected 7 8 false label uBody _ uCore) (UIntBindingBody.body_selected 7 uBody _ uCore)
    (input 255) fuel (machine (input 255) (wmod 0)) (wmod (input 255).size)
    rfl rfl (by decide) (by decide) (by decide) (by decide)

theorem bool_raw_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry (input 1) (fuel+2) (singleWordParams .bool)=.ok (.cons (.val (.word value)) .nil) ∧
      (bBound (input 1) (wmod 0)).mem 9=.val ⟨value.val,value.lt⟩ ∧
      run (bWhole false).code (machine (input 1) (wmod 0))=run bBack.code (bBound (input 1) (wmod 0)) :=
  ValueCheckedBodies.Bool.decoded_body 7 false label bBody _ bCore (bWhole false) bBack
    (ValueCheckedBodies.Bool.selected 7 false label bBody _ bCore) (BoolBindingBody.body_selected 7 bBody _ bCore)
    (input 1) fuel (machine (input 1) (wmod 0)) (wmod (input 1).size)
    rfl rfl (by decide) (by decide) (by decide) (by decide)

private def rejecting : Prog C UIntBoundCtx UIntBoundCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init UIntBoundCtx) rejecting=some (Frag.init UIntBoundCtx) := by rfl
private def rejectWhole := ValueCheckedBodies.UInt.compiled 7 8 false label rejecting _ rejectingCore
private def rejectBack := UIntBindingBody.selectedBody 7 rejecting _ rejectingCore

theorem body_rejection_preserved (fuel : Nat) :
    run rejectWhole.code (machine (input 255) (wmod 0))=.revert ∧
    ∃ value : Solidity.AbiEntry.Word (.uint 8),
      Solidity.AbiEntry.entry (input 255) (fuel+2) (singleWordParams (.uint 8))=.ok (.cons (.val (.word value)) .nil) := by
  have ordered : run rejectWhole.code (machine (input 255) (wmod 0))=
      (if false || decide ((wmod 0).val=0) then
        if (wmod (input 255).size).val<36 then .revert else
        if (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord (input 255)).val then
          run rejectBack.code (uBound (input 255) (wmod 0)) else .revert else .revert) :=
    ValueCheckedBodies.UInt.executed 7 8 false label rejecting _ rejectingCore rejectWhole rejectBack
      (ValueCheckedBodies.UInt.selected 7 8 false label rejecting _ rejectingCore)
      (UIntBindingBody.body_selected 7 rejecting _ rejectingCore) (machine (input 255) (wmod 0)) _ _ rfl rfl
  constructor
  · have allowed : (false || decide ((wmod 0).val=0))=true := by decide
    have full : ¬(wmod (input 255).size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.uint 8).valid (rawArgumentWord (input 255)).val=true := by decide
    rw [ordered,ite_eq_left allowed,ite_eq_right full,ite_eq_left valid]
    rfl
  · exact ⟨_,SingleWordGate.entry_success (input 255) fuel (.uint 8) (by decide) (by decide)⟩

theorem protected_and_saved (value : Fin W) :
    (uDone (input 255) value).mem 7=.val (rawArgumentWord (input 255)) ∧
    (uDone (input 255) value).mem 9=.val (rawArgumentWord (input 255)) ∧
    (uDone (input 255) value).mem 10=.val (wmod 71) ∧
    (uDone (input 255) value).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (uDone (input 255) value).callvalue=value ∧ (uDone (input 255) value).store=(machine (input 255) value).store ∧
    (uDone (input 255) value).bal=(machine (input 255) value).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.uint_payable_all_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_payable_all_values
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.bool_payable_all_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_payable_all_values
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.zero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.value_before_any_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms value_before_any_local
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.zero_value_still_validates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_value_still_validates
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.uint_raw_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_raw_body
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.bool_raw_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_raw_body
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.body_rejection_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_rejection_preserved
/-- info: 'Solidity.Backend.AbiEntry.ValueCheckedBodiesControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.ValueCheckedBodiesControls
