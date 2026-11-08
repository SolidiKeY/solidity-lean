import Solidity.Backend.AbiEntry.SingleWordGate

/-! Composed guards exercise actual selected code and actual raw entry decoding.
Trailing bytes/selectors are unrestricted; fuel and malformed-memory failures
remain explicit boundaries of the represented-input comparison. -/
namespace Solidity.Backend.AbiEntry.SingleWordGateControls
open Solidity.Evm
open Interface (singleWordParams rawArgumentWord singleWordOutcome wordGateOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (kind : Solidity.AbiEntry.Kind) := SingleWordGate.compiled C 7 kind label
private def good : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[1,0x77,0x88,0x99],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[2],free := 71}
private def short : Solidity.AbiEntry.Input := {data := List.replicate 35 0,free := 71}
private def machine (input : Solidity.AbiEntry.Input) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (input : Solidity.AbiEntry.Input) : Machine :=
  {machine input with mem := upd (machine input).mem 8 (.val label)}

private theorem actual (kind : Solidity.AbiEntry.Kind) (input : Solidity.AbiEntry.Input) :
    run (compiled kind).code (machine input)=
      singleWordOutcome 7 kind label (rawArgumentWord input) (wmod input.size) (machine input) :=
  SingleWordGate.executed C 7 kind label (compiled kind) (SingleWordGate.selected C 7 kind label)
    (machine input) _ _ rfl rfl

theorem raw_success (fuel : Nat) :
    Solidity.AbiEntry.load good.data 4=1 ∧ good.size=39 ∧
    run (compiled .bool).code (machine good)=.ok (written good) 0 ∧
    ∃ value : Solidity.AbiEntry.Val (.word .bool),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams .bool)=.ok (.cons (.val value) .nil) := by
  have full : ¬(wmod good.size).val<36 := by decide
  have valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord good).val=true := by decide
  refine ⟨by decide,by decide,?_,?_⟩
  · simpa only [written,singleWordOutcome,ite_eq_right full,wordGateOutcome,ite_eq_left valid] using actual .bool good
  · exact ⟨_,SingleWordGate.entry_success good fuel .bool (by decide) valid⟩

theorem raw_dirty_rejection (fuel : Nat) :
    run (compiled .bool).code (machine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams .bool)=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord dirty).val=true := by decide
  have rejected : run (compiled .bool).code (machine dirty)=.revert := by
    simpa only [singleWordOutcome,ite_eq_right full,wordGateOutcome,ite_eq_right invalid] using actual .bool dirty
  exact ⟨rejected,(SingleWordGate.entry_rejection C 7 .bool label (compiled .bool)
    (SingleWordGate.selected C 7 .bool label) dirty fuel (machine dirty) (wmod dirty.size)
    rfl rfl (by decide)).mp rejected⟩

theorem short_before_malformed_word :
    run (compiled .bool).code {machine short with
      mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert :=
  SingleWordGate.short_before_word C 7 .bool label _ (wmod 35) rfl (by decide)

theorem short_before_fuel : Solidity.AbiEntry.entry short 0 (singleWordParams .bool)=.error .revert :=
  HeadCheck.early_revert short 0 _ (by decide)

theorem full_word_fault :
    run (compiled .bool).code {machine good with
      mem := fun address => if address=8 then .val (wmod 39) else .slot (.root 0)}=.fault := by
  let broken : Machine := {machine good with
    mem := fun address => if address=8 then .val (wmod 39) else .slot (.root 0)}
  have head := HeadGate.run_program C 7 (singleWordParams .bool) label broken (wmod 39) rfl
  have full : ¬(wmod 39).val<36 := by decide
  change run (compileProg 7 (HeadGate.program C (singleWordParams .bool) label)) broken=
    (if (wmod 39).val<36 then .revert else .ok {broken with mem := upd broken.mem 8 (.val label)} 0) at head
  rw [ite_eq_right full] at head
  change run (compileProg 7 (HeadGate.program C (singleWordParams .bool) label) ++
    compileProg 7 (WordGate.program C .bool label)) broken=.fault
  rw [run_append_ok head]
  simp only [WordGate.program,UnsignedGate.program,dite_eq_left (by decide : 2<W),compileProg,compileStmt,
    UnsignedGate.condition_code]
  rfl

theorem fuel_boundary :
    run (compiled .bool).code (machine good)=.ok (written good) 0 ∧
    Solidity.AbiEntry.entry good 0 (singleWordParams .bool)=.error .fuel ∧
    Solidity.AbiEntry.entry good 1 (singleWordParams .bool)=.error .fuel :=
  ⟨(raw_success 0).2.2.1,SingleWordGate.insufficient_fuel good .bool (by decide)⟩

theorem protected_and_saved :
    (written good).mem 7=.val (rawArgumentWord good) ∧
    (written good).mem 9=.val (wmod 71) ∧
    (written good).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written good).callvalue=wmod 17 ∧ (written good).store=(machine good).store ∧
    (written good).bal=(machine good).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.raw_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_success
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.raw_dirty_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_dirty_rejection
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.short_before_malformed_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_malformed_word
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.short_before_fuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_fuel
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.full_word_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_word_fault
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGateControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SingleWordGateControls
