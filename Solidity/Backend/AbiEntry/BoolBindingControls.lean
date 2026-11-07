import Solidity.Backend.AbiEntry.BoolBinding

/-! Both actual Boolean bindings and a compiled typed branch use the raw bit.
Dirty values are rejected before conversion; Source/native entry remains open. -/
namespace Solidity.Backend.AbiEntry.BoolBindingControls
open Solidity.Evm
open Interface (RouteCtx BoolBoundCtx rawArgumentWord singleWordParams boolValueWord boolBoundMachine boolBindingOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled := BoolBinding.compiled C 7 label
private def yes : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[1,0x77,0x88],free := 71}
private def no : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 32 0++[0x77],free := 71}
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
private theorem actual (input : Solidity.AbiEntry.Input) :
    run compiled.code (machine input)=boolBindingOutcome 7 label (rawArgumentWord input) (wmod input.size) (machine input) :=
  BoolBinding.executed C 7 label compiled (BoolBinding.selected C 7 label) (machine input) _ _ rfl rfl
private theorem accept (input : Solidity.AbiEntry.Input) (full : ¬(wmod input.size).val<36)
    (valid : Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord input).val=true) :
    run compiled.code (machine input)=.ok (bound input) 0 := by
  simpa only [boolBindingOutcome,if_neg full,if_pos valid] using actual input

theorem both_bits :
    run compiled.code (machine yes)=.ok (bound yes) 0 ∧ (bound yes).mem 9=.val (bword true) ∧
    run compiled.code (machine no)=.ok (bound no) 0 ∧ (bound no).mem 9=.val (bword false) :=
  ⟨accept yes (by decide) (by decide),by decide,accept no (by decide) (by decide),by decide⟩

theorem raw_decoded_and_bound (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry yes (fuel+2) (singleWordParams .bool)=.ok (.cons (.val (.word value)) .nil) ∧
      run compiled.code (machine yes)=.ok (bound yes) 0 ∧
      (bound yes).mem (cellOf 7 (.here : Idx BoolBoundCtx (.val .bool)))=.val ⟨value.val,value.lt⟩ :=
  BoolBinding.decoded_and_bound C 7 label compiled (BoolBinding.selected C 7 label) yes fuel
    (machine yes) (wmod yes.size) rfl rfl (by decide) (by decide) (by decide)

theorem dirty_not_laundered (fuel : Nat) :
    boolValueWord (rawArgumentWord dirty)=bword false ∧
    run compiled.code (machine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams .bool)=.error .revert := by
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬Solidity.AbiEntry.Kind.bool.valid (rawArgumentWord dirty).val=true := by decide
  have rejected : run compiled.code (machine dirty)=.revert := by
    simpa only [boolBindingOutcome,if_neg full,if_neg invalid] using actual dirty
  exact ⟨by decide,rejected,(BoolBinding.entry_rejection C 7 label compiled (BoolBinding.selected C 7 label)
    dirty fuel (machine dirty) (wmod dirty.size) rfl rfl (by decide)).mp rejected⟩

theorem short_before_malformed_word :
    run compiled.code {machine yes with
      mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert :=
  BoolBinding.short_before_word C 7 label _ (wmod 35) rfl (by decide)

private def branchBody : Prog C BoolBoundCtx BoolBoundCtx :=
  .cons (.ite (.simple (.local .here))
    (.cons (.assignLocal (.there .here) (.simple (.lit 11 (by decide)))) .nil)
    (.cons (.assignLocal (.there .here) (.simple (.lit 22 (by decide)))) .nil)) .nil
private theorem bodyCore : inFragP (Frag.init BoolBoundCtx) branchBody=some (Frag.init BoolBoundCtx) := by rfl
private def back : Compiler.Compilation 7 (Frag.init BoolBoundCtx) branchBody :=
  .core (Frag.init BoolBoundCtx) bodyCore

theorem typed_branch_reads_argument :
    Compiler.compile 7 (Frag.init BoolBoundCtx) branchBody=some back ∧
    run back.code (bound yes)=.ok {bound yes with mem := upd (bound yes).mem 8 (.val (wmod 11))} 0 ∧
    run back.code (bound no)=.ok {bound no with mem := upd (bound no).mem 8 (.val (wmod 22))} 0 :=
  ⟨ValueGateBody.body_selected 7 _ _ _ bodyCore,by rfl,by rfl⟩

theorem fuel_boundary :
    run compiled.code (machine yes)=.ok (bound yes) 0 ∧
    Solidity.AbiEntry.entry yes 0 (singleWordParams .bool)=.error .fuel ∧
    Solidity.AbiEntry.entry yes 1 (singleWordParams .bool)=.error .fuel :=
  ⟨both_bits.1,SingleWordGate.insufficient_fuel yes .bool (by decide)⟩

theorem protected_and_saved :
    (bound yes).mem 7=.val (rawArgumentWord yes) ∧ (bound yes).mem 8=.val label ∧
    (bound yes).mem 10=.val (wmod 71) ∧ (bound yes).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (bound yes).callvalue=wmod 17 ∧ (bound yes).store=(machine yes).store ∧
    (bound yes).bal=(machine yes).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.both_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms both_bits
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.raw_decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.dirty_not_laundered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_not_laundered
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.short_before_malformed_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_malformed_word
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.typed_branch_reads_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed_branch_reads_argument
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.BoolBindingControls
