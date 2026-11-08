import Solidity.Backend.AbiEntry.UIntBinding

/-! Actual uint parameter declaration, raw failure boundaries and subsequent
compiled reads of the new typed local. Whole Source-body linkage is separate. -/
namespace Solidity.Backend.AbiEntry.UIntBindingControls
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx singleWordParams rawArgumentWord uintBoundMachine uintBindingOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (bits : Nat) := UIntBinding.compiled C 7 bits label
private def good : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[255,0x77,0x88],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 30 0++[1,0],free := 71}
private def zero : Solidity.AbiEntry.Input := {data := List.replicate 36 0,free := 71}
private def machine (input : Solidity.AbiEntry.Input) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) : Machine :=
  uintBoundMachine 7 label (rawArgumentWord input) (machine input)
private theorem actual (bits : Nat) (input : Solidity.AbiEntry.Input) :
    run (compiled bits).code (machine input)=
      uintBindingOutcome 7 bits label (rawArgumentWord input) (wmod input.size) (machine input) :=
  UIntBinding.executed C 7 bits label (compiled bits) (UIntBinding.selected C 7 bits label)
    (machine input) _ _ rfl rfl

private theorem accept (bits : Nat) (input : Solidity.AbiEntry.Input)
    (full : ¬(wmod input.size).val<36)
    (valid : (Solidity.AbiEntry.Kind.uint bits).valid (rawArgumentWord input).val=true) :
    run (compiled bits).code (machine input)=.ok (bound input) 0 := by
  simpa only [uintBindingOutcome,ite_eq_right full,ite_eq_left valid, bound] using actual bits input

private theorem reject (bits : Nat) (input : Solidity.AbiEntry.Input)
    (full : ¬(wmod input.size).val<36)
    (invalid : ¬(Solidity.AbiEntry.Kind.uint bits).valid (rawArgumentWord input).val=true) :
    run (compiled bits).code (machine input)=.revert := by
  simpa only [uintBindingOutcome,ite_eq_right full,ite_eq_right invalid] using actual bits input

theorem raw_value_and_frame (fuel : Nat) :
    Solidity.AbiEntry.load good.data 4=255 ∧ good.size=38 ∧
    ∃ value : Solidity.AbiEntry.Word (.uint 8),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams (.uint 8))=
        .ok (.cons (.val (.word value)) .nil) ∧
      run (compiled 8).code (machine good)=.ok (bound good) 0 ∧
      (bound good).mem (cellOf 7 (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ :=
  ⟨by decide,by decide,UIntBinding.decoded_and_bound C 7 8 label (compiled 8)
    (UIntBinding.selected C 7 8 label) good fuel (machine good) (wmod good.size)
    rfl rfl (by decide) (by decide) (by decide)⟩

theorem dirty_high_bits (fuel : Nat) :
    Solidity.AbiEntry.load dirty.data 4=256 ∧ run (compiled 8).code (machine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.uint 8))=.error .revert := by
  have rejected := reject 8 dirty (by decide) (by decide)
  exact ⟨by decide,rejected,(UIntBinding.entry_rejection C 7 8 label (compiled 8)
    (UIntBinding.selected C 7 8 label) dirty fuel (machine dirty) (wmod dirty.size)
    rfl rfl (by decide)).mp rejected⟩

theorem zero_width_boundaries :
    run (compiled 0).code (machine zero)=.ok (bound zero) 0 ∧
    run (compiled 0).code (machine good)=.revert :=
  ⟨accept 0 zero (by decide) (by decide),reject 0 good (by decide) (by decide)⟩

theorem wide_accepts (bits : Nat) (wide : 256≤bits) (word size : Fin W) (full : ¬size.val<36)
    (initial : Machine) (wordCell : initial.mem 7=.val word) (sizeCell : initial.mem 8=.val size) :
    run (compiled bits).code initial=.ok (uintBoundMachine 7 label word initial) 0 := by
  have valid : (Solidity.AbiEntry.Kind.uint bits).valid word.val=true := by
    exact decide_eq_true (Nat.lt_of_lt_of_le word.isLt (Nat.pow_le_pow_right (by decide : 0<2) wide))
  simpa only [uintBindingOutcome,ite_eq_right full,ite_eq_left valid] using
    UIntBinding.executed C 7 bits label (compiled bits) (UIntBinding.selected C 7 bits label)
      initial word size wordCell sizeCell

private def short : Solidity.AbiEntry.Input := {data := List.replicate 35 0,free := 71}
theorem short_head : run (compiled 8).code (machine short)=.revert := by
  have small : (wmod short.size).val<36 := by decide
  simpa only [uintBindingOutcome,ite_eq_left small] using actual 8 short

theorem insufficient_fuel :
    run (compiled 8).code (machine good)=.ok (bound good) 0 ∧
    Solidity.AbiEntry.entry good 0 (singleWordParams (.uint 8))=.error .fuel ∧
    Solidity.AbiEntry.entry good 1 (singleWordParams (.uint 8))=.error .fuel :=
  ⟨accept 8 good (by decide) (by decide),SingleWordGate.insufficient_fuel good (.uint 8) (by decide)⟩

private def readBody : Prog C UIntBoundCtx UIntBoundCtx :=
  .cons (.assignLocal (.there .here) (.simple (.local .here))) .nil
private def bodyCompiled : Compiler.Compilation 7 (Frag.init UIntBoundCtx) readBody :=
  .core (Frag.init UIntBoundCtx) (by rfl)
theorem bound_argument_read :
    Compiler.compile 7 (Frag.init UIntBoundCtx) readBody=some bodyCompiled ∧
    run bodyCompiled.code (bound good)=.ok {bound good with mem := upd (bound good).mem 8 (.val (wmod 255))} 0 :=
  ⟨ValueGateBody.body_selected 7 _ _ _ (by rfl),by rfl⟩

theorem protected_and_saved :
    (bound good).mem 7=.val (rawArgumentWord good) ∧ (bound good).mem 8=.val label ∧
    (bound good).mem 9=.val (wmod 255) ∧ (bound good).mem 10=.val (wmod 71) ∧
    (bound good).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (bound good).callvalue=wmod 17 ∧ (bound good).store=(machine good).store ∧
    (bound good).bal=(machine good).bal := ⟨rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.raw_value_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_value_and_frame
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.dirty_high_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_high_bits
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.zero_width_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_width_boundaries
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.wide_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_accepts
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.short_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_head
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.insufficient_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_fuel
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.bound_argument_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bound_argument_read
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.UIntBindingControls
