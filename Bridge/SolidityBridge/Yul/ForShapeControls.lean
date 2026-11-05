import SolidityBridge.Yul.ForShape

/-! Existing intrinsic shapes/room at the complete numeric input height,
separate from actual mathematical model success. No native realization or
Source-G24 certificate is fabricated from these checks. -/
namespace SolidityBridge.Yul.ForShape.Controls
open Solidity Backend Scalar Selection LabelExec
open StructuredFor.Controls

/-- Five live words and 1017 caller words leave exactly two temporary words. -/
theorem last_caller : BlockShape target 1022 1022 ∧ ExpansionRoom target 1022 1022 :=
  ⟨shape 1022 (by decide) (by decide),expansion_room 1022 (by decide) (by decide)⟩

/-- One extra caller word cannot inhabit the EXISTING BlockShape contract. -/
theorem next_caller_refused : ¬ BlockShape target 1023 1023 :=
  fun checked => (by decide : ¬ (1023+2 ≤ 1024)) (requires_room checked)

/-- The plain scalar condition fits, but ignores the structured test's extra
PUSH. Both this and body arithmetic peak must be included in the whole shape. -/
theorem condition_only_insufficient : stackBound testCode 1023 = true ∧
    ¬ BlockShape target 1023 1023 := ⟨by decide,next_caller_refused⟩

/-- Actual finite model success at 1023 input words remains available; it
must not be relabelled a physical shape/capacity or native execution proof. -/
theorem model_without_shape :
    Evm.run selected.realization.ir (machine ([77,dirty,99,dirty,high] ++ List.replicate 1018 0)) =
      .ok {(machine ([77,dirty,99,dirty,high] ++ List.replicate 1018 0)) with
        stack := irStack ([77,dirty,0,dirty+1,high] ++ List.replicate 1018 0)} 0 ∧
    ¬ BlockShape target 1023 1023 :=
  ⟨model_two (List.replicate 1018 0) _ rfl,next_caller_refused⟩

/-- Shape holds uniformly over the complete five-word frame plus caller,
whose actual list length is computed here rather than a local-count alias. -/
theorem caller_frame (caller : Stack) (room : caller.length ≤ 1017) :
    BlockShape target ([77,dirty,99,dirty,high] ++ caller).length
      ([77,dirty,99,dirty,high] ++ caller).length :=
  shape _ (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)

#guard ([77,dirty,99,dirty,high] ++ List.replicate 1017 (0 : Word)).length = 1022
#guard ([77,dirty,99,dirty,high] ++ List.replicate 1018 (0 : Word)).length = 1023
#guard run flagCode [0,0,0,0] == none
#guard run testCode [0,0] == none
#guard run flagCode [77,dirty,99,dirty,high] == some [high,77,dirty,99,dirty,high]
#guard !(stackBound bodyCode 1023)
#guard !(stackBound postCode 1023)
#guard high.toNat % 256 = 0
#guard observe (Evm.run selected.realization.ir (machine [77,dirty,99,dirty,high,88])) ==
  some ([some 77,some dirty.toNat,some 0,some (dirty+1).toNat,some high.toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
/-- info: 'SolidityBridge.Yul.ForShape.Controls.last_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms last_caller
/-- info: 'SolidityBridge.Yul.ForShape.Controls.next_caller_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_caller_refused
/-- info: 'SolidityBridge.Yul.ForShape.Controls.condition_only_insufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms condition_only_insufficient
/-- info: 'SolidityBridge.Yul.ForShape.Controls.model_without_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_without_shape
/-- info: 'SolidityBridge.Yul.ForShape.Controls.caller_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms caller_frame
end SolidityBridge.Yul.ForShape.Controls
