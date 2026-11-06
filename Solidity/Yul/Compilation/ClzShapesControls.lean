import Solidity.Yul.Compilation.ClzShapes

/-! Software-only CLZ boundary witnesses. Full expansion runs use the already
proved word semantics, rather than evaluating4867 instructions in the kernel. -/
namespace Solidity.Yul.Compilation.ClzShapes.Controls
open Backend Scalar LabelExec

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem step_first : CodeShape (clzStepCode ⟨0,by decide⟩) 2 2 :=
  step_shape ⟨0,by decide⟩ 2 (by decide)
theorem step_last : CodeShape (clzStepCode ⟨255,by decide⟩) 2 2 :=
  step_shape ⟨255,by decide⟩ 2 (by decide)
theorem scan_two : run (clzScanCode 2 (by decide)) [256,5,88] = some [255,5,88] := by decide

theorem exact_run (x : Scalar.Word) (caller : Stack) :
    run clzExpansion (x::caller) = some (x.clz::caller) := clzExpansion_run x caller

theorem dirty_value : dirty.clz = 55 := by decide

theorem dirty_run (caller : Stack) :
    run clzExpansion (dirty::caller) = some (55::caller) :=
  (exact_run dirty caller).trans (congrArg (fun value : Scalar.Word => some (value::caller)) dirty_value)

theorem zero_run (caller : Stack) :
    run clzExpansion ((0 : Scalar.Word)::caller) = some (256::caller) := by
  have value : (0 : Scalar.Word).clz = 256 := BitVec.clz_eq_iff_eq_zero.mpr rfl
  exact (exact_run 0 caller).trans (congrArg (fun result : Scalar.Word => some (result::caller)) value)

theorem last_capacity : stackBound clzExpansion 1019 = true :=
  (expansion_capacity 1019).mpr ⟨by decide,by decide⟩

theorem next_capacity : stackBound clzExpansion 1020 ≠ true := by
  intro accepted
  have bound := (expansion_capacity 1020).mp accepted
  omega

/-- Scalar success on1020 input words does not prove actual1024 capacity:
the scan transiently reaches1025. Arbitrary caller contents remain identical. -/
theorem oversized (x : Scalar.Word) (caller : Vector Scalar.Word 1019) :
    run clzExpansion (x::caller.toList) = some (x.clz::caller.toList) ∧
      stackBound clzExpansion 1020 ≠ true := ⟨exact_run x caller.toList,next_capacity⟩

theorem empty_capacity : stackBound clzExpansion 0 = true :=
  (expansion_capacity 0).mpr ⟨by decide,by decide⟩

/-- A capacity check cannot supply the missing copied argument. The very first
bit step lacks its second word even after the expansion initializer. -/
theorem missing_operand : run (clzStepCode ⟨0,by decide⟩) [256] = none := by decide

theorem native_refused : run [.op .CLZ] [0] = none := by rfl

theorem packet_instructions : (expansionCode 1 (by decide) (by decide)).instructions = clzExpansion := by rfl

/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.step_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_first
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.step_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_last
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.scan_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scan_two
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.exact_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_run
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.dirty_value' depends on axioms: [propext] -/
#guard_msgs in #print axioms dirty_value
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.dirty_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dirty_run
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.zero_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero_run
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.last_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms last_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.next_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms next_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.oversized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms oversized
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.empty_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms empty_capacity
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.missing_operand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms missing_operand
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.native_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms native_refused
/-- info: 'Solidity.Yul.Compilation.ClzShapes.Controls.packet_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms packet_instructions

end Solidity.Yul.Compilation.ClzShapes.Controls
