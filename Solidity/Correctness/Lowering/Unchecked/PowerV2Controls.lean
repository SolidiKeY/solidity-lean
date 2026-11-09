import Solidity.Source.PowerV2Correct

/-!
# V2 operator migration controls

Guard accidentally consuming V1 at the 301-bit cutoff and losing checked
arithmetic panics while migrating the explicitly named power operator.
These are operator controls; the live Source evaluator still uses V1 and no
production endpoint, amount association or external-solc agreement is asserted.
The original V1 witness is preserved, rather than rewritten to describe V2.
-/
namespace Solidity.Correctness.Lowering.Unchecked.PowerV2Controls

private def byteTy : Source.IntTy := ⟨false, 8, by decide⟩

/-- The repaired unchecked operator returns the correct wrapped zero beyond
V1's cutoff, while the frozen helper still exhibits its original result. -/
theorem cutoff_value {D : Source.Layout} :
    Source.PowerV2.intPow (D := D) byteTy false 2 Source.PowerV2.cutoffExponent =
        .ok (Source.intWrap byteTy 0) ∧
      Source.powMod 2 Source.PowerV2.cutoffExponent 256 = 1 := by
  refine ⟨?_, Source.PowerV2.cutoff_repaired.2⟩
  have residue : Source.PowerV2.powMod 2 Source.PowerV2.cutoffExponent 256 % (256 : Int) = 0 :=
    Source.PowerV2.cutoff_repaired.1
  change Except.ok (Source.Val.int
    ((Source.PowerV2.powMod 2 Source.PowerV2.cutoffExponent 256) % 256) _) =
      Except.ok (Source.Val.int 0 _)
  simp only [residue]

/-- Checked uint8 power still returns the actual Source arithmetic panic,
including its existing bytes, instead of becoming a wrapping success. -/
theorem checked_overflow {D : Source.Layout} :
    Source.PowerV2.intPow (D := D) byteTy true 2 8 = Source.panic .arithmetic := by
  exact (Source.PowerV2.intPow_checked byteTy 2 8).trans rfl

/-- Guard the new typed dispatcher against bypassing checked overflow while
retaining the actual Source panic result and its bytes. -/
theorem typed_checked_overflow {D : Source.Layout} :
    Source.PowerV2.shiftVal (D := D) true .exp 8 (Source.intWrap byteTy 2) =
      Source.panic .arithmetic := by
  exact checked_overflow

#print axioms cutoff_value
#print axioms checked_overflow
#print axioms typed_checked_overflow

end Solidity.Correctness.Lowering.Unchecked.PowerV2Controls
