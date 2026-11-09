import Solidity.Lowering.G16.SignedNegation
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited checked/unchecked negation clients and a minimum-value control. -/
namespace Solidity.Lowering.G16.SignedNegationControls
open Solidity.Lowering.V07

/-- The actual source and target are instantiated without a nonminimum
premise, so the same client includes checked arithmetic panic. -/
def client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (checked : Bool) (x : Int)
    (hx : (SignedWidthCasts.ty bits valid).lo ≤ x ∧ x ≤ (SignedWidthCasts.ty bits valid).hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  Solidity.Lowering.G16.SignedNegation.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (SignedWidthCasts.ty bits valid) x 0 hx
      (integer_zero_range (SignedWidthCasts.ty bits valid)))
    (WordCastControls.target (SignedWidthCasts.ty bits valid) x 0 hx
      (integer_zero_range (SignedWidthCasts.ty bits valid)))
    bits valid .here .here x hx rfl rfl

/-- Guards against treating checked minimum negation as wrapping success or
performing unchecked minimum negation without restoring the signed width. -/
theorem wrong_minimum_negation_rejected {D : Source.Layout} :
    (Source.unaryVal true .neg
      (.int (-128) (by decide) : Source.Val D (.int (SignedWidthCasts.ty 8 (by decide))))).map Source.Val.key ≠
      .ok (some (-128)) ∧
    (Source.unaryVal false .neg
      (.int (-128) (by decide) : Source.Val D (.int (SignedWidthCasts.ty 8 (by decide))))).map Source.Val.key ≠
      .ok (some 128) := by
  change (Except.error (.revert (Source.panicData .arithmetic)) : Source.R (Option Int)) ≠
      .ok (some (-128)) ∧
    (Except.ok (some (-128)) : Source.R (Option Int)) ≠ .ok (some 128)
  exact ⟨(by intro h; cases h),(by intro h; cases h)⟩

/-- A failure-boundary instance of the headline, for each pipeline and mode. -/
def minimum_client (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client 8 (by decide) checked (-128) (by decide) pipeline fuel

end Solidity.Lowering.G16.SignedNegationControls

/-- info: 'Solidity.Lowering.G16.SignedNegationControls.wrong_minimum_negation_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.SignedNegationControls.wrong_minimum_negation_rejected
