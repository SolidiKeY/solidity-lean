import Solidity.Lowering.G16.UnsignedQuotRem
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited quotient/remainder clients, including the failure branch, and
negative controls for operation selection and operand order. -/
namespace Solidity.Lowering.G16.UnsignedQuotRemControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.UnsignedQuotRem

/-- Every width, pipeline, mode and quotient/remainder choice is instantiated
on the existing mixed local/reference input family. -/
def client (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (pipeline : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) (x y : Int)
    (hx : (UnsignedNarrowing.ty bits valid).lo ≤ x ∧ x ≤ (UnsignedNarrowing.ty bits valid).hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi) :=
  transport bits valid (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source (UnsignedNarrowing.ty bits valid) x y hx hy)
    (WordCastControls.target (UnsignedNarrowing.ty bits valid) x y hx hy) rem
    (WordCastControls.si _) (WordCastControls.ti _)
    (WordCastControls.initial _ x y hx hy) false true x y hx hy rfl rfl

/-- The generic theorem is instantiated with a zero divisor in both modes
and both pipelines. The selected local changes before failure: legacy writes
17 over 0, while via-IR writes 0 over 5. -/
def zero_client (pipeline : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  client 8 (by decide) pipeline checked rem fuel
    (if pipeline = .legacy then 17 else 0) (if pipeline = .legacy then 0 else 5)
    (by cases pipeline <;> decide) (by cases pipeline <;> decide)

/-- Guards against reversing operands and replacing quotient with remainder. -/
theorem wrong_quotrem_rejected :
    Solidity.Lowering.V07.UnsignedQuotRem.calculate false 17 5 ≠
      Solidity.Lowering.V07.UnsignedQuotRem.calculate false 5 17 ∧
    Solidity.Lowering.V07.UnsignedQuotRem.calculate false 17 5 ≠
      Solidity.Lowering.V07.UnsignedQuotRem.calculate true 17 5 := by
  decide

end Solidity.Lowering.G16.UnsignedQuotRemControls

/-- info: 'Solidity.Lowering.G16.UnsignedQuotRemControls.wrong_quotrem_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.UnsignedQuotRemControls.wrong_quotrem_rejected
