import Solidity.Lowering.G16.Arithmetic
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited clients and negative controls for the generic wrapping arithmetic
helper. These check actual Source/target instances without new native axioms. -/
namespace Solidity.Lowering.G16.ArithmeticControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.Arithmetic

/-- A concrete mixed-location input family witnesses the generic theorem's
premises for each operation, width, sign and pipeline. -/
def client (t : Source.IntTy) (op : RingOp) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  wrapping_transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (WordCastControls.source t x y hx hy) (WordCastControls.target t x y hx hy) t op
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t x y hx hy)
    true false x y hx hy rfl rfl

/-- Guards against dropping the unsigned mask, using unsigned interpretation
for signed output, and reversing subtraction operands. -/
theorem wrong_wrapping_rejected :
    Source.IntTy.u8.wrap (RingOp.calculate .add 255 1) ≠ 256 ∧
    (SignedWidthCasts.ty 8 (by decide)).wrap (RingOp.calculate .add 127 1) ≠ 128 ∧
    Source.IntTy.u8.wrap (RingOp.calculate .sub 0 1) ≠
      Source.IntTy.u8.wrap (RingOp.calculate .sub 1 0) := by
  decide

/-- Exercises the headline on an overflowing unsigned addition, rather than
only checking its mathematical observation separately. -/
def unsigned_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client .u8 .add 255 1 (by decide) (by decide) pipeline fuel

/-- Exercises the same generic statement on signed overflow. -/
def signed_boundary (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client (SignedWidthCasts.ty 8 (by decide)) .add 127 1 (by decide) (by decide) pipeline fuel

end Solidity.Lowering.G16.ArithmeticControls

/-- info: 'Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ArithmeticControls.wrong_wrapping_rejected
