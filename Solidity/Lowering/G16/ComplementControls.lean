import Solidity.Lowering.G16.Complement
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.AliasRhsSubtraction

/-! Inhabited mixed-location complement clients and width/sign controls. -/
namespace Solidity.Lowering.G16.ComplementControls
open Solidity.Lowering.V07

/-- Instantiate the actual transport with mixed local/memory/storage clients
for every width, sign, checked mode and pipeline. -/
def client (t : Source.IntTy) (checked : Bool) (x : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  Complement.transport (MixedAssignmentControls.globals pipeline)
    {Source.SemanticsExamples.F0 with checked := checked} fuel
    (WordCastControls.source t x 0 hx (integer_zero_range t))
    (WordCastControls.target t x 0 hx (integer_zero_range t)) t
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t x 0 hx (integer_zero_range t)) true x hx rfl

/-- Guards against forgetting unsigned width restoration and interpreting a
signed complement as the nonnegative word bit pattern. -/
theorem wrong_complement_rejected :
    Source.IntTy.u8.wrap (-0-1) ≠ -1 ∧
    (SignedWidthCasts.ty 8 (by decide)).wrap (-0-1) ≠ 255 := by
  decide

def unsigned_boundary (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client .u8 checked 0 (by decide) pipeline fuel

def signed_boundary (checked : Bool) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  client (SignedWidthCasts.ty 8 (by decide)) checked 0 (by decide) pipeline fuel

end Solidity.Lowering.G16.ComplementControls

/-- info: 'Solidity.Lowering.G16.ComplementControls.wrong_complement_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.ComplementControls.wrong_complement_rejected
