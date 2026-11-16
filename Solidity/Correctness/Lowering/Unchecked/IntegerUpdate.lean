import Solidity.Correctness.Lowering.Unchecked.Relation

/-!
# Shared integer compound-update ingredient

Provides the Source arithmetic identity needed to guard incorrect checkedness
or width transport during increment rewriting. This is a
Source arithmetic ingredient only: it does not prove raw rewriting, lvalue
single evaluation, intrinsic target association, or pass correctness.
-/
namespace Solidity.Correctness.Lowering.Unchecked

open Solidity.Source

/-- Increment and decrement use the same typed result operation as compound
addition/subtraction by one, at every integer width/signedness and in either
checkedness mode. The Boolean index avoids separate per-operator proofs.
Panics and wrapped values are retained in the actual `Source.R` equality. -/
theorem integerUpdate {D : Layout} (t : IntTy) (checked inc : Bool)
    (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi) :
    intBin (D := D) t checked (if inc then .add else .sub) x 1 =
      incDecVal checked inc (Source.Val.int x range) := by
  cases inc <;> rfl

#print axioms integerUpdate

end Solidity.Correctness.Lowering.Unchecked
