import Solidity.Correctness.Lowering.Unchecked.IntegerUpdate
import Solidity.Lowering.V07.SignedLocalUpdate

/-!
# Shared typed update arithmetic

Guards incorrect width or signedness transport in the arithmetic ingredient
for compound-one and increment/decrement rewriting. Existing V07 numeric
proofs are reused, not restated once per raw operator. This module does not
certify a raw output, lvalue evaluation, a callee, or an elaborated program.
The operand observation below is a local lemma hypothesis, not a field a
validator may accept as a semantic-correctness oracle.
-/
namespace Solidity.Correctness.Lowering.Unchecked

open Solidity.Lowering.V07
open UnsignedLocalUpdate (changed)

/-- The existing intrinsic wrapping operation at the source integer type.
The case split selects an existing representation; it adds no value carrier. -/
def updateValue {C : Contract} {Γ : Ctx} :
    (t : Source.IntTy) → Bool → Solidity.Val C Γ (integerPrim t) →
      Solidity.Val C Γ (integerPrim t)
  | ⟨false, bits, _⟩, inc, value => UnsignedLocalUpdate.updateValue bits inc value
  | ⟨true, bits, _⟩, inc, value => SignedLocalUpdate.updateValue bits inc value

/-- One numeric family for compound addition/subtraction by one and
increment/decrement, at every legal integer width and signedness. The Source
side is the real unchecked operation, retaining its exact result type. The
target side is the real intrinsic evaluator. A future checker must discharge
`read` from its recognized operand and initial state correspondence; it cannot
assume an arbitrary operand evaluation to certify an output. Pure arithmetic
has no operand effect order; stateful order remains a separate obligation. -/
theorem updateArithmetic {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (t : Source.IntTy) (inc : Bool)
    (value : Solidity.Val C Γ (integerPrim t)) (x : Int)
    (range : t.lo ≤ x ∧ x ≤ t.hi)
    (read : value.evalT target = .ok (integerValue t x range)) :
    Source.intBin (D := D) t false (if inc then .add else .sub) x 1 =
        .ok (Source.intWrap t (changed inc x)) ∧
      (updateValue t inc value).evalT target =
        .ok (integerValue t (t.wrap (changed inc x)) (t.wrap_mem (changed inc x))) := by
  rcases t with ⟨sign, bits, valid⟩
  cases sign with
  | false =>
    exact ⟨(integerUpdate (D := D) _ false inc x range).trans
      (UnsignedLocalUpdate.source_value bits valid inc x range),
      UnsignedLocalUpdate.value_run bits valid target inc value x range read⟩
  | true =>
    exact ⟨(integerUpdate (D := D) _ false inc x range).trans
      (SignedLocalUpdate.source_value bits valid inc x range),
      SignedLocalUpdate.value_run bits valid target inc value x range read⟩

#print axioms updateArithmetic

end Solidity.Correctness.Lowering.Unchecked
