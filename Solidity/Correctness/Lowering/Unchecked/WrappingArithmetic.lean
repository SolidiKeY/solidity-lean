import Solidity.Lowering.G16.Arithmetic

/-!
# Shared typed wrapping arithmetic

Guards width/signedness transport for the three compound arithmetic operators
rewritten by `uncheckStmts`. This total value-template selector reuses the
G16 selector and its V07 operations. It is not the supplied-output validator:
an actual checker
must associate the raw/Source input and exact emitted code with these values.
Unsupported value operators return `none`; this is not a final source-language
exclusion or a claim of complete arithmetic coverage.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- Select an existing typed wrapping operation, without a new value carrier. -/
def wrappingValue {C : Contract} {Γ : Ctx} (op : Source.BinOp)
    (t : Source.IntTy) (a b : Val C Γ (integerPrim t)) :
    Option (Val C Γ (integerPrim t)) :=
  match op with
  | .add => some (Solidity.Lowering.G16.Arithmetic.wrappingValue t .add a b)
  | .sub => some (Solidity.Lowering.G16.Arithmetic.wrappingValue t .sub a b)
  | .mul => some (Solidity.Lowering.G16.Arithmetic.wrappingValue t .mul a b)
  | _ => none

/-- Every selected numeric template agrees with actual unchecked Source
arithmetic. Operand observations are local value-lemma inputs, not execution
certificates a validator may assume: recognized operands must establish them,
and compositional proofs must retain operand failures/effects separately.
There is no bound on the arithmetic result and no overflow exclusion. -/
theorem wrappingValue_sound {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (op : Source.BinOp) (t : Source.IntTy)
    (a b value : Val C Γ (integerPrim t))
    (accepted : wrappingValue op t a b = some value)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (left : a.evalT target = .ok (integerValue t x hx))
    (right : b.evalT target = .ok (integerValue t y hy)) :
    ∃ (sourceResult : Source.Val D (.int t)) (modelResult : (integerPrim t).Denote),
      Source.binVal false op (.int x hx) (.int y hy) = .ok sourceResult ∧
      value.evalT target = .ok modelResult ∧ IntValueRel t sourceResult modelResult := by
  have finish (z : Int)
      (source : Source.binVal (D := D) false op (.int x hx) (.int y hy) =
        .ok (Source.intWrap t z))
      (model : value.evalT target = .ok (integerValue t (t.wrap z) (t.wrap_mem z))) :
      ∃ (sourceResult : Source.Val D (.int t)) (modelResult : (integerPrim t).Denote),
        Source.binVal false op (.int x hx) (.int y hy) = .ok sourceResult ∧
        value.evalT target = .ok modelResult ∧ IntValueRel t sourceResult modelResult := by
    exact ⟨Source.intWrap t z, integerValue t (t.wrap z) (t.wrap_mem z),
      source, model, integer_related t (t.wrap z) (t.wrap_mem z)⟩
  rcases t with ⟨sign, bits, valid⟩
  cases sign <;> cases op <;> simp only [wrappingValue, Solidity.Lowering.G16.Arithmetic.wrappingValue] at accepted <;> cases accepted
  all_goals first
  | exact finish (x + y) (UnsignedAddition.source_add_unchecked bits valid x y hx hy)
      (UnsignedAddition.add_value_run target bits valid a b x y hx hy left right)
  | exact finish (x - y) (UnsignedNarrowing.source_sub_unchecked bits valid x y hx hy)
      (UnsignedNarrowing.sub_value_run target bits valid a b x y hx hy left right)
  | exact finish (x * y) (UnsignedMultiplication.source_mul_unchecked bits valid x y hx hy)
      (UnsignedMultiplication.mul_value_run target bits valid a b x y hx hy left right)
  | exact finish (x + y) (SignedNarrowAddition.source_add_unchecked bits valid x y hx hy)
      (SignedNarrowAddition.add_value_run bits valid target a b x y hx hy left right)
  | exact finish (x - y) (SignedNarrowSubtraction.source_sub_unchecked bits valid x y hx hy)
      (SignedNarrowSubtraction.sub_value_run bits valid target a b x y hx hy left right)
  | exact finish (x * y) (SignedNarrowMultiplication.source_mul_unchecked bits valid x y hx hy)
      (SignedNarrowMultiplication.mul_value_run bits valid target a b x y hx hy left right)

#print axioms wrappingValue_sound

end Solidity.Correctness.Lowering.Unchecked
