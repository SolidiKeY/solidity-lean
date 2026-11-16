import Solidity.Correctness.Lowering.Unchecked.WrappingArithmetic

/-!
# Supplied word-value association

Guards accepting an unrelated supplied intrinsic value as wrapping arithmetic.
The total recognizer inspects that value and returns its actual operands plus
an equality to the selected existing template. The certificate contains only
syntax association, not execution correctness. This is the uint256 value-leaf
boundary, not the all-arm raw/program validator or its production endpoint;
other widths, casts, input bindings, program effects and refusals remain visible.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- Static association of a supplied value with one wrapping word operation. -/
structure WordAssociation {C : Contract} {Γ : Ctx}
    (op : Source.BinOp) (value : Val C Γ .uint) where
  left : Val C Γ .uint
  right : Val C Γ .uint
  output : wrappingValue op Source.IntTy.u256 left right = some value

/-- A total, proof-producing inspection of the supplied intrinsic value.
No caller-supplied execution equation is accepted. Rejection is an explicit
coverage gap; this initial word boundary does not exclude other source types
from the final assignment. -/
def checkWordValue {C : Contract} {Γ : Ctx}
    (op : Source.BinOp) (value : Val C Γ .uint) : Option (WordAssociation op value) :=
  match op, value with
  | .add, .binop (p := .uint) .addW _ _ a b => some ⟨a, b, by rfl⟩
  | .sub, .binop (p := .uint) .subW _ _ a b => some ⟨a, b, by rfl⟩
  | .mul, .binop (p := .uint) .mulW _ _ a b => some ⟨a, b, by rfl⟩
  | _, _ => none

/-- A returned static certificate connects the actual supplied value evaluator
to Source arithmetic, using the previously proved semantic family. Operand
observations must still be derived from recognized source operands and initial
correspondence; they are not complete-program correctness certificates. -/
theorem wordAssociation_sound {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (op : Source.BinOp) (value : Val C Γ .uint)
    (certificate : WordAssociation op value)
    (x y : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (hy : Source.IntTy.u256.lo ≤ y ∧ y ≤ Source.IntTy.u256.hi)
    (left : certificate.left.evalT target = .ok (integerValue Source.IntTy.u256 x hx))
    (right : certificate.right.evalT target = .ok (integerValue Source.IntTy.u256 y hy)) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256)) (modelResult : PrimTy.uint.Denote),
      Source.binVal false op (.int x hx) (.int y hy) = .ok sourceResult ∧
      value.evalT target = .ok modelResult ∧ IntValueRel Source.IntTy.u256 sourceResult modelResult := by
  exact wrappingValue_sound target op Source.IntTy.u256 certificate.left certificate.right value
    certificate.output x y hx hy left right

#print axioms wordAssociation_sound

end Solidity.Correctness.Lowering.Unchecked
