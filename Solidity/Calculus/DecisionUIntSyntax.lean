import Solidity.Calculus.HashPremise

/-! # Intrinsic literal-linear uint source syntax
This lower layer contains only the existing typed source predicate and its
structural hash fact; translation/coverage proofs remain above Decision.
-/
namespace Solidity

/-- UInt locals/literals, addition/subtraction, and a literal multiplication operand. -/
inductive Tm.UIntLinear {C : Contract} {Γ : Ctx} : Tm C Γ (.val .uint) → Prop where
  | local (i : Idx Γ (.val .uint)) : Tm.UIntLinear (.pvV i)
  | lit (v : PrimTy.uint.Denote) : Tm.UIntLinear (.app0 (.lit v))
  | add {a b : Tm C Γ (.val .uint)} : Tm.UIntLinear a → Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .add rfl) a b)
  | sub {a b : Tm C Γ (.val .uint)} : Tm.UIntLinear a → Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .sub rfl) a b)
  | mulL (v : PrimTy.uint.Denote) {b : Tm C Γ (.val .uint)} : Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .mul rfl) (.app0 (.lit v)) b)
  | mulR {a : Tm C Γ (.val .uint)} (v : PrimTy.uint.Denote) : Tm.UIntLinear a →
      Tm.UIntLinear (.app2 (.binop .mul rfl) a (.app0 (.lit v)))

namespace Decide

/-- The grammar contains no hash terms. -/
theorem uintLinear_hashFree {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) : t.hasHash = false := by
  induction h <;> simp_all only [Tm.hasHash, Op2.isHash, Bool.false_or]

end Decide
end Solidity
