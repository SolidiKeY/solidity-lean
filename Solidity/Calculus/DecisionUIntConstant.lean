import Solidity.Calculus.DecisionUIntSyntax

/-! # Optional denotation of memory-only uint arithmetic
The existing literal-linear grammar cannot read a scalar local in a context
containing only one memory local. Its full optional denotation is therefore
state-independent, including partial arithmetic; no termination premise is used.
-/
namespace Solidity.Decide

/-- In a memory-only context, literal-linear uint terms have the same optional
Theory denotation at every pair of typed states, even across different heaps. -/
theorem uintLinear_memoryOnly_denote {C : Contract} {R : RefTy}
    {t : Tm C [.mem R] (.val .uint)} (h : t.UIntLinear)
    (σ τ : State C [.mem R]) : t.denote σ = t.denote τ := by
  induction h with
  | «local» i => cases i with | there j => cases j
  | lit v => rfl
  | add ha hb iha ihb | sub ha hb iha ihb =>
    simp only [Tm.denote, Op2.denote, iha, ihb]
  | mulL v hb ihb =>
    simp only [Tm.denote, Op2.denote, Op0.denote, ihb]
  | mulR v ha iha =>
    simp only [Tm.denote, Op2.denote, Op0.denote, iha]

end Solidity.Decide
