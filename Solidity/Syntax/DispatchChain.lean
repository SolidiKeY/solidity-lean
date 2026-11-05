import Solidity.Syntax.Scoped

/-!
# Finite dispatch chains

A call through an internal function value elaborates to a finite chain
`if (c₁) { b₁ } else if (c₂) { b₂ } … else { fail }` (`fnDispatch`,
`Syntax/Elab/Stmt.lean`): one arm per candidate, its guard the comparison of
the callee's tag with the candidate's, its body the ordinary internal call of
the candidate on the captured arguments, and `fail` the unassigned-value
revert. `DispatchArm.chain` is that shape; `Semantics/Dispatch.lean` proves
which arm a run takes.
-/

namespace Solidity

/-- One arm of a finite dispatch: its guard and its body. -/
structure DispatchArm (C : Contract) (Γ : Ctx) where
  cond : Val C Γ .bool
  {Γ' : Ctx}
  body : Prog C Γ Γ'

/-- `if (c₁) { b₁ } else if (c₂) { b₂ } … else { fail }`. -/
def DispatchArm.chain {C : Contract} {Γ : Ctx} : List (DispatchArm C Γ) → Stmt C Γ Γ → Stmt C Γ Γ
  | [], fail => fail
  | a :: as, fail => .ite a.cond a.body (.cons (DispatchArm.chain as fail) .nil)

end Solidity
