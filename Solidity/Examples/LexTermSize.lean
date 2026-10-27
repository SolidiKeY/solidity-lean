import Solidity.Calculus.TermSize

/-!
# Honest tuple VC update and node budgets

The ordinary tuple rule emits every captured component. Its update length is
arity plus the condition, while other dispatches retain the two-element bound.
The global linear term-size bound continues to count the full tuple VC.
-/
namespace Solidity.Examples.LexTermSize

variable {C : Contract} {Γ : Ctx}

private def yes : Val C Γ .bool := .simple (.bool true)
private def pair : LoopMetrics C Γ 2 :=
  .cons (.simple (.lit 0 (by decide))) (.cons (.simple (.lit 0 (by decide))) .nil)
private def triple : LoopMetrics C Γ 3 :=
  .cons (.simple (.lit 0 (by decide))) pair

example : (LoopLex.snapshot 0 (pair : LoopMetrics C Γ 2)).length = 2 := rfl
example : (LoopLex.snapshot 0 (triple : LoopMetrics C Γ 3)).length = 3 := rfl

example : (Stmt.loop (.invLex yes pair false []) yes (.nil : Prog C Γ Γ)).updateLimit .diamond = 3 := rfl
example : (Stmt.loop (.invLex yes triple false []) yes (.nil : Prog C Γ Γ)).updateLimit .diamond = 4 := rfl
example : (Stmt.loop (.invLex yes triple false []) yes (.nil : Prog C Γ Γ)).updateLimit .box = 2 := rfl
example : (Stmt.loop (.invLex yes triple true []) yes (.nil : Prog C Γ Γ)).updateLimit .diamond = 2 := rfl
example : (Stmt.loop (.inv yes (some (.simple (.lit 0 (by decide)))) false []) yes
    (.nil : Prog C Γ Γ)).updateLimit .diamond = 2 := rfl

/-- A three-component rule really has four elements in its initial update. -/
example : ∃ U ∈ ((Stmt.loop (.invLex yes triple false []) yes
    (.nil : Prog C Γ Γ)).step 0 .diamond).upds, U.2.2.length = 4 := by
  refine ⟨⟨Γ, .val .bool :: LoopLex.SavedCtx 3 Γ,
    (LoopLex.snapshot 0 (triple : LoopMetrics C Γ 3)).decl (fse 3) (.val (yes : Val C Γ .bool).lower)⟩,
    ?_, rfl⟩
  exact .head _

example (k : Nat) :
    ∀ U ∈ ((Stmt.loop (.invLex yes triple false []) yes
      (.nil : Prog C Γ Γ)).step k .diamond).upds, U.2.2.length ≤ 4 :=
  Stmt.step_upds_le k .diamond _

example (k : Nat) :
    ∀ U ∈ ((Stmt.loop (.invLex yes triple false []) yes
      (.nil : Prog C Γ Γ)).step k .box).upds, U.2.2.length ≤ 2 :=
  Stmt.step_upds_le_two k .box _ rfl

/-- The global coefficient is unchanged for arbitrary tuple arity and values. -/
example (k : Nat) (I c : Val C Γ .bool) (metrics : LoopMetrics C Γ (n + 2))
    (body : Prog C Γ Δ) :
    (∀ U ∈ ((Stmt.loop (.invLex I metrics false []) c body).step k .diamond).upds,
      U.2.2.tmSize ≤ 16 * (Stmt.loop (.invLex I metrics false []) c body).size + 16) ∧
    (∀ φ ∈ ((Stmt.loop (.invLex I metrics false []) c body).step k .diamond).fmls,
      φ.2.tmSize ≤ 16 * (Stmt.loop (.invLex I metrics false []) c body).size + 16) :=
  Stmt.step_tmSize_le k .diamond _

end Solidity.Examples.LexTermSize
