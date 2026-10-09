import Solidity.Calculus.ChainKit
import Solidity.Calculus.RuleExists

/-!
# Every step of a chain has its rule

A step `φ ~> ψ` is `φ ~[r]~> ψ` for the rule `r` of the statement it fires on
(`Fml.OneStep.stepBy`, by `Stmt.rule_exists`), as master's
`Calculus/Chains.lean` stated it at `ad728b16`.  It sits beside
`Calculus/ChainKit.lean`, which `Calculus/RuleExists.lean` is not below.
With `Fml.StepBy.unique` the rule is the only one, so master's
`Fml.StepBy.ofOneStep` (a step and the rule `Fml.rule` finds) needs no
counterpart.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- The rule a focus names: the statement's (`Stmt.rule_exists`), or the
empty modality going through its frames. -/
def Focus.rule : Focus C → StepRule C
  | .stmt k m s => .taclet k m s (s.step k m) (Stmt.rule_exists k m s)
  | .empty => .emptyModality

theorem Focus.rule_focus : (f : Focus C) → f.rule.focus = f
  | .stmt .. | .empty => rfl

/-- **Every step has its rule**: `φ ~> ψ` is `φ ~[r]~> ψ` for the `r` that
fires (`localValueAssign` on `⟨ x = 1; ⟩ x == 1`). -/
theorem Fml.OneStep.stepBy {φ ψ : Fml C Γ} (h : Fml.OneStep φ ψ) : ∃ r, Fml.StepBy r φ ψ := by
  have hs := Fml.stepFocusR_snd (k := φ.fresh) φ
  unfold Fml.OneStep Fml.step at h
  rw [h] at hs
  obtain ⟨⟨f, ψ'⟩, hf, rfl⟩ := Option.map_eq_some_iff.1 hs
  refine ⟨f.rule, ?_⟩
  unfold Fml.StepBy
  rw [Focus.rule_focus]
  exact hf

end Solidity
