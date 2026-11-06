import Solidity.Lowering.Readonly.SourceHistory

/-! Actual zero-bound base for all 17 Source evaluator components. This is
exhaustion, not successful call coverage or the positive-bound induction step. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}

theorem at_zero (global : Glob E) : At global 0 := by
  constructor <;> intros <;> first
  | (unfold Effect; intro locals state; exact .start _ _)
  | assumption

end Solidity.Lowering.Readonly.SourceHistory
