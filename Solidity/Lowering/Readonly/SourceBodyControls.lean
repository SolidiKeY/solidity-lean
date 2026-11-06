import Solidity.Lowering.Readonly.SourceBodyEffects
import Solidity.Source.SemanticsExamples

/-! Inhabited Source observations for the body-history components. Static mode
permits local return updates; these observations do not certify native calls. -/
namespace Solidity.Lowering.Readonly.SourceBodyControls
open Solidity.Source Solidity.Source.SemanticsExamples
def staticCall (p : Solidity.Roadmap.Pipeline) (twice : Bool) :=
  (callInternal (G1 p) { F0 with static := true } 30 fDecl
    (Vals.cons (D := E0.layout) (.bool twice) .nil) [uint]).run (.nil, s0)
theorem legacy_value : intOf (staticCall .legacy true) = some 2 := by decide
theorem viaIR_value : intOf (staticCall .viaIR true) = some 1 := by decide
theorem once_value : intOf (staticCall .legacy false) = some 1 := by decide
theorem local_update_not_frozen : intOf (staticCall .legacy true) ≠ some 0 := by decide
theorem legacy_journal : (staticCall .legacy true).2.2.ex = (s0 : St E0).ex := by rfl
theorem viaIR_journal : (staticCall .viaIR true).2.2.ex = (s0 : St E0).ex := by rfl
theorem saved_function_locals :
    (staticCall .legacy true).2.2.fnLocals = (s0 : St E0).fnLocals := by rfl
end Solidity.Lowering.Readonly.SourceBodyControls
