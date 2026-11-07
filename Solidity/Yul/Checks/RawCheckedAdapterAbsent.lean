import Solidity.Yul.RawCheckedAdapterAbsent
import Solidity.Yul.Checks.RawCheckedAdapterFor
/-! Kernel-only omitted-guard witnesses over real checked producers.
The initializer writes a local before break; malformed initializer control and
zero fuel are preserved. Runtime refusal is not an admission claim. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterAbsent
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterFor.Old (ctx env initial frame clean clearExpr)
export Solidity.Yul.Checks.RawCheckedAdapterFor (initializer broken)
export Solidity.Yul.Checks.RawCheckedAdapterLoop.Old (always)
end Old
def present := Solidity.Yul.RawCheckedAdapterFor.adapter Old.initializer Old.always Old.broken
def absent := Solidity.Yul.RawCheckedAdapterAbsent.adapter present
def refused := Solidity.Yul.RawCheckedAdapterAbsent.adapter
  (Solidity.Yul.RawCheckedAdapterFor.adapter Old.broken Old.always Old.broken)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.forLoop (l := true) (.expr Old.clearExpr) .none .none .brk)) := ⟨absent⟩
end Solidity.Yul.Checks.RawCheckedAdapterAbsent

namespace Solidity.Yul.Checks.RawCheckedAdapterAbsent
theorem runtimeRetained : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.ctx), Solidity.Yul.Checks.RawCheckedAdapterAbsent.absent.run pipeline fuel state = Solidity.Yul.Checks.RawCheckedAdapterAbsent.present.run pipeline fuel state := by
  intro pipeline fuel state
  rfl

theorem initialWriteBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env), Solidity.Yul.Checks.RawCheckedAdapterAbsent.absent.run pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.initial 2 257 2 world) = (.ok .normal, Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rfl

theorem initializerRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env), Solidity.Yul.Checks.RawCheckedAdapterAbsent.refused.run pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.initial 2 257 2 world) = (.error (.stuck "for initializer"), Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.ctx), Solidity.Yul.Checks.RawCheckedAdapterAbsent.absent.run pipeline 0 state = (.error .timeout,state) := by
  intro pipeline state
  rfl

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterFor.dirtyBoundary world

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env))
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterAbsent.absent.run glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (R := []) (M := false) (u := false) (l := true) (.expr Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.clearExpr) .none .none .brk) state.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterAbsent.absent.run glob.pipeline fuel state) := by
  intro glob frame checked fuel nps ph state same
  exact absent.correct glob frame checked fuel nps ph state same

end Solidity.Yul.Checks.RawCheckedAdapterAbsent
#print axioms Solidity.Yul.RawCheckedAdapterAbsent.adapter
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.runtimeRetained
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.initialWriteBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.initializerRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.zero
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.sourceAll

namespace Solidity.Yul.Checks.RawCheckedAdapterAbsent
theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env), (Solidity.Source.execS glob frame 21 nps ph
 (Solidity.Source.RStmt.forLoop (R := []) (M := false) (u := false) (l := true) (.expr Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.clearExpr) .none .none .brk)
 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceRefuses : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env), (Solidity.Source.execS glob frame 21 nps ph
 (Solidity.Source.RStmt.forLoop (R := []) (M := false) (u := false) (l := true) .brk .none .none .brk)
 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env,world) =
 (.error (.stuck "for initializer"),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterAbsent.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawCheckedAdapterAbsent
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.sourceCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterAbsent.sourceRefuses
