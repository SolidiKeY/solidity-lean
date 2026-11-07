import Solidity.Yul.RawCheckedForPost
import Solidity.Yul.Checks.RawCheckedAdapterLoop
/-! Kernel-only checked post-loop controls. Posts run after normal/continue,
are skipped on break and preserve partial error states. No admission claim. -/
namespace Solidity.Yul.Checks.RawCheckedForPost
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterLoop.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag clean partialGuard always)
export Solidity.Yul.Checks.RawCheckedAdapterLoop (body normalBody repeated)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearExpr)
end Old
def clear : LocalBoolControl.Supported Old.env Old.ctx.tys Old.clearExpr :=
 .assign Old.flag (.base (.literal false))
def witness : Nonempty (LocalBoolControl.Supported Old.env Old.ctx.tys Old.clearExpr) := ⟨clear⟩
end Solidity.Yul.Checks.RawCheckedForPost

namespace Solidity.Yul.Checks.RawCheckedForPost
theorem clearPostStage : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawCheckedForPost.clear 19 (Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedForPost.Old.rawFlag 2) world) = (.ok (),Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro world
  rfl

theorem partialPostStage : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard 3 (Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedForPost.Old.rawFlag 2) world) = (.error .timeout,Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro world
  rfl

theorem falseGuardStage : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag 18 (Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro world
  rfl

theorem guardThree : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag 3 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedForPost.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedForPost.Old.rawFlag 2) world) := by
  intro world
  rfl

end Solidity.Yul.Checks.RawCheckedForPost

namespace Solidity.Yul.Checks.RawCheckedForPost
theorem breakSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedForPost.Old.body pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.Checks.RawCheckedForPost.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedForPost.Old.rawFlag 2) world) := by
  intro pipeline world
  simp only [Solidity.Yul.RawCheckedForPost.run,
    Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,Old.body,
    Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedTrue,if_true]

theorem continuePost : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env),(Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  let first := Old.frame 2 257 (Old.rawFlag 2) world
  let next := Old.frame 2 257 (LocalValue.clean (.bool false)) world
  have actual : RawCheckedForPost.run Old.readFlag clear Old.repeated pipeline 20 (Old.initial 2 257 2 world) =
      RawCheckedForPost.run Old.readFlag clear Old.repeated pipeline 19 next := by
    rw [RawCheckedForPost.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue]
    change RawSourceForPost.after clear (RawCheckedForPost.run Old.readFlag clear Old.repeated pipeline 19)
      19 first = _
    rw [RawSourceForPost.after,clearPostStage]
  rw [actual,RawCheckedForPost.run.eq_def]
  dsimp only
  rw [falseGuardStage]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem normalPost : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env),(Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.normalBody pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.normalBody pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.normalBody pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.normalBody pipeline 20 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedForPost.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,
    Solidity.Yul.Checks.RawCheckedAdapterLoop.normalBodyRuns]
  exact ⟨by rfl,by rfl,by rfl,by rfl⟩

theorem postTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env),(Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 4 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 4 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 4 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedForPost.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedForPost.Old.repeated pipeline 4 (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  let first := Old.frame 2 257 (Old.rawFlag 2) world
  let next := Old.frame 2 257 (LocalValue.clean (.bool false)) world
  have actual : RawCheckedForPost.run Old.readFlag Old.partialGuard Old.repeated pipeline 4
      (Old.initial 2 257 2 world) = (.error .timeout,next) := by
    rw [RawCheckedForPost.run,guardThree]
    change RawSourceForPost.after Old.partialGuard
      (RawCheckedForPost.run Old.readFlag Old.partialGuard Old.repeated pipeline 3) 3 first = _
    rw [RawSourceForPost.after,partialPostStage]
  rw [actual]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedForPost.Old.ctx), Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.body pipeline 0 state = (.error .timeout,state) := by
  intro pipeline state
  rfl

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedForPost.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterLoop.dirtyBoundary world

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedForPost.Old.env) (frame : Solidity.Source.Fr) (_checked : frame.checked = true)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedForPost.Old.env))
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedForPost.Old.ctx) (_same : Solidity.Yul.RawCoherent.coherent state = true),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.body glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.forIter glob frame fuel nps ph (.some (.local Solidity.Yul.Checks.RawCheckedForPost.Old.flag)) (.some Solidity.Yul.Checks.RawCheckedForPost.Old.clearExpr)
 (Solidity.Source.RStmt.block (R := []) (M := false) (k := ⟨true,false⟩) Solidity.Yul.Checks.RawCheckedAdapterSequence.items) state.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedForPost.Old.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedForPost.run Solidity.Yul.Checks.RawCheckedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedForPost.clear Solidity.Yul.Checks.RawCheckedForPost.Old.body glob.pipeline fuel state) := by
  intro glob frame checked fuel nps ph state same
  exact Solidity.Yul.RawCheckedForPost.correct Old.readFlag clear Old.body glob frame checked fuel nps ph state same

theorem sourceContinue : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedForPost.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedForPost.Old.env),
 (Solidity.Source.forIter glob frame 20 nps ph (.some (.local Solidity.Yul.Checks.RawCheckedForPost.Old.flag)) (.some Solidity.Yul.Checks.RawCheckedForPost.Old.clearExpr)
 (Solidity.Source.RStmt.cont (E := Solidity.Yul.Checks.RawCheckedForPost.Old.env) (R := []) (M := false) (u := false) (Γ := Solidity.Yul.Checks.RawCheckedForPost.Old.ctx.tys)) Solidity.Yul.Checks.RawCheckedForPost.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedForPost.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedForPost.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawCheckedForPost
#print axioms Solidity.Yul.RawCheckedForPost.correct
#print axioms Solidity.Yul.Checks.RawCheckedForPost.breakSkips
#print axioms Solidity.Yul.Checks.RawCheckedForPost.continuePost
#print axioms Solidity.Yul.Checks.RawCheckedForPost.normalPost
#print axioms Solidity.Yul.Checks.RawCheckedForPost.postTimeout
#print axioms Solidity.Yul.Checks.RawCheckedForPost.zero
#print axioms Solidity.Yul.Checks.RawCheckedForPost.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedForPost.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedForPost.sourceContinue
#print axioms Solidity.Yul.Checks.RawCheckedForPost.clearPostStage
#print axioms Solidity.Yul.Checks.RawCheckedForPost.partialPostStage
#print axioms Solidity.Yul.Checks.RawCheckedForPost.falseGuardStage
#print axioms Solidity.Yul.Checks.RawCheckedForPost.guardThree
