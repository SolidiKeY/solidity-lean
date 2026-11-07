import Solidity.Yul.RawCheckedInitializedForPost
import Solidity.Yul.Checks.RawCheckedForPost
import Solidity.Yul.Checks.RawCheckedAdapterFor
/-! Kernel-only initializer/post combinations. Actual post controls and errors
are composed with initializers; refusals are runtime, not admission claims. -/
namespace Solidity.Yul.Checks.RawCheckedInitializedForPost
namespace Old
export Solidity.Yul.Checks.RawCheckedForPost.Old (ctx env initial frame rawFlag clean readFlag flag xCell flagCell repeated body partialGuard clearExpr)
export Solidity.Yul.Checks.RawCheckedForPost (clear)
export Solidity.Yul.Checks.RawCheckedAdapterFor (initializer broken continued)
end Old
def noop : RawCheckedAdapter.Adapter Old.ctx [] false false .skip :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .skip)
def packed := Solidity.Yul.RawCheckedInitializedForPost.adapter noop Old.readFlag Old.clear Old.repeated
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.forLoop (l := true) .skip (.some (.local Old.flag)) (.some Old.clearExpr) .cont)) := ⟨packed⟩
end Solidity.Yul.Checks.RawCheckedInitializedForPost

namespace Solidity.Yul.Checks.RawCheckedInitializedForPost
theorem initializerSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env), Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initializer Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [RawCheckedInitializedForPost.run,Solidity.Yul.Checks.RawCheckedAdapterFor.initializes]
  change RawCheckedForPost.run Old.readFlag Old.clear Old.body pipeline 20
    (Old.frame 2 257 (LocalValue.clean (.bool false)) world) = _
  rw [RawCheckedForPost.run.eq_def]
  dsimp only
  rw [Solidity.Yul.Checks.RawCheckedAdapterFor.clearedGuard]
  rfl

theorem nestedBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env), Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.rawFlag 2) world) := by
  intro pipeline world
  change RawCheckedForPost.run Old.readFlag Old.clear Old.body pipeline 20 (Old.initial 2 257 2 world) = _
  simp only [RawCheckedForPost.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,
    Old.body,Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedTrue,if_true]

theorem continuePost : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env),(Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  have actual : RawCheckedInitializedForPost.run noop Old.readFlag Old.clear Old.repeated pipeline 21
      (Old.initial 2 257 2 world) =
      RawCheckedForPost.run Old.readFlag Old.clear Old.repeated pipeline 20 (Old.initial 2 257 2 world) := by rfl
  rw [actual]
  exact Solidity.Yul.Checks.RawCheckedForPost.continuePost pipeline world

theorem postTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env),(Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 5 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 5 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 5 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.noop Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.partialGuard Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.repeated pipeline 5 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact Solidity.Yul.Checks.RawCheckedForPost.postTimeout pipeline world

theorem breakRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env), Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.broken Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) = (.error (.stuck "for initializer"),Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem continueRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env), Solidity.Yul.RawCheckedInitializedForPost.run Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.continued Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.readFlag Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clear Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) = (.error (.stuck "for initializer"),Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.ctx), Solidity.Yul.Checks.RawCheckedInitializedForPost.packed.run pipeline 0 state = (.error .timeout,state) := by
  intro pipeline state
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env))
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedInitializedForPost.packed.run glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.forLoop (R := []) (M := false) (u := false) (l := true) .skip
 (.some (.local Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.flag)) (.some Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clearExpr) .cont) state.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedInitializedForPost.packed.run glob.pipeline fuel state) := by
  intro glob frame checked fuel nps ph state same
  exact packed.correct glob frame checked fuel nps ph state same

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env),
 (Solidity.Source.execS glob frame 21 nps ph
 (Solidity.Source.RStmt.forLoop (R := []) (M := false) (u := false) (l := true) .skip
 (.some (.local Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.flag)) (.some Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clearExpr) .cont) Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedInitializedForPost.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawCheckedInitializedForPost
#print axioms Solidity.Yul.RawCheckedInitializedForPost.correct
#print axioms Solidity.Yul.RawCheckedInitializedForPost.adapter
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.initializerSkips
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.nestedBreak
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.continuePost
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.postTimeout
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.breakRefuses
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.continueRefuses
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.zero
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedInitializedForPost.sourceCompletes
