import Solidity.Yul.RawCheckedAdapterLoop
import Solidity.Yul.RawCheckedAdapterIfElse
import Solidity.Yul.Checks.RawCheckedAdapterIfElse
/-! Concrete nested checked while producers. Break is consumed; normal and
continue recheck the real guard on the actual body frame. Independent Source
completions, all-fuel divergence and raw dirty/error controls remain explicit. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterLoop
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag clean partialGuard always)
export Solidity.Yul.Checks.RawCheckedAdapterSequence.Old (clearContinueItems clearContinueProof)
export Solidity.Yul.Checks.RawCheckedWhile (guardNext)
end Old
def body : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items) :=
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch
def normalBody : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.normalItems) :=
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch
def continued : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.ifElse (.bool true) (.block Old.clearContinueItems) .brk) :=
 Solidity.Yul.RawCheckedAdapterIfElse.adapter Old.always
   (Solidity.Yul.RawCheckedAdapter.block Old.clearContinueProof)
   Solidity.Yul.Checks.RawCheckedAdapter.pureBreak
def repeated : RawCheckedAdapter.Adapter Old.ctx [] false false .cont :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .continue_)
def packed : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.whileLoop (l := true) (.local Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) :=
 Solidity.Yul.RawCheckedAdapterLoop.loop Old.readFlag body
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.whileLoop (l := true) (.local Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items))) := ⟨packed⟩
end Solidity.Yul.Checks.RawCheckedAdapterLoop

namespace Solidity.Yul.Checks.RawCheckedAdapterLoop
theorem normalHeadCaptured : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) := by
  intro pipeline world
  rfl

theorem normalBodyRuns : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterLoop.normalBody.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons
    Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead
    Solidity.Yul.Checks.RawCheckedAdapterSequence.clearRest pipeline 18
    (Old.frame 2 257 (Old.rawFlag 2) world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,normalHeadCaptured]
  exact Solidity.Yul.Checks.RawCheckedAdapterSequence.normalTail pipeline world

theorem constantGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.always 18 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) = (.ok true,Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) := by
  intro world
  rfl

theorem clearBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueProof pipeline 18 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem continuedBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterLoop.continued.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change RawCheckedAdapterIfElse.run Old.always (Solidity.Yul.RawCheckedAdapter.block Old.clearContinueProof)
    Solidity.Yul.Checks.RawCheckedAdapter.pureBreak pipeline 19
    (Old.frame 2 257 (Old.rawFlag 2) world) = _
  rw [RawCheckedAdapterIfElse.run,constantGuard]
  change RawCheckedControlSequence.block Old.clearContinueProof pipeline 18
    (Old.frame 2 257 (Old.rawFlag 2) world) = _
  exact clearBody pipeline world

theorem afterClearGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag 18 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro world
  rfl

theorem rawBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) := by
  intro pipeline world
  simp only [Solidity.Yul.RawCheckedAdapterLoop.run,
    Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,body,
    Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedTrue,if_true]


theorem rawContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.continued pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterLoop.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,continuedBody]
  change Solidity.Yul.RawCheckedAdapterLoop.run Old.readFlag continued pipeline 19
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world) = _
  rw [Solidity.Yul.RawCheckedAdapterLoop.run.eq_def]
  dsimp only
  rw [afterClearGuard]
  rfl

theorem rawNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.normalBody pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterLoop.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue,normalBodyRuns]
  change Solidity.Yul.RawCheckedAdapterLoop.run Old.readFlag normalBody pipeline 19
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world) = _
  rw [Solidity.Yul.RawCheckedAdapterLoop.run.eq_def]
  dsimp only
  rw [afterClearGuard]
  rfl

theorem falseSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 0 world) = (.ok (),Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 0) world) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterLoop.run,Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardFalse]
  rfl

theorem guardTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem packedBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterLoop.packed.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.rawFlag 2) world) := by
  intro pipeline world
  change ((Solidity.Yul.RawCheckedAdapterLoop.run Old.readFlag body pipeline 20 (Old.initial 2 257 2 world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterLoop.run Old.readFlag body pipeline 20 (Old.initial 2 257 2 world)).2) = _
  rw [rawBreak]
  rfl

theorem diverges : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx),
 (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.always Solidity.Yul.Checks.RawCheckedAdapterLoop.repeated pipeline fuel state).1 = .error .timeout := by
  intro pipeline fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    cases fuel with
    | zero => rfl
    | succ n =>
      rw [Solidity.Yul.RawCheckedAdapterLoop.run,Old.guardNext]
      change (Solidity.Yul.RawCheckedAdapterLoop.run Old.always repeated pipeline (n+1)
        (RawCoherent.capture state (RawCoherent.prepare state))).1 = .error .timeout
      exact ih _

theorem foreverRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx),
 (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.always Solidity.Yul.Checks.RawCheckedAdapterLoop.repeated pipeline fuel state).1 ≠ .error .timeout → False := by
  intro pipeline fuel state terminal
  exact terminal (diverges pipeline fuel state)

theorem sourcePacked : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterLoop.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := true) (.local Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterLoop.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact packed.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceContinued : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.continued glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flag) (.ifElse (.bool true) (.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueItems) .brk)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.continued glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedAdapterLoop.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    _ continued glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceBreakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceContinueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flag) (.ifElse (.bool true) (.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueItems) .brk)) Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceNormalCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.normalItems)) Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 0 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterLoop.body pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (Solidity.Yul.RawCheckedAdapterLoop.run Old.readFlag body pipeline 20 (Old.initial 2 257 2 world)).1 at tags
  rw [rawBreak pipeline world] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterIfElse.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapterLoop
#print axioms Solidity.Yul.RawCheckedAdapterLoop.correct
#print axioms Solidity.Yul.RawCheckedAdapterLoop.lift_correct
#print axioms Solidity.Yul.RawCheckedAdapterLoop.loop
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.normalHeadCaptured
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.normalBodyRuns
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.constantGuard
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.clearBody
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.continuedBody
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.afterClearGuard
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.rawBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.rawContinue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.rawNormal
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.falseSkips
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.guardTimeout
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.packedBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.diverges
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.foreverRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourcePacked
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourceContinued
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourceBreakCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourceContinueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourceNormalCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.dirtyBoundary

namespace Solidity.Yul.Checks.RawCheckedAdapterLoop
theorem sourceDiverges : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env)
 (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx.tys)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env),
 ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.bool true)
     (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env []
       false ⟨true,false⟩ Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx.tys
       Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.ctx.tys)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.env,world)).1 = .error .timeout := by
  intro glob frame checked fuel nps ph locals world
  have actual := Solidity.Yul.RawCheckedAdapterLoop.correct Old.ctx [] false false false (.bool true) Old.always
    .cont repeated glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)
  have tag := congrArg Prod.fst actual.2
  simp only [RawSequence.represented,diverges,Except.map] at tag
  exact tag
end Solidity.Yul.Checks.RawCheckedAdapterLoop
#print axioms Solidity.Yul.Checks.RawCheckedAdapterLoop.sourceDiverges
