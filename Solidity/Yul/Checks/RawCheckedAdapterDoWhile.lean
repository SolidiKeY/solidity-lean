import Solidity.Yul.RawCheckedAdapterDoWhile
import Solidity.Yul.Checks.RawCheckedAdapterLoop
/-! Concrete nested body-first checked producers, effectful skipped guards,
normal/continue postbody tests, all-fuel divergence and Source observations.
Kernel evidence only; no general admission or compiler adequacy claim. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterDoWhile
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterLoop.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag clean partialGuard always guardNext)
export Solidity.Yul.Checks.RawCheckedAdapterLoop (body normalBody continued repeated)
end Old
def packed : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.doWhile (l := true) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)
   (.binary .or (.assign (.local Old.flag) (.bool false)) (.unary .not (.unary .not (.local Old.flag))))) :=
 Solidity.Yul.RawCheckedAdapterDoWhile.adapter Old.partialGuard Old.body
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.doWhile (l := true) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)
   (.binary .or (.assign (.local Old.flag) (.bool false)) (.unary .not (.unary .not (.local Old.flag)))))) := ⟨packed⟩
end Solidity.Yul.Checks.RawCheckedAdapterDoWhile

namespace Solidity.Yul.Checks.RawCheckedAdapterDoWhile
theorem alwaysFirst : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.always 18 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 2) world) := by
  intro world
  rfl

theorem continuedFirst : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.continued.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change RawCheckedAdapterIfElse.run Old.always
    (Solidity.Yul.RawCheckedAdapter.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueProof)
    Solidity.Yul.Checks.RawCheckedAdapter.pureBreak pipeline 19 (Old.initial 2 257 2 world) = _
  rw [RawCheckedAdapterIfElse.run,alwaysFirst]
  change RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueProof pipeline 18
    (Old.frame 2 257 (Old.rawFlag 2) world) = _
  exact Solidity.Yul.Checks.RawCheckedAdapterLoop.clearBody pipeline world

theorem normalHeadFirst : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 flag world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) := by
  intro pipeline flag world
  rfl

theorem normalTailFirst : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.clearRest.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem normalFirst : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody.run pipeline 18 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 flag world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline flag world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons
    Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead
    Solidity.Yul.Checks.RawCheckedAdapterSequence.clearRest pipeline 17
    (Old.initial 2 257 flag world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,normalHeadFirst]
  exact normalTailFirst pipeline world

theorem postGuard : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag (fuel+1) (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro fuel world
  rfl

theorem rawBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.body pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 2) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterDoWhile.run Old.partialGuard
    Solidity.Yul.Checks.RawCheckedAdapterSequence.boxed pipeline 19 (Old.initial 2 257 2 world) = _
  simp only [Solidity.Yul.RawCheckedAdapterDoWhile.run,
    Solidity.Yul.Checks.RawCheckedAdapterSequence.blockBreak]


theorem rawContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.continued pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterDoWhile.run,continuedFirst]
  change RawSourceAdapterDoWhile.after Old.readFlag
    (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.readFlag Old.continued pipeline 19) 19
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world) = _
  rw [RawSourceAdapterDoWhile.after,postGuard]
  rfl

theorem rawNormalFalse : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 0 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterDoWhile.run,normalFirst]
  change RawSourceAdapterDoWhile.after Old.readFlag
    (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.readFlag Old.normalBody pipeline 18) 18
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world) = _
  rw [RawSourceAdapterDoWhile.after,postGuard]
  rfl

theorem rawNormalTrue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterDoWhile.run,normalFirst]
  change RawSourceAdapterDoWhile.after Old.readFlag
    (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.readFlag Old.normalBody pipeline 18) 18
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world) = _
  rw [RawSourceAdapterDoWhile.after,postGuard]
  rfl

theorem whileFalse : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 0 world) = (.ok (),Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 0) world) := by
  intro pipeline world
  rfl

theorem orderDistinguishes : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 0 world) ≠ Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.normalBody pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 0 world) := by
  intro pipeline world bad
  rw [rawNormalFalse pipeline world,whileFalse pipeline world] at bad
  have view := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  change (RawFrame.view (RawCoherent.capture
    (Old.frame 257 257 (LocalValue.clean (.bool false)) world)
    (RawCoherent.prepare (Old.frame 257 257 (LocalValue.clean (.bool false)) world))) Old.xCell).val = 2 at view
  rw [(Solidity.Yul.Checks.RawCheckedControlWhileStages.clearViews world).1] at view
  cases view

theorem guardWouldWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.partialGuard 18 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 2) world)).1 = .ok false ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.partialGuard 18 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 2) world)).2 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flagCell).val = 0 := by
  intro world
  exact ⟨rfl,rfl⟩

theorem packedBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.packed.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.rawFlag 2) world) := by
  intro pipeline world
  change ((Solidity.Yul.RawCheckedAdapterDoWhile.run Old.partialGuard Old.body pipeline 19 (Old.initial 2 257 2 world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.partialGuard Old.body pipeline 19 (Old.initial 2 257 2 world)).2) = _
  rw [rawBreak]
  rfl

theorem diverges : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx),
 (Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.always Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.repeated pipeline fuel state).1 = .error .timeout := by
  intro pipeline fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    cases fuel with
    | zero => rfl
    | succ n =>
      rw [Solidity.Yul.RawCheckedAdapterDoWhile.run]
      change (RawSourceAdapterDoWhile.after Old.always
        (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.always Old.repeated pipeline (n+1)) (n+1) state).1 = .error .timeout
      rw [RawSourceAdapterDoWhile.after,Old.guardNext]
      exact ih _

theorem foreverRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx),
 (Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.always Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.repeated pipeline fuel state).1 ≠ .error .timeout → False := by
  intro pipeline fuel state terminal
  exact terminal (diverges pipeline fuel state)

theorem sourcePacked : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := true) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items) (.binary .or (.assign (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag) (.bool false)) (.unary .not (.unary .not (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag))))) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact packed.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceContinued : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.continued glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.ifElse (.bool true) (.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueItems) .brk) (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.continued glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedAdapterDoWhile.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    _ Old.continued glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceBreakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 (Solidity.Source.execS glob frame 19 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items) (.binary .or (.assign (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag) (.bool false)) (.unary .not (.unary .not (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag))))) Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceContinueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.ifElse (.bool true) (.block Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.clearContinueItems) .brk) (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag)) Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceFalseCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 (Solidity.Source.execS glob frame 19 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.normalItems) (.local Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.flag)) Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceDiverges : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false)
     (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx.tys Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.ctx.tys)
     (.bool true)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env,world)).1 = .error .timeout := by
  intro glob frame checked fuel nps ph locals world
  have actual := Solidity.Yul.RawCheckedAdapterDoWhile.correct Old.ctx [] false false false (.bool true) Old.always
    .cont Old.repeated glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)
  have tag := congrArg Prod.fst actual.2
  simp only [RawSequence.represented,diverges,Except.map] at tag
  exact tag

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.body pipeline 0 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedAdapterDoWhile.run Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.body pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (Solidity.Yul.RawCheckedAdapterDoWhile.run Old.partialGuard Old.body pipeline 19 (Old.initial 2 257 2 world)).1 at tags
  rw [rawBreak pipeline world] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterDoWhile.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterLoop.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapterDoWhile
#print axioms Solidity.Yul.RawCheckedAdapterDoWhile.correct
#print axioms Solidity.Yul.RawCheckedAdapterDoWhile.lift_correct
#print axioms Solidity.Yul.RawCheckedAdapterDoWhile.adapter
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.alwaysFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.continuedFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.normalHeadFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.normalTailFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.normalFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.postGuard
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.rawBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.rawContinue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.rawNormalFalse
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.rawNormalTrue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.whileFalse
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.orderDistinguishes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.guardWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.packedBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.diverges
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.foreverRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourcePacked
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourceContinued
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourceBreakCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourceContinueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourceFalseCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.sourceDiverges
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterDoWhile.dirtyBoundary
