import Solidity.Yul.RawCheckedAdapterIfElse
import Solidity.Yul.Checks.RawCheckedAdapterSequence
import Solidity.Yul.Checks.RawCheckedWhile
/-! Nested checked conditionals over actual sequence/block producer inhabitants.
Selected flow and raw frames remain exact; guard errors and dirty boundaries
stay explicit. Source completion checks are separate kernel computations. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterIfElse
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterSequence.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag clean)
export Solidity.Yul.Checks.RawCheckedAdapterSequence.Old (breakProof clearContinueProof)
export Solidity.Yul.Checks.RawCheckedAdapterSequence (items normalItems)
export Solidity.Yul.Checks.RawCheckedControlWhile.Old (partialGuard)
export Solidity.Yul.Checks.RawCheckedWhile (always)
end Old
def controlBranch : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.items) :=
 Solidity.Yul.Checks.RawCheckedAdapterSequence.boxed
def normalBranch : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.normalItems) :=
 Solidity.Yul.RawCheckedAdapterSequence.block Solidity.Yul.Checks.RawCheckedAdapterSequence.normal
def stmt : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .ifElse (.local Old.flag) (.block Old.items) (.block Old.normalItems)
def outer : RawCheckedAdapter.Adapter Old.ctx [] false false stmt :=
 Solidity.Yul.RawCheckedAdapterIfElse.adapter Old.readFlag controlBranch normalBranch
def forcedStmt : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .ifElse (.bool true) (.block Old.items) (.block Old.normalItems)
def forced : RawCheckedAdapter.Adapter Old.ctx [] false false forcedStmt :=
 Solidity.Yul.RawCheckedAdapterIfElse.adapter Old.always controlBranch normalBranch
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false stmt) := ⟨outer⟩
end Solidity.Yul.Checks.RawCheckedAdapterIfElse

namespace Solidity.Yul.Checks.RawCheckedAdapterIfElse
theorem capturedNormalHead : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) =
 (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) := by
  intro pipeline world
  rfl

theorem innerGuardFalse : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.readFlag 16 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) = (.ok false,Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) := by
  intro world
  rfl

theorem innerContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem guardTrue : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.readFlag 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 2) world) := by
  intro world
  rfl

theorem guardFalse : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.readFlag 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 0 world) = (.ok false,Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) := by
  intro world
  rfl

theorem forcedGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.always 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 0 world) = (.ok true,Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) := by
  intro world
  rfl

theorem selectedTrue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 2) world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 2) world) := by
  intro pipeline world
  rfl

theorem selectedFalse : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) = (.ok (.normal),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons
    Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead
    Solidity.Yul.Checks.RawCheckedAdapterSequence.clearRest pipeline 18
    (Old.frame 2 257 (Old.rawFlag 0) world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,capturedNormalHead]
  exact Solidity.Yul.Checks.RawCheckedAdapterSequence.normalTail pipeline world

theorem selectedContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch.run pipeline 19 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 0) world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons
    Solidity.Yul.Checks.RawCheckedAdapterSequence.head
    Solidity.Yul.Checks.RawCheckedAdapterSequence.rest pipeline 18
    (Old.frame 2 257 (Old.rawFlag 0) world) = _
  have first : Solidity.Yul.Checks.RawCheckedAdapterSequence.head.run pipeline 17
      (Old.frame 2 257 (Old.rawFlag 0) world) =
      (.ok (.continue_ rfl),Old.frame 257 257 (LocalValue.clean (.bool false)) world) := by
    change RawCheckedControlIfElse.run Old.readFlag Old.breakProof Old.clearContinueProof pipeline 17
      (Old.frame 2 257 (Old.rawFlag 0) world) = _
    rw [RawCheckedControlIfElse.run,innerGuardFalse,innerContinue]
    rfl
  simp only [Solidity.Yul.RawCheckedAdapterSequence.runCons,first]

theorem trueBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.rawFlag 2) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterIfElse.run Old.readFlag controlBranch normalBranch pipeline 20
    (Old.initial 2 257 2 world) = _
  rw [Solidity.Yul.RawCheckedAdapterIfElse.run,guardTrue,selectedTrue]
  rfl

theorem falseNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 0 world) = (.ok (.normal),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterIfElse.run Old.readFlag controlBranch normalBranch pipeline 20
    (Old.initial 2 257 0 world) = _
  rw [Solidity.Yul.RawCheckedAdapterIfElse.run,guardFalse,selectedFalse]
  rfl

theorem forcedContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.forced.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 0 world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterIfElse.run Old.always controlBranch normalBranch pipeline 20
    (Old.initial 2 257 0 world) = _
  rw [Solidity.Yul.RawCheckedAdapterIfElse.run,forcedGuard,selectedContinue]
  rfl

theorem guardTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 (Solidity.Yul.RawCheckedAdapterIfElse.run Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterIfElse.run Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterIfElse.run Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedAdapterIfElse.run Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedAdapterIfElse.controlBranch Solidity.Yul.Checks.RawCheckedAdapterIfElse.normalBranch pipeline 4 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.stmt locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact outer.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceTrueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.stmt Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world) =
 (.ok (.brk Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceFalseCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.stmt Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceForcedCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 (Solidity.Source.execS glob frame 20 nps ph Solidity.Yul.Checks.RawCheckedAdapterIfElse.forcedStmt Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world) =
 (.ok (.cont Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run pipeline 0 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world) ≠ Solidity.Yul.Checks.RawCheckedAdapterIfElse.outer.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (outer.run pipeline 20 (Old.initial 2 257 2 world)).1 at tags
  rw [trueBreak pipeline world] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterIfElse.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterSequence.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapterIfElse
#print axioms Solidity.Yul.RawCheckedAdapterIfElse.correct
#print axioms Solidity.Yul.RawCheckedAdapterIfElse.adapter
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.capturedNormalHead
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.innerGuardFalse
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.innerContinue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTrue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardFalse
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.forcedGuard
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedTrue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedFalse
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.selectedContinue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.trueBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.falseNormal
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.forcedContinue
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.guardTimeout
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.sourceTrueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.sourceFalseCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.sourceForcedCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterIfElse.dirtyBoundary
