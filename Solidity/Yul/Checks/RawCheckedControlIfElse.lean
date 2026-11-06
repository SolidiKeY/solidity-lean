import Solidity.Yul.RawCheckedControlIfElse
import Solidity.Yul.Checks.RawCheckedControlWhileHorizon
import Solidity.Yul.Checks.RawCheckedControlSequence
/-! Actual normal/break/continue selection, effectful unselected tails,
dirty words, guard prefixes and checked/coherent Source observations.
Kernel witnesses only; no general admission or external compiler claim. -/
namespace Solidity.Yul.Checks.RawCheckedControlIfElse
namespace Old
export Solidity.Yul.Checks.RawCheckedControlWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard frame rawFlag breakItems breakProof)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearContinueItems clearContinueProof)
export Solidity.Yul.Checks.RawCheckedControlSequence (normalProof partialProof tailProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def cleanFalse : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 1 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def witness :
 Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.breakItems) ∧
 Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.clearContinueItems) :=
 ⟨⟨Old.breakProof⟩,⟨Old.clearContinueProof⟩⟩
end Solidity.Yul.Checks.RawCheckedControlIfElse

namespace Solidity.Yul.Checks.RawCheckedControlIfElse
theorem falseGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag 15 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 0 world) = (.ok false,Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.rawFlag 0) world) := by
  intro world
  rfl

theorem falseBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 15 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.rawFlag 0) world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem trueBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world) =
 (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.rawFlag 2) world) := by
  intro pipeline world
  rw [RawCheckedControlIfElse.run,Solidity.Yul.Checks.RawCheckedControlWhileStages.guard,
    Solidity.Yul.Checks.RawCheckedControlWhileStages.breakBody]
  rfl

theorem falseContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 0 world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rw [RawCheckedControlIfElse.run,falseGuard,falseBody]
  rfl

theorem reverseTrue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rw [RawCheckedControlIfElse.run,Solidity.Yul.Checks.RawCheckedControlWhileStages.guard,
    Solidity.Yul.Checks.RawCheckedControlWhileStages.clearBody]
  rfl

theorem normalSelected : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.normalProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.normalProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.normalProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.normalProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem guardTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem tailWouldWrite : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flagCell).val = 1 := by
  intro pipeline world
  exact Solidity.Yul.Checks.RawCheckedControlWhile.tailWouldWrite pipeline world

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env.layout Solidity.Yul.Checks.RawCheckedControlIfElse.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifElse (.local Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakItems) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueItems)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedControlIfElse.run Solidity.Yul.Checks.RawCheckedControlIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakProof Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlIfElse.correct Old.ctx [] false false (.local Old.flag) Old.readFlag
    Old.breakItems Old.clearContinueItems Old.breakProof Old.clearContinueProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceTrueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.ifElse (.local Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakItems) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueItems)) Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env,world) =
 (.ok (.brk Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceFalseCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.ifElse (.local Solidity.Yul.Checks.RawCheckedControlIfElse.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.breakItems) (.block Solidity.Yul.Checks.RawCheckedControlIfElse.Old.clearContinueItems)) Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env,world) =
 (.ok (.cont Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlIfElse.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlIfElse.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedControlWhile.dirtyBoundary world]
  intro bad
  cases bad

end Solidity.Yul.Checks.RawCheckedControlIfElse
#print axioms Solidity.Yul.RawCheckedControlIfElse.correct
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.falseGuard
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.falseBody
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.trueBreak
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.falseContinue
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.reverseTrue
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.normalSelected
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.guardTimeout
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.tailWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.viaIRPartial
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.sourceTrueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.sourceFalseCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlIfElse.dirtyBoundary
