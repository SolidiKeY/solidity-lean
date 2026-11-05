import Solidity.Yul.RawCheckedControlDoWhile
import Solidity.Yul.Checks.RawCheckedControlWhile
/-! Body-first mixed control witnesses; checked/coherent Source agreement,
effectful skipped guards/tails and pipeline-sensitive timeout prefixes.
Kernel checks only, not general admission or external compiler evidence. -/
namespace Solidity.Yul.Checks.RawCheckedControlDoWhile
namespace Old
export Solidity.Yul.Checks.RawCheckedControlWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard frame rawFlag breakItems breakProof tailItems tailProof)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearContinueItems clearContinueProof)
export Solidity.Yul.Checks.RawCheckedControlSequence (partialProof)
end Old
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.clearContinueItems) := ⟨Old.clearContinueProof⟩
end Solidity.Yul.Checks.RawCheckedControlDoWhile

namespace Solidity.Yul.Checks.RawCheckedControlDoWhile
theorem bodyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 15 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world) =
 (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.rawFlag 2) world) := by
  intro pipeline world
  rfl

theorem bodyContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 15 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 flag world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline flag world
  rfl

theorem conditionAfter : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag 15 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro world
  rfl

theorem sourceBreakAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flag)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env,world) = Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlDoWhile.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.breakItems Old.breakProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceContinueAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flag)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env,world) = Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlDoWhile.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.clearContinueItems Old.clearContinueProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem rawBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [RawCheckedControlDoWhile.run,bodyBreak]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  have actual : Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
    rw [RawCheckedControlDoWhile.run,bodyContinue]
    change RawSourceAdapterDoWhile.after Old.readFlag
      (RawCheckedControlDoWhile.run Old.readFlag Old.clearContinueProof pipeline 15) 15 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = _
    rw [RawSourceAdapterDoWhile.after,conditionAfter]
    rfl
  rw [actual]
  exact ⟨rfl,Solidity.Yul.Checks.RawCheckedControlWhileStages.clearViews world⟩

theorem falseStillRuns : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 0 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 0 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 0 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 0 world)).2.world = world := by
  intro pipeline world
  have actual : Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 0 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
    rw [RawCheckedControlDoWhile.run,bodyContinue]
    change RawSourceAdapterDoWhile.after Old.readFlag
      (RawCheckedControlDoWhile.run Old.readFlag Old.clearContinueProof pipeline 15) 15 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = _
    rw [RawSourceAdapterDoWhile.after,conditionAfter]
    rfl
  rw [actual]
  exact ⟨rfl,Solidity.Yul.Checks.RawCheckedControlWhileStages.clearViews world⟩

theorem tailWouldWrite : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).1 = .ok .normal ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 1 := by
  intro pipeline world
  exact Solidity.Yul.Checks.RawCheckedControlWhile.tailWouldWrite pipeline world

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 0 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (RawCheckedControlDoWhile.run Old.partialGuard Old.breakProof pipeline 16 (Old.initial 2 257 2 world)).1 at tags
  rw [(rawBreak pipeline world).1] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 2 257 2 world) = false := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedControlWhile.dirtyBoundary world

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlDoWhile.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Checks.RawCheckedControlDoWhile
#print axioms Solidity.Yul.RawCheckedControlDoWhile.correct
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.bodyBreak
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.bodyContinue
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.conditionAfter
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.sourceBreakAll
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.sourceContinueAll
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.rawBreak
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.rawContinue
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.falseStillRuns
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.tailWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhile.viaIRPartial
