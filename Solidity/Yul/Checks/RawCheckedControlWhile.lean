import Solidity.Yul.RawCheckedControlWhile
import Solidity.Yul.Checks.RawCheckedControlSequence
import Solidity.Yul.Checks.RawCheckedIf
/-! Concrete mixed loop break/continue consumption and retained dirty words.
Kernel controls only, not admission or external compiler/EVM evidence. -/
namespace Solidity.Yul.Checks.RawCheckedControlWhile
namespace Old
export Solidity.Yul.Checks.RawCheckedControlSequence.Old (ctx env initial xCell flagCell flag assignExpr assign frame rawFlag)
export Solidity.Yul.Checks.RawCheckedControlSequence (breakItems breakProof continueItems continueProof tailItems tailProof)
export Solidity.Yul.Checks.RawCheckedIf (readFlag partialGuard)
end Old
def clearExpr : Solidity.Source.RExpr Old.env Old.ctx.tys .bool := .assign (.local Old.flag) (.bool false)
def clearHead : RawSource.Supported Old.ctx [] false ⟨true,false⟩ (.expr clearExpr) :=
 .expression (.assign Old.flag (.base (.literal false)))
def clearItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr clearExpr) .nil
def clearBlock : RawLoopBody.Supported Old.ctx [] false false (.block clearItems) :=
 .plain (.cons clearHead .nil)
def clearContinueItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.assignExpr) (.stmt (.block clearItems) (.stmt .cont Old.tailItems))
def clearContinueProof : RawCheckedControlSequence.Supported Old.ctx [] false false clearContinueItems :=
 .uint8 Old.assign (.cons clearBlock (.cons .continue_ Old.tailProof))
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false clearContinueItems) := ⟨clearContinueProof⟩
end Solidity.Yul.Checks.RawCheckedControlWhile

namespace Solidity.Yul.Checks.RawCheckedControlWhileStages
theorem guard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag 15 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.rawFlag 2) world) := by
  intro world
  rfl

theorem breakBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 15 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.rawFlag 2) world) =
 (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.rawFlag 2) world) := by
  intro pipeline world
  rfl

theorem clearBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 15 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.rawFlag 2) world) =
 (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem clearGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag 14 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) =
 (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro world
  rfl

theorem clearViews : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) Solidity.Yul.Checks.RawCheckedControlWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))).world = world := by
  intro world
  simp only [RawCoherent.capture_view,RawCoherent.prepare_view]
  exact ⟨by first | rfl | trivial,by first | rfl | trivial,by first | rfl | trivial⟩

end Solidity.Yul.Checks.RawCheckedControlWhileStages

namespace Solidity.Yul.Checks.RawCheckedControlWhile
theorem sourceBreakAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedControlWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhile.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakItems)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhile.Old.env,world) = Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlWhile.correct (l := false) Old.readFlag Old.breakProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceContinueAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedControlWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhile.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueItems)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhile.Old.env,world) = Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlWhile.correct (l := false) Old.readFlag clearContinueProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem rawBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [RawCheckedControlWhile.run,RawCheckedControlWhileStages.guard,RawCheckedControlWhileStages.breakBody]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  let next := Old.frame 257 257 (LocalValue.clean (.bool false)) world
  have actual : RawCheckedControlWhile.run Old.readFlag clearContinueProof pipeline 16 (Old.initial 2 257 2 world) =
      (.ok (),RawCoherent.capture next (RawCoherent.prepare next)) := by
    rw [RawCheckedControlWhile.run,RawCheckedControlWhileStages.guard,RawCheckedControlWhileStages.clearBody]
    change RawCheckedControlWhile.run Old.readFlag clearContinueProof pipeline 15 next = _
    rw [RawCheckedControlWhile.run.eq_def]
    dsimp only
    rw [RawCheckedControlWhileStages.clearGuard]
    rfl
  rw [actual]
  exact ⟨rfl,RawCheckedControlWhileStages.clearViews world⟩

theorem falseSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 0 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 0 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 0 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 0 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem tailWouldWrite : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.tailProof pipeline 12 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 1 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem differentControlPaths : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhile.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.flagCell).val) bad
  dsimp only at cells
  rw [(rawBreak pipeline world).2.2.1,(rawContinue pipeline world).2.2.1] at cells
  cases cells


theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world) = false := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedControlSequence.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedControlWhile
#print axioms Solidity.Yul.RawCheckedControlWhile.correct
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileStages.guard
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileStages.breakBody
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileStages.clearBody
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileStages.clearGuard
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileStages.clearViews
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.sourceBreakAll
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.sourceContinueAll
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.rawBreak
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.rawContinue
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.falseSkips
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.tailWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.differentControlPaths
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.dirtyBoundary

namespace Solidity.Yul.Checks.RawCheckedControlWhile
theorem guardWrites : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhile.Old.env),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhile.Old.breakProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Checks.RawCheckedControlWhile
#print axioms Solidity.Yul.Checks.RawCheckedControlWhile.guardWrites
