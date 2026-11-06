import Solidity.Yul.RawCheckedWhile
import Solidity.Yul.Checks.RawCheckedIfElse
/-! Mixed terminating loops, divergent horizons and retained dirty prefixes.
These are kernel controls, not solc admission or external EVM evidence. -/
namespace Solidity.Yul.Checks.RawCheckedWhile
namespace Old
export Solidity.Yul.Checks.RawCheckedSequence.Old
 (ctx env initial xCell argCell flagCell flag assignExpr assign timeoutExpr timeout)
export Solidity.Yul.Checks.RawCheckedIf (readFlag partialGuard)
end Old
def boolExpr : Solidity.Source.RExpr Old.env Old.ctx.tys .bool :=
 .assign (.local Old.flag) (.bool false)
def boolProof : RawSource.Supported Old.ctx [] false ⟨true,false⟩ (.expr boolExpr) :=
 .expression (.assign Old.flag (.base (.literal false)))
def copyItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr boolExpr) (.stmt (.expr Old.assignExpr) .nil)
def copyProof : RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ copyItems :=
 .boolean boolProof (.uint8 Old.assign .nil)
def partialItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr boolExpr) (.stmt (.expr Old.timeoutExpr) .nil)
def partialProof : RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ partialItems :=
 .boolean boolProof (.uint8 Old.timeout .nil)
def always : LocalBoolControl.Supported Old.env Old.ctx.tys (.bool true) := .base (.literal true)
def emptyProof : RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ .nil := .nil
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ copyItems) := ⟨copyProof⟩
theorem guardNext : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedWhile.Old.ctx),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedWhile.always (fuel+1) state = (.ok true,Solidity.Yul.RawCoherent.capture state (Solidity.Yul.RawCoherent.prepare state)) := by
  intro fuel state
  rfl

theorem emptyNext : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedWhile.Old.ctx),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedWhile.emptyProof pipeline (fuel+2) state = (.ok (),state) := by
  intro pipeline fuel state
  rfl




theorem falseSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof pipeline 2 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 511 1 0 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof pipeline 2 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 511 1 0 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 511 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof pipeline 2 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 511 1 0 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof pipeline 2 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 511 1 0 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem guardWrites : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩



theorem diverges : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedWhile.Old.ctx),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.always Solidity.Yul.Checks.RawCheckedWhile.emptyProof pipeline fuel state).1 = .error .timeout := by
  intro pipeline fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [RawCheckedWhile.run,guardNext]
      simp only [if_true]
      cases fuel with
      | zero => rfl
      | succ n =>
        rw [emptyNext]
        exact ih _

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world) = false := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedIfElse.dirtyNotSource world

end Solidity.Yul.Checks.RawCheckedWhile
#print axioms Solidity.Yul.RawCheckedWhile.correct
#print axioms Solidity.Yul.Checks.RawCheckedWhile.guardNext
#print axioms Solidity.Yul.Checks.RawCheckedWhile.emptyNext
#print axioms Solidity.Yul.Checks.RawCheckedWhile.falseSkips
#print axioms Solidity.Yul.Checks.RawCheckedWhile.guardWrites
#print axioms Solidity.Yul.Checks.RawCheckedWhile.diverges
#print axioms Solidity.Yul.Checks.RawCheckedWhile.dirtyBoundary

namespace Solidity.Yul.Checks.RawCheckedWhileStages
theorem guardEarly : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag 5 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedIfStages.frame 2 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) := by
  intro world
  rfl
theorem bodyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfStages.frame 2 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro pipeline world
  rfl
theorem bodyEarly : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedIfStages.frame 2 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedIfStages.frame 2 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro pipeline world
  rfl
theorem bodyLegacy : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedWhile.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 2 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedIfStages.frame 257 2 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro world
  rfl
theorem bodyVia : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedWhile.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 2 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedIfStages.frame 2 2 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro world
  rfl
theorem guardPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag 8 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world) = (.ok true,Solidity.Yul.Checks.RawCheckedIfStages.frame 257 2 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 2) world) := by
  intro world
  rfl
theorem guardAfter : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag 5 (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) =
 (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world))) := by
  intro world
  rfl
end Solidity.Yul.Checks.RawCheckedWhileStages

namespace Solidity.Yul.Checks.RawCheckedWhile
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedWhile.Old.flag) (.block Solidity.Yul.Checks.RawCheckedWhile.copyItems)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhile.Old.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedWhile.correct (l := false) Old.readFlag copyProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)


theorem earlyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [RawCheckedWhile.run,RawCheckedWhileStages.guardEarly,RawCheckedWhileStages.bodyEarly]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  rw [RawCheckedWhile.run,RawCheckedWhileStages.guardPartial,RawCheckedWhileStages.bodyLegacy]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  rw [RawCheckedWhile.run,RawCheckedWhileStages.guardPartial,RawCheckedWhileStages.bodyVia]
  exact ⟨rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Checks.RawCheckedWhile
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.guardEarly
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.bodyCopy
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.bodyEarly
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.bodyLegacy
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.bodyVia
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.guardPartial
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.guardAfter
#print axioms Solidity.Yul.Checks.RawCheckedWhile.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedWhile.earlyCopy
#print axioms Solidity.Yul.Checks.RawCheckedWhile.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedWhile.viaIRPartial

namespace Solidity.Yul.Checks.RawCheckedWhileStages
theorem finalViews : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world))) Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world))) Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world))).world = world := by
  intro world
  simp only [RawCoherent.capture_view,RawCoherent.prepare_view]
  exact ⟨by first | rfl | trivial,by first | rfl | trivial,by first | rfl | trivial⟩
end Solidity.Yul.Checks.RawCheckedWhileStages
namespace Solidity.Yul.Checks.RawCheckedWhile
theorem rawCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedWhile.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  let next := Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257
    (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world
  have outcome : RawCheckedWhile.run Old.readFlag copyProof pipeline 7 (Old.initial 2 257 2 world) =
      (.ok (),RawCoherent.capture next (RawCoherent.prepare next)) := by
    rw [RawCheckedWhile.run,Solidity.Yul.Checks.RawCheckedIfStages.guardRead,
      RawCheckedWhileStages.bodyCopy]
    change RawCheckedWhile.run Old.readFlag copyProof pipeline 6 next = _
    rw [RawCheckedWhile.run.eq_def]
    dsimp only
    rw [RawCheckedWhileStages.guardAfter]
    rfl
  rw [outcome]
  exact ⟨rfl,RawCheckedWhileStages.finalViews world⟩

end Solidity.Yul.Checks.RawCheckedWhile
#print axioms Solidity.Yul.Checks.RawCheckedWhileStages.finalViews
#print axioms Solidity.Yul.Checks.RawCheckedWhile.rawCopy

namespace Solidity.Yul.Checks.RawCheckedWhile
theorem sourceDiverges : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedWhile.Old.env) (frame : Solidity.Source.Fr),
 frame.checked = true → ∀ (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedWhile.Old.ctx.tys)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhile.Old.env),
 ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.bool true) (.block (Solidity.Source.RItems.nil : Solidity.Source.RItems Solidity.Yul.Checks.RawCheckedWhile.Old.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawCheckedWhile.Old.ctx.tys Solidity.Yul.Checks.RawCheckedWhile.Old.ctx.tys))) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhile.Old.env,world)).1 = .error .timeout := by
  intro glob frame checked fuel nps ph locals world
  have actual := RawCheckedWhile.correct (l := false) always emptyProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)
  have result : (RawSequence.represented (RawCheckedWhile.run always emptyProof glob.pipeline fuel
      (RawFrame.ofClean locals world))).1 = .error .timeout := by
    simp only [RawSequence.represented,diverges,Except.map]
  exact (congrArg Prod.fst actual.2).trans result
end Solidity.Yul.Checks.RawCheckedWhile
#print axioms Solidity.Yul.Checks.RawCheckedWhile.sourceDiverges
