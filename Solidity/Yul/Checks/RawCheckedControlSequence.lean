import Solidity.Yul.RawCheckedControlSequence
import Solidity.Yul.RawU8Horizon
import Solidity.Yul.Checks.RawCheckedSequence
import Solidity.Yul.Checks.RawCheckedIf
/-! Mixed dirty-word/control witnesses; skipped tails remain observable.
Certificate refusal is not frontend admission or external EVM evidence. -/
namespace Solidity.Yul.Checks.RawCheckedControlSequence
namespace Old
export Solidity.Yul.Checks.RawCheckedSequence.Old (ctx env initial xCell flagCell x arg flag assignExpr assign sumExpr sum timeoutExpr timeout)
export Solidity.Yul.Checks.RawCheckedIfStages (frame rawFlag)
end Old
def boolExpr : Solidity.Source.RExpr Old.env Old.ctx.tys .bool := .assign (.local Old.flag) (.bool true)
def boolHead : RawSource.Supported Old.ctx [] false ⟨true,false⟩ (.expr boolExpr) :=
 .expression (.assign Old.flag (.base (.literal true)))
def boolItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr boolExpr) .nil
def boolBlock : RawLoopBody.Supported Old.ctx [] false false (.block boolItems) :=
 .plain (.cons boolHead .nil)
def tailItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.block boolItems) .nil
def tailProof : RawCheckedControlSequence.Supported Old.ctx [] false false tailItems :=
 .cons boolBlock .nil
def breakItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.assignExpr) (.stmt .brk tailItems)
def breakProof : RawCheckedControlSequence.Supported Old.ctx [] false false breakItems :=
 .uint8 Old.assign (.cons .break_ tailProof)
def continueItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.assignExpr) (.stmt .cont tailItems)
def continueProof : RawCheckedControlSequence.Supported Old.ctx [] false false continueItems :=
 .uint8 Old.assign (.cons .continue_ tailProof)
def normalItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.assignExpr) tailItems
def normalProof : RawCheckedControlSequence.Supported Old.ctx [] false false normalItems :=
 .uint8 Old.assign tailProof
def skipCopyItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt .brk (.stmt (.expr Old.assignExpr) .nil)
def skipCopyProof : RawCheckedControlSequence.Supported Old.ctx [] false false skipCopyItems :=
 .cons .break_ (.uint8 Old.assign .nil)
def panicItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.sumExpr) (.stmt .brk .nil)
def panicProof : RawCheckedControlSequence.Supported Old.ctx [] false false panicItems :=
 .uint8 Old.sum (.cons .break_ .nil)
def partialItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.timeoutExpr) (.stmt .brk .nil)
def partialProof : RawCheckedControlSequence.Supported Old.ctx [] false false partialItems :=
 .uint8 Old.timeout (.cons .break_ .nil)
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false breakItems) := ⟨breakProof⟩
end Solidity.Yul.Checks.RawCheckedControlSequence

namespace Solidity.Yul.Checks.RawCheckedControlSequenceStages
theorem copyHead : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawCheckedControlSequence.Old.assign pipeline 7 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedControlSequence.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.rawFlag 2) world) := by
  intro pipeline world
  rfl
theorem normalTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.tailProof pipeline 7 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.rawFlag 2) world) =
 (.ok .normal,Solidity.Yul.Checks.RawCheckedControlSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) := by
  intro pipeline world
  rfl
end Solidity.Yul.Checks.RawCheckedControlSequenceStages

namespace Solidity.Yul.Checks.RawCheckedControlSequence
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequence.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlSequence.Old.env.layout Solidity.Yul.Checks.RawCheckedControlSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawCheckedControlSequence.breakItems locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequence.Old.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlSequence.correct Old.ctx [] false false breakItems breakProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem blockAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequence.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedControlSequence.Old.env.layout Solidity.Yul.Checks.RawCheckedControlSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlSequence.continueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedControlSequence.continueItems) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequence.Old.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlSequence.continueProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedControlSequence.block_correct continueProof glob frame checked fuel nps ph
    (RawFrame.ofClean locals world) (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem rawBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.breakProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [breakProof,RawCheckedControlSequence.run_uint8,RawCheckedControlSequenceStages.copyHead]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawContinue : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.continueProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).1 = .ok (.continue_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.continueProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.continueProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.continueProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  rw [continueProof,RawCheckedControlSequence.run_uint8,RawCheckedControlSequenceStages.copyHead]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem skipCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.skipCopyProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.skipCopyProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.skipCopyProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.skipCopyProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem normalRuns : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.normalProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.normalProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.normalProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.normalProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  have actual : RawCheckedControlSequence.run normalProof pipeline 8 (Old.initial 2 257 2 world) =
      RawCheckedControlSequence.run tailProof pipeline 7 (Old.frame 257 257 (Old.rawFlag 2) world) := by
    simp only [normalProof,RawCheckedControlSequence.run_uint8,RawCheckedControlSequenceStages.copyHead]
  rw [actual,RawCheckedControlSequenceStages.normalTail]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem tailWouldWrite : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.tailProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.tailProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 1 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem panicStops : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 511 1 2 world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 511 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 2 ∧
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  have facts := Solidity.Yul.Checks.RawU8Statement.panicPrefix pipeline world
  have ready : (RawU8Statement.run Old.sum pipeline 4 (Old.initial 511 1 2 world)).1 ≠ .error .timeout := by
    rw [facts.1]
    intro bad
    cases bad
  have stable := RawU8Horizon.extension Old.ctx Old.sumExpr Old.sum pipeline 4 1 (Old.initial 511 1 2 world) ready
  simp only [panicProof,RawCheckedControlSequence.run_uint8,stable,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .legacy 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .legacy 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .legacy 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .legacy 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  have facts := Solidity.Yul.Checks.RawU8Statement.legacyPartial world
  simp only [partialProof,RawCheckedControlSequence.run_uint8,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .viaIR 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .viaIR 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .viaIR 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedControlSequence.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequence.partialProof .viaIR 6 (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  have facts := Solidity.Yul.Checks.RawU8Statement.viaIRPartial world
  simp only [partialProof,RawCheckedControlSequence.run_uint8,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.RawCheckedControlSequence.Supported Solidity.Yul.Checks.RawCheckedControlSequence.Old.ctx [] false false
 (.stmt (.expr (.binary .sub (.local Solidity.Yul.Checks.RawCheckedControlSequence.Old.x) (.local Solidity.Yul.Checks.RawCheckedControlSequence.Old.arg))) .nil)) := by
  intro ⟨proof⟩
  cases proof with
  | cons head tail => cases head
  | uint8 head tail => cases head

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlSequence.Old.initial 2 257 2 world) = false := by
  intro world
  exact Solidity.Yul.Checks.RawU8Statement.dirtyRefusal world

end Solidity.Yul.Checks.RawCheckedControlSequence
#print axioms Solidity.Yul.RawCheckedControlSequence.run_cons
#print axioms Solidity.Yul.RawCheckedControlSequence.run_uint8
#print axioms Solidity.Yul.RawCheckedControlSequence.correct
#print axioms Solidity.Yul.RawCheckedControlSequence.block_correct
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceStages.copyHead
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceStages.normalTail
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.blockAll
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.rawBreak
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.rawContinue
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.skipCopy
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.normalRuns
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.tailWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.panicStops
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.viaIRPartial
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.unsupportedSub
#print axioms Solidity.Yul.Checks.RawCheckedControlSequence.dirtyBoundary
