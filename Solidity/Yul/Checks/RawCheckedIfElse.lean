import Solidity.Yul.RawCheckedIfElse
import Solidity.Yul.Checks.RawCheckedIf
/-! Actual branch selection, raw words, partial prefixes and Source transport. -/
namespace Solidity.Yul.Checks.RawCheckedIfElse
namespace Old
export Solidity.Yul.Checks.RawCheckedIf (selected readFlag writeFalse partialGuard)
export Solidity.Yul.Checks.RawCheckedIf.Old (ctx initial copyProof copyItems panicProof partialProof xCell flagCell flag)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
theorem guardFalse (world : Solidity.Source.St Old.ctx.env) :
 RawCondition.eval Old.writeFalse 6 (Old.initial 2 257 2 world) =
 (.ok false,Solidity.Yul.Checks.RawCheckedIfStages.frame 2 257
   Solidity.Yul.Checks.RawCheckedIfStages.zeroFlag world) := by rfl

theorem trueCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedIfElse.run,Solidity.Yul.Checks.RawCheckedIfStages.guardCopy]
  exact Solidity.Yul.Checks.RawCheckedIfStages.copyZero pipeline world

theorem falseCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.writeFalse Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedIfElse.run,guardFalse]
  exact Solidity.Yul.Checks.RawCheckedIfStages.copyZero pipeline world

theorem dirtyTruth : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.readFlag Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedIfStages.frame 257 257 (Solidity.Yul.Checks.RawCheckedIfStages.rawFlag 0) world) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedIfElse.run,Solidity.Yul.Checks.RawCheckedIfStages.guardRead]
  exact Solidity.Yul.Checks.RawCheckedIfStages.copyRaw pipeline world

theorem earlyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem guardTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.partialGuard Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIfElse.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIfElse.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  rw [Solidity.Yul.RawCheckedIfElse.run,Solidity.Yul.Checks.RawCheckedIfStages.guardPartial]
  exact Solidity.Yul.Checks.RawCheckedIfStages.viaPrefix world

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env) (frame : Solidity.Source.Fr),
 frame.checked = true → ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env.layout Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifElse (.unary .not (.assign (.local Solidity.Yul.Checks.RawCheckedIfElse.Old.flag) (.bool false))) (.block Solidity.Yul.Checks.RawCheckedIfElse.Old.copyItems) (.block Solidity.Yul.Checks.RawCheckedIfElse.Old.copyItems)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedIfElse.Old.ctx.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElse.Old.selected Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElse.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedIfElse.correct Old.selected Old.copyProof Old.copyProof
    glob frame checked fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world)

theorem dirtyNotSource : ∀ (world : Solidity.Source.St Old.ctx.env),
 RawCoherent.coherent (Old.initial 2 257 2 world) = false := by
  intro world
  rfl

end Solidity.Yul.Checks.RawCheckedIfElse
#print axioms Solidity.Yul.RawCheckedIfElse.correct
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.guardFalse
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.trueCopy
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.falseCopy
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.dirtyTruth
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.earlyCopy
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.guardTimeout
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.viaIRPartial
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedIfElse.dirtyNotSource
