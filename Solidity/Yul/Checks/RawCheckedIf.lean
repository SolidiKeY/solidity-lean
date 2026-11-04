import Solidity.Yul.RawCheckedIf
import Solidity.Yul.Checks.RawCheckedSequence
namespace Solidity.Yul.Checks.RawCheckedIf
namespace Old
export Solidity.Yul.Checks.RawCheckedSequence (copyProof copyItems partialProof panicProof)
export Solidity.Yul.Checks.RawCheckedSequence.Old (ctx initial xCell argCell flagCell flag)
end Old
def writeFalse : LocalBoolControl.Supported Old.ctx.env Old.ctx.tys
 (.assign (.local Old.flag) (.bool false)) := .assign Old.flag (.base (.literal false))
def selected : LocalBoolControl.Supported Old.ctx.env Old.ctx.tys
 (.unary .not (.assign (.local Old.flag) (.bool false))) := .not writeFalse
def readFlag : LocalBoolControl.Supported Old.ctx.env Old.ctx.tys (.local Old.flag) := .base (.local Old.flag)
def partialGuard : LocalBoolControl.Supported Old.ctx.env Old.ctx.tys
 (.binary .or (.assign (.local Old.flag) (.bool false))
   (.unary .not (.unary .not (.local Old.flag)))) := .or writeFalse (.not (.not readFlag))
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
end Solidity.Yul.Checks.RawCheckedIf

namespace Solidity.Yul.Checks.RawCheckedIfStages
open Solidity.Yul.Checks.RawCheckedIf
def frame (a b : Nat) (flag : LocalValue Old.ctx.env .bool)
 (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.ctx :=
 RawCoherent.capture (Old.initial a b 2 world)
   ((Solidity.Yul.Checks.LocalU8Representation.raw8 a,
     (Solidity.Yul.Checks.LocalU8Representation.raw8 b,(flag,()))),world)
def zeroFlag : LocalValue Old.ctx.env .bool := .clean (.bool false)
def rawFlag (n : Nat) : LocalValue Old.ctx.env .bool := .scalar (LocalOperations.boolShape Old.ctx.env) (word n)
theorem guardCopy (world : Solidity.Source.St Old.ctx.env) :
 RawCondition.eval selected 6 (Old.initial 2 257 2 world) = (.ok true,frame 2 257 zeroFlag world) := by rfl
theorem guardRead (world : Solidity.Source.St Old.ctx.env) :
 RawCondition.eval readFlag 6 (Old.initial 2 257 2 world) = (.ok true,frame 2 257 (rawFlag 2) world) := by rfl
theorem guardPartial (world : Solidity.Source.St Old.ctx.env) :
 RawCondition.eval selected 8 (Old.initial 257 2 2 world) = (.ok true,frame 257 2 zeroFlag world) := by rfl
theorem copyZero (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) :
 RawCheckedSequence.block Old.copyProof pipeline 6 (frame 2 257 zeroFlag world) =
 (.ok (),frame 257 257 (rawFlag 0) world) := by rfl
theorem copyRaw (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) :
 RawCheckedSequence.block Old.copyProof pipeline 6 (frame 2 257 (rawFlag 2) world) =
 (.ok (),frame 257 257 (rawFlag 0) world) := by rfl
theorem viaPrefix (world : Solidity.Source.St Old.ctx.env) :
 (RawCheckedSequence.block Old.partialProof .viaIR 8 (frame 257 2 zeroFlag world)).1 = .error .timeout ∧
 (RawFrame.view (RawCheckedSequence.block Old.partialProof .viaIR 8 (frame 257 2 zeroFlag world)).2 Old.xCell).val = 2 ∧
 (RawFrame.view (RawCheckedSequence.block Old.partialProof .viaIR 8 (frame 257 2 zeroFlag world)).2 Old.flagCell).val = 0 ∧
 (RawCheckedSequence.block Old.partialProof .viaIR 8 (frame 257 2 zeroFlag world)).2.world = world := by
 exact ⟨rfl,rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawCheckedIfStages

namespace Solidity.Yul.Checks.RawCheckedIf
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env.layout Solidity.Yul.Checks.RawCheckedIf.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifThen (.unary .not (.assign (.local Solidity.Yul.Checks.RawCheckedIf.Old.flag) (.bool false))) (.block Solidity.Yul.Checks.RawCheckedIf.Old.copyItems)) locals).run
     (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedIf.correct Solidity.Yul.Checks.RawCheckedIf.Old.ctx [] false ⟨false,false⟩ _ Solidity.Yul.Checks.RawCheckedIf.Old.copyItems Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof
    glob frame checked fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world)

theorem selectedCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.argCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  have outcome : RawCheckedIf.run selected Old.copyProof pipeline 7 (Old.initial 2 257 2 world) =
    (.ok (),RawCheckedIfStages.frame 257 257 (RawCheckedIfStages.rawFlag 0) world) := by
    rw [RawCheckedIf.run,RawCheckedIfStages.guardCopy]
    exact RawCheckedIfStages.copyZero pipeline world
  rw [outcome]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem earlyBody : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem guardPartial : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.partialGuard Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.partialGuard Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.partialGuard Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.partialGuard Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem skipFalse : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.writeFalse Solidity.Yul.Checks.RawCheckedIf.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 511 1 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.writeFalse Solidity.Yul.Checks.RawCheckedIf.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 511 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.writeFalse Solidity.Yul.Checks.RawCheckedIf.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.writeFalse Solidity.Yul.Checks.RawCheckedIf.Old.panicProof pipeline 4 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem nonzeroTruth : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.readFlag Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.readFlag Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.readFlag Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.readFlag Solidity.Yul.Checks.RawCheckedIf.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  have outcome : RawCheckedIf.run readFlag Old.copyProof pipeline 7 (Old.initial 2 257 2 world) =
    (.ok (),RawCheckedIfStages.frame 257 257 (RawCheckedIfStages.rawFlag 0) world) := by
    rw [RawCheckedIf.run,RawCheckedIfStages.guardRead]
    exact RawCheckedIfStages.copyRaw pipeline world
  rw [outcome]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem unselectedBudget : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedIf.Old.panicProof pipeline 3 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 511 1 2 world)).1 = .error .timeout := by
  intro pipeline world
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIf.Old.ctx.env), (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedIf.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedIf.run Solidity.Yul.Checks.RawCheckedIf.selected Solidity.Yul.Checks.RawCheckedIf.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIf.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  have outcome : RawCheckedIf.run selected Old.partialProof .viaIR 9 (Old.initial 257 2 2 world) =
    RawCheckedSequence.block Old.partialProof .viaIR 8 (RawCheckedIfStages.frame 257 2 RawCheckedIfStages.zeroFlag world) := by
    rw [RawCheckedIf.run,RawCheckedIfStages.guardPartial]
    rfl
  rw [outcome]
  exact RawCheckedIfStages.viaPrefix world

#print axioms Solidity.Yul.RawCheckedIf.correct
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.guardCopy
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.guardRead
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.guardPartial
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.copyZero
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.copyRaw
#print axioms Solidity.Yul.Checks.RawCheckedIfStages.viaPrefix
#print axioms sourceAll
#print axioms selectedCopy
#print axioms earlyBody
#print axioms guardPartial
#print axioms skipFalse
#print axioms nonzeroTruth
#print axioms unselectedBudget
#print axioms legacyPartial
#print axioms viaIRPartial
end Solidity.Yul.Checks.RawCheckedIf
