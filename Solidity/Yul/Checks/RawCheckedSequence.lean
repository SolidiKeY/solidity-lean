import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.Checks.RawU8Statement
/-! Mixed checked LOCAL composition controls. Raw partial effects and skipped
tails remain observable; certificate refusal is not frontend admission. -/
namespace Solidity.Yul.Checks.RawCheckedSequence
namespace Old
export Solidity.Yul.Checks.RawU8Statement (ctx initial xCell argCell flagCell)
export Solidity.Yul.Checks.LocalU8Representation
 (env x arg flag assignExpr assign timeoutExpr timeout sumExpr sum)
end Old
def boolExpr (b : Bool) : Solidity.Source.RExpr Old.env Old.ctx.tys .bool :=
 .assign (.local Old.flag) (.bool b)
def boolProof (b : Bool) : RawSource.Supported Old.ctx [] false ⟨false,false⟩ (.expr (boolExpr b)) :=
 .expression (.assign Old.flag (.base (.literal b)))
def copyItems : Solidity.Source.RItems Old.env [] false ⟨false,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr (boolExpr false)) (.stmt (.expr Old.assignExpr) .nil)
def copyProof : RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ copyItems :=
 .boolean (boolProof false) (.uint8 Old.assign .nil)
def partialItems : Solidity.Source.RItems Old.env [] false ⟨false,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr (boolExpr false)) (.stmt (.expr Old.timeoutExpr) .nil)
def partialProof : RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ partialItems :=
 .boolean (boolProof false) (.uint8 Old.timeout .nil)
def panicItems : Solidity.Source.RItems Old.env [] false ⟨false,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.expr Old.sumExpr) (.stmt (.expr (boolExpr true)) .nil)
def panicProof : RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ panicItems :=
 .uint8 Old.sum (.boolean (boolProof true) .nil)
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ copyItems) := ⟨copyProof⟩
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env.layout Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawCheckedSequence.copyItems locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedSequence.correct Solidity.Yul.Checks.RawCheckedSequence.Old.ctx [] false ⟨false,false⟩ Solidity.Yul.Checks.RawCheckedSequence.copyItems Solidity.Yul.Checks.RawCheckedSequence.copyProof
    glob frame checked fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world)

theorem blockAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env.layout Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedSequence.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedSequence.copyItems) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequence.Old.ctx.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedSequence.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact Solidity.Yul.RawCheckedSequence.block_correct Solidity.Yul.Checks.RawCheckedSequence.Old.ctx [] false ⟨false,false⟩ Solidity.Yul.Checks.RawCheckedSequence.copyItems Solidity.Yul.Checks.RawCheckedSequence.copyProof
    glob frame checked fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world)

theorem rawCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.argCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem earlyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .legacy 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .legacy 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .legacy 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .legacy 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .viaIR 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .viaIR 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .viaIR 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.partialProof .viaIR 7 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem panicStops : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.panicProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.panicProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.xCell).val = 511 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.panicProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequence.panicProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  have actual := Solidity.Yul.Checks.RawU8Statement.panicPrefix pipeline world
  simp only [Solidity.Yul.Checks.RawCheckedSequence.panicProof,RawCheckedSequence.run_uint8,actual.1]
  exact ⟨by decide,actual.2.1,actual.2.2.1,actual.2.2.2⟩

theorem tailWouldWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequence.Old.env), (Solidity.Yul.RawCoherent.execS (Solidity.Yul.Checks.RawCheckedSequence.boolProof true) 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS (Solidity.Yul.Checks.RawCheckedSequence.boolProof true) 4 (Solidity.Yul.Checks.RawCheckedSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedSequence.Old.flagCell).val = 1 := by
  intro world
  exact ⟨rfl,rfl⟩

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.RawCheckedSequence.Supported Solidity.Yul.Checks.RawCheckedSequence.Old.ctx [] false ⟨false,false⟩ (.stmt (.expr (.binary .sub (.local Solidity.Yul.Checks.RawCheckedSequence.Old.x) (.local Solidity.Yul.Checks.RawCheckedSequence.Old.arg))) .nil)) := by
  intro ⟨proof⟩
  cases proof with
  | boolean head tail => cases head
  | uint8 head tail => cases head

#print axioms Solidity.Yul.RawCheckedSequence.run_boolean
#print axioms Solidity.Yul.RawCheckedSequence.run_uint8
#print axioms Solidity.Yul.RawCheckedSequence.correct
#print axioms Solidity.Yul.RawCheckedSequence.block_correct
#print axioms sourceAll
#print axioms blockAll
#print axioms rawCopy
#print axioms earlyCopy
#print axioms legacyPartial
#print axioms viaIRPartial
#print axioms panicStops
#print axioms tailWouldWrite
#print axioms unsupportedSub
end Solidity.Yul.Checks.RawCheckedSequence
