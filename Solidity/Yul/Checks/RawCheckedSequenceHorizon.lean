import Solidity.Yul.RawCheckedSequenceHorizon
import Solidity.Yul.Checks.RawCheckedSequence
/-! Exact completed whole-frame and actual Source horizons, with timeout
and cross-pipeline counterexamples. Coherence refusal is not admission. -/
namespace Solidity.Yul.Checks.RawCheckedSequenceHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedSequence (copyProof copyItems panicProof partialProof)
export Solidity.Yul.Checks.RawCheckedSequence.Old (ctx initial xCell)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
theorem copyStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env) (extra : Nat), Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline (5+extra) (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) = Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawCheckedSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedSequence.rawCopy pipeline world).1]
  intro bad
  cases bad

theorem panicStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env) (extra : Nat), Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.panicProof pipeline (5+extra) (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 511 1 2 world) = Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.panicProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 511 1 2 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawCheckedSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedSequence.panicStops pipeline world).1]
  intro bad
  cases bad

theorem blockStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env) (extra : Nat), Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline (6+extra) (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) = Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply Solidity.Yul.RawCheckedSequenceHorizon.blockExtension
  change (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world)).1 ≠ .error .timeout
  rw [(Solidity.Yul.Checks.RawCheckedSequence.rawCopy pipeline world).1]
  intro bad
  cases bad

theorem earlyCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env), Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedSequence.earlyCopy pipeline world).1,
    (Solidity.Yul.Checks.RawCheckedSequence.rawCopy pipeline world).1] at tags
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env), Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.partialProof .legacy 7 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 257 2 2 world) ≠ Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.partialProof .viaIR 7 (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 257 2 2 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx =>
    (Solidity.Yul.RawFrame.view out.2 Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedSequence.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedSequence.viaIRPartial world).2.1] at cells
  cases cells

theorem sourceItemsStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env),
 (Solidity.Source.execItems glob frame (5+extra) nps ph Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env,world) =
 (Solidity.Source.execItems glob frame 5 nps ph Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env,world) := by
  intro glob frame checked extra nps ph world
  have ready : (Solidity.Yul.RawCheckedSequence.run Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof glob.pipeline 5 (Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    cases bad
  exact Solidity.Yul.RawCheckedSequenceHorizon.sourceItemsExtension Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx [] false ⟨false,false⟩
    Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof glob frame checked 5 extra nps ph
    (Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world)
    (Solidity.Yul.RawCoherent.coherent_ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world) ready

theorem sourceBlockStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env),
 (Solidity.Source.execS glob frame (6+extra) nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems) Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env,world) =
 (Solidity.Source.execS glob frame 6 nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems) Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env,world) := by
  intro glob frame checked extra nps ph world
  have ready : (Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof glob.pipeline 6 (Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    cases bad
  exact Solidity.Yul.RawCheckedSequenceHorizon.sourceBlockExtension Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx [] false ⟨false,false⟩
    Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyItems Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.copyProof glob frame checked 6 extra nps ph
    (Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world)
    (Solidity.Yul.RawCoherent.coherent_ofClean Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.clean world) ready

theorem dirtyRefusal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.initial 2 257 2 world) = false := by
  exact Solidity.Yul.Checks.RawU8Statement.dirtyRefusal

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.RawCheckedSequence.Supported Solidity.Yul.Checks.RawCheckedSequenceHorizon.Old.ctx [] false ⟨false,false⟩ (.stmt (.expr (.binary .sub (.local .here) (.local (.there .here)))) .nil)) := by
  exact Solidity.Yul.Checks.RawCheckedSequence.unsupportedSub

#print axioms Solidity.Yul.RawCheckedSequenceHorizon.successor
#print axioms Solidity.Yul.RawCheckedSequenceHorizon.extension
#print axioms Solidity.Yul.RawCheckedSequenceHorizon.blockExtension
#print axioms Solidity.Yul.RawCheckedSequenceHorizon.sourceItemsExtension
#print axioms Solidity.Yul.RawCheckedSequenceHorizon.sourceBlockExtension
#print axioms copyStable
#print axioms panicStable
#print axioms blockStable
#print axioms earlyCounterexample
#print axioms pipelineCounterexample
#print axioms sourceItemsStable
#print axioms sourceBlockStable
#print axioms dirtyRefusal
#print axioms unsupportedSub
end Solidity.Yul.Checks.RawCheckedSequenceHorizon
