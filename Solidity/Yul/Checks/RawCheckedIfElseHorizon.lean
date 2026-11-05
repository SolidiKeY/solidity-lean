import Solidity.Yul.RawCheckedIfElseHorizon
import Solidity.Yul.Checks.RawCheckedIfElse
/-! Completed whole-frame horizons, actual clean Source transport, and
timeout/pipeline/coherence boundary controls for concrete mixed branches. -/
namespace Solidity.Yul.Checks.RawCheckedIfElseHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedIfElse.Old (ctx initial copyProof copyItems panicProof partialProof selected writeFalse readFlag xCell flag)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
theorem trueStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env) (extra : Nat),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedIfElseHorizon.extension
  rw [Solidity.Yul.Checks.RawCheckedIfElse.trueCopy pipeline world]
  intro bad
  cases bad

theorem falseStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env) (extra : Nat),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.writeFalse Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.writeFalse Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedIfElseHorizon.extension
  rw [Solidity.Yul.Checks.RawCheckedIfElse.falseCopy pipeline world]
  intro bad
  cases bad

theorem dirtyTruthStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env) (extra : Nat),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedIfElseHorizon.extension
  rw [Solidity.Yul.Checks.RawCheckedIfElse.dirtyTruth pipeline world]
  intro bad
  cases bad

theorem earlyCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.panicProof pipeline 7 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedIfElse.earlyCopy pipeline world).1,
    Solidity.Yul.Checks.RawCheckedIfElse.trueCopy pipeline world] at tags
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env),
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof .legacy 9 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 257 2 2 world) ≠
 Solidity.Yul.RawCheckedIfElse.run Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.selected Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.partialProof Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 257 2 2 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedIfElse.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedIfElse.viaIRPartial world).2.1] at cells
  cases cells

theorem cleanSourceStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env) (frame : Solidity.Source.Fr),
 frame.checked = true → ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env),
 (Solidity.Source.execS glob frame (7+extra) nps ph
   (Solidity.Source.RStmt.ifElse (.unary .not (.assign (.local Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.flag) (.bool false))) (.block Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyItems) (.block Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyItems)) Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env,world) =
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.ifElse (.unary .not (.assign (.local Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.flag) (.bool false))) (.block Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyItems) (.block Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.copyItems)) Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env,world) := by
  intro glob frame checked extra nps ph world
  have ready : (RawCheckedIfElse.run Old.selected Old.copyProof Old.copyProof glob.pipeline 7
    (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    cases bad
  exact RawCheckedIfElseHorizon.sourceExtension Old.ctx [] false ⟨false,false⟩ _
    Old.copyItems Old.copyItems Old.selected Old.copyProof Old.copyProof glob frame checked 7 extra nps ph
    (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world) ready

theorem dirtySourceBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedIfElseHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedIfElse.dirtyNotSource world]
  intro bad
  cases bad

end Solidity.Yul.Checks.RawCheckedIfElseHorizon
#print axioms Solidity.Yul.RawCheckedIfElseHorizon.successor
#print axioms Solidity.Yul.RawCheckedIfElseHorizon.extension
#print axioms Solidity.Yul.RawCheckedIfElseHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.trueStable
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.falseStable
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.dirtyTruthStable
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.earlyCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.cleanSourceStable
#print axioms Solidity.Yul.Checks.RawCheckedIfElseHorizon.dirtySourceBoundary
