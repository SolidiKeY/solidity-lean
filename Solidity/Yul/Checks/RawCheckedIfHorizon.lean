import Solidity.Yul.RawCheckedIfHorizon
import Solidity.Yul.Checks.RawCheckedIf
/-! Inhabited mixed execution, full-frame stability and exact timeout/pipeline refusals. -/
namespace Solidity.Yul.Checks.RawCheckedIfHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedIf (selected readFlag writeFalse)
export Solidity.Yul.Checks.RawCheckedIf.Old (ctx initial copyProof copyItems panicProof partialProof xCell flag)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨false,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
theorem selectedStable (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) (extra : Nat) :
 RawCheckedIf.run Old.selected Old.copyProof pipeline (7+extra) (Old.initial 2 257 2 world) =
 RawCheckedIf.run Old.selected Old.copyProof pipeline 7 (Old.initial 2 257 2 world) := by
  apply RawCheckedIfHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedIf.selectedCopy pipeline world).1]
  intro bad
  cases bad

theorem dirtyTruthStable (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) (extra : Nat) :
 RawCheckedIf.run Old.readFlag Old.copyProof pipeline (7+extra) (Old.initial 2 257 2 world) =
 RawCheckedIf.run Old.readFlag Old.copyProof pipeline 7 (Old.initial 2 257 2 world) := by
  apply RawCheckedIfHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedIf.nonzeroTruth pipeline world).1]
  intro bad
  cases bad

theorem skippedStable (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) (extra : Nat) :
 RawCheckedIf.run Old.writeFalse Old.panicProof pipeline (4+extra) (Old.initial 511 1 2 world) =
 RawCheckedIf.run Old.writeFalse Old.panicProof pipeline 4 (Old.initial 511 1 2 world) := by
  apply RawCheckedIfHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedIf.skipFalse pipeline world).1]
  intro bad
  cases bad

theorem earlyCounterexample (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.ctx.env) :
 RawCheckedIf.run Old.selected Old.copyProof pipeline 6 (Old.initial 2 257 2 world) ≠
 RawCheckedIf.run Old.selected Old.copyProof pipeline 7 (Old.initial 2 257 2 world) := by
  intro bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedIf.earlyBody pipeline world).1,
    (Solidity.Yul.Checks.RawCheckedIf.selectedCopy pipeline world).1] at tags
  cases tags

theorem pipelineCounterexample (world : Solidity.Source.St Old.ctx.env) :
 RawCheckedIf.run Old.selected Old.partialProof .legacy 9 (Old.initial 257 2 2 world) ≠
 RawCheckedIf.run Old.selected Old.partialProof .viaIR 9 (Old.initial 257 2 2 world) := by
  intro bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedIf.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedIf.viaIRPartial world).2.1] at cells
  cases cells

theorem sourceStable (glob : Solidity.Source.Glob Old.ctx.env) (frame : Solidity.Source.Fr)
 (checked : frame.checked = true) (fuel extra nps : Nat)
 (ph : Option (Solidity.Source.Ph Old.ctx.env)) (state : RawFrame.State Old.ctx)
 (same : RawCoherent.coherent state = true)
 (ready : (RawCheckedIf.run Old.selected Old.copyProof glob.pipeline fuel state).1 ≠ .error .timeout) :
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.ifThen (.unary .not (.assign (.local Old.flag) (.bool false))) (.block Old.copyItems)) state.clean).run
   (Solidity.Source.L0 Old.ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifThen (.unary .not (.assign (.local Old.flag) (.bool false))) (.block Old.copyItems)) state.clean).run
   (Solidity.Source.L0 Old.ctx.env,state.world) := by
  exact RawCheckedIfHorizon.sourceExtension Old.ctx [] false ⟨false,false⟩ _ _ Old.selected Old.copyProof glob frame checked fuel extra nps ph state same ready

theorem cleanSourceStable (glob : Solidity.Source.Glob Old.ctx.env) (frame : Solidity.Source.Fr)
 (checked : frame.checked = true) (extra nps : Nat)
 (ph : Option (Solidity.Source.Ph Old.ctx.env)) (world : Solidity.Source.St Old.ctx.env) :
 (Solidity.Source.execS glob frame (7+extra) nps ph
   (Solidity.Source.RStmt.ifThen (.unary .not (.assign (.local Old.flag) (.bool false))) (.block Old.copyItems)) Old.clean).run
   (Solidity.Source.L0 Old.ctx.env,world) =
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.ifThen (.unary .not (.assign (.local Old.flag) (.bool false))) (.block Old.copyItems)) Old.clean).run
   (Solidity.Source.L0 Old.ctx.env,world) := by
  have ready : (RawCheckedIf.run Old.selected Old.copyProof glob.pipeline 7 (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    cases bad
  exact sourceStable glob frame checked 7 extra nps ph (RawFrame.ofClean Old.clean world)
    (RawCoherent.coherent_ofClean Old.clean world) ready

end Solidity.Yul.Checks.RawCheckedIfHorizon
#print axioms Solidity.Yul.RawCheckedIfHorizon.successor
#print axioms Solidity.Yul.RawCheckedIfHorizon.extension
#print axioms Solidity.Yul.RawCheckedIfHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.selectedStable
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.dirtyTruthStable
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.skippedStable
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.earlyCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.sourceStable
#print axioms Solidity.Yul.Checks.RawCheckedIfHorizon.cleanSourceStable
