import Solidity.Yul.RawCheckedControlSequenceHorizon
import Solidity.Yul.Checks.RawCheckedControlSequence
/-! Completed mixed control frames, reachable skipped tails, exact Source
witnesses and timeout/pipeline boundary controls. No admission claim. -/
namespace Solidity.Yul.Checks.RawCheckedControlSequenceHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedControlSequence.Old (ctx env initial xCell flagCell)
export Solidity.Yul.Checks.RawCheckedControlSequence (breakItems breakProof continueItems continueProof normalItems normalProof panicItems panicProof partialProof skipCopyProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def cleanDone : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.breakItems) := ⟨Old.breakProof⟩
end Solidity.Yul.Checks.RawCheckedControlSequenceHorizon

namespace Solidity.Yul.Checks.RawCheckedControlSequenceHorizon
theorem sourceItemsCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 (Solidity.Source.execItems glob frame 8 nps ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakItems Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) =
 (.ok (.brk Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.cleanDone),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceBlockCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 (Solidity.Source.execS glob frame 9 nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueItems) Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) =
 (.ok (.cont Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.cleanDone),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem breakStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) = Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.rawBreak pipeline world).1]
  intro bad
  cases bad

theorem continueStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) = Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.rawContinue pipeline world).1]
  intro bad
  cases bad

theorem normalStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.normalProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) = Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.normalProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.normalRuns pipeline world).1]
  intro bad
  cases bad

theorem panicStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.panicProof pipeline (6+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 511 1 2 world) = Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.panicProof pipeline 6 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 511 1 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlSequenceHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.panicStops pipeline world).1]
  intro bad
  cases bad

theorem blockStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueProof pipeline (9+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueProof pipeline 9 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlSequenceHorizon.blockExtension
  change (RawCheckedControlSequence.run Old.continueProof pipeline 8 (Old.initial 2 257 2 world)).1 ≠ .error .timeout
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.rawContinue pipeline world).1]
  intro bad
  cases bad

theorem skippedTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (extra : Nat),
 (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world)).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakProof pipeline (8+extra) (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world extra
  rw [breakStable pipeline world extra]
  exact Solidity.Yul.Checks.RawCheckedControlSequence.rawBreak pipeline world

theorem sourceItemsStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 (Solidity.Source.execItems glob frame (8+extra) nps ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakItems Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) =
 (Solidity.Source.execItems glob frame 8 nps ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.breakItems Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlSequence.correct Old.ctx [] false false Old.breakItems Old.breakProof glob frame checked 8 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawLoopBody.represented (RawCheckedControlSequence.run Old.breakProof glob.pipeline 8
      (RawFrame.ofClean Old.clean world))).1 = .ok (.brk cleanDone) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceItemsCompletes glob frame nps ph world))
  have ready : (RawCheckedControlSequence.run Old.breakProof glob.pipeline 8
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawLoopBody.represented (RawCheckedControlSequence.run Old.breakProof glob.pipeline 8
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawLoopBody.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlSequenceHorizon.sourceItemsExtension Old.ctx [] false false Old.breakItems Old.breakProof
    glob frame checked 8 extra nps ph (RawFrame.ofClean Old.clean world)
    (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem sourceBlockStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 (Solidity.Source.execS glob frame (9+extra) nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueItems) Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 9 nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.continueItems) Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlSequence.block_correct Old.continueProof glob frame checked 9 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawLoopBody.represented (RawCheckedControlSequence.block Old.continueProof glob.pipeline 9
      (RawFrame.ofClean Old.clean world))).1 = .ok (.cont cleanDone) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceBlockCompletes glob frame nps ph world))
  have ready : (RawCheckedControlSequence.block Old.continueProof glob.pipeline 9
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawLoopBody.represented (RawCheckedControlSequence.block Old.continueProof glob.pipeline 9
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawLoopBody.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlSequenceHorizon.sourceBlockExtension Old.ctx [] false false Old.continueItems Old.continueProof
    glob frame checked 9 extra nps ph (RawFrame.ofClean Old.clean world)
    (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.skipCopyProof pipeline 0 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.skipCopyProof pipeline 8 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.skipCopy pipeline world).1] at tags
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env),
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.partialProof .legacy 6 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 257 2 1 world) ≠
 Solidity.Yul.RawCheckedControlSequence.run Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.partialProof .viaIR 6 (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 257 2 1 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R RawLoopBody.Flow × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedControlSequence.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedControlSequence.viaIRPartial world).2.1] at cells
  cases cells

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedControlSequence.dirtyBoundary world]
  intro bad
  cases bad

end Solidity.Yul.Checks.RawCheckedControlSequenceHorizon
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.successor
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.blockSuccessor
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.extension
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.blockExtension
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.sourceItemsExtension
#print axioms Solidity.Yul.RawCheckedControlSequenceHorizon.sourceBlockExtension
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.sourceItemsCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.sourceBlockCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.breakStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.continueStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.normalStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.panicStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.blockStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.skippedTail
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.sourceItemsStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.sourceBlockStable
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedControlSequenceHorizon.dirtyBoundary
