import Solidity.Yul.RawCheckedControlDoWhileHorizon
import Solidity.Yul.Checks.RawCheckedControlDoWhile
import Solidity.Yul.Checks.RawCheckedControlWhileHorizon
import Solidity.Yul.Checks.RawCheckedWhile
/-! Whole-frame completion horizons, actual Source readback and all-fuel
divergence controls. Dirty frames and timeout prefixes remain distinct.
Kernel evidence only, not general admission or external compiler validation. -/
namespace Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedControlDoWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard breakItems breakProof clearContinueItems clearContinueProof partialProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
export Solidity.Yul.Checks.RawCheckedWhile (always guardNext)
end Old
def emptyProof : RawCheckedControlSequence.Supported Old.ctx [] false false .nil := .nil
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.clearContinueItems) := ⟨Old.clearContinueProof⟩
end Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon

namespace Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon
theorem breakStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.breakProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlDoWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlDoWhile.rawBreak pipeline world).1]
  intro bad
  cases bad

theorem continueStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlDoWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlDoWhile.rawContinue pipeline world).1]
  intro bad
  cases bad

theorem falseStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 0 world) =
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 0 world) := by
  intro pipeline world extra
  apply RawCheckedControlDoWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlDoWhile.falseStillRuns pipeline world).1]
  intro bad
  cases bad

theorem skippedTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (extra : Nat),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).1 = .ok () ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world extra
  rw [continueStable pipeline world extra]
  exact Solidity.Yul.Checks.RawCheckedControlDoWhile.rawContinue pipeline world

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 257 2 1 world) ≠
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 257 2 1 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedControlDoWhile.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedControlDoWhile.viaIRPartial world).2.1] at cells
  cases cells

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedControlDoWhile.dirtyBoundary world]
  intro bad
  cases bad

theorem sourceBreakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.breakItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceBreakStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (16+extra) nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.breakItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.breakItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlDoWhile.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.breakItems Old.breakProof glob frame checked 16 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedControlDoWhile.run Old.readFlag Old.breakProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world))).1 = .ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceBreakCompletes glob frame nps ph world))
  have ready : (RawCheckedControlDoWhile.run Old.readFlag Old.breakProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedControlDoWhile.run Old.readFlag Old.breakProof glob.pipeline 16
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlDoWhileHorizon.sourceExtension Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.breakItems Old.breakProof glob frame checked 16 extra nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem sourceContinueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceContinueStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (16+extra) nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clearContinueItems) (.local Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlDoWhile.correct Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.clearContinueItems Old.clearContinueProof glob frame checked 16 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedControlDoWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world))).1 = .ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceContinueCompletes glob frame nps ph world))
  have ready : (RawCheckedControlDoWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedControlDoWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlDoWhileHorizon.sourceExtension Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.clearContinueItems Old.clearContinueProof glob frame checked 16 extra nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem emptyNext : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.ctx),
 Solidity.Yul.RawCheckedControlSequence.block Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline (fuel+2) state = (.ok .normal,state) := by
  intro pipeline fuel state
  rfl

theorem diverges : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.ctx),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.always Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline fuel state).1 = .error .timeout := by
  intro pipeline fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ n =>
        rw [RawCheckedControlDoWhile.run,emptyNext]
        dsimp only
        rw [RawSourceAdapterDoWhile.after,Old.guardNext]
        exact ih _

theorem foreverRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.ctx),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.always Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline fuel state).1 ≠ .error .timeout → False := by
  intro pipeline fuel state terminal
  exact terminal (diverges pipeline fuel state)

theorem earlyGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flagCell).val = 2 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem lateGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.flagCell).val = 0 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem timeoutProgress : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedControlDoWhile.run Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.flagCell).val) bad
  dsimp only at cells
  rw [(earlyGuard pipeline world).2,(lateGuard pipeline world).2] at cells
  cases cells

end Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon
#print axioms Solidity.Yul.RawCheckedControlDoWhileHorizon.successor
#print axioms Solidity.Yul.RawCheckedControlDoWhileHorizon.extension
#print axioms Solidity.Yul.RawCheckedControlDoWhileHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.breakStable
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.continueStable
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.falseStable
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.skippedTail
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.sourceBreakCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.sourceBreakStable
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.sourceContinueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.sourceContinueStable
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.emptyNext
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.diverges
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.foreverRefuses
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.earlyGuard
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.lateGuard
#print axioms Solidity.Yul.Checks.RawCheckedControlDoWhileHorizon.timeoutProgress
