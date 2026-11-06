import Solidity.Yul.RawCheckedControlWhileHorizon
import Solidity.Yul.Checks.RawCheckedControlWhile
/-! Completed mixed-control loop frames and concrete Source horizons.
Timeout prefixes and dirty boundary remain explicit negative controls. Kernel evidence only. -/
namespace Solidity.Yul.Checks.RawCheckedControlWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedControlWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard breakItems breakProof)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearContinueItems clearContinueProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def cleanBreak : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def cleanContinue : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def witness : Nonempty (RawCheckedControlSequence.Supported Old.ctx [] false false Old.clearContinueItems) := ⟨Old.clearContinueProof⟩
end Solidity.Yul.Checks.RawCheckedControlWhileHorizon

namespace Solidity.Yul.Checks.RawCheckedControlWhileHorizon
theorem breakStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlWhile.rawBreak pipeline world).1]
  intro bad
  cases bad

theorem continueStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedControlWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlWhile.rawContinue pipeline world).1]
  intro bad
  cases bad

theorem falseStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 0 world) =
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline 16 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 0 world) := by
  intro pipeline world extra
  apply RawCheckedControlWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedControlWhile.falseSkips pipeline world).1]
  intro bad
  cases bad

theorem earlyGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flagCell).val = 2 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem timeoutProgress : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline 3 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline 4 (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.flagCell).val) bad
  dsimp only at cells
  rw [(earlyGuard pipeline world).2,
    (Solidity.Yul.Checks.RawCheckedControlWhile.guardWrites pipeline world).2.2.1] at cells
  cases cells

theorem differentPaths : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  rw [breakStable pipeline world extra,continueStable pipeline world extra]
  exact Solidity.Yul.Checks.RawCheckedControlWhile.differentControlPaths pipeline world

theorem skippedTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (extra : Nat),
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).1 = .ok () ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flagCell).val = 0 ∧
 (Solidity.Yul.RawCheckedControlWhile.run Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueProof pipeline (16+extra) (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world extra
  rw [continueStable pipeline world extra]
  exact Solidity.Yul.Checks.RawCheckedControlWhile.rawContinue pipeline world

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedControlWhile.dirtyBoundary world]
  intro bad
  cases bad

theorem sourceBreakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceBreakStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (16+extra) nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.breakItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlWhile.correct (l := false) Old.readFlag Old.breakProof glob frame checked 16 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedControlWhile.run Old.readFlag Old.breakProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world))).1 = .ok (.normal cleanBreak) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceBreakCompletes glob frame nps ph world))
  have ready : (RawCheckedControlWhile.run Old.readFlag Old.breakProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedControlWhile.run Old.readFlag Old.breakProof glob.pipeline 16
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlWhileHorizon.sourceExtension Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.breakItems Old.breakProof glob frame checked 16 extra nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem sourceContinueCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceContinueStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (16+extra) nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 16 nps ph (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clearContinueItems)) Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedControlWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedControlWhile.correct (l := false) Old.readFlag Old.clearContinueProof glob frame checked 16 nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedControlWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world))).1 = .ok (.normal cleanContinue) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceContinueCompletes glob frame nps ph world))
  have ready : (RawCheckedControlWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedControlWhile.run Old.readFlag Old.clearContinueProof glob.pipeline 16
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedControlWhileHorizon.sourceExtension Old.ctx [] false false false (.local Old.flag) Old.readFlag
    Old.clearContinueItems Old.clearContinueProof glob frame checked 16 extra nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

end Solidity.Yul.Checks.RawCheckedControlWhileHorizon
#print axioms Solidity.Yul.RawCheckedControlWhileHorizon.successor
#print axioms Solidity.Yul.RawCheckedControlWhileHorizon.extension
#print axioms Solidity.Yul.RawCheckedControlWhileHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.breakStable
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.continueStable
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.falseStable
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.earlyGuard
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.timeoutProgress
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.differentPaths
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.skippedTail
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.sourceBreakCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.sourceBreakStable
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.sourceContinueCompletes
#print axioms Solidity.Yul.Checks.RawCheckedControlWhileHorizon.sourceContinueStable
