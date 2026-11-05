import Solidity.Yul.RawCheckedWhileHorizon
import Solidity.Yul.Checks.RawCheckedWhile
/-! Completed raw loop frames and actual Source horizons, with exact
timeout-prefix, pipeline and divergence-premise boundary controls. -/
namespace Solidity.Yul.Checks.RawCheckedWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard)
export Solidity.Yul.Checks.RawCheckedWhile (copyItems copyProof partialProof always emptyProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
theorem copyStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) =
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world extra
  apply RawCheckedWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedWhile.rawCopy pipeline world).1]
  intro bad
  cases bad

theorem falseStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialProof pipeline (2+extra) (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 511 1 0 world) =
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialProof pipeline 2 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 511 1 0 world) := by
  intro pipeline world extra
  apply RawCheckedWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedWhile.falseSkips pipeline world).1]
  intro bad
  cases bad

theorem earlyCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedWhile.earlyCopy pipeline world).1,
    (Solidity.Yul.Checks.RawCheckedWhile.rawCopy pipeline world).1] at tags
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 257 2 2 world) ≠
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 257 2 2 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedWhile.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedWhile.viaIRPartial world).2.1] at cells
  cases cells


theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedWhile.dirtyBoundary world]
  intro bad
  cases bad

theorem foreverRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.ctx),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.always Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.emptyProof pipeline fuel state).1 ≠ .error .timeout → False := by
  intro pipeline fuel state terminal
  exact terminal (Solidity.Yul.Checks.RawCheckedWhile.diverges pipeline fuel state)

theorem earlyGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.flagCell).val = 2 ∧
 (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl⟩

theorem timeoutProgress : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.flagCell).val) bad
  dsimp only at cells
  rw [(earlyGuard pipeline world).2.1,
    (Solidity.Yul.Checks.RawCheckedWhile.guardWrites pipeline world).2.2.1] at cells
  cases cells

end Solidity.Yul.Checks.RawCheckedWhileHorizon
#print axioms Solidity.Yul.RawCheckedWhileHorizon.successor
#print axioms Solidity.Yul.RawCheckedWhileHorizon.extension
#print axioms Solidity.Yul.RawCheckedWhileHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.copyStable
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.falseStable
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.earlyCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.foreverRefuses
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.earlyGuard
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.timeoutProgress

namespace Solidity.Yul.Checks.RawCheckedWhileHorizonStages
namespace Old
export Solidity.Yul.Checks.RawCheckedWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard)
export Solidity.Yul.Checks.RawCheckedWhile (copyItems copyProof partialProof always emptyProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def cleanDone : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
end Solidity.Yul.Checks.RawCheckedWhileHorizonStages

namespace Solidity.Yul.Checks.RawCheckedWhileHorizonStages
theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.env),
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.flag) (.block Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.copyItems)) Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedWhileHorizonStages.cleanDone),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhileHorizonStages.Old.env,world)) := by
  intro glob frame nps ph world
  rfl
end Solidity.Yul.Checks.RawCheckedWhileHorizonStages
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizonStages.sourceCompletes

namespace Solidity.Yul.Checks.RawCheckedWhileHorizon
theorem cleanSourceStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env) (frame : Solidity.Source.Fr),
 frame.checked = true → ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (7+extra) nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyItems)) Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.whileLoop (l := false) (.local Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.flag) (.block Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.copyItems)) Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedWhile.correct (l := false) Old.readFlag Old.copyProof glob frame checked
    7 nps ph (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedWhile.run Old.readFlag Old.copyProof glob.pipeline 7
      (RawFrame.ofClean Old.clean world))).1 =
      .ok (.normal RawCheckedWhileHorizonStages.cleanDone) :=
    (congrArg Prod.fst actual.2).symm.trans
      (congrArg Prod.fst (RawCheckedWhileHorizonStages.sourceCompletes glob frame nps ph world))
  have ready : (RawCheckedWhile.run Old.readFlag Old.copyProof glob.pipeline 7
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedWhile.run Old.readFlag Old.copyProof glob.pipeline 7
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedWhileHorizon.sourceExtension Old.ctx [] false false false _
    Old.readFlag Old.copyItems Old.copyProof glob frame checked 7 extra nps ph
    (RawFrame.ofClean Old.clean world) (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready
end Solidity.Yul.Checks.RawCheckedWhileHorizon
#print axioms Solidity.Yul.Checks.RawCheckedWhileHorizon.cleanSourceStable
