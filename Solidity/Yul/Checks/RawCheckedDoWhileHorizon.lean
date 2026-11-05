import Solidity.Yul.RawCheckedDoWhileHorizon
import Solidity.Yul.RawCheckedWhileHorizon
import Solidity.Yul.Checks.RawCheckedDoWhile
/-! Exact completed frame transport with body-first order, timeout-prefix,
pipeline and concrete Source witness controls. No frontend admission claim. -/
namespace Solidity.Yul.Checks.RawCheckedDoWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawCheckedDoWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard copyItems copyProof partialProof always emptyProof)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def cleanDone : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
end Solidity.Yul.Checks.RawCheckedDoWhileHorizon

namespace Solidity.Yul.Checks.RawCheckedDoWhileHorizon
theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyItems) (.local Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedDoWhileHorizon.cleanDone),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem copyStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 flag world) =
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 flag world) := by
  intro pipeline flag world extra
  apply RawCheckedDoWhileHorizon.extension
  rw [(Solidity.Yul.Checks.RawCheckedDoWhile.rawCopy pipeline flag world).1]
  intro bad
  cases bad

theorem earlyCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 flag world) ≠
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 flag world) := by
  intro pipeline flag world bad
  have tags := congrArg Prod.fst bad
  rw [(Solidity.Yul.Checks.RawCheckedDoWhile.earlyCopy pipeline flag world).1,
    (Solidity.Yul.Checks.RawCheckedDoWhile.rawCopy pipeline flag world).1] at tags
  cases tags

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 257 2 2 world) ≠
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 257 2 2 world) := by
  intro world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(Solidity.Yul.Checks.RawCheckedDoWhile.legacyPartial world).2.1,
    (Solidity.Yul.Checks.RawCheckedDoWhile.viaIRPartial world).2.1] at cells
  cases cells

theorem cleanSourceStable : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (extra nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 (Solidity.Source.execS glob frame (7+extra) nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyItems) (.local Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env,world) =
 (Solidity.Source.execS glob frame 7 nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyItems) (.local Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.flag)) Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env,world) := by
  intro glob frame checked extra nps ph world
  have actual := RawCheckedDoWhile.correct Old.ctx [] false false false _ Old.readFlag Old.copyItems Old.copyProof
    glob frame checked 7 nps ph (RawFrame.ofClean Old.clean world)
    (@RawCoherent.coherent_ofClean Old.ctx Old.clean world)
  have completion : (RawSequence.represented (RawCheckedDoWhile.run Old.readFlag Old.copyProof glob.pipeline 7
      (RawFrame.ofClean Old.clean world))).1 = .ok (.normal cleanDone) :=
    (congrArg Prod.fst actual.2).symm.trans (congrArg Prod.fst (sourceCompletes glob frame nps ph world))
  have ready : (RawCheckedDoWhile.run Old.readFlag Old.copyProof glob.pipeline 7
      (RawFrame.ofClean Old.clean world)).1 ≠ .error .timeout := by
    intro bad
    have timed : (RawSequence.represented (RawCheckedDoWhile.run Old.readFlag Old.copyProof glob.pipeline 7
        (RawFrame.ofClean Old.clean world))).1 = .error .timeout := by
      simp only [RawSequence.represented,bad,Except.map]
    have impossible := completion.symm.trans timed
    cases impossible
  exact RawCheckedDoWhileHorizon.sourceExtension Old.ctx [] false false false _ Old.readFlag Old.copyItems Old.copyProof
    glob frame checked 7 extra nps ph (RawFrame.ofClean Old.clean world)
    (@RawCoherent.coherent_ofClean Old.ctx Old.clean world) ready

theorem foreverRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.ctx),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.always Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline fuel state).1 ≠ .error .timeout → False := by
  intro pipeline fuel state terminal
  exact terminal (Solidity.Yul.Checks.RawCheckedDoWhile.diverges pipeline fuel state)

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world) ≠ true := by
  intro world
  rw [Solidity.Yul.Checks.RawCheckedDoWhile.dirtyBoundary world]
  intro bad
  cases bad

theorem earlyGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.flagCell).val = 2 ∧
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl⟩

theorem timeoutProgress : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline 3 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world) ≠
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.flagCell).val) bad
  dsimp only at cells
  rw [(earlyGuard pipeline world).2.1,
    (Solidity.Yul.Checks.RawCheckedDoWhile.afterGuard pipeline world).2.2.1] at cells
  cases cells

theorem falseOrderStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.env) (extra : Nat),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 0 world) ≠
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.copyProof pipeline (7+extra) (Solidity.Yul.Checks.RawCheckedDoWhileHorizon.Old.initial 2 257 0 world) := by
  intro pipeline world extra
  have ready : (RawCheckedWhile.run Old.readFlag Old.copyProof pipeline 7 (Old.initial 2 257 0 world)).1 ≠ .error .timeout := by
    rw [(Solidity.Yul.Checks.RawCheckedDoWhile.whileFalse pipeline world).2]
    intro bad
    cases bad
  rw [copyStable pipeline 0 world extra,
    RawCheckedWhileHorizon.extension Old.ctx [] false false _ Old.readFlag Old.copyItems Old.copyProof
      pipeline 7 extra (Old.initial 2 257 0 world) ready]
  exact Solidity.Yul.Checks.RawCheckedDoWhile.orderDistinguishes pipeline world

end Solidity.Yul.Checks.RawCheckedDoWhileHorizon
#print axioms Solidity.Yul.RawCheckedDoWhileHorizon.successor
#print axioms Solidity.Yul.RawCheckedDoWhileHorizon.extension
#print axioms Solidity.Yul.RawCheckedDoWhileHorizon.sourceExtension
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.sourceCompletes
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.copyStable
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.earlyCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.cleanSourceStable
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.foreverRefuses
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.dirtyBoundary
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.earlyGuard
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.timeoutProgress
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileHorizon.falseOrderStable
