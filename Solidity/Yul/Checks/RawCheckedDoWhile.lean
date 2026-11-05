import Solidity.Yul.RawCheckedDoWhile
import Solidity.Yul.Checks.RawCheckedWhile
/-! Body-first mixed execution, retained raw prefixes, and real Source transport.
Normal-flow certificates only; no general admission or external EVM claim. -/
namespace Solidity.Yul.Checks.RawCheckedDoWhile
namespace Old
export Solidity.Yul.Checks.RawCheckedWhile.Old (ctx env initial xCell flagCell flag readFlag partialGuard)
export Solidity.Yul.Checks.RawCheckedWhile (copyItems copyProof partialProof always emptyProof guardNext emptyNext)
export Solidity.Yul.Checks.RawCheckedWhileStages (finalViews)
export Solidity.Yul.Checks.RawCheckedIfStages (frame rawFlag)
end Old
def witness : Nonempty (RawCheckedSequence.Supported Old.ctx [] false ⟨true,false⟩ Old.copyItems) := ⟨Old.copyProof⟩
end Solidity.Yul.Checks.RawCheckedDoWhile

namespace Solidity.Yul.Checks.RawCheckedDoWhileStages
theorem bodyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world) =
 (.ok (),Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) := by
  intro pipeline flag world
  rfl
theorem bodyEarly : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 5 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 2 257 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) := by
  intro pipeline flag world
  rfl
theorem bodyLegacy : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .legacy 8 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 257 2 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) := by
  intro world
  rfl
theorem bodyVia : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCheckedSequence.block Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .viaIR 8 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world) =
 (.error .timeout,Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 2 2 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) := by
  intro world
  rfl
theorem conditionAfter : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) =
 (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedDoWhile.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.rawFlag 0) world))) := by
  intro world
  rfl
end Solidity.Yul.Checks.RawCheckedDoWhileStages

namespace Solidity.Yul.Checks.RawCheckedDoWhile
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false) (.block Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyItems) (.local Solidity.Yul.Checks.RawCheckedDoWhile.Old.flag)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhile.Old.env,world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact RawCheckedDoWhile.correct Old.ctx [] false false false _ Old.readFlag Old.copyItems Old.copyProof
    glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem rawCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2.world = world := by
  intro pipeline flag world
  let next := Old.frame 257 257 (Old.rawFlag 0) world
  have outcome : RawCheckedDoWhile.run Old.readFlag Old.copyProof pipeline 7 (Old.initial 2 257 flag world) =
      (.ok (),RawCoherent.capture next (RawCoherent.prepare next)) := by
    rw [RawCheckedDoWhile.run,RawCheckedDoWhileStages.bodyCopy]
    change RawSourceAdapterDoWhile.after Old.readFlag (RawCheckedDoWhile.run Old.readFlag Old.copyProof pipeline 6) 6 next = _
    rw [RawSourceAdapterDoWhile.after,RawCheckedDoWhileStages.conditionAfter]
    rfl
  rw [outcome]
  exact ⟨rfl,Old.finalViews world⟩

theorem earlyCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (flag : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 6 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 flag world)).2.world = world := by
  intro pipeline flag world
  rw [RawCheckedDoWhile.run,RawCheckedDoWhileStages.bodyEarly]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem afterGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhile.Old.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhile.Old.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhile.Old.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialGuard Solidity.Yul.Checks.RawCheckedDoWhile.Old.emptyProof pipeline 4 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 2 world)).2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .legacy 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  rw [RawCheckedDoWhile.run,RawCheckedDoWhileStages.bodyLegacy]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.partialProof .viaIR 9 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 257 2 2 world)).2.world = world := by
  intro world
  rw [RawCheckedDoWhile.run,RawCheckedDoWhileStages.bodyVia]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem whileFalse : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 0 world)).2 Solidity.Yul.Checks.RawCheckedDoWhile.Old.xCell).val = 2 ∧ (Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 0 world)).1 = .ok () := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem orderDistinguishes : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 0 world) ≠
 Solidity.Yul.RawCheckedWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.readFlag Solidity.Yul.Checks.RawCheckedDoWhile.Old.copyProof pipeline 7 (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 0 world) := by
  intro pipeline world bad
  have cells := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at cells
  rw [(rawCopy pipeline 0 world).2.1,(whileFalse pipeline world).1] at cells
  cases cells

theorem diverges : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedDoWhile.Old.ctx),
 (Solidity.Yul.RawCheckedDoWhile.run Solidity.Yul.Checks.RawCheckedDoWhile.Old.always Solidity.Yul.Checks.RawCheckedDoWhile.Old.emptyProof pipeline fuel state).1 = .error .timeout := by
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
        rw [RawCheckedDoWhile.run,Old.emptyNext]
        dsimp only
        rw [RawSourceAdapterDoWhile.after,Old.guardNext]
        exact ih _

theorem sourceDiverges : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedDoWhile.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedDoWhile.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedDoWhile.Old.env.layout Solidity.Yul.Checks.RawCheckedDoWhile.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := false)
     (.block (Solidity.Source.RItems.nil : Solidity.Source.RItems Solidity.Yul.Checks.RawCheckedDoWhile.Old.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawCheckedDoWhile.Old.ctx.tys Solidity.Yul.Checks.RawCheckedDoWhile.Old.ctx.tys))
     (.bool true)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedDoWhile.Old.env,world)).1 = .error .timeout := by
  intro glob frame checked fuel nps ph locals world
  have actual := RawCheckedDoWhile.correct Old.ctx [] false false false _ Old.always .nil Old.emptyProof
    glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)
  have result : (RawSequence.represented (RawCheckedDoWhile.run Old.always Old.emptyProof glob.pipeline fuel
      (RawFrame.ofClean locals world))).1 = .error .timeout := by
    simp only [RawSequence.represented,diverges,Except.map]
  exact (congrArg Prod.fst actual.2).trans result

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedDoWhile.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedDoWhile.Old.initial 2 257 2 world) = false := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedWhile.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedDoWhile
#print axioms Solidity.Yul.RawCheckedDoWhile.correct
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileStages.bodyCopy
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileStages.bodyEarly
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileStages.bodyLegacy
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileStages.bodyVia
#print axioms Solidity.Yul.Checks.RawCheckedDoWhileStages.conditionAfter
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.rawCopy
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.earlyCopy
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.afterGuard
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.viaIRPartial
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.whileFalse
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.orderDistinguishes
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.diverges
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.sourceDiverges
#print axioms Solidity.Yul.Checks.RawCheckedDoWhile.dirtyBoundary
