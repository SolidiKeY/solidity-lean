import Solidity.Yul.RawCheckedAdapterFor
import Solidity.Yul.Checks.RawCheckedAdapterLoop
/-! Same-context checked no-post for witnesses: initializer state is visible
to the guard; errors/control stop before iteration. Runtime controls are not
frontend admission claims. Kernel evidence only. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterFor
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapterLoop.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag clean)
export Solidity.Yul.Checks.RawCheckedAdapterLoop (body)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearExpr clearHead)
export Solidity.Yul.Checks.RawCheckedControlSequence (panicItems panicProof partialItems partialProof)
end Old
def initializer : RawCheckedAdapter.Adapter Old.ctx [] false false (.expr Old.clearExpr) :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.atom Old.clearHead)
def broken : RawCheckedAdapter.Adapter Old.ctx [] false false .brk :=
 Solidity.Yul.Checks.RawCheckedAdapter.pureBreak
def continued : RawCheckedAdapter.Adapter Old.ctx [] false false .cont :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .continue_)
def panic : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.panicItems) :=
 Solidity.Yul.RawCheckedAdapter.block Old.panicProof
def partialInit : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.partialItems) :=
 Solidity.Yul.RawCheckedAdapter.block Old.partialProof
def packed : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.forLoop (l := true) (.expr Old.clearExpr) (.some (.local Old.flag)) .none
   (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) :=
 Solidity.Yul.RawCheckedAdapterFor.adapter initializer Old.readFlag Old.body
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.forLoop (l := true) (.expr Old.clearExpr) (.some (.local Old.flag)) .none
   (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items))) := ⟨packed⟩
end Solidity.Yul.Checks.RawCheckedAdapterFor

namespace Solidity.Yul.Checks.RawCheckedAdapterFor
theorem initializes : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterFor.initializer.run pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem clearedGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag 19 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) = (.ok false,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro world
  rfl

theorem initializedRun : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.initializer Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) = (.ok (),Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  rw [Solidity.Yul.RawCheckedAdapterFor.run,initializes]
  change RawCheckedAdapterLoop.run Old.readFlag Old.body pipeline 20
    (Old.frame 2 257 (LocalValue.clean (.bool false)) world) = _
  rw [RawCheckedAdapterLoop.run,clearedGuard]
  rfl

theorem finalViews : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) Solidity.Yul.Checks.RawCheckedAdapterFor.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flagCell).val = 0 ∧ (Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))).world = world := by
  intro world
  simp only [RawCoherent.capture_view,RawCoherent.prepare_view]
  exact ⟨by first | rfl | trivial,by first | rfl | trivial,by first | rfl | trivial⟩

theorem packedRun : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterFor.packed.run pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.frame 2 257 (Solidity.Yul.LocalValue.clean (.bool false)) world))) := by
  intro pipeline world
  change ((Solidity.Yul.RawCheckedAdapterFor.run initializer Old.readFlag Old.body pipeline 21 (Old.initial 2 257 2 world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterFor.run initializer Old.readFlag Old.body pipeline 21 (Old.initial 2 257 2 world)).2) = _
  rw [initializedRun]
  rfl

theorem breakRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.broken Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) = (.error (.stuck "for initializer"),Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem continueRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.continued Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) = (.error (.stuck "for initializer"),Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem panicPropagates : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.panic Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 511 1 2 world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.panic Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.xCell).val = 511 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.panic Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flagCell).val = 2 ∧ (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.panic Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  have facts := Solidity.Yul.Checks.RawCheckedControlSequence.panicStops pipeline world
  simp only [Solidity.Yul.RawCheckedAdapterFor.run,panic,
    Solidity.Yul.RawCheckedAdapter.block,RawCheckedControlSequence.block,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .legacy 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .legacy 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .legacy 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .legacy 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  have facts := Solidity.Yul.Checks.RawCheckedControlSequence.legacyPartial world
  simp only [Solidity.Yul.RawCheckedAdapterFor.run,partialInit,
    Solidity.Yul.RawCheckedAdapter.block,RawCheckedControlSequence.block,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .viaIR 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .viaIR 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .viaIR 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flagCell).val = 1 ∧ (Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .viaIR 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world)).2.world = world := by
  intro world
  have facts := Solidity.Yul.Checks.RawCheckedControlSequence.viaIRPartial world
  simp only [Solidity.Yul.RawCheckedAdapterFor.run,partialInit,
    Solidity.Yul.RawCheckedAdapter.block,RawCheckedControlSequence.block,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem pipelineCounterexample : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .legacy 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world) ≠
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.partialInit Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body .viaIR 8 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 257 2 1 world) := by
  intro world bad
  have view := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  dsimp only at view
  rw [(legacyPartial world).2.1,(viaIRPartial world).2.1] at view
  cases view

theorem initializationMatters : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.initializer Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedAdapterLoop.run Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 20 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  rw [initializedRun pipeline world,Solidity.Yul.Checks.RawCheckedAdapterLoop.rawBreak pipeline world] at bad
  have view := congrArg (fun out : Solidity.Source.R Unit × RawFrame.State Old.ctx =>
    (RawFrame.view out.2 Old.xCell).val) bad
  change (RawFrame.view (RawCoherent.capture
    (Old.frame 2 257 (LocalValue.clean (.bool false)) world)
    (RawCoherent.prepare (Old.frame 2 257 (LocalValue.clean (.bool false)) world))) Old.xCell).val = 257 at view
  rw [(finalViews world).1] at view
  cases view

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterFor.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterFor.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := true) (.expr Solidity.Yul.Checks.RawCheckedAdapterFor.Old.clearExpr) (.some (.local Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flag)) .none (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterFor.packed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact packed.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Source.execS glob frame 21 nps ph (Solidity.Source.RStmt.forLoop (l := true) (.expr Solidity.Yul.Checks.RawCheckedAdapterFor.Old.clearExpr) (.some (.local Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flag)) .none (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) Solidity.Yul.Checks.RawCheckedAdapterFor.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlIfElse.cleanFalse),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceRefuses : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 (Solidity.Source.execS glob frame 21 nps ph (Solidity.Source.RStmt.forLoop (l := false) .brk (.some (.local Solidity.Yul.Checks.RawCheckedAdapterFor.Old.flag)) .none (.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items)) Solidity.Yul.Checks.RawCheckedAdapterFor.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env,world) =
 (.error (.stuck "for initializer"),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.initializer Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 0 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) ≠ Solidity.Yul.RawCheckedAdapterFor.run Solidity.Yul.Checks.RawCheckedAdapterFor.initializer Solidity.Yul.Checks.RawCheckedAdapterFor.Old.readFlag Solidity.Yul.Checks.RawCheckedAdapterFor.Old.body pipeline 21 (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (Solidity.Yul.RawCheckedAdapterFor.run initializer Old.readFlag Old.body pipeline 21 (Old.initial 2 257 2 world)).1 at tags
  rw [initializedRun pipeline world] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterFor.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterFor.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapterLoop.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapterFor
#print axioms Solidity.Yul.RawCheckedAdapterFor.correct
#print axioms Solidity.Yul.RawCheckedAdapterFor.lift_correct
#print axioms Solidity.Yul.RawCheckedAdapterFor.adapter
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.initializes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.clearedGuard
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.initializedRun
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.finalViews
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.packedRun
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.breakRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.continueRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.panicPropagates
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.viaIRPartial
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.pipelineCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.initializationMatters
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.sourceCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.sourceRefuses
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterFor.dirtyBoundary
