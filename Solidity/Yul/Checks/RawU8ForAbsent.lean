import Solidity.Yul.RawU8ForAbsent
import Solidity.Yul.Checks.RawCheckedGrowingAbsent
/-! Actual uint8 loops with neither condition nor post: mutation/break,
continue horizon, dirty frame retention and initializer error prefixes. -/
namespace Solidity.Yul.Checks.RawU8ForAbsent
namespace Old
export Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old
 (ctx clean canonical captured unsignedCtx timeout frame copiedClean dirtyFrame dirtyDropped dirtyInit dirtyPrepare dirtyDrop)
export Solidity.Yul.Checks.RawU8ForPost (initial body breakBody continueBody)
export Solidity.Yul.Checks.RawU8Statement (initial)
export Solidity.Yul.Checks.RawCheckedGrowingAbsent (mutatingBody bodyItems trueTest)
end Old
def packed := RawU8ForAbsent.adapter Old.ctx "n" [] false false _ Old.initial _ Old.mutatingBody
def literal := RawU8For.adapter Old.ctx "n" [] false false _ Old.initial _ _ Old.trueTest Old.mutatingBody
def program : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) (.local (.there .here)) (by rfl))
 .none .none (.block Old.bodyItems)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩

theorem runtimeSame : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx), Solidity.Yul.Checks.RawU8ForAbsent.packed.run pipeline fuel state = Solidity.Yul.Checks.RawU8ForAbsent.literal.run pipeline fuel state := by
  intro pipeline fuel state
  rfl

theorem normalRaw : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env), Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.initial Solidity.Yul.Checks.RawU8ForAbsent.Old.mutatingBody pipeline 10 (Solidity.Yul.Checks.RawU8ForAbsent.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8ForAbsent.Old.captured Solidity.Yul.Checks.RawU8ForAbsent.Old.copiedClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 9 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.trueTest 8 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have copy : Old.body.run pipeline 6 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.copiedClean world) := by rfl
  have stop : Old.breakBody.run pipeline 5 (Old.frame Old.copiedClean world) = (.ok (.break_ rfl),Old.frame Old.copiedClean world) := by rfl
  have branch : Old.mutatingBody.run pipeline 8 (Old.frame Old.clean world) = (.ok (.break_ rfl),Old.frame Old.copiedClean world) := by
    change RawCheckedAdapterSequence.runBlock
      (RawCheckedAdapterSequence.cons Old.body
        (RawCheckedAdapterSequence.cons Old.breakBody RawCheckedAdapterSequence.nil)) pipeline 8 (Old.frame Old.clean world) = _
    simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,RawCheckedAdapterSequence.runCons]
    rw [copy,stop]
  have iteration : RawCheckedAdapterLoop.run Old.trueTest Old.mutatingBody pipeline 9 (Old.frame Old.clean world) =
      (.ok (),Old.frame Old.copiedClean world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    rfl
  change RawU8For.run Old.initial Old.trueTest Old.mutatingBody pipeline 10 (Old.canonical world) = _
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.copiedClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env), Solidity.Yul.Checks.RawU8ForAbsent.packed.run pipeline 10 (Solidity.Yul.Checks.RawU8ForAbsent.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawU8ForAbsent.Old.captured Solidity.Yul.Checks.RawU8ForAbsent.Old.copiedClean world) := by
  intro pipeline world
  change ((RawU8ForAbsent.run Old.initial Old.mutatingBody pipeline 10 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawU8ForAbsent.run Old.initial Old.mutatingBody pipeline 10 (Old.canonical world)).2) = _
  rw [normalRaw]
  rfl

theorem continuedTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env), Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.initial Solidity.Yul.Checks.RawU8ForAbsent.Old.continueBody pipeline 4 (Solidity.Yul.Checks.RawU8ForAbsent.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawU8ForAbsent.Old.captured Solidity.Yul.Checks.RawU8ForAbsent.Old.clean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 3 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard2 : RawCondition.eval Old.trueTest 2 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have guard1 : RawCondition.eval Old.trueTest 1 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have guard0 : RawCondition.eval Old.trueTest 0 (Old.frame Old.clean world) = (.error .timeout,Old.frame Old.clean world) := by rfl
  have branch2 : Old.continueBody.run pipeline 2 (Old.frame Old.clean world) = (.ok (.continue_ rfl),Old.frame Old.clean world) := by rfl
  have branch1 : Old.continueBody.run pipeline 1 (Old.frame Old.clean world) = (.ok (.continue_ rfl),Old.frame Old.clean world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.trueTest Old.continueBody pipeline 3 (Old.frame Old.clean world) =
      (.error .timeout,Old.frame Old.clean world) := by
    rw [RawCheckedAdapterLoop.run,guard2,branch2]
    dsimp only
    rw [RawCheckedAdapterLoop.run.eq_def]
    dsimp only
    rw [guard1,branch1]
    dsimp only
    rw [RawCheckedAdapterLoop.run.eq_def]
    dsimp only
    rw [guard0]
    rfl
  change RawU8For.run Old.initial Old.trueTest Old.continueBody pipeline 4 (Old.canonical world) = _
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.error .timeout : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.clean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env), Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.initial Solidity.Yul.Checks.RawU8ForAbsent.Old.mutatingBody pipeline 0 (Solidity.Yul.Checks.RawU8ForAbsent.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawU8ForAbsent.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.initial Solidity.Yul.Checks.RawU8ForAbsent.Old.breakBody pipeline 8 (Solidity.Yul.Checks.RawU8ForAbsent.Old.initial 2 257 2 world)
 actual.1 = .ok () ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = false ∧ actual.2.world = world := by
  intro pipeline world
  have guard : RawCondition.eval Old.trueTest 6 (Old.dirtyFrame world) = (.ok true,Old.dirtyFrame world) := by
    unfold RawCondition.eval
    rw [Old.dirtyPrepare]
    rfl
  have branch : Old.breakBody.run pipeline 6 (Old.dirtyFrame world) = (.ok (.break_ rfl),Old.dirtyFrame world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.trueTest Old.breakBody pipeline 7 (Old.dirtyFrame world) =
      (.ok (),Old.dirtyFrame world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    rfl
  simp only [Solidity.Yul.Checks.RawCheckedGrowingAbsent.trueTest] at iteration
  unfold RawU8ForAbsent.run
  rw [RawU8For.run,Old.dirtyInit]
  dsimp only
  rw [iteration,Old.dirtyDrop]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8ForAbsent.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8ForAbsent.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawU8ForAbsent.program Solidity.Yul.Checks.RawU8ForAbsent.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawU8ForAbsent.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8ForAbsent.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env),
 (Solidity.Source.execS glob frame 10 nps ph Solidity.Yul.Checks.RawU8ForAbsent.program Solidity.Yul.Checks.RawU8ForAbsent.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawU8ForAbsent.Old.copiedClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 10 nps ph world).2,packedNormal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.timeout Solidity.Yul.Checks.RawU8ForAbsent.Old.mutatingBody .legacy 6 (Solidity.Yul.Checks.RawU8ForAbsent.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForAbsent.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawU8ForAbsent.Old.timeout Solidity.Yul.Checks.RawU8ForAbsent.Old.mutatingBody .viaIR 6 (Solidity.Yul.Checks.RawU8ForAbsent.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8ForAbsent
#print axioms Solidity.Yul.RawU8ForAbsent.correct
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.runtimeSame
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.normalRaw
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.packedNormal
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.continuedTimeout
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.zero
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.dirtyBreak
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.sourceAll
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8ForAbsent.viaIRPartial
