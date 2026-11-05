import Solidity.Yul.RawU8For
import Solidity.Yul.Checks.RawU8ForPost
/-! Concrete uint8-initialized no-post loops with body mutation, control and
partial errors. Kernel evidence only; general admission remains open. -/
namespace Solidity.Yul.Checks.RawU8For
namespace Old
export Solidity.Yul.Checks.RawU8ForPost.Old (ctx clean initial canonical unsignedCtx timeout captured)
export Solidity.Yul.Checks.RawU8ForPost
 (initial test clear falseTest body breakBody continueBody frame copiedClean afterClean continuedClean deepPost dirtyFrame dirtyDropped dirtyInit dirtyPrepare dirtyDrop)
end Old
def clearBody := RawCheckedAdapter.fromAdapter (RawSourceAdapter.body (ctx := Old.unsignedCtx) (returns := []) (modifier := false) (u := false)
 (RawLoopBody.Supported.plain (RawSequence.Supported.cons (RawSource.Supported.expression Old.clear) .nil)))
def deepBody := RawCheckedAdapter.fromAdapter (RawSourceAdapter.body (ctx := Old.unsignedCtx) (returns := []) (modifier := false) (u := false)
 (RawLoopBody.Supported.plain (RawSequence.Supported.cons (RawSource.Supported.expression Old.deepPost) .nil)))
def bodyItems : Solidity.Source.RItems Old.ctx.env [] false ⟨true,false⟩ Old.unsignedCtx.tys Old.unsignedCtx.tys :=
 .stmt (.block Solidity.Yul.Checks.RawIntegerSequence.items)
 (.stmt (.block (.stmt (.expr (.assign (.local Solidity.Yul.Checks.RawU8ForPost.flag) (.bool false))) .nil)) .nil)
def body := RawCheckedAdapterSequence.block
 (RawCheckedAdapterSequence.cons Old.body (RawCheckedAdapterSequence.cons clearBody RawCheckedAdapterSequence.nil))
def continueBody := RawCheckedAdapterSequence.block
 (RawCheckedAdapterSequence.cons clearBody (RawCheckedAdapterSequence.cons Old.continueBody RawCheckedAdapterSequence.nil))
def failingBody := RawCheckedAdapterSequence.block
 (RawCheckedAdapterSequence.cons Old.body (RawCheckedAdapterSequence.cons deepBody RawCheckedAdapterSequence.nil))
def packed := RawU8For.adapter Old.ctx "n" [] false false _ Old.initial _ _ Old.test body
def program : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) (.local (.there .here)) (by rfl))
 (.some (.local Solidity.Yul.Checks.RawU8ForPost.flag)) .none (.block bodyItems)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.body pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.afterClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 11 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.test 10 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have copy : Old.body.run pipeline 8 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.copiedClean world) := by rfl
  have clear : clearBody.run pipeline 7 (Old.frame Old.copiedClean world) = (.ok .normal,Old.frame Old.afterClean world) := by rfl
  have branch : body.run pipeline 10 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.afterClean world) := by
    change RawCheckedAdapterSequence.runBlock
      (RawCheckedAdapterSequence.cons Old.body
        (RawCheckedAdapterSequence.cons clearBody RawCheckedAdapterSequence.nil)) pipeline 10 (Old.frame Old.clean world) = _
    simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,RawCheckedAdapterSequence.runCons]
    rw [copy,clear]
    all_goals rfl
  have stop : RawCondition.eval Old.test 9 (Old.frame Old.afterClean world) = (.ok false,Old.frame Old.afterClean world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.test body pipeline 11 (Old.frame Old.clean world) = (.ok (),Old.frame Old.afterClean world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    dsimp only
    rw [RawCheckedAdapterLoop.run.eq_def]
    dsimp only
    rw [stop]
    rfl
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.afterClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.Checks.RawU8For.packed.run pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.afterClean world) := by
  intro pipeline world
  change ((RawU8For.run Old.initial Old.test body pipeline 12 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawU8For.run Old.initial Old.test body pipeline 12 (Old.canonical world)).2) = _
  rw [normal]
  rfl

theorem falseGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.falseTest Solidity.Yul.Checks.RawU8For.body pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.clean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 11 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.falseTest 10 (Old.frame Old.clean world) = (.ok false,Old.frame Old.clean world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.falseTest body pipeline 11 (Old.frame Old.clean world) = (.ok (),Old.frame Old.clean world) := by
    rw [RawCheckedAdapterLoop.run,guard]
    rfl
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.clean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem broken : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.Old.breakBody pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.clean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 11 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.test 10 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have branch : Old.breakBody.run pipeline 10 (Old.frame Old.clean world) = (.ok (.break_ rfl),Old.frame Old.clean world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.test Old.breakBody pipeline 11 (Old.frame Old.clean world) = (.ok (),Old.frame Old.clean world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    rfl
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.clean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem continued : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.continueBody pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.continuedClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 11 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.test 10 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have clear : clearBody.run pipeline 8 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.continuedClean world) := by rfl
  have cont : Old.continueBody.run pipeline 7 (Old.frame Old.continuedClean world) = (.ok (.continue_ rfl),Old.frame Old.continuedClean world) := by rfl
  have branch : continueBody.run pipeline 10 (Old.frame Old.clean world) = (.ok (.continue_ rfl),Old.frame Old.continuedClean world) := by
    change RawCheckedAdapterSequence.runBlock
      (RawCheckedAdapterSequence.cons clearBody
        (RawCheckedAdapterSequence.cons Old.continueBody RawCheckedAdapterSequence.nil)) pipeline 10 (Old.frame Old.clean world) = _
    simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,RawCheckedAdapterSequence.runCons]
    rw [clear,cont]
    all_goals rfl
  have stop : RawCondition.eval Old.test 9 (Old.frame Old.continuedClean world) = (.ok false,Old.frame Old.continuedClean world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.test continueBody pipeline 11 (Old.frame Old.clean world) = (.ok (),Old.frame Old.continuedClean world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    dsimp only
    rw [RawCheckedAdapterLoop.run.eq_def]
    dsimp only
    rw [stop]
    rfl
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.continuedClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem bodyTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.failingBody pipeline 12 (Solidity.Yul.Checks.RawU8For.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawU8For.Old.captured Solidity.Yul.Checks.RawU8For.Old.afterClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 11 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval Old.test 10 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have copy : Old.body.run pipeline 8 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.copiedClean world) := by rfl
  have fail : deepBody.run pipeline 7 (Old.frame Old.copiedClean world) = (.error .timeout,Old.frame Old.afterClean world) := by rfl
  have branch : failingBody.run pipeline 10 (Old.frame Old.clean world) = (.error .timeout,Old.frame Old.afterClean world) := by
    change RawCheckedAdapterSequence.runBlock
      (RawCheckedAdapterSequence.cons Old.body
        (RawCheckedAdapterSequence.cons deepBody RawCheckedAdapterSequence.nil)) pipeline 10 (Old.frame Old.clean world) = _
    simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,RawCheckedAdapterSequence.runCons]
    rw [copy,fail]
    all_goals rfl
  have iteration : RawCheckedAdapterLoop.run Old.test failingBody pipeline 11 (Old.frame Old.clean world) = (.error .timeout,Old.frame Old.afterClean world) := by
    rw [RawCheckedAdapterLoop.run,guard,branch]
    rfl
  rw [RawU8For.run,init]
  dsimp only
  rw [iteration]
  change ((.error .timeout : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.afterClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env), Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.body pipeline 0 (Solidity.Yul.Checks.RawU8For.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawU8For.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env),
 let actual := Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.initial Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.Old.breakBody pipeline 8 (Solidity.Yul.Checks.RawU8For.Old.initial 2 257 2 world)
 actual.1 = .ok () ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = false ∧ actual.2.world = world := by
  intro pipeline world
  have branch : Old.breakBody.run pipeline 6 (Old.dirtyFrame world) = (.ok (.break_ rfl),Old.dirtyFrame world) := by rfl
  have iteration : RawCheckedAdapterLoop.run Old.test Old.breakBody pipeline 7 (Old.dirtyFrame world) = (.ok (),Old.dirtyFrame world) := by
    rw [RawCheckedAdapterLoop.run,Solidity.Yul.Checks.RawU8ForPost.dirtyGuard,branch]
    rfl
  change (RawU8For.run Old.initial Old.test Old.breakBody pipeline 8 (Old.initial 2 257 2 world)).1 = .ok () ∧ _
  rw [RawU8For.run,Old.dirtyInit]
  dsimp only
  rw [iteration,Old.dirtyDrop]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8For.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8For.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8For.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8For.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawU8For.program Solidity.Yul.Checks.RawU8For.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8For.Old.ctx.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawU8For.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8For.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8For.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8For.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env),
 (Solidity.Source.execS glob frame 12 nps ph Solidity.Yul.Checks.RawU8For.program Solidity.Yul.Checks.RawU8For.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8For.Old.ctx.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawU8For.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8For.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 12 nps ph world).2,packedNormal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env),
 let actual := Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.timeout Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.body .legacy 6 (Solidity.Yul.Checks.RawU8For.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8For.Old.ctx.env),
 let actual := Solidity.Yul.RawU8For.run Solidity.Yul.Checks.RawU8For.Old.timeout Solidity.Yul.Checks.RawU8For.Old.test Solidity.Yul.Checks.RawU8For.body .viaIR 6 (Solidity.Yul.Checks.RawU8For.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8For
#print axioms Solidity.Yul.RawU8For.correct
#print axioms Solidity.Yul.Checks.RawU8For.normal
#print axioms Solidity.Yul.Checks.RawU8For.packedNormal
#print axioms Solidity.Yul.Checks.RawU8For.falseGuard
#print axioms Solidity.Yul.Checks.RawU8For.broken
#print axioms Solidity.Yul.Checks.RawU8For.continued
#print axioms Solidity.Yul.Checks.RawU8For.bodyTimeout
#print axioms Solidity.Yul.Checks.RawU8For.zero
#print axioms Solidity.Yul.Checks.RawU8For.dirtyBreak
#print axioms Solidity.Yul.Checks.RawU8For.sourceAll
#print axioms Solidity.Yul.Checks.RawU8For.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8For.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8For.viaIRPartial
