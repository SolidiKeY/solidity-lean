import Solidity.Yul.RawU8ForPost
import Solidity.Yul.Checks.RawU8GrowingBlock
/-! A real uint8 initializer, new-local copy body, outer-Boolean post, and scope
exit. Kernel controls distinguish partial initializer and reached post errors. -/
namespace Solidity.Yul.Checks.RawU8ForPost
namespace Old
export Solidity.Yul.Checks.RawU8Declaration.Old (ctx clean initial canonical unsignedCtx timeout)
export Solidity.Yul.Checks.RawIntegerSequence (tail breakTail continueTail)
export Solidity.Yul.Checks.RawPreparedInteger.Old (captured)
end Old
def initial : LocalU8Expr.Supported Old.ctx.env Old.ctx.tys (.local (.there .here)) := .local (.there .here)
def flag : Solidity.Source.Idx Old.unsignedCtx.tys .bool := .there (.there (.there .here))
def test : LocalBoolControl.Supported Old.ctx.env Old.unsignedCtx.tys (.local flag) := .base (.local flag)
def clear : LocalBoolControl.Supported Old.ctx.env Old.unsignedCtx.tys (.assign (.local flag) (.bool false)) :=
 .assign flag (.base (.literal false))
def falseTest : LocalBoolControl.Supported Old.ctx.env Old.unsignedCtx.tys (.bool false) := .base (.literal false)
def body := RawCheckedAdapterSequence.block Old.tail
def breakBody := RawCheckedAdapter.fromAdapter (RawSourceAdapter.body (ctx := Old.unsignedCtx) (returns := []) (modifier := false) (u := false) .break_)
def continueBody := RawCheckedAdapter.fromAdapter (RawSourceAdapter.body (ctx := Old.unsignedCtx) (returns := []) (modifier := false) (u := false) .continue_)
def afterClean : Solidity.Source.Locals Old.ctx.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def continuedClean : Solidity.Source.Locals Old.ctx.env.layout Old.ctx.tys :=
 .cons (.int 1 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def frame (locals : Solidity.Source.Locals Old.ctx.env.layout Old.ctx.tys) (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.unsignedCtx :=
 RawFrame.capture (RawFrame.ofClean (.cons (.int 2 (by decide)) locals) world)
 (localWordCells Old.unsignedCtx (LocalValues.ofClean (.cons (.int 2 (by decide)) locals)))
def copiedClean := Solidity.Yul.Checks.RawU8Declaration.changed
def deep := LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not test)))))))))
def deepPost := LocalBoolControl.Supported.or clear deep
def packed := RawU8ForPost.adapter Old.ctx "n" [] false false _ initial _ _ _ test clear body
def program : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) (.local (.there .here)) (by rfl))
 (.some (.local flag)) (.some (.assign (.local flag) (.bool false))) (.block Solidity.Yul.Checks.RawIntegerSequence.items)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩

def dirtyValues : LocalValues Old.ctx.env Old.unsignedCtx.tys :=
 (.scalar (LocalOperations.u8Shape Old.ctx.env) (word 257),
  (.scalar (LocalOperations.u8Shape Old.ctx.env) (word 2),
   (.scalar (LocalOperations.u8Shape Old.ctx.env) (word 257),
    (.scalar (LocalOperations.boolShape Old.ctx.env) (word 2),()))))
def dirtyFrame (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.unsignedCtx :=
 RawCoherent.capture (RawFrame.ofClean (.cons (.int 0 (by decide)) Old.clean) world)
 (dirtyValues,world)
def dirtyDropped (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.ctx :=
 RawDeclarationFrame.ofSnapshot ⟨Old.clean,dirtyValues.2,world⟩

theorem dirtyInit : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8ForPost.initial pipeline 7 (Solidity.Yul.Checks.RawU8ForPost.Old.initial 2 257 2 world) = .inr (Solidity.Yul.Checks.RawU8ForPost.dirtyFrame world) := by
  intro pipeline world
  rfl

theorem dirtyPrepare : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawU8ForPost.dirtyFrame world) = (Solidity.Yul.Checks.RawU8ForPost.dirtyValues,world) := by
  intro world
  rfl

theorem dirtyGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawU8ForPost.test 6 (Solidity.Yul.Checks.RawU8ForPost.dirtyFrame world) = (.ok true,Solidity.Yul.Checks.RawU8ForPost.dirtyFrame world) := by
  intro world
  unfold RawCondition.eval
  rw [dirtyPrepare]
  rfl

theorem dirtyDrop : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawU8ForPost.dirtyFrame world) = Solidity.Yul.Checks.RawU8ForPost.dirtyDropped world := by
  intro world
  unfold RawTypedScope.drop
  rw [dirtyPrepare]
  rfl
theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.body pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.afterClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" initial pipeline 7 (Old.canonical world) = .inr (frame Old.clean world) := by rfl
  have guard : RawCondition.eval test 6 (frame Old.clean world) = (.ok true,frame Old.clean world) := by rfl
  have copy : body.run pipeline 6 (frame Old.clean world) = (.ok .normal,frame copiedClean world) := by rfl
  have post : RawSourceForPost.discard clear 6 (frame copiedClean world) = (.ok (),frame afterClean world) := by rfl
  have stop : RawCondition.eval test 5 (frame afterClean world) = (.ok false,frame afterClean world) := by rfl
  have iteration : RawCheckedForPost.run test clear body pipeline 7 (frame Old.clean world) = (.ok (),frame afterClean world) := by
    rw [RawCheckedForPost.run,guard,copy]
    dsimp only
    rw [RawSourceForPost.after,post,RawCheckedForPost.run.eq_def]
    dsimp only
    rw [stop]
    rfl
  rw [RawU8ForPost.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (frame afterClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.Checks.RawU8ForPost.packed.run pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.afterClean world) := by
  intro pipeline world
  change ((RawU8ForPost.run initial test clear body pipeline 8 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawU8ForPost.run initial test clear body pipeline 8 (Old.canonical world)).2) = _
  rw [normal]
  rfl

theorem falseGuard : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.falseTest Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.body pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.Old.clean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" initial pipeline 7 (Old.canonical world) = .inr (frame Old.clean world) := by rfl
  have guard : RawCondition.eval falseTest 6 (frame Old.clean world) = (.ok false,frame Old.clean world) := by rfl
  have iteration : RawCheckedForPost.run falseTest clear body pipeline 7 (frame Old.clean world) = (.ok (),frame Old.clean world) := by
    rw [RawCheckedForPost.run,guard]
    rfl
  rw [RawU8ForPost.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (frame Old.clean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem broken : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.breakBody pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.Old.clean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" initial pipeline 7 (Old.canonical world) = .inr (frame Old.clean world) := by rfl
  have guard : RawCondition.eval test 6 (frame Old.clean world) = (.ok true,frame Old.clean world) := by rfl
  have stop : breakBody.run pipeline 6 (frame Old.clean world) = (.ok (.break_ rfl),frame Old.clean world) := by rfl
  have iteration : RawCheckedForPost.run test clear breakBody pipeline 7 (frame Old.clean world) = (.ok (),frame Old.clean world) := by
    rw [RawCheckedForPost.run,guard,stop]
    rfl
  rw [RawU8ForPost.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (frame Old.clean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem continued : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.continueBody pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.continuedClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" initial pipeline 7 (Old.canonical world) = .inr (frame Old.clean world) := by rfl
  have guard : RawCondition.eval test 6 (frame Old.clean world) = (.ok true,frame Old.clean world) := by rfl
  have branch : continueBody.run pipeline 6 (frame Old.clean world) = (.ok (.continue_ rfl),frame Old.clean world) := by rfl
  have post : RawSourceForPost.discard clear 6 (frame Old.clean world) = (.ok (),frame continuedClean world) := by rfl
  have stop : RawCondition.eval test 5 (frame continuedClean world) = (.ok false,frame continuedClean world) := by rfl
  have iteration : RawCheckedForPost.run test clear continueBody pipeline 7 (frame Old.clean world) = (.ok (),frame continuedClean world) := by
    rw [RawCheckedForPost.run,guard,branch]
    dsimp only
    rw [RawSourceForPost.after,post,RawCheckedForPost.run.eq_def]
    dsimp only
    rw [stop]
    rfl
  rw [RawU8ForPost.run,init]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (frame continuedClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.body pipeline 0 (Solidity.Yul.Checks.RawU8ForPost.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawU8ForPost.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem postTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env), Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.deepPost Solidity.Yul.Checks.RawU8ForPost.body pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawU8ForPost.Old.captured Solidity.Yul.Checks.RawU8ForPost.afterClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" initial pipeline 7 (Old.canonical world) = .inr (frame Old.clean world) := by rfl
  have guard : RawCondition.eval test 6 (frame Old.clean world) = (.ok true,frame Old.clean world) := by rfl
  have copy : body.run pipeline 6 (frame Old.clean world) = (.ok .normal,frame copiedClean world) := by rfl
  have post : RawSourceForPost.discard deepPost 6 (frame copiedClean world) = (.error .timeout,frame afterClean world) := by rfl
  have iteration : RawCheckedForPost.run test deepPost body pipeline 7 (frame Old.clean world) = (.error .timeout,frame afterClean world) := by
    rw [RawCheckedForPost.run,guard,copy]
    dsimp only
    rw [RawSourceForPost.after,post]
    rfl
  rw [RawU8ForPost.run,init]
  dsimp only
  rw [iteration]
  change ((.error .timeout : Solidity.Source.R Unit),RawTypedScope.drop (frame afterClean world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.initial Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.breakBody pipeline 8 (Solidity.Yul.Checks.RawU8ForPost.Old.initial 2 257 2 world)
 actual.1 = .ok () ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = false ∧ actual.2.world = world := by
  intro pipeline world
  have branch : breakBody.run pipeline 6 (dirtyFrame world) = (.ok (.break_ rfl),dirtyFrame world) := by rfl
  have iteration : RawCheckedForPost.run test clear breakBody pipeline 7 (dirtyFrame world) = (.ok (),dirtyFrame world) := by
    rw [RawCheckedForPost.run,dirtyGuard,branch]
    rfl
  change (RawU8ForPost.run initial test clear breakBody pipeline 8 (Old.initial 2 257 2 world)).1 = .ok () ∧ _
  rw [RawU8ForPost.run,dirtyInit]
  dsimp only
  rw [iteration,dirtyDrop]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8ForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawU8ForPost.program Solidity.Yul.Checks.RawU8ForPost.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawU8ForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8ForPost.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.RawU8ForPost.program Solidity.Yul.Checks.RawU8ForPost.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawU8ForPost.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 8 nps ph world).2,packedNormal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.Old.timeout Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.body .legacy 6 (Solidity.Yul.Checks.RawU8ForPost.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8ForPost.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForPost.run Solidity.Yul.Checks.RawU8ForPost.Old.timeout Solidity.Yul.Checks.RawU8ForPost.test Solidity.Yul.Checks.RawU8ForPost.clear Solidity.Yul.Checks.RawU8ForPost.body .viaIR 6 (Solidity.Yul.Checks.RawU8ForPost.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8ForPost
#print axioms Solidity.Yul.RawU8ForPost.correct
#print axioms Solidity.Yul.Checks.RawU8ForPost.normal
#print axioms Solidity.Yul.Checks.RawU8ForPost.packedNormal
#print axioms Solidity.Yul.Checks.RawU8ForPost.falseGuard
#print axioms Solidity.Yul.Checks.RawU8ForPost.broken
#print axioms Solidity.Yul.Checks.RawU8ForPost.continued
#print axioms Solidity.Yul.Checks.RawU8ForPost.zero
#print axioms Solidity.Yul.Checks.RawU8ForPost.postTimeout
#print axioms Solidity.Yul.Checks.RawU8ForPost.dirtyBreak
#print axioms Solidity.Yul.Checks.RawU8ForPost.sourceAll
#print axioms Solidity.Yul.Checks.RawU8ForPost.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8ForPost.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8ForPost.viaIRPartial

#print axioms Solidity.Yul.Checks.RawU8ForPost.dirtyInit
#print axioms Solidity.Yul.Checks.RawU8ForPost.dirtyPrepare
#print axioms Solidity.Yul.Checks.RawU8ForPost.dirtyGuard
#print axioms Solidity.Yul.Checks.RawU8ForPost.dirtyDrop
