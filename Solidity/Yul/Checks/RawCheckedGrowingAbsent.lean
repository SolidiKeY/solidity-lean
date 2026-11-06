import Solidity.Yul.RawCheckedGrowingAbsent
import Solidity.Yul.Checks.RawU8ForPost
/-! Concrete context-growing omitted-guard loops consume actual uint8 producers.
Transport preserves runtime exactly; general loop admission remains open. -/
namespace Solidity.Yul.Checks.RawCheckedGrowingAbsent
namespace Old
export Solidity.Yul.Checks.RawU8ForPost.Old (ctx clean canonical initial captured unsignedCtx timeout)
export Solidity.Yul.Checks.RawU8ForPost (initial clear body breakBody frame copiedClean dirtyFrame dirtyDropped dirtyInit dirtyPrepare dirtyDrop)
end Old
def trueTest : LocalBoolControl.Supported Old.ctx.env Old.unsignedCtx.tys (.bool true) := .base (.literal true)
def bodyItems := Solidity.Source.RItems.stmt
 (.block Solidity.Yul.Checks.RawIntegerSequence.items) (.stmt (.brk : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.unsignedCtx.tys Old.unsignedCtx.tys) .nil)
def mutatingBody := RawCheckedAdapterSequence.block
 (RawCheckedAdapterSequence.cons Old.body
  (RawCheckedAdapterSequence.cons Old.breakBody RawCheckedAdapterSequence.nil))
def literal := RawU8ForPost.adapter Old.ctx "n" [] false false _ Old.initial _ _ _ trueTest Old.clear mutatingBody
def omitted := RawCheckedGrowingAbsent.adapter literal
def breakLiteral := RawU8ForPost.adapter Old.ctx "n" [] false false _ Old.initial _ _ _ trueTest Old.clear Old.breakBody
def breakOmitted := RawCheckedGrowingAbsent.adapter breakLiteral
def partialLiteral := RawU8ForPost.adapter Old.ctx "n" [] false false _ Old.timeout _ _ _ trueTest Old.clear mutatingBody
def partialOmitted := RawCheckedGrowingAbsent.adapter partialLiteral
def program : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) (.local (.there .here)) (by rfl))
 .none (.some (.assign (.local Solidity.Yul.Checks.RawU8ForPost.flag) (.bool false))) (.block bodyItems)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨omitted⟩

theorem runtimeSame : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx), Solidity.Yul.Checks.RawCheckedGrowingAbsent.omitted.run pipeline fuel state = Solidity.Yul.Checks.RawCheckedGrowingAbsent.literal.run pipeline fuel state := by
  intro pipeline fuel state
  rfl

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env), Solidity.Yul.Checks.RawCheckedGrowingAbsent.omitted.run pipeline 10 (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.captured Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.copiedClean world) := by
  intro pipeline world
  have init : RawU8Declaration.run "n" Old.initial pipeline 9 (Old.canonical world) = .inr (Old.frame Old.clean world) := by rfl
  have guard : RawCondition.eval trueTest 8 (Old.frame Old.clean world) = (.ok true,Old.frame Old.clean world) := by rfl
  have copy : Old.body.run pipeline 6 (Old.frame Old.clean world) = (.ok .normal,Old.frame Old.copiedClean world) := by rfl
  have stop : Old.breakBody.run pipeline 5 (Old.frame Old.copiedClean world) = (.ok (.break_ rfl),Old.frame Old.copiedClean world) := by rfl
  have branch : mutatingBody.run pipeline 8 (Old.frame Old.clean world) = (.ok (.break_ rfl),Old.frame Old.copiedClean world) := by
    change RawCheckedAdapterSequence.runBlock
      (RawCheckedAdapterSequence.cons Old.body
        (RawCheckedAdapterSequence.cons Old.breakBody RawCheckedAdapterSequence.nil)) pipeline 8 (Old.frame Old.clean world) = _
    simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,
      RawCheckedAdapterSequence.runCons]
    rw [copy,stop]
  have iteration : RawCheckedForPost.run trueTest Old.clear mutatingBody pipeline 9 (Old.frame Old.clean world) =
      (.ok (),Old.frame Old.copiedClean world) := by
    rw [RawCheckedForPost.run,guard,branch]
    rfl
  have actual : RawU8ForPost.run Old.initial trueTest Old.clear mutatingBody pipeline 10 (Old.canonical world) =
      (.ok (),Old.captured Old.copiedClean world) := by
    rw [RawU8ForPost.run,init]
    dsimp only
    rw [iteration]
    change ((.ok () : Solidity.Source.R Unit),RawTypedScope.drop (Old.frame Old.copiedClean world)) = _
    unfold RawTypedScope.drop
    rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
    rfl
  change ((RawU8ForPost.run Old.initial trueTest Old.clear mutatingBody pipeline 10 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawU8ForPost.run Old.initial trueTest Old.clear mutatingBody pipeline 10 (Old.canonical world)).2) = _
  rw [actual]
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env), Solidity.Yul.Checks.RawCheckedGrowingAbsent.omitted.run pipeline 0 (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env),
 let actual := Solidity.Yul.Checks.RawCheckedGrowingAbsent.breakOmitted.run pipeline 8 (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.initial 2 257 2 world)
 actual.1 = .ok .normal ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = false ∧ actual.2.world = world := by
  intro pipeline world
  have guard : RawCondition.eval trueTest 6 (Old.dirtyFrame world) = (.ok true,Old.dirtyFrame world) := by
    unfold RawCondition.eval
    rw [Old.dirtyPrepare]
    rfl
  have branch : Old.breakBody.run pipeline 6 (Old.dirtyFrame world) = (.ok (.break_ rfl),Old.dirtyFrame world) := by rfl
  have iteration : RawCheckedForPost.run trueTest Old.clear Old.breakBody pipeline 7 (Old.dirtyFrame world) =
      (.ok (),Old.dirtyFrame world) := by
    rw [RawCheckedForPost.run,guard,branch]
    rfl
  dsimp only [breakOmitted,RawCheckedGrowingAbsent.adapter,breakLiteral,RawU8ForPost.adapter]
  rw [RawU8ForPost.run,Old.dirtyInit]
  dsimp only
  rw [iteration,Old.dirtyDrop]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedGrowingAbsent.omitted.run glob.pipeline fuel (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawCheckedGrowingAbsent.program Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedGrowingAbsent.omitted.run glob.pipeline fuel (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact omitted.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env),
 (Solidity.Source.execS glob frame 10 nps ph Solidity.Yul.Checks.RawCheckedGrowingAbsent.program Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.copiedClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 10 nps ph world).2,normal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env),
 let actual := Solidity.Yul.Checks.RawCheckedGrowingAbsent.partialOmitted.run .legacy 6 (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.ctx.env),
 let actual := Solidity.Yul.Checks.RawCheckedGrowingAbsent.partialOmitted.run .viaIR 6 (Solidity.Yul.Checks.RawCheckedGrowingAbsent.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawCheckedGrowingAbsent
#print axioms Solidity.Yul.RawCheckedGrowingAbsent.correct
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.runtimeSame
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.normal
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.zero
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.dirtyBreak
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.sourceAll
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.sourceNormal
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.legacyPartial
#print axioms Solidity.Yul.Checks.RawCheckedGrowingAbsent.viaIRPartial
