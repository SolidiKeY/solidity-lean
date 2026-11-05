import Solidity.Yul.RawU8GrowingSequence
import Solidity.Yul.Checks.RawU8Declaration
import Solidity.Yul.Checks.RawIntegerSequence
/-! Checked nonliteral uint8 declarations feed their real new value into a
mutating item tail. Pipeline prefix and dirty controls are kernel evidence. -/
namespace Solidity.Yul.Checks.RawU8GrowingSequence
namespace Old
export Solidity.Yul.Checks.RawU8Declaration.Old (ctx clean initial canonical assign timeout unsignedCtx grownX grownArg grownFlag)
export Solidity.Yul.Checks.RawU8Declaration (statement nextCell)
export Solidity.Yul.Checks.RawIntegerSequence (breakTail continueTail)
end Old
def expr : Solidity.Source.RExpr Old.ctx.env Old.unsignedCtx.tys LocalU8Expr.Ty :=
 .assign (.local (.there .here)) (.binary .add (.local .here) (.local .here))
def proof : LocalU8Expr.Supported Old.ctx.env Old.unsignedCtx.tys expr :=
 .assign (.there .here) (.add (.local .here) (.local .here))
def items : Solidity.Source.RItems Old.ctx.env [] false ⟨true,false⟩ Old.unsignedCtx.tys Old.unsignedCtx.tys :=
 .stmt (.expr expr) .nil
def tail : RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false items :=
 RawCheckedAdapterSequence.ofSequence (.uint8 proof .nil)
def changed : Solidity.Source.Locals Old.ctx.env.layout Old.ctx.tys :=
 .cons (.int 4 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def next (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.unsignedCtx :=
 RawFrame.capture (RawFrame.ofClean (.cons (.int 2 (by decide)) changed) world)
 (localWordCells Old.unsignedCtx (LocalValues.ofClean (.cons (.int 2 (by decide)) changed)))
def joined : Solidity.Source.RItems Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.unsignedCtx.tys := .stmt Old.statement items
def witness : Nonempty (RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false items) := ⟨tail⟩

theorem mutation : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env),
 Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8GrowingSequence.proof pipeline 5
 (Solidity.Yul.Checks.RawU8Declaration.next world) =
 (.ok (),Solidity.Yul.Checks.RawU8GrowingSequence.next world) := by
  intro pipeline world
  have coherent : RawCoherent.coherent (Solidity.Yul.Checks.RawU8Declaration.next world) = true :=
    (RawCoherent.coherent_iff _).mpr rfl
  unfold RawU8Statement.run RawU8Statement.localRun
  rw [RawCoherent.prepare_coherent _ coherent]
  have read : ((LocalState.ofClean
      ((Solidity.Yul.Checks.RawU8Declaration.next world).clean,
       (Solidity.Yul.Checks.RawU8Declaration.next world).world)).1.get
      (.here : Solidity.Source.Idx Old.unsignedCtx.tys LocalU8Expr.Ty)) =
      .clean (.int 2 (by decide)) := rfl
  cases pipeline <;>
    simp only [LocalU8Statement.step,proof,LocalU8Expr.assign_step,
      LocalU8Expr.add_legacy,LocalU8Expr.add_viaIR,LocalU8Expr.local_read,
      read,Except.bind,LocalOperations.u8Binary_clean] <;> rfl

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.tail pipeline 7 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world) = .inr (.ok .normal,Solidity.Yul.Checks.RawU8GrowingSequence.next world) := by
  intro pipeline world
  have initial : RawU8Declaration.run "n" Old.assign pipeline 6 (Old.canonical world) =
      .inr (Solidity.Yul.Checks.RawU8Declaration.next world) := by rfl
  rw [RawU8GrowingSequence.run,initial]
  change Sum.inr (RawCheckedControlSequence.run (.uint8 proof .nil) pipeline 6
    (Solidity.Yul.Checks.RawU8Declaration.next world)) = _
  rw [RawCheckedControlSequence.run_uint8,mutation]
  rfl

theorem breakProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.Old.breakTail pipeline 4 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world)) = (.ok (.brk Solidity.Yul.Checks.RawU8Declaration.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env,world)) := by
  intro pipeline world
  rfl

theorem continueProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.Old.continueTail pipeline 4 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world)) = (.ok (.cont Solidity.Yul.Checks.RawU8Declaration.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env,world)) := by
  intro pipeline world
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.tail pipeline 0 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawU8GrowingSequence.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.tail pipeline 4 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world) = .inr (.error .timeout,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawU8Declaration.next world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawU8Declaration.next world))) := by
  intro pipeline world
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), match Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.Old.breakTail pipeline 4 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr next => next.1 = .ok (.break_ rfl) ∧
 (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawU8GrowingSequence.Old.nextCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawU8GrowingSequence.Old.grownX).val = 257 ∧
 (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawU8GrowingSequence.Old.grownArg).val = 257 ∧
 (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawU8GrowingSequence.Old.grownFlag).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent next.2 = false ∧ next.2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env),
 Solidity.Yul.RawIntegerSequence.Coherent (Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world)) ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawU8GrowingSequence.joined Solidity.Yul.Checks.RawU8GrowingSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env,world) = Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.assign Solidity.Yul.Checks.RawU8GrowingSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawU8GrowingSequence.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  have actual := RawU8GrowingSequence.correct Old.ctx "n" [] false false _ Old.assign items tail
    glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)
  have clean : (Old.canonical world).clean = Old.clean := rfl
  have worldSame : (Old.canonical world).world = world := rfl
  simpa only [clean,worldSame,joined,Solidity.Yul.Checks.RawU8Declaration.statement] using actual

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env),
 (Solidity.Source.execItems glob frame 7 nps ph Solidity.Yul.Checks.RawU8GrowingSequence.joined Solidity.Yul.Checks.RawU8GrowingSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env,world) =
 (.ok (.normal (Solidity.Yul.Checks.RawU8GrowingSequence.next world).clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 7 nps ph world).2,normal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), match Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.timeout Solidity.Yul.Checks.RawU8GrowingSequence.tail .legacy 6 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.initial 257 2 1 world) with
 | .inr _ => False
 | .inl failure => failure.1 = .timeout ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧
 failure.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingSequence.Old.ctx.env), match Solidity.Yul.RawU8GrowingSequence.run Solidity.Yul.Checks.RawU8GrowingSequence.Old.timeout Solidity.Yul.Checks.RawU8GrowingSequence.tail .viaIR 6 (Solidity.Yul.Checks.RawU8GrowingSequence.Old.initial 257 2 1 world) with
 | .inr _ => False
 | .inl failure => failure.1 = .timeout ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 failure.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8GrowingSequence
#print axioms Solidity.Yul.RawU8GrowingSequence.correct
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.normal
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.breakProjection
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.continueProjection
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.zero
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.tailTimeout
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.dirtyBreak
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.sourceAll
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.viaIRPartial

#print axioms Solidity.Yul.Checks.RawU8GrowingSequence.mutation
