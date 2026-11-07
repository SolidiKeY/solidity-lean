import Solidity.Yul.RawIntegerSequence
import Solidity.Yul.Checks.RawPreparedInteger

/-! Concrete integer-declaration/tail computations. Kernel controls only;
no general integer initializer or enclosing block admission follows. -/
namespace Solidity.Yul.Checks.RawIntegerSequence
namespace Old
export Solidity.Yul.Checks.RawPreparedInteger.Old (ctx env clean canonical unsignedCtx signedCtx grownX grownArg grownFlag)
export Solidity.Yul.Checks.RawPreparedInteger (boundU boundS copyExpr copyProof nextUnsigned afterCopy changed)
end Old
def items : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.unsignedCtx.tys Old.unsignedCtx.tys :=
 .stmt (.expr Old.copyExpr) .nil
def tail : RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false items :=
 RawCheckedAdapterSequence.ofSequence (.uint8 Old.copyProof .nil)
def breakTail : RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false (.stmt .brk .nil) :=
 RawCheckedAdapterSequence.ofSequence (.cons .break_ .nil)
def continueTail : RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false (.stmt .cont .nil) :=
 RawCheckedAdapterSequence.ofSequence (.cons .continue_ .nil)
def signedTail : RawCheckedAdapterSequence.Items Old.signedCtx [] false false .nil := RawCheckedAdapterSequence.nil
def joined : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.unsignedCtx.tys :=
 .stmt Solidity.Yul.Checks.RawPreparedInteger.statement items
def witness : Nonempty (RawCheckedAdapterSequence.Items Old.unsignedCtx [] false false items) := ⟨tail⟩

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail pipeline 5 (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world) = .inr (.ok .normal,Solidity.Yul.Checks.RawIntegerSequence.Old.afterCopy world) := by
  intro pipeline world
  rfl

theorem breakProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.breakTail pipeline 3 (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world)) = (.ok (.brk Solidity.Yul.Checks.RawIntegerSequence.Old.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem continueProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.continueTail pipeline 3 (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world)) = (.ok (.cont Solidity.Yul.Checks.RawIntegerSequence.Old.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem preTimeouts : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail pipeline 0 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) ∧ Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail pipeline 2 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail pipeline 3 (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world) = .inr (.error .timeout,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawIntegerSequence.Old.nextUnsigned world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawIntegerSequence.Old.nextUnsigned world))) := by
  intro pipeline world
  rfl

theorem dirtyBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), match Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.breakTail pipeline 3 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr next => next.1 = .ok (.break_ rfl) ∧
   (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawIntegerSequence.Old.grownX).val = 2 ∧
   (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawIntegerSequence.Old.grownArg).val = 257 ∧
   (Solidity.Yul.RawFrame.view next.2 Solidity.Yul.Checks.RawIntegerSequence.Old.grownFlag).val = 2 ∧
   Solidity.Yul.RawCoherent.coherent next.2 = false ∧ next.2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem signed : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env), Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawIntegerSequence.run Solidity.Yul.Checks.RawPreparedInteger.Old.signed8 (-128) Solidity.Yul.Checks.RawIntegerSequence.Old.boundS Solidity.Yul.Checks.RawIntegerSequence.signedTail pipeline 3 (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world)) = (.ok (.normal (Solidity.Yul.Checks.RawPreparedInteger.nextSigned world).clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env),
 Solidity.Yul.RawIntegerSequence.Coherent (Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world)) ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawIntegerSequence.joined Solidity.Yul.Checks.RawIntegerSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world) = Solidity.Yul.RawIntegerSequence.project (Solidity.Yul.RawIntegerSequence.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerSequence.Old.boundU Solidity.Yul.Checks.RawIntegerSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawIntegerSequence.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact RawIntegerSequence.correct Old.ctx "n" Solidity.Source.IntTy.u8 255 Old.boundU
    [] false false items tail glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerSequence.Old.env),
 (Solidity.Source.execItems glob frame 5 nps ph Solidity.Yul.Checks.RawIntegerSequence.joined Solidity.Yul.Checks.RawIntegerSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world) =
 (.ok (.normal (Solidity.Yul.Checks.RawIntegerSequence.Old.afterCopy world).clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerSequence.Old.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 5 nps ph world).2,normal]
  rfl
end Solidity.Yul.Checks.RawIntegerSequence

#print axioms Solidity.Yul.RawIntegerSequence.correct
#print axioms Solidity.Yul.Checks.RawIntegerSequence.normal
#print axioms Solidity.Yul.Checks.RawIntegerSequence.breakProjection
#print axioms Solidity.Yul.Checks.RawIntegerSequence.continueProjection
#print axioms Solidity.Yul.Checks.RawIntegerSequence.preTimeouts
#print axioms Solidity.Yul.Checks.RawIntegerSequence.tailTimeout
#print axioms Solidity.Yul.Checks.RawIntegerSequence.dirtyBreak
#print axioms Solidity.Yul.Checks.RawIntegerSequence.signed
#print axioms Solidity.Yul.Checks.RawIntegerSequence.sourceAll
#print axioms Solidity.Yul.Checks.RawIntegerSequence.sourceNormal
