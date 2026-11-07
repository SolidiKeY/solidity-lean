import Solidity.Yul.RawGrowingSequence
import Solidity.Yul.Checks.RawPreparedDeclaration
/-! Kernel-only joined declaration/tail controls. Source item sequencing and
control restoration are concrete; final block scope closure remains separate. -/
namespace Solidity.Yul.Checks.RawGrowingSequence
namespace Old
export Solidity.Yul.Checks.RawPreparedDeclaration.Old (ctx env grown initial clean tmp x arg flag declaration)
export Solidity.Yul.Checks.RawPreparedDeclaration (canonical next loop breakBody)
end Old
def loopItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.grown.tys Old.grown.tys :=
 .stmt (.whileLoop (l := true) (.local .here) .brk) .nil
def tail : RawCheckedAdapterSequence.Items Old.grown [] false false loopItems :=
 Solidity.Yul.RawCheckedAdapterSequence.cons Old.loop Solidity.Yul.RawCheckedAdapterSequence.nil
def breakTail := Solidity.Yul.RawCheckedAdapterSequence.cons Old.breakBody
 (Solidity.Yul.RawCheckedAdapterSequence.nil (ctx := Old.grown) (returns := []) (modifier := false) (u := false))
def continueBody : RawCheckedAdapter.Adapter Old.grown [] false false .cont :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .continue_)
def continueTail := Solidity.Yul.RawCheckedAdapterSequence.cons continueBody
 (Solidity.Yul.RawCheckedAdapterSequence.nil (ctx := Old.grown) (returns := []) (modifier := false) (u := false))
def joined : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.grown.tys :=
 .stmt Old.declaration loopItems
def witness : Nonempty (Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.grown.tys) := ⟨joined⟩
end Solidity.Yul.Checks.RawGrowingSequence

namespace Solidity.Yul.Checks.RawGrowingSequence
theorem normalProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail pipeline 6 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world)) = (.ok (.normal (.cons (.bool true) Solidity.Yul.Checks.RawGrowingSequence.Old.clean)),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem breakRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.breakTail pipeline 4 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world)) = (.ok (.brk Solidity.Yul.Checks.RawGrowingSequence.Old.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem continueRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.continueTail pipeline 4 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world)) = (.ok (.cont Solidity.Yul.Checks.RawGrowingSequence.Old.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world)) := by
  intro pipeline world
  rfl

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail pipeline 3 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world) = .inr (.error .timeout,Solidity.Yul.RawCoherent.capture (Solidity.Yul.Checks.RawGrowingSequence.Old.next world) (Solidity.Yul.RawCoherent.prepare (Solidity.Yul.Checks.RawGrowingSequence.Old.next world))) := by
  intro pipeline world
  rfl

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail pipeline 0 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world) ∧ Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail pipeline 2 (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem dirtyBits : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),match Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.breakTail pipeline 4 (Solidity.Yul.Checks.RawGrowingSequence.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr result => result.1 = .ok (.break_ rfl) ∧
   (Solidity.Yul.RawFrame.view result.2 Solidity.Yul.Checks.RawGrowingSequence.Old.tmp).val = 1 ∧
   (Solidity.Yul.RawFrame.view result.2 Solidity.Yul.Checks.RawGrowingSequence.Old.x).val = 2 ∧
   (Solidity.Yul.RawFrame.view result.2 Solidity.Yul.Checks.RawGrowingSequence.Old.arg).val = 257 ∧
   (Solidity.Yul.RawFrame.view result.2 Solidity.Yul.Checks.RawGrowingSequence.Old.flag).val = 2 ∧ result.2.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingSequence.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),
 Solidity.Yul.RawGrowingSequence.Coherent (Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world)) ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawGrowingSequence.joined Solidity.Yul.Checks.RawGrowingSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world) =
 Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawGrowingSequence.run true Solidity.Yul.Checks.RawGrowingSequence.tail glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingSequence.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact Solidity.Yul.RawGrowingSequence.correct Old.ctx "tmp" true [] false false loopItems tail
    glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingSequence.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingSequence.Old.env),
 (Solidity.Source.execItems glob frame 6 nps ph Solidity.Yul.Checks.RawGrowingSequence.joined Solidity.Yul.Checks.RawGrowingSequence.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world) =
 (.ok (.normal (.cons (.bool true) Solidity.Yul.Checks.RawGrowingSequence.Old.clean)),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingSequence.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawGrowingSequence
#print axioms Solidity.Yul.RawGrowingSequence.lift_run
#print axioms Solidity.Yul.RawGrowingSequence.correct
#print axioms Solidity.Yul.Checks.RawGrowingSequence.normalProjection
#print axioms Solidity.Yul.Checks.RawGrowingSequence.breakRestores
#print axioms Solidity.Yul.Checks.RawGrowingSequence.continueRestores
#print axioms Solidity.Yul.Checks.RawGrowingSequence.tailTimeout
#print axioms Solidity.Yul.Checks.RawGrowingSequence.preTimeout
#print axioms Solidity.Yul.Checks.RawGrowingSequence.dirtyBits
#print axioms Solidity.Yul.Checks.RawGrowingSequence.sourceAll
#print axioms Solidity.Yul.Checks.RawGrowingSequence.sourceCompletes
