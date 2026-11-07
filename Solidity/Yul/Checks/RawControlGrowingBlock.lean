import Solidity.Yul.RawControlGrowingBlock
import Solidity.Yul.Checks.RawControlGrowingSequence

/-! Closed nonliteral declaration blocks and a nested actual checked block.
Older initializer/tail effects survive scope exit; the new binder does not.
Source computations and raw frame boundaries are checked separately. -/
namespace Solidity.Yul.Checks.RawControlGrowingBlock
namespace Old
export Solidity.Yul.Checks.RawControlGrowingSequence.Old
 (ctx env grown canonical clean captured changed frame initial afterClean copyItems copyTail breakTail continueTail)
export Solidity.Yul.Checks.RawControlGrowingSequence (joined errorTail errorItems)
end Old
def packed := RawControlGrowingBlock.adapter Old.ctx "tmp" [] false false _ Old.initial _ Old.copyTail
def breakBlock := RawControlGrowingBlock.adapter Old.ctx "tmp" [] false false _ Old.initial _ Old.breakTail
def continueBlock := RawControlGrowingBlock.adapter Old.ctx "tmp" [] false false _ Old.initial _ Old.continueTail
def errorBlock := RawControlGrowingBlock.adapter Old.ctx "tmp" [] false false _ Old.initial _ Old.errorTail
def program : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys := .block Old.joined
def initialDecl : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.grown.tys :=
 .declInit (τ := .bool) (.unary .not Solidity.Yul.Checks.RawControlDeclaration.expr) (by rfl)
def breakProgram : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .block (.stmt initialDecl (.stmt .brk .nil))
def nestedItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt program .nil
def nested := RawCheckedAdapterSequence.block
 (RawCheckedAdapterSequence.cons packed RawCheckedAdapterSequence.nil)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩
def nestedWitness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false (.block nestedItems)) := ⟨nested⟩
end Solidity.Yul.Checks.RawControlGrowingBlock

namespace Solidity.Yul.Checks.RawControlGrowingBlock
theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.RawControlGrowingBlock.run Solidity.Yul.Checks.RawControlGrowingBlock.Old.initial Solidity.Yul.Checks.RawControlGrowingBlock.Old.copyTail pipeline 13 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.afterClean world) := by
  intro pipeline world
  rw [RawControlGrowingBlock.run,Solidity.Yul.Checks.RawControlGrowingSequence.normal]
  change ((.ok .normal : Solidity.Source.R RawLoopBody.Flow),
    RawGrowingBlock.drop (Old.frame true Old.afterClean world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.Checks.RawControlGrowingBlock.packed.run pipeline 13 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.afterClean world) := by
  intro pipeline world
  exact normal pipeline world

theorem breakRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.Checks.RawControlGrowingBlock.breakBlock.run pipeline 13 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.changed world) := by
  intro pipeline world
  change RawControlGrowingBlock.run Old.initial Old.breakTail pipeline 13 (Old.canonical world) = _
  rw [RawControlGrowingBlock.run,Solidity.Yul.Checks.RawControlGrowingSequence.breakRaw]
  change ((.ok (.break_ rfl) : Solidity.Source.R RawLoopBody.Flow),
    RawGrowingBlock.drop (Old.frame true Old.changed world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem continueRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.Checks.RawControlGrowingBlock.continueBlock.run pipeline 13 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.changed world) := by
  intro pipeline world
  change RawControlGrowingBlock.run Old.initial Old.continueTail pipeline 13 (Old.canonical world) = _
  rw [RawControlGrowingBlock.run,Solidity.Yul.Checks.RawControlGrowingSequence.continueRaw]
  change ((.ok (.continue_ rfl) : Solidity.Source.R RawLoopBody.Flow),
    RawGrowingBlock.drop (Old.frame true Old.changed world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem initTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.RawControlGrowingBlock.run Solidity.Yul.Checks.RawControlGrowingBlock.Old.initial Solidity.Yul.Checks.RawControlGrowingBlock.Old.copyTail pipeline 7 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.changed world) := by
  intro pipeline world
  rw [RawControlGrowingBlock.run,Solidity.Yul.Checks.RawControlGrowingSequence.initTimeout]
  rfl

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.Checks.RawControlGrowingBlock.errorBlock.run pipeline 13 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingBlock.Old.captured Solidity.Yul.Checks.RawControlGrowingBlock.Old.afterClean world) := by
  intro pipeline world
  change RawControlGrowingBlock.run Old.initial Old.errorTail pipeline 13 (Old.canonical world) = _
  rw [RawControlGrowingBlock.run,Solidity.Yul.Checks.RawControlGrowingSequence.tailTimeout]
  change ((.error .timeout : Solidity.Source.R RawLoopBody.Flow),
    RawGrowingBlock.drop (Old.frame true Old.afterClean world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.RawControlGrowingBlock.run Solidity.Yul.Checks.RawControlGrowingBlock.Old.initial Solidity.Yul.Checks.RawControlGrowingBlock.Old.copyTail pipeline 0 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) ∧ Solidity.Yul.RawControlGrowingBlock.run Solidity.Yul.Checks.RawControlGrowingBlock.Old.initial Solidity.Yul.Checks.RawControlGrowingBlock.Old.copyTail pipeline 1 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) ∧ Solidity.Yul.RawControlGrowingBlock.run Solidity.Yul.Checks.RawControlGrowingBlock.Old.initial Solidity.Yul.Checks.RawControlGrowingBlock.Old.copyTail pipeline 2 (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl⟩

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = false := by
  intro world
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlGrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawControlGrowingBlock.program Solidity.Yul.Checks.RawControlGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawControlGrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem nestedAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlGrowingBlock.nested.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (.block Solidity.Yul.Checks.RawControlGrowingBlock.nestedItems) Solidity.Yul.Checks.RawControlGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawControlGrowingBlock.nested.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingBlock.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact nested.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingBlock.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env),
 (Solidity.Source.execS glob frame 13 nps ph Solidity.Yul.Checks.RawControlGrowingBlock.program Solidity.Yul.Checks.RawControlGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawControlGrowingBlock.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem nestedCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingBlock.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env),
 (Solidity.Source.execS glob frame 17 nps ph (.block Solidity.Yul.Checks.RawControlGrowingBlock.nestedItems) Solidity.Yul.Checks.RawControlGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawControlGrowingBlock.Old.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceBreak : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingBlock.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingBlock.Old.env),
 (Solidity.Source.execS glob frame 13 nps ph Solidity.Yul.Checks.RawControlGrowingBlock.breakProgram Solidity.Yul.Checks.RawControlGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world) =
 (.ok (.brk Solidity.Yul.Checks.RawControlGrowingBlock.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingBlock.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawControlGrowingBlock
#print axioms Solidity.Yul.RawControlGrowingBlock.correct
#print axioms Solidity.Yul.RawControlGrowingBlock.adapter
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.normal
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.packedNormal
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.breakRestores
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.continueRestores
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.initTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.tailTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.preTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.sourceAll
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.nestedAll
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.sourceCompletes
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.nestedCompletes
#print axioms Solidity.Yul.Checks.RawControlGrowingBlock.sourceBreak
