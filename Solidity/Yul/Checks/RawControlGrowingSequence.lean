import Solidity.Yul.RawControlGrowingSequence
import Solidity.Yul.Checks.RawControlForPost

/-! Nonliteral initializer/item combinations with actual control projection.
Initializer and tail errors retain their differently indexed raw frames.
This is not enclosing block closure or frontend admission. -/
namespace Solidity.Yul.Checks.RawControlGrowingSequence
namespace Old
export Solidity.Yul.Checks.RawControlForPost.Old (ctx env grown canonical clean captured changed frame)
export Solidity.Yul.Checks.RawControlForPost (initial afterClean deep)
export Solidity.Yul.Checks.RawGrowingBlock (copyItems copyTail copyExpr copyProof)
export Solidity.Yul.Checks.RawGrowingSequence (breakTail continueTail)
end Old
def deepExpr : Solidity.Source.RExpr Old.env Old.grown.tys .bool :=
 .unary .not (.unary .not (.unary .not (.unary .not
  (.unary .not (.unary .not (.unary .not (.unary .not
   (.unary .not (.unary .not (.unary .not (.unary .not (.local .here))))))))))))
def errorItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.grown.tys Old.grown.tys :=
 .stmt (.block Old.copyItems) (.stmt (.expr deepExpr) .nil)
def deepAdapter : RawCheckedAdapter.Adapter Old.grown [] false false (.expr deepExpr) :=
 RawCheckedAdapter.fromAdapter (RawSourceAdapter.atom (.expression Old.deep))
def errorTail : RawCheckedAdapterSequence.Items Old.grown [] false false errorItems :=
 RawCheckedAdapterSequence.cons Solidity.Yul.Checks.RawGrowingForPost.body
  (RawCheckedAdapterSequence.cons deepAdapter RawCheckedAdapterSequence.nil)
def joined : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.grown.tys :=
 .stmt (.declInit (τ := .bool) (.unary .not Solidity.Yul.Checks.RawControlDeclaration.expr) (by rfl)) Old.copyItems
def witness : Nonempty (RawCheckedAdapterSequence.Items Old.grown [] false false errorItems) := ⟨errorTail⟩
end Solidity.Yul.Checks.RawControlGrowingSequence

namespace Solidity.Yul.Checks.RawControlGrowingSequence
theorem tailCopy11 : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail.run pipeline 11 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed world) = (.ok .normal,Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.afterClean world) := by
  intro pipeline world
  rfl

theorem deep9 (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Old.env) :
 deepAdapter.run pipeline 9 (Old.frame true Old.afterClean world) =
 (.error .timeout,Old.frame true Old.afterClean world) := by
  rfl

theorem tailError11 : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.Checks.RawControlGrowingSequence.errorTail.run pipeline 11 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed world) = (.error .timeout,Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.afterClean world) := by
  intro pipeline world
  simp only [errorTail,RawCheckedAdapterSequence.cons]
  rw [RawCheckedAdapterSequence.runCons,Solidity.Yul.Checks.RawControlForPost.copy10]
  dsimp only
  rw [RawCheckedAdapterSequence.runCons,deep9]

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inr (.ok .normal,Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.afterClean world) := by
  intro pipeline world
  rw [RawControlGrowingSequence.run,Solidity.Yul.Checks.RawControlForPost.prepared11]
  dsimp only
  rw [tailCopy11]

theorem breakRaw : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.breakTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inr (.ok (.break_ rfl),Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed world) := by
  intro pipeline world
  rw [RawControlGrowingSequence.run,Solidity.Yul.Checks.RawControlForPost.prepared11]
  rfl

theorem continueRaw : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.continueTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inr (.ok (.continue_ rfl),Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed world) := by
  intro pipeline world
  rw [RawControlGrowingSequence.run,Solidity.Yul.Checks.RawControlForPost.prepared11]
  rfl

theorem initTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail pipeline 6 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlGrowingSequence.Old.captured Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed world) := by
  intro pipeline world
  have first : RawControlDeclaration.run "tmp" Old.initial 5 (Old.canonical world) =
      .inl (.timeout,Old.captured Old.changed world) := by rfl
  rw [RawControlGrowingSequence.run,first]

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.errorTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inr (.error .timeout,Solidity.Yul.Checks.RawControlGrowingSequence.Old.frame true Solidity.Yul.Checks.RawControlGrowingSequence.Old.afterClean world) := by
  intro pipeline world
  rw [RawControlGrowingSequence.run,Solidity.Yul.Checks.RawControlForPost.prepared11]
  dsimp only
  rw [tailError11]

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail pipeline 0 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) ∧ Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail pipeline 1 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem breakProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.breakTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world)) = (.ok (.brk Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingSequence.Old.env,world)) := by
  intro pipeline world
  rw [breakRaw]
  rfl

theorem continueProjection : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.continueTail pipeline 12 (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world)) = (.ok (.cont Solidity.Yul.Checks.RawControlGrowingSequence.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingSequence.Old.env,world)) := by
  intro pipeline world
  rw [continueRaw]
  rfl

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = false := by
  intro world
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env),
 Solidity.Yul.RawGrowingSequence.Coherent (Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world)) ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawControlGrowingSequence.joined Solidity.Yul.Checks.RawControlGrowingSequence.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingSequence.Old.env,world) =
 Solidity.Yul.RawGrowingSequence.project (Solidity.Yul.RawControlGrowingSequence.run Solidity.Yul.Checks.RawControlGrowingSequence.Old.initial Solidity.Yul.Checks.RawControlGrowingSequence.Old.copyTail glob.pipeline fuel (Solidity.Yul.Checks.RawControlGrowingSequence.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact Solidity.Yul.RawControlGrowingSequence.correct Old.ctx "tmp" [] false false _ Old.initial
    Old.copyItems Old.copyTail glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlGrowingSequence.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlGrowingSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlGrowingSequence.Old.env),
 (Solidity.Source.execItems glob frame 12 nps ph Solidity.Yul.Checks.RawControlGrowingSequence.joined Solidity.Yul.Checks.RawControlGrowingSequence.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingSequence.Old.env,world) =
 (.ok (.normal (.cons (.bool true) Solidity.Yul.Checks.RawControlGrowingSequence.Old.afterClean)),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlGrowingSequence.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawControlGrowingSequence
#print axioms Solidity.Yul.RawControlGrowingSequence.correct
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.tailCopy11
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.tailError11
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.normal
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.breakRaw
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.continueRaw
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.initTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.tailTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.preTimeout
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.breakProjection
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.continueProjection
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.sourceAll
#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.sourceCompletes

#print axioms Solidity.Yul.Checks.RawControlGrowingSequence.deep9
