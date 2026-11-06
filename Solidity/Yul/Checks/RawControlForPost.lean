import Solidity.Yul.RawControlForPost
import Solidity.Yul.Checks.RawControlDeclaration

/-! Initializer write, checked narrow-copy body and post/scope composition.
Source tests and raw prefix frames are separate observations. -/
namespace Solidity.Yul.Checks.RawControlForPost
namespace Old
export Solidity.Yul.Checks.RawControlDeclaration.Old (ctx env grown canonical initial clean captured)
export Solidity.Yul.Checks.RawControlDeclaration (changed)
export Solidity.Yul.Checks.RawGrowingForPost (body clear clearOuter frame)
export Solidity.Yul.Checks.RawPreparedDeclaration (test breakBody)
export Solidity.Yul.Checks.RawGrowingSequence (continueBody)
end Old
def initial := LocalBoolControl.Supported.not Solidity.Yul.Checks.RawControlDeclaration.proof
def afterClean : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def raiseOuter : LocalBoolControl.Supported Old.env Old.grown.tys
 (.assign (.local (.there (.there (.there .here)))) (.bool true)) :=
 .assign (.there (.there (.there .here))) (.base (.literal true))
def deep := LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not
 (LocalBoolControl.Supported.not (LocalBoolControl.Supported.not Old.test)))))))))))
def deepPost := LocalBoolControl.Supported.or Old.clear deep
def packed := RawControlForPost.adapter Old.ctx "tmp" [] false false _ initial _ _ _
 Old.test Old.clear Old.body
def program : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true)
  (.declInit (τ := .bool) (.unary .not Solidity.Yul.Checks.RawControlDeclaration.expr) (by rfl))
  (.some (.local .here)) (.some (.assign (.local .here) (.bool false)))
  (.block Solidity.Yul.Checks.RawGrowingBlock.copyItems)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩
end Solidity.Yul.Checks.RawControlForPost

namespace Solidity.Yul.Checks.RawControlForPost
theorem prepared11 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlForPost.initial 11 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = .inr (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro world
  rfl

theorem guard10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawControlForPost.Old.test 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) = (.ok true,Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro world
  rfl

theorem copy10 : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.Checks.RawControlForPost.Old.body.run pipeline 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) = (.ok .normal,Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro pipeline world
  rfl

theorem post10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawControlForPost.Old.clear 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.afterClean world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro world
  rfl

theorem false9 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawControlForPost.Old.test 9 (Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.afterClean world) = (.ok false,Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro world
  rfl

theorem postContinue10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawControlForPost.Old.clear 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro world
  rfl

theorem falseChanged9 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawControlForPost.Old.test 9 (Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.Old.changed world) = (.ok false,Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro world
  rfl

theorem continue10 : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.Checks.RawControlForPost.Old.continueBody.run pipeline 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro pipeline world
  rfl

theorem deep10 : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawControlForPost.deepPost 10 (Solidity.Yul.Checks.RawControlForPost.Old.frame true Solidity.Yul.Checks.RawControlForPost.afterClean world) = (.error .timeout,Solidity.Yul.Checks.RawControlForPost.Old.frame false Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro world
  rfl

end Solidity.Yul.Checks.RawControlForPost

namespace Solidity.Yul.Checks.RawControlForPost
theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.Old.clear Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test Old.clear Old.body pipeline 11
      (Old.frame true Old.changed world) = (.ok (),Old.frame false afterClean world) := by
    rw [RawCheckedForPost.run,guard10,copy10]
    dsimp only
    rw [RawSourceForPost.after,post10,RawCheckedForPost.run.eq_def]
    dsimp only
    rw [false9]
    rfl
  rw [RawControlForPost.run,prepared11]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (Old.frame false afterClean world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem packedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.Checks.RawControlForPost.packed.run pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro pipeline world
  change ((RawControlForPost.run initial Old.test Old.clear Old.body pipeline 12 (Old.canonical world)).1.map
    (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
    (RawControlForPost.run initial Old.test Old.clear Old.body pipeline 12 (Old.canonical world)).2) = _
  rw [normal]
  rfl

theorem continued : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.Old.clear Solidity.Yul.Checks.RawControlForPost.Old.continueBody pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test Old.clear Old.continueBody pipeline 11
      (Old.frame true Old.changed world) = (.ok (),Old.frame false Old.changed world) := by
    rw [RawCheckedForPost.run,guard10,continue10]
    dsimp only
    rw [RawSourceForPost.after,postContinue10,RawCheckedForPost.run.eq_def]
    dsimp only
    rw [falseChanged9]
    rfl
  rw [RawControlForPost.run,prepared11]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (Old.frame false Old.changed world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem breakSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.raiseOuter Solidity.Yul.Checks.RawControlForPost.Old.breakBody pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test raiseOuter Old.breakBody pipeline 11
      (Old.frame true Old.changed world) = (.ok (),Old.frame true Old.changed world) := by
    rw [RawCheckedForPost.run,guard10]
    rfl
  rw [RawControlForPost.run,prepared11]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (Old.frame true Old.changed world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem falseSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlDeclaration.proof Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.raiseOuter Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.ok (),Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro pipeline world
  have first : RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof 11
      (Old.canonical world) = .inr (Old.frame false Old.changed world) := by rfl
  have iteration : RawCheckedForPost.run Old.test raiseOuter Old.body pipeline 11
      (Old.frame false Old.changed world) = (.ok (),Old.frame false Old.changed world) := by
    rw [RawCheckedForPost.run]
    rfl
  rw [RawControlForPost.run,first]
  dsimp only
  rw [iteration]
  change ((.ok () : Solidity.Source.R Unit),RawGrowingBlock.drop (Old.frame false Old.changed world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem initTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.Old.clear Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 6 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.Old.changed world) := by
  intro pipeline world
  have first : RawControlDeclaration.run "tmp" initial 5 (Old.canonical world) =
      .inl (.timeout,Old.captured Old.changed world) := by rfl
  rw [RawControlForPost.run,first]

theorem postTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.deepPost Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 12 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlForPost.Old.captured Solidity.Yul.Checks.RawControlForPost.afterClean world) := by
  intro pipeline world
  have iteration : RawCheckedForPost.run Old.test deepPost Old.body pipeline 11
      (Old.frame true Old.changed world) = (.error .timeout,Old.frame false afterClean world) := by
    rw [RawCheckedForPost.run,guard10,copy10]
    dsimp only
    rw [RawSourceForPost.after,deep10]
    rfl
  rw [RawControlForPost.run,prepared11]
  dsimp only
  rw [iteration]
  change ((.error .timeout : Solidity.Source.R Unit),RawGrowingBlock.drop (Old.frame false afterClean world)) = _
  rw [Solidity.Yul.Checks.RawGrowingForPost.dropFrame]

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.Old.clear Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 0 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlForPost.Old.canonical world) ∧ Solidity.Yul.RawControlForPost.run Solidity.Yul.Checks.RawControlForPost.initial Solidity.Yul.Checks.RawControlForPost.Old.test Solidity.Yul.Checks.RawControlForPost.Old.clear Solidity.Yul.Checks.RawControlForPost.Old.body pipeline 1 (Solidity.Yul.Checks.RawControlForPost.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawControlForPost.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlForPost.Old.initial 2 257 2 world) = false := by
  intro world
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlForPost.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlForPost.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawControlForPost.program Solidity.Yul.Checks.RawControlForPost.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlForPost.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawControlForPost.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawControlForPost.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlForPost.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlForPost.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlForPost.Old.env),
 (Solidity.Source.execS glob frame 12 nps ph Solidity.Yul.Checks.RawControlForPost.program Solidity.Yul.Checks.RawControlForPost.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlForPost.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawControlForPost.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlForPost.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawControlForPost
#print axioms Solidity.Yul.RawControlForPost.correct
#print axioms Solidity.Yul.RawControlForPost.adapter
#print axioms Solidity.Yul.Checks.RawControlForPost.prepared11
#print axioms Solidity.Yul.Checks.RawControlForPost.guard10
#print axioms Solidity.Yul.Checks.RawControlForPost.copy10
#print axioms Solidity.Yul.Checks.RawControlForPost.post10
#print axioms Solidity.Yul.Checks.RawControlForPost.false9
#print axioms Solidity.Yul.Checks.RawControlForPost.postContinue10
#print axioms Solidity.Yul.Checks.RawControlForPost.falseChanged9
#print axioms Solidity.Yul.Checks.RawControlForPost.continue10
#print axioms Solidity.Yul.Checks.RawControlForPost.deep10
#print axioms Solidity.Yul.Checks.RawControlForPost.normal
#print axioms Solidity.Yul.Checks.RawControlForPost.packedNormal
#print axioms Solidity.Yul.Checks.RawControlForPost.continued
#print axioms Solidity.Yul.Checks.RawControlForPost.breakSkips
#print axioms Solidity.Yul.Checks.RawControlForPost.falseSkips
#print axioms Solidity.Yul.Checks.RawControlForPost.initTimeout
#print axioms Solidity.Yul.Checks.RawControlForPost.postTimeout
#print axioms Solidity.Yul.Checks.RawControlForPost.preTimeout
#print axioms Solidity.Yul.Checks.RawControlForPost.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawControlForPost.sourceAll
#print axioms Solidity.Yul.Checks.RawControlForPost.sourceCompletes
