import Solidity.Yul.RawGrowingBlock
import Solidity.Yul.Checks.RawGrowingSequence
/-! Kernel-only complete scoped block controls. Closing the bound prefix must
preserve updates to older locals, control and reached error state. -/
namespace Solidity.Yul.Checks.RawGrowingBlock
namespace Old
export Solidity.Yul.Checks.RawGrowingSequence.Old (ctx env grown initial clean canonical declaration x arg flag)
export Solidity.Yul.Checks.RawGrowingSequence (loopItems tail breakTail continueTail joined)
end Old
def packed := RawGrowingBlock.adapter Old.ctx "tmp" true [] false false Old.loopItems Old.tail
def breakBlock := RawGrowingBlock.adapter Old.ctx "tmp" true [] false false _ Old.breakTail
def continueBlock := RawGrowingBlock.adapter Old.ctx "tmp" true [] false false _ Old.continueTail
def copyExpr : Solidity.Source.RExpr Old.env Old.grown.tys LocalU8Expr.Ty :=
 .assign (.local (.there .here)) (.local (.there (.there .here)))
def copyProof : LocalU8Expr.Supported Old.env Old.grown.tys copyExpr :=
 .assign (.there .here) (.local (.there (.there .here)))
def copyItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.grown.tys Old.grown.tys :=
 .stmt (.expr copyExpr) .nil
def copyTail : RawCheckedAdapterSequence.Items Old.grown [] false false copyItems :=
 RawCheckedAdapterSequence.ofSequence (.uint8 copyProof .nil)
def copyBlock := RawGrowingBlock.adapter Old.ctx "tmp" true [] false false copyItems copyTail
def afterClean : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.joined)) := ⟨packed⟩
end Solidity.Yul.Checks.RawGrowingBlock

namespace Solidity.Yul.Checks.RawGrowingBlock
def captured (locals : Solidity.Source.Locals Old.env.layout Old.ctx.tys)
 (world : Solidity.Source.St Old.env) : RawFrame.State Old.ctx :=
 RawDeclarationFrame.ofSnapshot ⟨locals,LocalValues.ofClean locals,world⟩
end Solidity.Yul.Checks.RawGrowingBlock

namespace Solidity.Yul.Checks.RawGrowingBlock
def grownAfter (locals : Solidity.Source.Locals Old.env.layout Old.ctx.tys)
 (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.bool true) locals,LocalValues.ofClean (.cons (.bool true) locals),world⟩
end Solidity.Yul.Checks.RawGrowingBlock

namespace Solidity.Yul.Checks.RawGrowingBlock
theorem nextFrameEq : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env), Solidity.Yul.Checks.RawPreparedDeclaration.next world = Solidity.Yul.Checks.RawGrowingBlock.grownAfter Solidity.Yul.Checks.RawGrowingBlock.Old.clean world := by
  intro world
  unfold Solidity.Yul.Checks.RawPreparedDeclaration.next
  rw [RawCoherent.prepare_coherent _
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)]
  rfl

theorem loopTailStage : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.Old.tail.run pipeline 5 (Solidity.Yul.Checks.RawPreparedDeclaration.next world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingBlock.grownAfter Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  rw [nextFrameEq]
  rfl

theorem copyTailStage : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.copyTail.run pipeline 6 (Solidity.Yul.Checks.RawPreparedDeclaration.next world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingBlock.grownAfter Solidity.Yul.Checks.RawGrowingBlock.afterClean world) := by
  intro pipeline world
  rw [nextFrameEq]
  rfl

theorem timeoutTailStage : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.Old.tail.run pipeline 2 (Solidity.Yul.Checks.RawPreparedDeclaration.next world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingBlock.grownAfter Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  rw [nextFrameEq]
  rfl

theorem dropGrownStage : ∀ (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawGrowingBlock.Old.env.layout Solidity.Yul.Checks.RawGrowingBlock.Old.ctx.tys)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),
 Solidity.Yul.RawGrowingBlock.drop (Solidity.Yul.Checks.RawGrowingBlock.grownAfter locals world) = Solidity.Yul.Checks.RawGrowingBlock.captured locals world := by
  intro locals world
  have same : RawCoherent.coherent (grownAfter locals world) = true :=
    (RawCoherent.coherent_iff _).mpr rfl
  unfold RawGrowingBlock.drop
  rw [RawCoherent.prepare_coherent _ same]
  rfl

end Solidity.Yul.Checks.RawGrowingBlock

namespace Solidity.Yul.Checks.RawGrowingBlock
theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.packed.run pipeline 7 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingBlock.captured Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  change RawGrowingBlock.close (RawGrowingSequence.run true Old.tail pipeline 6
    (Old.canonical world)) = _
  rw [RawGrowingSequence.run,RawPreparedDeclaration.run_success]
  change RawGrowingBlock.close (.inr (Old.tail.run pipeline 5
    (Solidity.Yul.Checks.RawPreparedDeclaration.next world))) = _
  rw [loopTailStage]
  change ((.ok .normal : Solidity.Source.R RawLoopBody.Flow),RawGrowingBlock.drop (grownAfter Old.clean world)) = _
  rw [dropGrownStage]

theorem mutation : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.copyBlock.run pipeline 8 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawGrowingBlock.captured Solidity.Yul.Checks.RawGrowingBlock.afterClean world) := by
  intro pipeline world
  change RawGrowingBlock.close (RawGrowingSequence.run true copyTail pipeline 7
    (Old.canonical world)) = _
  rw [RawGrowingSequence.run,RawPreparedDeclaration.run_success]
  change RawGrowingBlock.close (.inr (copyTail.run pipeline 6
    (Solidity.Yul.Checks.RawPreparedDeclaration.next world))) = _
  rw [copyTailStage]
  change ((.ok .normal : Solidity.Source.R RawLoopBody.Flow),RawGrowingBlock.drop (grownAfter afterClean world)) = _
  rw [dropGrownStage]

theorem breakRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.breakBlock.run pipeline 5 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawGrowingBlock.captured Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  rfl

theorem continueRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.continueBlock.run pipeline 5 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawGrowingBlock.captured Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  rfl

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.packed.run pipeline 4 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingBlock.captured Solidity.Yul.Checks.RawGrowingBlock.Old.clean world) := by
  intro pipeline world
  change RawGrowingBlock.close (RawGrowingSequence.run true Old.tail pipeline 3
    (Old.canonical world)) = _
  rw [RawGrowingSequence.run,RawPreparedDeclaration.run_success]
  change RawGrowingBlock.close (.inr (Old.tail.run pipeline 2
    (Solidity.Yul.Checks.RawPreparedDeclaration.next world))) = _
  rw [timeoutTailStage]
  change ((.error .timeout : Solidity.Source.R RawLoopBody.Flow),RawGrowingBlock.drop (grownAfter Old.clean world)) = _
  rw [dropGrownStage]

theorem preTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),Solidity.Yul.Checks.RawGrowingBlock.packed.run pipeline 0 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) ∧ Solidity.Yul.Checks.RawGrowingBlock.packed.run pipeline 3 (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem dirtyWords : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),let result := Solidity.Yul.Checks.RawGrowingBlock.breakBlock.run pipeline 5 (Solidity.Yul.Checks.RawGrowingBlock.Old.initial 2 257 2 world)
 result.1 = .ok (.break_ rfl) ∧
 (Solidity.Yul.RawFrame.view result.2 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.xCell)).val = 2 ∧
 (Solidity.Yul.RawFrame.view result.2 (Solidity.Yul.Checks.RawCheckedAdapterLoop.Old.flagCell)).val = 2 ∧
 result.2.world = world ∧ Solidity.Yul.RawCoherent.coherent result.2 ≠ true := by
  intro pipeline world
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  change false ≠ true
  decide

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawGrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawGrowingBlock.Old.joined) Solidity.Yul.Checks.RawGrowingBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingBlock.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawGrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawGrowingBlock.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceCopyCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawGrowingBlock.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawGrowingBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),
 (Solidity.Source.execS glob frame 8 nps ph
 (Solidity.Source.RStmt.block (Solidity.Source.RItems.stmt Solidity.Yul.Checks.RawGrowingBlock.Old.declaration Solidity.Yul.Checks.RawGrowingBlock.copyItems))
 Solidity.Yul.Checks.RawGrowingBlock.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingBlock.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawGrowingBlock.afterClean),(Solidity.Source.L0 Solidity.Yul.Checks.RawGrowingBlock.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem dirtyNarrow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawGrowingBlock.Old.env),
 (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawGrowingBlock.breakBlock.run pipeline 5 (Solidity.Yul.Checks.RawGrowingBlock.Old.initial 2 257 2 world)).2
 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 := by
  intro pipeline world
  rfl

end Solidity.Yul.Checks.RawGrowingBlock
#print axioms Solidity.Yul.RawGrowingBlock.restore_drop
#print axioms Solidity.Yul.RawGrowingBlock.drop_coherent
#print axioms Solidity.Yul.RawGrowingBlock.close_correct
#print axioms Solidity.Yul.RawGrowingBlock.correct
#print axioms Solidity.Yul.RawGrowingBlock.adapter
#print axioms Solidity.Yul.Checks.RawGrowingBlock.normal
#print axioms Solidity.Yul.Checks.RawGrowingBlock.mutation
#print axioms Solidity.Yul.Checks.RawGrowingBlock.breakRestores
#print axioms Solidity.Yul.Checks.RawGrowingBlock.continueRestores
#print axioms Solidity.Yul.Checks.RawGrowingBlock.tailTimeout
#print axioms Solidity.Yul.Checks.RawGrowingBlock.preTimeout
#print axioms Solidity.Yul.Checks.RawGrowingBlock.dirtyWords
#print axioms Solidity.Yul.Checks.RawGrowingBlock.sourceAll
#print axioms Solidity.Yul.Checks.RawGrowingBlock.sourceCopyCompletes
#print axioms Solidity.Yul.Checks.RawGrowingBlock.dirtyNarrow
#print axioms Solidity.Yul.Checks.RawGrowingBlock.nextFrameEq
#print axioms Solidity.Yul.Checks.RawGrowingBlock.loopTailStage
#print axioms Solidity.Yul.Checks.RawGrowingBlock.copyTailStage
#print axioms Solidity.Yul.Checks.RawGrowingBlock.timeoutTailStage
#print axioms Solidity.Yul.Checks.RawGrowingBlock.dropGrownStage
