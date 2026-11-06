import Solidity.Yul.RawU8GrowingBlock
import Solidity.Yul.Checks.RawU8GrowingSequence
/-! Actual checked uint8 declaration blocks close their new binder, retaining
older effects, raw dirty words and pipeline-dependent initializer prefixes. -/
namespace Solidity.Yul.Checks.RawU8GrowingBlock
namespace Old
export Solidity.Yul.Checks.RawU8GrowingSequence.Old (ctx clean initial canonical assign timeout breakTail continueTail)
export Solidity.Yul.Checks.RawU8GrowingSequence (tail items joined changed)
export Solidity.Yul.Checks.RawPreparedInteger.Old (captured)
end Old
def packed := RawU8GrowingBlock.adapter Old.ctx "n" [] false false _ Old.assign Old.items Old.tail
def breakBlock := RawU8GrowingBlock.adapter Old.ctx "n" [] false false _ Old.assign _ Old.breakTail
def continueBlock := RawU8GrowingBlock.adapter Old.ctx "n" [] false false _ Old.assign _ Old.continueTail
def partialBlock := RawU8GrowingBlock.adapter Old.ctx "n" [] false false _ Old.timeout Old.items Old.tail
def program : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys := .block Old.joined
def nestedItems : Solidity.Source.RItems Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys := .stmt program .nil
def nested := RawCheckedAdapterSequence.block (RawCheckedAdapterSequence.cons packed RawCheckedAdapterSequence.nil)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩
def nestedWitness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false (.block nestedItems)) := ⟨nested⟩

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.packed.run pipeline 8 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawU8GrowingBlock.Old.captured Solidity.Yul.Checks.RawU8GrowingBlock.Old.changed world) := by
  intro pipeline world
  change RawU8GrowingBlock.run Old.assign Old.tail pipeline 8 (Old.canonical world) = _
  rw [RawU8GrowingBlock.run,Solidity.Yul.Checks.RawU8GrowingSequence.normal]
  change ((.ok .normal : Solidity.Source.R RawLoopBody.Flow),
    RawTypedScope.drop (Solidity.Yul.Checks.RawU8GrowingSequence.next world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem nestedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.nested.run pipeline 10 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawU8GrowingBlock.Old.captured Solidity.Yul.Checks.RawU8GrowingBlock.Old.changed world) := by
  intro pipeline world
  change RawCheckedAdapterSequence.runBlock
    (RawCheckedAdapterSequence.cons packed RawCheckedAdapterSequence.nil) pipeline 10 (Old.canonical world) = _
  simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,
    RawCheckedAdapterSequence.runCons]
  rw [normal]
  rfl

theorem breakRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.breakBlock.run pipeline 5 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawU8GrowingBlock.Old.captured Solidity.Yul.Checks.RawU8Declaration.changed world) := by
  intro pipeline world
  rfl

theorem continueRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.continueBlock.run pipeline 5 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawU8GrowingBlock.Old.captured Solidity.Yul.Checks.RawU8Declaration.changed world) := by
  intro pipeline world
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.packed.run pipeline 0 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawU8GrowingBlock.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env), Solidity.Yul.Checks.RawU8GrowingBlock.packed.run pipeline 5 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawU8GrowingBlock.Old.captured Solidity.Yul.Checks.RawU8Declaration.changed world) := by
  intro pipeline world
  change RawU8GrowingBlock.run Old.assign Old.tail pipeline 5 (Old.canonical world) = _
  rw [RawU8GrowingBlock.run,Solidity.Yul.Checks.RawU8GrowingSequence.tailTimeout]
  change ((.error .timeout : Solidity.Source.R RawLoopBody.Flow),
    RawTypedScope.drop (RawCoherent.capture
      (Solidity.Yul.Checks.RawU8Declaration.next world)
      (RawCoherent.prepare (Solidity.Yul.Checks.RawU8Declaration.next world)))) = _
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem dirtyRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 let next := (Solidity.Yul.Checks.RawU8GrowingBlock.breakBlock.run pipeline 5 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.initial 2 257 2 world)).2
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent next = false ∧ next.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8GrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawU8GrowingBlock.program Solidity.Yul.Checks.RawU8GrowingBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawU8GrowingBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawU8GrowingBlock.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.RawU8GrowingBlock.program Solidity.Yul.Checks.RawU8GrowingBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env,world) = (.ok (.normal Solidity.Yul.Checks.RawU8GrowingBlock.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 8 nps ph world).2,normal]
  rfl

theorem sourceNested : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 (Solidity.Source.execS glob frame 10 nps ph (.block Solidity.Yul.Checks.RawU8GrowingBlock.nestedItems) Solidity.Yul.Checks.RawU8GrowingBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env,world) = (.ok (.normal Solidity.Yul.Checks.RawU8GrowingBlock.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  have actual := nested.correct glob frame checked 10 nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)
  have execution : (Solidity.Source.execS glob frame 10 nps ph (.block nestedItems) Old.clean).run
      (Solidity.Source.L0 Old.ctx.env,world) =
      RawLoopBody.represented (nested.run glob.pipeline 10 (Old.canonical world)) := actual.2
  rw [execution,nestedNormal]
  rfl

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 let actual := Solidity.Yul.Checks.RawU8GrowingBlock.partialBlock.run .legacy 7 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8GrowingBlock.Old.ctx.env),
 let actual := Solidity.Yul.Checks.RawU8GrowingBlock.partialBlock.run .viaIR 7 (Solidity.Yul.Checks.RawU8GrowingBlock.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8GrowingBlock
#print axioms Solidity.Yul.RawU8GrowingBlock.correct
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.normal
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.nestedNormal
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.breakRestores
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.continueRestores
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.zero
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.tailTimeout
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.dirtyRestores
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.sourceAll
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.sourceNested
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8GrowingBlock.viaIRPartial
