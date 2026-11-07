import Solidity.Yul.RawIntegerBlock
import Solidity.Yul.Checks.RawIntegerSequence
/-! Closed integer declaration blocks, raw-word retention and concrete nested
checked block execution. Kernel evidence only; no frontend admission follows. -/
namespace Solidity.Yul.Checks.RawIntegerBlock
namespace Old
export Solidity.Yul.Checks.RawIntegerSequence.Old (ctx env clean canonical boundU boundS changed)
export Solidity.Yul.Checks.RawIntegerSequence (items tail breakTail continueTail signedTail joined)
export Solidity.Yul.Checks.RawPreparedInteger.Old (captured)
end Old
def packed := RawIntegerBlock.adapter Old.ctx "n" Solidity.Source.IntTy.u8 255 Old.boundU [] false false Old.items Old.tail
def breakBlock := RawIntegerBlock.adapter Old.ctx "n" Solidity.Source.IntTy.u8 255 Old.boundU [] false false _ Old.breakTail
def continueBlock := RawIntegerBlock.adapter Old.ctx "n" Solidity.Source.IntTy.u8 255 Old.boundU [] false false _ Old.continueTail
def signedBlock := RawIntegerBlock.adapter Old.ctx "n" Solidity.Yul.Checks.RawPreparedInteger.Old.signed8 (-128) Old.boundS [] false false _ Old.signedTail
def program : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys := .block Old.joined
def nestedItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys := .stmt program .nil
def nested := RawCheckedAdapterSequence.block (RawCheckedAdapterSequence.cons packed RawCheckedAdapterSequence.nil)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false program) := ⟨packed⟩
def nestedWitness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false (.block nestedItems)) := ⟨nested⟩


theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.packed.run pipeline 6 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.changed world) := by
  intro pipeline world
  change RawIntegerBlock.run _ _ _ Old.tail pipeline 6 (Old.canonical world) = _
  rw [RawIntegerBlock.run,Solidity.Yul.Checks.RawIntegerSequence.normal]
  change ((.ok .normal : Solidity.Source.R RawLoopBody.Flow),
    RawTypedScope.drop (Solidity.Yul.Checks.RawPreparedInteger.afterCopy world)) = _
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem nestedNormal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.nested.run pipeline 8 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.changed world) := by
  intro pipeline world
  change RawCheckedAdapterSequence.runBlock
    (RawCheckedAdapterSequence.cons packed RawCheckedAdapterSequence.nil) pipeline 8 (Old.canonical world) = _
  simp only [RawCheckedAdapterSequence.runBlock,RawCheckedAdapterSequence.cons,
    RawCheckedAdapterSequence.runCons]
  rw [normal]
  rfl

theorem breakRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.breakBlock.run pipeline 4 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.clean world) := by
  intro pipeline world
  rfl

theorem continueRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.continueBlock.run pipeline 4 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.clean world) := by
  intro pipeline world
  rfl

theorem preTimeouts : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.RawIntegerBlock.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerBlock.Old.boundU Solidity.Yul.Checks.RawIntegerBlock.Old.tail pipeline 0 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) ∧ Solidity.Yul.RawIntegerBlock.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerBlock.Old.boundU Solidity.Yul.Checks.RawIntegerBlock.Old.tail pipeline 3 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = (.error .timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem tailTimeout : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.packed.run pipeline 4 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.error .timeout,Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.clean world) := by
  intro pipeline world
  change RawIntegerBlock.run _ _ _ Old.tail pipeline 4 (Old.canonical world) = _
  rw [RawIntegerBlock.run,Solidity.Yul.Checks.RawIntegerSequence.tailTimeout]
  change ((.error .timeout : Solidity.Source.R RawLoopBody.Flow),
    RawTypedScope.drop (RawCoherent.capture
      (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world)
      (RawCoherent.prepare (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world)))) = _
  rw [RawCoherent.prepare_coherent _ (Solidity.Yul.Checks.RawPreparedInteger.unsignedCoherent world)]
  unfold RawTypedScope.drop
  rw [RawCoherent.prepare_coherent _ ((RawCoherent.coherent_iff _).mpr rfl)]
  rfl

theorem dirtyRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env),
 let next := (Solidity.Yul.Checks.RawIntegerBlock.breakBlock.run pipeline 4 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world)).2
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent next = false ∧ next.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem signedRestores : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env), Solidity.Yul.Checks.RawIntegerBlock.signedBlock.run pipeline 4 (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world) = (.ok .normal,Solidity.Yul.Checks.RawIntegerBlock.Old.captured Solidity.Yul.Checks.RawIntegerBlock.Old.clean world) := by
  intro pipeline world
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawIntegerBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawIntegerBlock.program Solidity.Yul.Checks.RawIntegerBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerBlock.Old.env,world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawIntegerBlock.packed.run glob.pipeline fuel (Solidity.Yul.Checks.RawIntegerBlock.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  exact packed.correct glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env),
 (Solidity.Source.execS glob frame 6 nps ph Solidity.Yul.Checks.RawIntegerBlock.program Solidity.Yul.Checks.RawIntegerBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerBlock.Old.env,world) = (.ok (.normal Solidity.Yul.Checks.RawIntegerBlock.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerBlock.Old.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 6 nps ph world).2,normal]
  rfl

theorem sourceNested : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawIntegerBlock.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawIntegerBlock.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawIntegerBlock.Old.env),
 (Solidity.Source.execS glob frame 8 nps ph (.block Solidity.Yul.Checks.RawIntegerBlock.nestedItems) Solidity.Yul.Checks.RawIntegerBlock.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerBlock.Old.env,world) = (.ok (.normal Solidity.Yul.Checks.RawIntegerBlock.Old.changed),(Solidity.Source.L0 Solidity.Yul.Checks.RawIntegerBlock.Old.env,world)) := by
  intro glob frame checked nps ph world
  have actual := nested.correct glob frame checked 8 nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)
  have execution : (Solidity.Source.execS glob frame 8 nps ph (.block nestedItems) Old.clean).run
      (Solidity.Source.L0 Old.env,world) =
      RawLoopBody.represented (nested.run glob.pipeline 8 (Old.canonical world)) := actual.2
  rw [execution,nestedNormal]
  rfl
end Solidity.Yul.Checks.RawIntegerBlock
#print axioms Solidity.Yul.RawIntegerBlock.close_correct
#print axioms Solidity.Yul.RawIntegerBlock.correct
#print axioms Solidity.Yul.Checks.RawIntegerBlock.normal
#print axioms Solidity.Yul.Checks.RawIntegerBlock.nestedNormal
#print axioms Solidity.Yul.Checks.RawIntegerBlock.breakRestores
#print axioms Solidity.Yul.Checks.RawIntegerBlock.continueRestores
#print axioms Solidity.Yul.Checks.RawIntegerBlock.preTimeouts
#print axioms Solidity.Yul.Checks.RawIntegerBlock.tailTimeout
#print axioms Solidity.Yul.Checks.RawIntegerBlock.dirtyRestores
#print axioms Solidity.Yul.Checks.RawIntegerBlock.signedRestores
#print axioms Solidity.Yul.Checks.RawIntegerBlock.sourceAll
#print axioms Solidity.Yul.Checks.RawIntegerBlock.sourceNormal
#print axioms Solidity.Yul.Checks.RawIntegerBlock.sourceNested
