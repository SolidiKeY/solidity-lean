import Solidity.Yul.RawCheckedAdapterSequence
import Solidity.Yul.Checks.RawCheckedAdapter
/-! Nested concrete conditional/sequence/block producers. Normal flow executes
an effectful tail; break/continue skip it and errors retain partial frames.
Source controls keep actual checked/coherent premises. Kernel evidence only. -/
namespace Solidity.Yul.Checks.RawCheckedAdapterSequence
namespace Old
export Solidity.Yul.Checks.RawCheckedAdapter.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag breakItems breakProof clearContinueItems clearContinueProof)
export Solidity.Yul.Checks.RawCheckedControlSequence (tailItems tailProof normalItems normalProof panicItems panicProof)
export Solidity.Yul.Checks.RawCheckedControlWhile (clearItems clearBlock)
export Solidity.Yul.Checks.RawU8Statement (clean)
end Old
def stmt : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .ifElse (.local Old.flag) (.block Old.breakItems) (.block Old.clearContinueItems)
def head : RawCheckedAdapter.Adapter Old.ctx [] false false stmt :=
 Solidity.Yul.Checks.RawCheckedAdapter.branch
def rest : RawCheckedAdapterSequence.Items Old.ctx [] false false Old.tailItems :=
 Solidity.Yul.RawCheckedAdapterSequence.ofSequence Old.tailProof
def items : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt stmt Old.tailItems
def joined : RawCheckedAdapterSequence.Items Old.ctx [] false false items :=
 Solidity.Yul.RawCheckedAdapterSequence.cons head rest
def boxed : RawCheckedAdapter.Adapter Old.ctx [] false false (.block items) :=
 Solidity.Yul.RawCheckedAdapterSequence.block joined
def clearRestItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.block Old.clearItems) .nil
def clearProof : RawCheckedControlSequence.Supported Old.ctx [] false false clearRestItems :=
 .cons Old.clearBlock .nil
def clearRest : RawCheckedAdapterSequence.Items Old.ctx [] false false clearRestItems :=
 Solidity.Yul.RawCheckedAdapterSequence.ofSequence clearProof
def normalHead : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.normalItems) :=
 Solidity.Yul.RawCheckedAdapter.block Old.normalProof
def normalItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.block Old.normalItems) clearRestItems
def normal : RawCheckedAdapterSequence.Items Old.ctx [] false false normalItems :=
 Solidity.Yul.RawCheckedAdapterSequence.cons normalHead clearRest
def panicItems : Solidity.Source.RItems Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .stmt (.block Old.panicItems) Old.tailItems
def panic : RawCheckedAdapterSequence.Items Old.ctx [] false false panicItems :=
 Solidity.Yul.RawCheckedAdapterSequence.cons (Solidity.Yul.RawCheckedAdapter.block Old.panicProof) rest
def witness : Nonempty (RawCheckedAdapterSequence.Items Old.ctx [] false false items) := ⟨joined⟩
end Solidity.Yul.Checks.RawCheckedAdapterSequence

namespace Solidity.Yul.Checks.RawCheckedAdapterSequence
theorem breakSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.rawFlag 2) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons Solidity.Yul.Checks.RawCheckedAdapter.branch rest pipeline 17
    (Old.initial 2 257 2 world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,Solidity.Yul.Checks.RawCheckedAdapter.trueFlow]

theorem continueSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 0 world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons Solidity.Yul.Checks.RawCheckedAdapter.branch rest pipeline 17
    (Old.initial 2 257 0 world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,Solidity.Yul.Checks.RawCheckedAdapter.falseFlow]

theorem blockBreak : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.boxed.run pipeline 18 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.rawFlag 2) world) := by
  intro pipeline world
  change joined.run pipeline 17 (Old.initial 2 257 2 world) = _
  exact breakSkips pipeline world

theorem normalFirst : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.normalHead.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) := by
  intro pipeline world
  rfl

theorem normalTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.clearRest.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool true)) world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  rfl

theorem normalRunsTail : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.normal.run pipeline 18 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) = (.ok .normal,Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  change Solidity.Yul.RawCheckedAdapterSequence.runCons normalHead clearRest pipeline 18 (Old.initial 2 257 2 world) = _
  rw [Solidity.Yul.RawCheckedAdapterSequence.runCons,normalFirst]
  exact normalTail pipeline world

theorem tailWouldWrite : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 (Solidity.Yul.Checks.RawCheckedAdapterSequence.rest.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawCheckedAdapterSequence.rest.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world)).2 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.flagCell).val = 1 := by
  intro pipeline world
  exact ⟨rfl,rfl⟩

theorem panicSkips : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 (Solidity.Yul.Checks.RawCheckedAdapterSequence.panic.run pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 511 1 2 world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawCheckedAdapterSequence.panic.run pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.xCell).val = 511 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawCheckedAdapterSequence.panic.run pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.flagCell).val = 2 ∧ (Solidity.Yul.Checks.RawCheckedAdapterSequence.panic.run pipeline 8 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  have facts := Solidity.Yul.Checks.RawCheckedControlSequence.panicStops pipeline world
  simp only [panic,Solidity.Yul.RawCheckedAdapterSequence.cons,Solidity.Yul.RawCheckedAdapterSequence.runCons,
    Solidity.Yul.RawCheckedAdapter.block,Solidity.Yul.RawCheckedControlSequence.block,facts.1]
  exact ⟨True.intro,facts.2.1,facts.2.2.1,facts.2.2.2⟩

theorem sourceItems : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph Solidity.Yul.Checks.RawCheckedAdapterSequence.items locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact joined.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceBlock : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterSequence.boxed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedAdapterSequence.items) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapterSequence.boxed.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact boxed.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceBreakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 (Solidity.Source.execItems glob frame 17 nps ph Solidity.Yul.Checks.RawCheckedAdapterSequence.items Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world) =
 (.ok (.brk Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanBreak),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourceNormalCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 (Solidity.Source.execItems glob frame 18 nps ph Solidity.Yul.Checks.RawCheckedAdapterSequence.normalItems Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world) =
 (.ok (.normal Solidity.Yul.Checks.RawCheckedControlWhileHorizon.cleanContinue),(Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem zeroCounterexample : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run pipeline 0 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) ≠ Solidity.Yul.Checks.RawCheckedAdapterSequence.joined.run pipeline 17 (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  change .error .timeout = (joined.run pipeline 17 (Old.initial 2 257 2 world)).1 at tags
  rw [breakSkips pipeline world] at tags
  cases tags

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapterSequence.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedAdapter.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapterSequence
#print axioms Solidity.Yul.RawCheckedAdapterSequence.cons_correct
#print axioms Solidity.Yul.RawCheckedAdapterSequence.block_correct
#print axioms Solidity.Yul.RawCheckedAdapterSequence.ofSequence
#print axioms Solidity.Yul.RawCheckedAdapterSequence.fromItems
#print axioms Solidity.Yul.RawCheckedAdapterSequence.nil
#print axioms Solidity.Yul.RawCheckedAdapterSequence.cons
#print axioms Solidity.Yul.RawCheckedAdapterSequence.block
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.breakSkips
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.continueSkips
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.blockBreak
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.normalFirst
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.normalTail
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.normalRunsTail
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.tailWouldWrite
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.panicSkips
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.sourceItems
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.sourceBlock
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.sourceBreakCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.sourceNormalCompletes
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.zeroCounterexample
#print axioms Solidity.Yul.Checks.RawCheckedAdapterSequence.dirtyBoundary
