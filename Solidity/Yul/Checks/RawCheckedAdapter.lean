import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.Checks.RawCheckedControlIfElse
/-! Concrete checked adapter inhabitants preserve the proved producers,
including selected control flow and the full checked/coherent Source boundary. -/
namespace Solidity.Yul.Checks.RawCheckedAdapter
namespace Old
export Solidity.Yul.Checks.RawCheckedControlIfElse.Old (ctx env initial xCell flagCell flag readFlag frame rawFlag breakItems breakProof clearContinueItems clearContinueProof)
end Old
def branch : RawCheckedAdapter.Adapter Old.ctx [] false false
 (.ifElse (.local Old.flag) (.block Old.breakItems) (.block Old.clearContinueItems)) :=
 Solidity.Yul.RawCheckedAdapter.conditional Old.readFlag Old.breakProof Old.clearContinueProof
def block : RawCheckedAdapter.Adapter Old.ctx [] false false (.block Old.breakItems) :=
 Solidity.Yul.RawCheckedAdapter.block Old.breakProof
def pureBreak : RawCheckedAdapter.Adapter Old.ctx [] false false .brk :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .break_)
def witness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false
 (.ifElse (.local Old.flag) (.block Old.breakItems) (.block Old.clearContinueItems))) := ⟨branch⟩
end Solidity.Yul.Checks.RawCheckedAdapter

namespace Solidity.Yul.Checks.RawCheckedAdapter
theorem trueFlow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapter.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapter.branch.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapter.Old.initial 2 257 2 world) = (.ok (.break_ rfl),Solidity.Yul.Checks.RawCheckedAdapter.Old.frame 257 257 (Solidity.Yul.Checks.RawCheckedAdapter.Old.rawFlag 2) world) := by
  intro pipeline world
  exact Solidity.Yul.Checks.RawCheckedControlIfElse.trueBreak pipeline world

theorem falseFlow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapter.Old.env),
 Solidity.Yul.Checks.RawCheckedAdapter.branch.run pipeline 16 (Solidity.Yul.Checks.RawCheckedAdapter.Old.initial 2 257 0 world) = (.ok (.continue_ rfl),Solidity.Yul.Checks.RawCheckedAdapter.Old.frame 257 257 (Solidity.Yul.LocalValue.clean (.bool false)) world) := by
  intro pipeline world
  exact Solidity.Yul.Checks.RawCheckedControlIfElse.falseContinue pipeline world

theorem pureBreakRun : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawCheckedAdapter.Old.ctx),
 Solidity.Yul.Checks.RawCheckedAdapter.pureBreak.run pipeline 1 state = (.ok (.break_ rfl),state) := by
  intro pipeline state
  rfl

theorem sourceBranch : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapter.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapter.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapter.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapter.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapter.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapter.branch.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.ifElse (.local Solidity.Yul.Checks.RawCheckedAdapter.Old.flag) (.block Solidity.Yul.Checks.RawCheckedAdapter.Old.breakItems) (.block Solidity.Yul.Checks.RawCheckedAdapter.Old.clearContinueItems)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapter.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapter.branch.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact branch.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem sourceBlock : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawCheckedAdapter.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawCheckedAdapter.Old.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawCheckedAdapter.Old.env.layout Solidity.Yul.Checks.RawCheckedAdapter.Old.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapter.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapter.block.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block Solidity.Yul.Checks.RawCheckedAdapter.Old.breakItems) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawCheckedAdapter.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawCheckedAdapter.block.run glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) := by
  intro glob frame checked fuel nps ph locals world
  exact block.correct glob frame checked fuel nps ph (RawFrame.ofClean locals world)
    (@RawCoherent.coherent_ofClean Old.ctx locals world)

theorem dirtyBoundary : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawCheckedAdapter.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawCheckedAdapter.Old.initial 2 257 2 world) ≠ true := by
  intro world
  exact Solidity.Yul.Checks.RawCheckedControlIfElse.dirtyBoundary world

end Solidity.Yul.Checks.RawCheckedAdapter
#print axioms Solidity.Yul.RawCheckedAdapter.fromAdapter
#print axioms Solidity.Yul.RawCheckedAdapter.block
#print axioms Solidity.Yul.RawCheckedAdapter.conditional
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.trueFlow
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.falseFlow
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.pureBreakRun
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.sourceBranch
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.sourceBlock
#print axioms Solidity.Yul.Checks.RawCheckedAdapter.dirtyBoundary
