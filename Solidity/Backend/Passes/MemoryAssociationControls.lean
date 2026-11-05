import Solidity.Backend.Passes.MemoryAssociation
import Solidity.Backend.Passes.MemoryJoinedOutputControls

namespace Solidity.Backend.Passes.MemoryAssociation.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation
open MemoryTripleAdmission.Controls

/-- Both actual public whole compiler selections retain the SAME full output
map before all tails, including all old aliases and reached allocator growth. -/
theorem both_outputs :
    ∃ (left : CompiledProg 1 (Frag.init [])
        ((ReachabilityControls.populatedBuilder.join appendAllocation).join capture))
      (right : CompiledProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture))),
      Memory.compileProg 1 (Frag.init [])
        ((ReachabilityControls.populatedBuilder.join appendAllocation).join capture) = some left ∧
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture)) = some right ∧
      ∃ (final : Machine) (selectedBase : Nat → Fin W), final.stack = [] ∧ ∀ tail,
        run left.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        run right.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory left) 1 7 initialBase (State.init C)
          {initialMachine with stack := tail} captureOut.st {final with stack := tail} selectedBase ∧
        MappedOutput (.memory right) 1 7 initialBase (State.init C)
          {initialMachine with stack := tail} captureOut.st {final with stack := tail} selectedBase ∧
        ¬ (Compilation.memory left).Input 1 6 initialBase (State.init C) initialMachine := by
  obtain ⟨right,hr,final,selectedBase,stack,tails⟩ := MemoryJoinedOutput.Controls.public_shared
  obtain ⟨left,hl⟩ := public_left right hr
  refine ⟨left,right,hl,hr,final,selectedBase,stack,?_⟩
  intro tail
  obtain ⟨target,mapped⟩ := tails tail
  refine ⟨?_,target,?_,mapped,?_⟩
  · rw [terminal_eq left right hl hr]
    exact target
  · exact (output_iff left right hl hr _ _ _ _ _ _).mpr mapped
  · intro input
    exact third_frame_required right ((input_iff left right _ _ _).mp input)

/-- Association does not erase the reached bounds failure or invent an output. -/
theorem both_failures :
    ∃ (left : CompiledProg 1 (Frag.init [])
        ((ReachabilityControls.populatedBuilder.join appendAllocation).join badCapture))
      (right : CompiledProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture))),
      Memory.compileProg 1 (Frag.init [])
        ((ReachabilityControls.populatedBuilder.join appendAllocation).join badCapture) = some left ∧
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture)) = some right ∧
      ∀ tail, run left.code {initialMachine with stack := tail} = .revert ∧
        run right.code {initialMachine with stack := tail} = .revert := by
  obtain ⟨right,hr,tails⟩ := MemoryJoinedOutput.Controls.public_failure
  obtain ⟨left,hl⟩ := public_left right hr
  refine ⟨left,right,hl,hr,?_⟩
  intro tail
  exact ⟨by rw [terminal_eq left right hl hr]; exact tails tail,tails tail⟩

#print axioms both_outputs
#print axioms both_failures
end Solidity.Backend.Passes.MemoryAssociation.Controls
