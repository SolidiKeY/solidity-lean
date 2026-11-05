import Solidity.Backend.Passes.MemoryJoinedOutput
import Solidity.Backend.Passes.MemoryTripleAdmissionControls

namespace Solidity.Backend.Passes.MemoryJoinedOutput.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation
open MemoryTripleAdmission.Controls

/-- The actual public whole certificate now keeps the final map already
chosen by its three stage executions, before every saved tail. -/
theorem public_shared :
    ∃ whole : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture)),
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture)) = some whole ∧
      ∃ (final : Machine) (selected : Nat → Fin W), final.stack = [] ∧ ∀ tail,
        run whole.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory whole) 1 7 initialBase (State.init C)
          {initialMachine with stack := tail} captureOut.st {final with stack := tail} selected := by
  obtain ⟨inner,whole,_,accepted,innerFrag,wholeFrag,wholeCode,_,_,_,_⟩ := admitted
  obtain ⟨mb,nb,ob,middle,next,final,_,_,stack,allTails⟩ := shared
  refine ⟨whole,accepted,final,ob,stack,?_⟩
  intro tail
  obtain ⟨_,_,_,_,target,first,second,third⟩ := allTails tail
  have innerMapped : MappedOutput (.memory inner) 1 7 mb σ {middle with stack := tail}
      captureOut.st {final with stack := tail} ob :=
    compose suffixCode captureCode inner (suffix_source σ) innerFrag second third
  have wholeMapped := compose allocationStage inner whole
    ReachabilityControls.fresh_state_reaches_fixture (wholeFrag.trans innerFrag.symm) first innerMapped
  refine ⟨?_,wholeMapped⟩
  rw [wholeCode]
  exact target

/-- Public recognition is also retained for the reached typed bounds failure;
there is no post-failure state or output map. -/
theorem public_failure :
    ∃ whole : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture)),
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture)) = some whole ∧
      ∀ tail, run whole.code {initialMachine with stack := tail} = .revert := by
  obtain ⟨inner,whole,_,accepted,_,_,code,_,_,_,_⟩ :=
    MemoryTripleAdmission.public_admission allocationStage suffixCode badCaptureCode
      prefix_public suffix_public bad_public initialBase (State.init C) initialMachine
      TripleControls.initial_repr7.1 (by decide) (by decide) (by decide) bad_budget
  refine ⟨whole,accepted,?_⟩
  intro tail
  rw [code]
  exact reached_third_failure tail

#print axioms public_shared
#print axioms public_failure
end Solidity.Backend.Passes.MemoryJoinedOutput.Controls
