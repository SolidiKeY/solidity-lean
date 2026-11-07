import tests.h62.item2.«audit-compiler-transport».Audit
import Solidity.Backend.Passes.LoopReframedFailureControls

/-! H69: deliberate contradictory input tuples are audited by impossibility.
Only literal-False original conclusions are used here. A negative conclusion
is never unfolded to fabricate an additional hypothesis. -/
namespace H62.CompilerTransport.H69

/-- A reference into the original empty initial heap cannot exist. -/
theorem empty_heap_joint_impossible :
    ¬ jointHypothesesStr% "_private.Solidity.Backend.Passes.MemoryCallControls.0.Solidity.Backend.Passes.MemoryCallControls.noRefs" :=
  jointImpossibleStr% "_private.Solidity.Backend.Passes.MemoryCallControls.0.Solidity.Backend.Passes.MemoryCallControls.noRefs"

/-- The same target cannot satisfy the stale pointer relation and the incompatible
reached address observation. Individual premise inhabitation is not inferred. -/
theorem stale_pointer_joint_impossible :
    ¬ jointHypothesesStr% "_private.Solidity.Backend.Passes.LoopReframedFailureControls.0.Solidity.Backend.Passes.LoopReframedFailureControls.stale_pointer" :=
  jointImpossibleStr% "_private.Solidity.Backend.Passes.LoopReframedFailureControls.0.Solidity.Backend.Passes.LoopReframedFailureControls.stale_pointer"

/-- Zero external parameters have the unique empty conjunction of premises. -/
theorem empty_joint_witness : True := True.intro

#print axioms empty_heap_joint_impossible
#print axioms stale_pointer_joint_impossible
#print axioms empty_joint_witness
end H62.CompilerTransport.H69
