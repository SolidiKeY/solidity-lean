import Solidity.Backend.Passes.MemoryJoinedOutputControls

/-! Guard loss of shared final-map selection across caller tails, and fabrication
of an output map after reached failure. Instantiate the existing public memory
compiler certificates; this does not assert native ByteWorld realization. -/
open Solidity Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

namespace Solidity.Backend.Passes.AuditJoinedMemory
/-! Regression: a recognized whole memory compilation must retain the same
selected final map before every caller tail; recognized reached failure must
not invent an output map. Use actual public admission, not stage-only success. -/
def successProgram := ReachabilityControls.populatedBuilder.join
  (MemoryJoinCost.Controls.appendAllocation.join MemoryTripleAdmission.Controls.capture)
def failureProgram := ReachabilityControls.populatedBuilder.join
  (MemoryJoinCost.Controls.appendAllocation.join MemoryTripleAdmission.Controls.badCapture)
theorem joint :
    Memory.StateRepr 1 1 7 (Frag.init []) (State.init Controls.Fixture.C)
      AllocatingControls.initialBase AllocatingControls.initialMachine ∧
    Memory.AllocationInput 1 7 (Memory.allocationCostProg successProgram (State.init Controls.Fixture.C))
      (State.init Controls.Fixture.C) AllocatingControls.initialBase AllocatingControls.initialMachine ∧
    Memory.AllocationInput 1 7 (Memory.allocationCostProg failureProgram (State.init Controls.Fixture.C))
      (State.init Controls.Fixture.C) AllocatingControls.initialBase AllocatingControls.initialMachine ∧
    Memory.allocationCostProg successProgram (State.init Controls.Fixture.C) = 9 ∧
    (∃ tail : List Word, tail = []) :=
  ⟨TripleControls.initial_repr7.1,MemoryTripleAdmission.Controls.budget,
    MemoryTripleAdmission.Controls.bad_budget,MemoryTripleAdmission.Controls.total_cost,[],rfl⟩
def public_shared := MemoryJoinedOutput.Controls.public_shared
def public_failure := MemoryJoinedOutput.Controls.public_failure

/-- info: 'Solidity.Backend.Passes.AuditJoinedMemory.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedMemory.joint
/-- info: 'Solidity.Backend.Passes.AuditJoinedMemory.public_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedMemory.public_shared
/-- info: 'Solidity.Backend.Passes.AuditJoinedMemory.public_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedMemory.public_failure
end Solidity.Backend.Passes.AuditJoinedMemory
