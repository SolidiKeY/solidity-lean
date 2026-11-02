import tests.«internal-flow».ArgumentFailureFacts
namespace Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks
open Evm Evm.Memory
open PublishedDirectCalls.Checks (prefixProducer caller initial bases machine initial_repr words)

theorem bad_capacity : AllocationInput 1 128
 (prefixProducer.cost initial + badProducer.cost caller.st) initial bases machine := by
 rw [costs.1,costs.2.1]
 exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩
theorem good_capacity : AllocationInput 1 128
 (prefixProducer.cost initial + goodProducer.cost caller.st) initial bases machine := by
 rw [costs.1,costs.2.2]
 exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

/-- Actual prefix representation, old-address extension, protected stack and
capacity transport. There is deliberately no failed-call output State. -/
theorem failed_endpoint : ∃ m₁ base₁,
 Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
 StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
 m₁.stack = machine.stack ∧ BaseExtends initial.H bases base₁ ∧
 GrowsAllocator 1 128 (prefixProducer.cost initial) initial bases machine caller.st base₁ m₁ ∧
 Evm.run badProducer.code m₁ = .revert :=
 after_prefix prefixProducer "arguments" badArgs ret body badProducer initial_repr.1
  frame_rooms.1 frame_rooms.2.1 caller prefix_execution bad_capacity failed_arguments

theorem failed_composition : Evm.run (prefixProducer.code ++ badProducer.code) machine = .revert := by
 obtain ⟨m₁,base₁,ht,hr,hk,he,hg,hbad⟩ := failed_endpoint
 rw [Evm.run_append_ok ht]
 exact hbad

/-- Same populated prefix and memory-result/private-allocation body, with only
its last argument changed to the live index. All midpoint premises are derived. -/
theorem successful_endpoint : ∃ m₁ base₁ m₂ base₂,
 Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
 StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
 Evm.run goodProducer.code m₁ = .ok m₂ 0 ∧
 StateRepr 1 1 128 goodProducer.frag exported.st base₂ m₂ ∧
 m₂.stack = machine.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
 GrowsAllocator 1 128 (goodProducer.cost caller.st) caller.st base₁ m₁ exported.st base₂ m₂ := by
 obtain ⟨m₁,base₁,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint prefixProducer
  initial_repr.1 frame_rooms.1 (good_capacity.of_le (Nat.le_add_right _ _)) caller prefix_execution
 obtain ⟨m₂,base₂,ht₂,hr₂,hk₂,he₂,hg₂⟩ := PublishedDirectCalls.statement_endpoint goodProducer
  hr frame_rooms.2.2 (hg.nextInput good_capacity) exported good_call
 exact ⟨m₁,base₁,m₂,base₂,ht,hr,ht₂,hr₂,hk₂.trans hk,he₂,hg₂⟩

theorem failure_not_success (m : Machine) (skip : Nat) :
 Evm.run (prefixProducer.code ++ badProducer.code) machine ≠ .ok m skip := by
 rw [failed_composition];intro h;cases h
theorem failure_not_fault : Evm.run (prefixProducer.code ++ badProducer.code) machine ≠ .fault := by
 rw [failed_composition];intro h;cases h
theorem failure_not_panic : badArgs.evalT caller.st ≠ .error .panic := by
 rw [failed_arguments];intro h;cases h
theorem failure_not_exhausted : badArgs.evalT caller.st ≠ .error .exhausted := by
 rw [failed_arguments];intro h;cases h
theorem failure_not_payload : badArgs.evalT caller.st ≠ .error (.revertWith [7]) := by
 rw [failed_arguments];intro h;cases h


/-- Complete successful word observation, including private physical cells.
Logical frame dropping does not erase these memory cells. -/
theorem ordered_target : words (Evm.run (prefixProducer.code ++ goodProducer.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] =
 some [77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by decide +kernel

theorem exact_frame : badProducer.need = 8 ∧ goodProducer.need = 8 := by decide +kernel

theorem wrong_target_alias : words (Evm.run (prefixProducer.code ++ goodProducer.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,263,99,42,256,260,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [ordered_target];decide

theorem wrong_cursor : words (Evm.run (prefixProducer.code ++ goodProducer.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,259,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [ordered_target];decide

/-- This is a rejected capacity premise, not a runtime error assertion. -/
theorem short_frame : ¬ 1 + goodProducer.need ≤ 8 := by rw [exact_frame.2];decide


/-- The separately compiled argument-declaration program reverts at the SAME
represented caller. No equality with a prefix of the full call code is assumed.
Any code appended to this argument program is absorbed. -/
theorem target_argument_program : ∃ m₁ base₁,
 Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
 StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
 Evm.run argumentProducer.code m₁ = .revert ∧
 ∀ suffix, Evm.run (argumentProducer.code ++ suffix) m₁ = .revert := by
 obtain ⟨m₁,base₁,ht,hr,hk,he,hg,hbad⟩ := failed_endpoint
 have capacity : AllocationInput 1 128 (argumentProducer.cost caller.st) caller.st base₁ m₁ := by
  rw [argument_cost_room.1]; exact .inl rfl
 have failed : Evm.run argumentProducer.code m₁ = .revert := by
  rcases argumentProducer.sound hr argument_cost_room.2 capacity with
   ⟨o,m,base,hs,_⟩ | ⟨_,target⟩
  · rw [argument_failure] at hs;contradiction
  · exact target
 exact ⟨m₁,base₁,ht,hr,failed,fun _ => Evm.run_append_revert failed⟩


#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.bad_capacity
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.good_capacity
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failed_endpoint
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failed_composition
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.successful_endpoint
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failure_not_success
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failure_not_fault
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failure_not_panic
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failure_not_exhausted
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failure_not_payload
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.ordered_target
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.exact_frame
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.wrong_target_alias
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.wrong_cursor
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.short_frame
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.target_argument_program
end Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks
