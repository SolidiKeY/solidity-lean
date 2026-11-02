import tests.«internal-flow».SharedArgumentFacts
import tests.«internal-flow».ArgumentFailureEndpoint
import Solidity.Backend.InternalFlow.SharedPrefixCapacity
namespace Solidity.Backend.InternalFlow.SharedCallPrefix.Checks
open Evm Evm.Memory
open ArgumentFailureTarget.Checks
open PublishedDirectCalls.Checks (prefixProducer caller initial machine bases words)

/-- Unlike C46's separate argument program, this couples its failure to the
ACTUAL emitted call prefix through a proved public-selector code equality. -/
theorem emitted_argument_failure : ∃ m₁ base₁,
 Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
 StateRepr 1 1 128 F caller.st base₁ m₁ ∧
 Evm.run argumentProducer.code m₁ = .revert ∧
 publicBad.code = argumentProducer.code ++ badSuffix ∧
 Evm.run publicBad.code m₁ = .revert ∧
 Evm.run (prefixProducer.code ++ publicBad.code) machine = .revert := by
 obtain ⟨m₁,base₁,ht,hr,harg,absorbs⟩ := target_argument_program
 have full : Evm.run publicBad.code m₁ = .revert := by
  rw [emitted_bad_prefix]
  exact absorbs badSuffix
 refine ⟨m₁,base₁,ht,hr,harg,emitted_bad_prefix,full,?_⟩
 rw [Evm.run_append_ok ht]
 exact full

theorem emitted_revert : Evm.run (prefixProducer.code ++ publicBad.code) machine = .revert := by
 obtain ⟨_,_,_,_,_,_,_,h⟩ := emitted_argument_failure
 exact h

/-- The original matched allocating success is preserved, including all cells,
private/default/result separation, ordered aliases and the entire stack. -/
theorem emitted_success_vector : words (Evm.run (prefixProducer.code ++ publicGood.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] =
 some [77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [public_good_code]
 exact ordered_target

theorem emitted_success_repr : ∃ m₁ base₁ m₂ base₂,
 Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
 StateRepr 1 1 128 F caller.st base₁ m₁ ∧
 Evm.run (prefixProducer.code ++ publicGood.code) machine = .ok m₂ 0 ∧
 StateRepr 1 1 128 publicGood.frag exported.st base₂ m₂ ∧
 m₂.stack = machine.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
 GrowsAllocator 1 128 (publicGood.cost caller.st) caller.st base₁ m₁ exported.st base₂ m₂ := by
 obtain ⟨m₁,base₁,m₂,base₂,ht,hr,ht₂,hr₂,hk,he,hg⟩ := successful_endpoint
 refine ⟨m₁,base₁,m₂,base₂,ht,hr,?_,?_,hk,he,?_⟩
 · rw [public_good_code,Evm.run_append_ok ht];exact ht₂
 · rw [public_good_frag];exact hr₂
 · rw [public_good_cost];exact hg

theorem emitted_not_fault : Evm.run (prefixProducer.code ++ publicBad.code) machine ≠ .fault := by
 rw [emitted_revert];intro h;cases h
theorem emitted_not_success (m : Machine) (skip : Nat) :
 Evm.run (prefixProducer.code ++ publicBad.code) machine ≠ .ok m skip := by
 rw [emitted_revert];intro h;cases h

theorem wrong_emitted_cursor : words (Evm.run (prefixProducer.code ++ publicGood.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,259,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [emitted_success_vector];decide


/-- A genuinely successful alternative cannot be substituted for the emitted
bad-index program. No instruction equality decider or execution replay needed. -/
theorem distinct_emitted_programs : publicBad.code ≠ publicGood.code := by
 intro same
 obtain ⟨m₁,base₁,m₂,base₂,ht,hr,hs,repr,stack,he,hg⟩ := emitted_success_repr
 have failed := emitted_revert
 rw [same,hs] at failed
 cases failed


/-- Actual selected root frame/cost fields, not supplied capacity assumptions.
Bad cost0 is metadata only, not a failed target frontier observation. -/
theorem public_metadata : publicBad.cost caller.st = 0 ∧ publicGood.cost caller.st = 4 ∧
 publicBad.need = 8 ∧ publicGood.need = 8 := by
 refine ⟨?_,?_,?_,?_⟩
 · rw [public_bad_cost];exact costs.2.1
 · rw [public_good_cost];exact costs.2.2
 · rw [selected_bad_root]
   change max sharedBadCall.need 4 = 8
   rw [← original_bad,exact_frame.1]
   rfl
 · rw [selected_good_root]
   change max sharedGoodCall.need 4 = 8
   rw [← original_good,exact_frame.2]
   rfl

/-- Both actual public alternatives use the SAME represented prefix endpoint.
The larger budget is established at entry, not assumed at the midpoint. -/
theorem shared_capacity : ∃ reached addresses,
 Evm.run prefixProducer.code machine = .ok reached 0 ∧
 StateRepr 1 1 128 F caller.st addresses reached ∧
 reached.stack = machine.stack ∧ BaseExtends initial.H bases addresses ∧
 GrowsAllocator 1 128 (prefixProducer.cost initial) initial bases machine caller.st addresses reached ∧
 AllocationInput 1 128 (publicBad.cost caller.st) caller.st addresses reached ∧
 AllocationInput 1 128 (publicGood.cost caller.st) caller.st addresses reached := by
 apply SharedPrefixCapacity.fork prefixProducer
   PublishedDirectCalls.Checks.initial_repr.1 frame_rooms.1 caller prefix_execution
 rw [public_metadata.1,public_metadata.2.1]
 change AllocationInput 1 128 (prefixProducer.cost initial + 4) initial bases machine
 simpa only [costs.2.2] using good_capacity

/-- The independent explicit prefix is publicly selected and preserves the
SAME complete successful argument-call observation, not a smaller surrogate. -/
theorem constructed_argument_vector : words
 (Evm.run ((Calls.plain PublishedDirectCalls.Checks.prefixConstructed).code ++ publicGood.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] =
 some [77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [← PublishedDirectCalls.Checks.prefix_constructor_eq]
 exact emitted_success_vector

/-- Original wrong-alias control transported without any target replay. -/
theorem constructed_wrong_alias : words
 (Evm.run ((Calls.plain PublishedDirectCalls.Checks.prefixConstructed).code ++ publicGood.code) machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,263,99,42,256,260,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [constructed_argument_vector]
 decide

#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_argument_failure
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_revert
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_vector
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_repr
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_fault
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_success
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.wrong_emitted_cursor
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.distinct_emitted_programs
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_metadata
#print axioms Solidity.Backend.InternalFlow.SharedPrefixCapacity.fork
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.shared_capacity
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_argument_vector
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_wrong_alias
end Solidity.Backend.InternalFlow.SharedCallPrefix.Checks
