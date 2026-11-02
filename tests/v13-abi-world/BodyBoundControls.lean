import Solidity.Backend.AbiWorld.RawFreeTransport
import tests.«v13-abi-world».BodyTripleControls
namespace Solidity.Backend.AbiWorld.BodyBoundControls
open AbiEntry TripleReadback BodyTripleControls

def phase (free : Nat) : Input := ⟨BodyTripleControls.sample.data,free⟩

theorem classes : ∀ p ∈ params true true, p.loc = .calldata ∨ ∃ k, p.shape = .word k := by
  intro p h
  simp only [params,BytesArrayReadback.params,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | rfl
  · rcases h with rfl | rfl <;> exact Or.inl rfl
  · exact Or.inr ⟨_,rfl⟩

/-- ALL free bounds keep the same ACTUAL raw entries, even where later body
copies fail. The starting successful entry is the real published fixture. -/
theorem origin (free : Nat) : entry (phase free) 2 (params true true) =
    .ok (entries true true bs xs marker) := by
  rw [show entry (phase free) 2 (params true true) = entry BodyTripleControls.sample 2 (params true true) from
    RawFreeTransport.entry_free _ free 128 2 _ classes]
  exact calldata_origins.1

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

theorem prefix_129 : bodyValues (phase 129) 2 [BytesArrayReadback.byteParam true] byteEs 0 = .ok (.cons (.bytes bs) .nil) := by
  exact bytes_prefix bs xs marker sel post 129 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tail_129 : bodyValues (phase 129) 2 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 32 = .error fuelError :=
  failed _ _ (by decide +kernel)

theorem tail_failure_129 : bodyValues (phase 129) 2 (params true true) (entries true true bs xs marker) 0 = .error fuelError := by
  exact BodyComposition.body_tail_failure (phase 129) 2 byteEs tailEs (.cons (.bytes bs) .nil) 0 _ prefix_129 tail_129

def validationError := "calldata element validation exhausted fuel"

theorem prefix_at_limit : bodyValues (phase lim) 2 [BytesArrayReadback.byteParam true] byteEs 0 = .error lazyError :=
  failed _ _ (by decide +kernel)
theorem tail_at_limit : bodyValues (phase lim) 2 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 32 = .error validationError :=
  failed _ _ (by decide +kernel)

theorem prefix_priority : bodyValues (phase lim) 2 (params true true) (entries true true bs xs marker) 0 = .error lazyError := by
  exact BodyComposition.body_prefix_failure (phase lim) 2 byteEs tailEs 0 _ prefix_at_limit

theorem distinct_errors : lazyError ≠ validationError := by decide +kernel

theorem actual_success : entry (phase 129) 5 (params true true) = .ok (entries true true bs xs marker) ∧
    bodyValues (phase 129) 5 (params true true) (entries true true bs xs marker) 0 = .ok (values bs xs marker) := by
  have h := roundtrip bs xs marker sel post 129 5 true true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨h.2.1,h.2.2.1⟩

theorem verdict_fuel : verdict (phase 129) 2 (params true true) = .blocked fuelError := by
  simp only [verdict,origin,tail_failure_129]

theorem verdict_priority : verdict (phase lim) 2 (params true true) = .blocked lazyError := by
  simp only [verdict,origin,prefix_priority]

/-- Allocating memory copies are deliberately outside enter_free's class. -/
theorem memory_positive : entry (phase 129) 5 (params false true) = .ok (entries false true bs xs marker) := by
  have h := roundtrip bs xs marker sel post 129 5 false true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact h.2.1

theorem memory_panic : entry (phase lim) 5 (params false true) = .error .panic :=
  failed _ _ (by decide +kernel)

theorem outside_class : ¬ ((BytesArrayReadback.byteParam false).loc = .calldata ∨
    ∃ k, (BytesArrayReadback.byteParam false).shape = .word k) := by
  intro h
  rcases h with bad | ⟨k,bad⟩ <;> cases bad

/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.word_free' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.word_free
/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.cref_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.cref_free
/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.calldata_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.calldata_step
/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.word_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.word_step
/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.enter_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.enter_free
/-- info: 'Solidity.Backend.AbiWorld.RawFreeTransport.entry_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawFreeTransport.entry_free
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.classes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.classes
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.origin
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.prefix_129' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.prefix_129
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.tail_129' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.tail_129
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.tail_failure_129' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.tail_failure_129
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.prefix_at_limit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.prefix_at_limit
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.tail_at_limit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.tail_at_limit
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.prefix_priority' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.prefix_priority
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.distinct_errors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.distinct_errors
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.actual_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.actual_success
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.verdict_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.verdict_fuel
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.verdict_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.verdict_priority
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.memory_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.memory_positive
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.memory_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.memory_panic
/-- info: 'Solidity.Backend.AbiWorld.BodyBoundControls.outside_class' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.BodyBoundControls.outside_class
end Solidity.Backend.AbiWorld.BodyBoundControls
