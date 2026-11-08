import tests.h62.item2.«audit-language».AbiDynamicWitness

/-!
Guarded regression: exact supported success does not determine failure kinds.
A decoder that swaps panic and revert preserves every successful result but must
fail the combined outcome specification. Bounds remain numeric, and this module
covers only mdec's bytes reference semantics, not compiler, gas or fork behavior.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.AbiBytesSpec
open AbiEntry AbiDynamicWitness

def MemoryBytesPanicBounds (I : Input) (pos a : Nat) : Prop :=
  pos + 31 < I.size ∧
    (lim < load I.data pos ∨
      (load I.data pos ≤ lim ∧
        lim < I.free + (a + roundUp (roundUp (load I.data pos) + 32))))

def MemoryBytesRevertBounds (I : Input) (pos a : Nat) : Prop :=
  (¬ pos + 31 < I.size) ∨
    (pos + 31 < I.size ∧ load I.data pos ≤ lim ∧
      I.free + (a + roundUp (roundUp (load I.data pos) + 32)) ≤ lim ∧
      I.size < pos + 32 + load I.data pos)

theorem memory_bytes_revert_numeric_iff (I : Input) (fuel pos a : Nat) :
    mdec I (fuel + 1) .bytes pos a = .error .revert ↔
      MemoryBytesRevertBounds I pos a := by
  unfold MemoryBytesRevertBounds
  rw [memory_bytes_revert_iff]
  constructor
  · rintro (missing | ⟨head, length, next, allocation, truncated⟩)
    · exact Or.inl missing
    · have bounds := (allocation_success_iff I a _ next).mp allocation
      refine Or.inr ⟨head, length, ?_, truncated⟩
      rw [← bounds.1]
      exact bounds.2
  · rintro (missing | ⟨head, length, capacity, truncated⟩)
    · exact Or.inl missing
    · exact Or.inr ⟨head, length, _,
        (allocation_success_iff I a _ _).mpr ⟨rfl, capacity⟩, truncated⟩

/-- Exact success and each distinct failure kind for one shared decoder. -/
def MemoryBytesBehaviorSpec
    (decode : Input → Nat → Nat → Nat → Except Fail (Val .bytes × Nat)) : Prop :=
  MemoryBytesSuccessSpec decode ∧
  (∀ I fuel pos a, decode I (fuel + 1) pos a = .error .panic ↔ MemoryBytesPanicBounds I pos a) ∧
  (∀ I fuel pos a, decode I (fuel + 1) pos a = .error .revert ↔ MemoryBytesRevertBounds I pos a) ∧
  (∀ I fuel pos a, decode I fuel pos a = .error .fuel ↔ fuel = 0)

theorem actual_memory_bytes_behavior_spec :
    MemoryBytesBehaviorSpec (fun I fuel pos a => mdec I fuel .bytes pos a) := by
  refine ⟨actual_memory_bytes_success_spec, ?_, ?_, ?_⟩
  · intro I fuel pos a
    exact memory_bytes_panic_bound_iff I fuel pos a
  · intro I fuel pos a
    exact memory_bytes_revert_numeric_iff I fuel pos a
  · intro I fuel pos a
    exact memory_bytes_fuel_iff I fuel pos a

def swapPanicRevert : Fail → Fail
  | .panic => .revert
  | .revert => .panic
  | .fuel => .fuel

def swappedFailureDecode (I : Input) (fuel pos a : Nat) : Except Fail (Val .bytes × Nat) :=
  match mdec I fuel .bytes pos a with
  | .ok value => .ok value
  | .error failure => .error (swapPanicRevert failure)

theorem swapped_failures_preserve_success : MemoryBytesSuccessSpec swappedFailureDecode := by
  intro I fuel pos a next
  have preserved :
      swappedFailureDecode I (fuel + 1) pos a =
        .ok (.bytes (bytesAt I.data (pos + 32) (load I.data pos)), next) ↔
      mdec I (fuel + 1) .bytes pos a =
        .ok (.bytes (bytesAt I.data (pos + 32) (load I.data pos)), next) := by
    unfold swappedFailureDecode
    cases decoded : mdec I (fuel + 1) .bytes pos a with
    | ok value => rfl
    | error failure =>
      constructor <;> intro impossible <;> cases impossible
  exact preserved.trans (memory_bytes_success_numeric_iff I fuel pos a next)

theorem swapped_failures_behavior_refused : ¬ MemoryBytesBehaviorSpec swappedFailureDecode := by
  intro contract
  have bounds : MemoryBytesPanicBounds (input lim) 36 0 := by
    unfold MemoryBytesPanicBounds
    decide
  have original := (memory_bytes_panic_bound_iff (input lim) 0 36 0).mpr bounds
  have observed : swappedFailureDecode (input lim) 1 36 0 = .error .revert := by
    unfold swappedFailureDecode
    rw [original]
    rfl
  have claimed := (contract.2.1 (input lim) 0 36 0).mpr bounds
  have impossible : (Except.error Fail.revert : Except Fail (Val .bytes × Nat)) = .error .panic :=
    observed.symm.trans claimed
  cases impossible

#print axioms memory_bytes_revert_numeric_iff
#print axioms actual_memory_bytes_behavior_spec
#print axioms swapped_failures_preserve_success
#print axioms swapped_failures_behavior_refused
end Solidity.H62.AuditLanguage.AbiBytesSpec
