import Solidity.Backend.AbiEntry.CompositionInterface
import Solidity.Backend.AbiEntry.EntryComposition

/-! Additive audit fixture for the mapped ABI-entry structural interfaces.
These are semantic entry observations, not compiled decoder, gas or fork proofs.
The interfaces and their hypotheses remain unchanged. -/
namespace Solidity.H62.AuditMemoryOperations.Entry
open Solidity.AbiEntry
open Solidity.Backend.AbiEntry

def wordParameter : Param := ⟨.word .bool, .value, false⟩
def emptyInput : Input := ⟨[], 0⟩
def zeroInput : Input := ⟨List.replicate 36 0, 0⟩
def zeroValue : Val (.word .bool) := .word ⟨0, by decide, by decide⟩
def zeroEntries : Entries [wordParameter] := .cons (.val zeroValue) .nil

/-- Both global fields hold together for the same append operation. -/
theorem compositionCertificate : Interface.EntryCompositionCertificate EntryComposition.appendEntries :=
  { head_extent := EntryComposition.heads_append
    ordered := EntryComposition.enter_append }

/-- A nonempty parameter list inhabits the prefix-failure antecedent. -/
theorem prefix_failure_hypothesis :
    enter emptyInput 0 [wordParameter] 0 0 = .error .fuel := rfl

theorem prefix_failure_application :
    enter emptyInput 0 ([wordParameter] ++ [wordParameter]) 0 0 = .error .fuel :=
  EntryComposition.prefix_failure emptyInput 0 [wordParameter] [wordParameter] 0 0 .fuel
    prefix_failure_hypothesis

/-- All dependent tail-failure antecedents hold for the same prefix entries,
reached cursor, input and fuel; separate inhabitation would not suffice. -/
theorem tail_failure_hypotheses :
    enter emptyInput 0 [] 0 0 = .ok (Entries.nil, 0) ∧
    enter emptyInput 0 [wordParameter] (0 + headsOf []) 0 = .error .fuel :=
  ⟨rfl, rfl⟩

theorem tail_failure_application :
    enter emptyInput 0 ([] ++ [wordParameter]) 0 0 = .error .fuel :=
  EntryComposition.tail_failure emptyInput 0 [] [wordParameter] 0 0 0 Entries.nil .fuel
    tail_failure_hypotheses.1 tail_failure_hypotheses.2

/-- A successful nonempty prefix advances the head by one word before
an invalid Boolean in the tail. The allocated cursor is unchanged for words. -/
def invalidTailInput : Input := ⟨List.replicate 67 0 ++ [2], 128⟩

theorem nonempty_tail_hypotheses :
    enter invalidTailInput 2 [wordParameter] 0 7 = .ok (zeroEntries, 7) ∧
    enter invalidTailInput 2 [wordParameter] (0 + headsOf [wordParameter]) 7 = .error .revert :=
  ⟨rfl, rfl⟩

theorem nonempty_tail_application :
    enter invalidTailInput 2 ([wordParameter] ++ [wordParameter]) 0 7 = .error .revert :=
  EntryComposition.tail_failure invalidTailInput 2 [wordParameter] [wordParameter] 0 7 7
    zeroEntries .revert nonempty_tail_hypotheses.1 nonempty_tail_hypotheses.2

/-- Nonempty support, rather than an empty-list implication. -/
theorem word_classes :
    ∀ p ∈ [wordParameter], p.loc = .calldata ∨ ∃ k, p.shape = .word k := by
  intro p member
  have same : p = wordParameter := List.mem_singleton.mp member
  subst p
  exact Or.inr ⟨.bool, rfl⟩

theorem word_location_hypothesis : wordParameter.loc ≠ .calldata := by
  intro same
  cases same

/-- Actual success, retaining the decoded Boolean and nonempty entry list. -/
theorem entry_success : entry zeroInput 2 [wordParameter] = .ok zeroEntries := rfl

/-- The adjacent fuel boundary is observable separately from empty REVERT. -/
theorem entry_low_fuel : entry zeroInput 1 [wordParameter] = .error .fuel := rfl

theorem entry_short_input : entry emptyInput 2 [wordParameter] = .error .revert := rfl

theorem always_revert_rejected :
    (Except.error .revert : Except Fail (Entries [wordParameter])) ≠
      entry zeroInput 2 [wordParameter] := by
  rw [entry_success]
  intro impossible
  cases impossible

#check @Interface.EntryCompositionCertificate.head_extent
#check @Interface.EntryCompositionCertificate.ordered
#check @EntryComposition.prefix_failure
#check @EntryComposition.tail_failure
#print axioms nonempty_tail_hypotheses
#print axioms nonempty_tail_application
#print axioms compositionCertificate
#print axioms prefix_failure_application
#print axioms tail_failure_application
#print axioms word_classes
#print axioms word_location_hypothesis
#print axioms entry_success
#print axioms entry_low_fuel
#print axioms entry_short_input
#print axioms always_revert_rejected
end Solidity.H62.AuditMemoryOperations.Entry
