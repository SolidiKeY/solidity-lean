import Solidity.Semantics.AbiEntry

/-! Actual one-boolean ABI entry runs, with nonzero output and observable
refusals. These concern the existing ABI decoder, not bytecode compilation,
gas charging, fork agreement, Source termination or complete frontend coverage. -/
namespace Solidity.H62.AuditLanguage
open AbiEntry

def boolParams : List Param := [⟨.word .bool, .value, false⟩]
def boolInput (b : UInt8) : Input := ⟨List.replicate 35 0 ++ [b], 128⟩
def trueWord : Word .bool := ⟨1, by decide, rfl⟩
def falseWord : Word .bool := ⟨0, by decide, rfl⟩

theorem bool_true_success (fuel : Nat) :
    entry (boolInput 1) (fuel + 2) boolParams =
      .ok (.cons (.val (.word trueWord)) .nil) := by
  rfl

theorem bool_false_success (fuel : Nat) :
    entry (boolInput 0) (fuel + 2) boolParams =
      .ok (.cons (.val (.word falseWord)) .nil) := by
  rfl

theorem malformed_bool_reverts (fuel : Nat) :
    entry (boolInput 2) (fuel + 2) boolParams = .error .revert := by
  rfl

theorem truncated_bool_reverts (fuel : Nat) :
    entry ⟨List.replicate 35 0, 128⟩ (fuel + 2) boolParams = .error .revert := by
  rfl

theorem insufficient_fuel :
    entry (boolInput 1) 1 boolParams = .error .fuel := by
  rfl

theorem allocation_panics :
    alloc ⟨[], lim⟩ 0 1 = .error .panic := by
  rfl

/-- Companion success requirement for this supported entry. Its existence of
an actual result rules out both error-only implementations below. -/
def BooleanEntrySuccess
    (decode : (I : Input) → Nat → (ps : List Param) → Except Fail (Entries ps)) : Prop :=
  ∃ es, decode (boolInput 1) 2 boolParams = .ok es

theorem actual_entry_success : BooleanEntrySuccess entry := by
  exact ⟨_, bool_true_success 0⟩

def rejectAllEntry (_ : Input) (_ : Nat) (ps : List Param) : Except Fail (Entries ps) :=
  .error .revert

def exhaustAllEntry (_ : Input) (_ : Nat) (ps : List Param) : Except Fail (Entries ps) :=
  .error .fuel

theorem reject_all_entry_refused : ¬ BooleanEntrySuccess rejectAllEntry := by
  intro h
  obtain ⟨es, ran⟩ := h
  cases ran

theorem exhaust_all_entry_refused : ¬ BooleanEntrySuccess exhaustAllEntry := by
  intro h
  obtain ⟨es, ran⟩ := h
  cases ran

#print axioms bool_true_success
#print axioms actual_entry_success
#print axioms reject_all_entry_refused
#print axioms exhaust_all_entry_refused
end Solidity.H62.AuditLanguage
