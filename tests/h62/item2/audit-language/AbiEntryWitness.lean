import Solidity.Semantics.AbiEntry

/-! Guarded regression: existential success alone must not credit an error-only
or always-success decoder, or lose exact output and failure boundaries.
Actual one-boolean ABI entry runs, with nonzero output and observable
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

/-- Stronger companion behavior for the fixed one-boolean family. All fuel
suffixes share the same decoder; the original success contract stays unchanged. -/
def BooleanEntryBehavior
    (decode : Input → Nat → Except Fail (Entries boolParams)) : Prop :=
  (∀ fuel : Nat,
    decode (boolInput 1) (fuel + 2) = .ok (.cons (.val (.word trueWord)) .nil) ∧
    decode (boolInput 0) (fuel + 2) = .ok (.cons (.val (.word falseWord)) .nil) ∧
    decode (boolInput 2) (fuel + 2) = .error .revert ∧
    decode ⟨List.replicate 35 0, 128⟩ (fuel + 2) = .error .revert) ∧
  decode (boolInput 1) 1 = .error .fuel

theorem actual_entry_behavior : BooleanEntryBehavior (fun I fuel => entry I fuel boolParams) := by
  exact ⟨fun fuel => ⟨bool_true_success fuel, bool_false_success fuel,
    malformed_bool_reverts fuel, truncated_bool_reverts fuel⟩, insufficient_fuel⟩

/-- No fixed result can satisfy both an actual success and a malformed-input
refusal. This covers every fixed-result decoder, including constant errors. -/
theorem constant_boolean_behavior_refused (result : Except Fail (Entries boolParams)) :
    ¬ BooleanEntryBehavior (fun _ _ => result) := by
  intro h
  have impossible := (h.1 0).1.symm.trans (h.1 0).2.2.1
  cases impossible

/-- An accept-everything decoder returns a valid-looking success even for a
malformed word. This must fail the observable behavior contract. -/
def acceptAllBoolean (_ : Input) (_ : Nat) : Except Fail (Entries boolParams) :=
  .ok (.cons (.val (.word trueWord)) .nil)

theorem accept_all_boolean_refused : ¬ BooleanEntryBehavior acceptAllBoolean := by
  exact constant_boolean_behavior_refused _

theorem reject_all_boolean_behavior_refused :
    ¬ BooleanEntryBehavior (fun I fuel => rejectAllEntry I fuel boolParams) := by
  exact constant_boolean_behavior_refused _

theorem exhaust_all_boolean_behavior_refused :
    ¬ BooleanEntryBehavior (fun I fuel => exhaustAllEntry I fuel boolParams) := by
  exact constant_boolean_behavior_refused _

#print axioms constant_boolean_behavior_refused
#print axioms actual_entry_behavior
#print axioms accept_all_boolean_refused
#print axioms reject_all_boolean_behavior_refused
#print axioms exhaust_all_boolean_behavior_refused

/-! Guarded regression: sequential ABI heads must advance by one word and
preserve parameter order; validating only the first boolean must not accept a
malformed second head. These controls cover a two-value family, not general ABI
progress or compiler correctness. -/
def boolPairParams : List Param := [⟨.word .bool, .value, false⟩, ⟨.word .bool, .value, false⟩]
def boolPairInput (a b : UInt8) : Input :=
  ⟨List.replicate 35 0 ++ [a] ++ List.replicate 31 0 ++ [b], 128⟩
def boolWord (b : Bool) : Word .bool := if b then trueWord else falseWord
def boolByte (b : Bool) : UInt8 := if b then 1 else 0
def boolPairResult (a b : Bool) : Entries boolPairParams :=
  .cons (.val (.word (boolWord a))) (.cons (.val (.word (boolWord b))) .nil)

theorem bool_pair_success (a b : Bool) (fuel : Nat) :
    entry (boolPairInput (boolByte a) (boolByte b)) (fuel + 2) boolPairParams =
      .ok (boolPairResult a b) := by
  cases a <;> cases b <;> rfl

theorem bool_pair_malformed_first (fuel : Nat) :
    entry (boolPairInput 2 1) (fuel + 2) boolPairParams = .error .revert := by
  rfl

theorem bool_pair_malformed_second (fuel : Nat) :
    entry (boolPairInput 1 2) (fuel + 2) boolPairParams = .error .revert := by
  rfl

theorem bool_pair_truncated (fuel : Nat) :
    entry ⟨(boolPairInput 1 0).data.take 67, 128⟩ (fuel + 2) boolPairParams =
      .error .revert := by
  rfl

theorem bool_pair_insufficient_fuel (a b : Bool) :
    entry (boolPairInput (boolByte a) (boolByte b)) 1 boolPairParams = .error .fuel := by
  cases a <;> cases b <;> rfl

/-- Exact observations on one shared decoder, including both head validators. -/
def BooleanPairBehavior (decode : Input → Nat → Except Fail (Entries boolPairParams)) : Prop :=
  (∀ a b fuel, decode (boolPairInput (boolByte a) (boolByte b)) (fuel + 2) =
    .ok (boolPairResult a b)) ∧
  (∀ fuel, decode (boolPairInput 2 1) (fuel + 2) = .error .revert) ∧
  (∀ fuel, decode (boolPairInput 1 2) (fuel + 2) = .error .revert) ∧
  (∀ fuel, decode ⟨(boolPairInput 1 0).data.take 67, 128⟩ (fuel + 2) = .error .revert) ∧
  (∀ a b, decode (boolPairInput (boolByte a) (boolByte b)) 1 = .error .fuel)

theorem actual_pair_behavior : BooleanPairBehavior (fun I fuel => entry I fuel boolPairParams) := by
  exact ⟨bool_pair_success, bool_pair_malformed_first, bool_pair_malformed_second,
    bool_pair_truncated, bool_pair_insufficient_fuel⟩

/-- A fixed result cannot implement the ordered pair's success and refusal observations. -/
theorem constant_pair_behavior_refused (result : Except Fail (Entries boolPairParams)) :
    ¬ BooleanPairBehavior (fun _ _ => result) := by
  intro h
  have impossible := (h.1 true false 0).symm.trans (h.2.2.1 0)
  cases impossible

/-- Deliberately wrong decoder: retain entry's refusals but reverse its outputs. -/
def swapPairResult : Entries boolPairParams → Entries boolPairParams
  | .cons first (.cons second .nil) => .cons second (.cons first .nil)

def swappedPairDecoder (I : Input) (fuel : Nat) : Except Fail (Entries boolPairParams) :=
  (entry I fuel boolPairParams).map swapPairResult

def firstPairWord : Entries boolPairParams → Nat
  | .cons (.val (.word word)) _ => word.val
  | _ => 2

theorem swapped_pair_behavior_refused : ¬ BooleanPairBehavior swappedPairDecoder := by
  intro h
  let observe : Except Fail (Entries boolPairParams) → Nat := fun result =>
    match result with
    | .ok values => firstPairWord values
    | .error _ => 2
  have impossible := congrArg observe (h.1 true false 0)
  change (0 : Nat) = 1 at impossible
  cases impossible

#print axioms swapped_pair_behavior_refused
#print axioms bool_pair_success
#print axioms actual_pair_behavior
#print axioms constant_pair_behavior_refused
end Solidity.H62.AuditLanguage
