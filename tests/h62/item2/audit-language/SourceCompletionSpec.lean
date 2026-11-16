import tests.h62.item2.«audit-language».SourceCompletionWitness

/-!
Guarded regression: reject-all and last-completion searches can evade a contract
that checks only the validity of returned results. The independent criterion
below requires the earliest completed horizon and its exact result/state, with
progress whenever that criterion holds. Negative searches remain uncredited
controls. This is a generic source horizon-search contract, not compiler
termination, EVM gas, historical replay or full audit acceptance.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceCompletionSpec
open Solidity.Source
open Solidity.H62.AuditLanguage.SourceCompletionWitness (delayed)

abbrev Search (α σ : Type) :=
  (Nat → Except Halt α × σ) → Nat → Option (Nat × (Except Halt α × σ))

/-- A bounded earliest completion, including the exact state at that horizon. -/
def Earliest {α σ : Type} (f : Nat → Except Halt α × σ) (n k : Nat)
    (r : Except Halt α × σ) : Prop :=
  k ≤ n ∧ r = f k ∧ Done (f k) = true ∧ ∀ j < k, Done (f j) = false

/-- Every valid earliest result must be returned, and every returned result valid. -/
def SearchContract {α σ : Type} (search : Search α σ) : Prop :=
  ∀ f n k r, search f n = some (k, r) ↔ Earliest f n k r

theorem earlier_none {α σ : Type} {f : Nat → Except Halt α × σ}
    {n k : Nat} {r : Except Halt α × σ} (found : firstDone f n = some (k, r))
    (j : Nat) (earlier : j < k) : firstDone f j = none := by
  have specification := firstDone_spec found
  cases atEarlier : firstDone f j with
  | none => rfl
  | some pair =>
    rcases pair with ⟨i, result⟩
    have persists := firstDone_mono f (show j ≤ n by omega) atEarlier
    rw [found] at persists
    have index := congrArg Prod.fst (Option.some.inj persists)
    have bound := (firstDone_spec atEarlier).1
    exfalso
    omega

theorem earlier_unfinished {α σ : Type} {f : Nat → Except Halt α × σ}
    {n k : Nat} {r : Except Halt α × σ} (found : firstDone f n = some (k, r))
    (j : Nat) (earlier : j < k) : Done (f j) = false := by
  have noResult := earlier_none found j earlier
  simp only [firstDone, List.findSome?_eq_none_iff] at noResult
  have atIndex := noResult j (List.mem_range.mpr (Nat.lt_succ_self j))
  cases done : Done (f j) with
  | false => rfl
  | true => simp only [done, if_true, reduceCtorEq] at atIndex

theorem firstDone_iff_earliest {α σ : Type} (f : Nat → Except Halt α × σ)
    (n k : Nat) (r : Except Halt α × σ) :
    firstDone f n = some (k, r) ↔ Earliest f n k r := by
  constructor
  · intro found
    obtain ⟨bound, value, completed⟩ := firstDone_spec found
    exact ⟨bound, value, completed, fun j before => earlier_unfinished found j before⟩
  · rintro ⟨bound, value, completed, earliest⟩
    cases result : firstDone f n with
    | none =>
      have noResult := result
      simp only [firstDone, List.findSome?_eq_none_iff] at noResult
      have atIndex := noResult k (List.mem_range.mpr (by omega))
      simp only [completed, if_true, reduceCtorEq] at atIndex
    | some pair =>
      rcases pair with ⟨j, actual⟩
      have specification := firstDone_spec result
      have notEarlier : ¬ j < k := by
        intro before
        have unfinished := earliest j before
        rw [specification.2.2] at unfinished
        cases unfinished
      have notLater : ¬ k < j := by
        intro before
        have unfinished := earlier_unfinished result k before
        rw [completed] at unfinished
        cases unfinished
      have index : j = k := by omega
      subst j
      have contents : actual = r := specification.2.1.trans value.symm
      exact congrArg (fun x => some (k, x)) contents

theorem contract_iff_reference {α σ : Type} (search : Search α σ) :
    SearchContract search ↔ ∀ f n, search f n = firstDone f n := by
  constructor
  · intro contract f n
    cases result : firstDone f n with
    | none =>
      cases output : search f n with
      | none => rfl
      | some pair =>
        rcases pair with ⟨k, r⟩
        have found := (firstDone_iff_earliest f n k r).2 ((contract f n k r).1 output)
        rw [result] at found
        cases found
    | some pair =>
      rcases pair with ⟨k, r⟩
      exact (contract f n k r).2 ((firstDone_iff_earliest f n k r).1 result)
  · intro agrees f n k r
    rw [agrees f n]
    exact firstDone_iff_earliest f n k r

theorem reference_contract {α σ : Type} : SearchContract (@firstDone α σ) :=
  (contract_iff_reference _).2 (fun _ _ => rfl)

def rejectAll {α σ : Type} (_f : Nat → Except Halt α × σ) (_n : Nat) :
    Option (Nat × (Except Halt α × σ)) := none

def pickBound {α σ : Type} (f : Nat → Except Halt α × σ) (n : Nat) :
    Option (Nat × (Except Halt α × σ)) :=
  if Done (f n) then some (n, f n) else none

/-- Picking the bound passes the weaker returned-result validity property. -/
theorem pickBound_locally_valid {α σ : Type} (f : Nat → Except Halt α × σ)
    (n k : Nat) (r : Except Halt α × σ) (found : pickBound f n = some (k, r)) :
    k ≤ n ∧ r = f k ∧ Done (f k) = true := by
  unfold pickBound at found
  split at found
  · rename_i completed
    have pair := Option.some.inj found
    have index : n = k := congrArg Prod.fst pair
    have contents : f n = r := congrArg Prod.snd pair
    subst k
    subst r
    exact ⟨Nat.le_refl _, rfl, completed⟩
  · cases found

theorem rejectAll_refused : ¬ SearchContract (@rejectAll Nat Nat) := by
  intro contract
  have required : Earliest (delayed 3) 3 3 (.ok 7, 3) := by
    refine ⟨Nat.le_refl _, rfl, rfl, ?_⟩
    intro j before
    have small : ¬ 3 ≤ j := by omega
    simp only [Done, delayed, small, if_false]
  have found := (contract (delayed 3) 3 3 (.ok 7, 3)).2 required
  cases found

theorem pickBound_refused : ¬ SearchContract (@pickBound Nat Nat) := by
  intro contract
  have required := (contract (delayed 3) 8 8 (.ok 7, 8)).1 rfl
  have earlier := required.2.2.2 3 (by decide)
  change true = false at earlier
  cases earlier

#print axioms earlier_none
#print axioms earlier_unfinished
#print axioms firstDone_iff_earliest
#print axioms contract_iff_reference
#print axioms reference_contract
#print axioms pickBound_locally_valid
#print axioms rejectAll_refused
#print axioms pickBound_refused
end Solidity.H62.AuditLanguage.SourceCompletionSpec
