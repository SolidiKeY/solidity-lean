import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Semantics

/-!
Guarded regression: timeout is unfinished, while revert and stuck results are
completed failures. A least-completion scan must retain the earliest horizon and
its state when the bound grows. Whole imported telescopes exercise a delayed
success and a never-completing run. These five generic headers match the frozen
source; no whole-program termination, compiler or EVM gas claim is made.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceCompletionWitness
open Solidity.Source

def delayed (cutoff k : Nat) : Except Halt Nat × Nat :=
  (if cutoff ≤ k then .ok 7 else .error .timeout, k)
def forever (k : Nat) : Except Halt Nat × Nat := (.error .timeout, k)
def revertFailure (k : Nat) : Except Halt Nat × Nat := (.error (.revert [1, 2]), k)
def stuckFailure (k : Nat) : Except Halt Nat × Nat := (.error (.stuck "guard"), k)

theorem ranges_full : hypotheses_of% range_succ_append := by
  exact ⟨2, 3, True.intro⟩
#verify_hypotheses ranges_full for Solidity.Source.range_succ_append
#print axioms ranges_full

theorem monotone_full : hypotheses_of% firstDone_mono := by
  exact ⟨Nat, Nat, delayed 3, 3, 8, by decide, (3, (.ok 7, 3)), rfl, True.intro⟩
#verify_hypotheses monotone_full for Solidity.Source.firstDone_mono
#print axioms monotone_full

theorem specification_full : hypotheses_of% firstDone_spec := by
  exact ⟨Nat, Nat, delayed 3, 8, 3, (.ok 7, 3), rfl, True.intro⟩
#verify_hypotheses specification_full for Solidity.Source.firstDone_spec
#print axioms specification_full

theorem no_completion_full : hypotheses_of% firstDone_none_iff := by
  exact ⟨Nat, Nat, forever, True.intro⟩
#verify_hypotheses no_completion_full for Solidity.Source.firstDone_none_iff
#print axioms no_completion_full

theorem prefix_full : hypotheses_of% prefix_of_append_prefix := by
  exact ⟨Nat, [1], [2], [1, 2, 3], List.prefix_append [1, 2] [3], True.intro⟩
#verify_hypotheses prefix_full for Solidity.Source.prefix_of_append_prefix
#print axioms prefix_full

/-- A finite all-timeout prefix cannot produce a completed result. -/
theorem timeout_prefix_none {α σ : Type} (f : Nat → Except Halt α × σ) (n : Nat)
    (unfinished : ∀ k ≤ n, Done (f k) = false) : firstDone f n = none := by
  simp only [firstDone, List.findSome?_eq_none_iff]
  intro k member
  have bound : k < n + 1 := List.mem_range.mp member
  rw [unfinished k (by omega)]
  rfl

/-- A scan result cannot be a timeout, independently of its state type. -/
theorem completed_result_not_timeout {α σ : Type} (f : Nat → Except Halt α × σ)
    (n k : Nat) (r : Except Halt α × σ) (found : firstDone f n = some (k, r)) :
    r.1 ≠ .error .timeout := by
  have specification := firstDone_spec found
  have completed : Done r = true := by
    rw [specification.2.1]
    exact specification.2.2
  intro timedOut
  unfold Done at completed
  rw [timedOut] at completed
  cases completed

/-- Every larger bound keeps the same first successful horizon and its state. -/
theorem delayed_persists (n : Nat) (enough : 3 ≤ n) :
    firstDone (delayed 3) n = some (3, (.ok 7, 3)) :=
  firstDone_mono (delayed 3) enough rfl

theorem forever_none (n : Nat) : firstDone forever n = none :=
  (firstDone_none_iff forever).2 (fun _ => rfl) n

example : firstDone (delayed 3) 2 = none := rfl
example : firstDone (delayed 3) 3 = some (3, (.ok 7, 3)) := rfl
example : firstDone revertFailure 0 = some (0, (.error (.revert [1, 2]), 0)) := rfl
example : firstDone stuckFailure 0 = some (0, (.error (.stuck "guard"), 0)) := rfl
example : firstDone forever 0 ≠ some (0, (.ok 7, 0)) := by
  intro impossible
  cases impossible

#print axioms timeout_prefix_none
#print axioms completed_result_not_timeout
#print axioms delayed_persists
#print axioms forever_none
end Solidity.H62.AuditLanguage.SourceCompletionWitness
