import tests.h62.item2.«audit-language».SourceCompletionSpec

/-!
Guarded regression: completion-preserving result/state transport is weaker than
exact outcome preservation. Swapping completed failure tags preserves `Done` and
all successes but violates the exact search contract; turning timeout into success
breaks transport itself. The generic map law retains its classification premise
and changes neither the source search nor any frozen interface. These are search
transport clients, not compiler correctness or a monetary semantics bridge.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceCompletionTransport
open Solidity.Source
open Solidity.H62.AuditLanguage.SourceCompletionWitness (timeout_prefix_none forever revertFailure)
open Solidity.H62.AuditLanguage.SourceCompletionSpec

/-- Completion absence is exactly a finite unfinished prefix, not divergence. -/
theorem none_iff_unfinished_prefix {α σ : Type} (f : Nat → Except Halt α × σ) (n : Nat) :
    firstDone f n = none ↔ ∀ k ≤ n, Done (f k) = false := by
  constructor
  · intro noResult k bound
    simp only [firstDone, List.findSome?_eq_none_iff] at noResult
    have atIndex := noResult k (List.mem_range.mpr (by omega))
    cases done : Done (f k) with
    | false => rfl
    | true => simp only [done, if_true, reduceCtorEq] at atIndex
  · exact timeout_prefix_none f n

def mapFound {α β σ τ : Type} (transform : (Except Halt α × σ) → (Except Halt β × τ))
    (found : Option (Nat × (Except Halt α × σ))) : Option (Nat × (Except Halt β × τ)) :=
  found.map fun (k, r) => (k, transform r)

/-- Transport may change values and state, but must preserve completion status. -/
theorem firstDone_map {α β σ τ : Type}
    (transform : (Except Halt α × σ) → (Except Halt β × τ))
    (preserves : ∀ r, Done (transform r) = Done r) (f : Nat → Except Halt α × σ) (n : Nat) :
    firstDone (fun k => transform (f k)) n = mapFound transform (firstDone f n) := by
  cases found : firstDone f n with
  | none =>
    simp only [mapFound, Option.map_none]
    apply timeout_prefix_none
    intro k bound
    rw [preserves (f k)]
    exact (none_iff_unfinished_prefix f n).1 found k bound
  | some pair =>
    rcases pair with ⟨k, r⟩
    simp only [mapFound, Option.map_some]
    apply (firstDone_iff_earliest _ n k (transform r)).2
    have original := (firstDone_iff_earliest f n k r).1 found
    refine ⟨original.1, congrArg transform original.2.1, ?_, ?_⟩
    · rw [preserves (f k)]
      exact original.2.2.1
    · intro j before
      rw [preserves (f j)]
      exact original.2.2.2 j before

-- Intentionally incorrect output normalization: failures are not interchangeable.
def swapFailure (r : Except Halt Nat × Nat) : Except Halt Nat × Nat :=
  (match r.1 with
   | .error (.revert _) => .error (.stuck "masked")
   | .error (.stuck _) => .error (.revert [])
   | result => result, r.2)

theorem swapFailure_preserves_done (r : Except Halt Nat × Nat) :
    Done (swapFailure r) = Done r := by
  rcases r with ⟨result, state⟩
  cases result with
  | ok value => rfl
  | error halt => cases halt <;> rfl

def swappedSearch : Search Nat Nat := fun f n => mapFound swapFailure (firstDone f n)

/-- Preserving every successful result does not certify exact failure behavior. -/
theorem swappedSearch_preserves_success (f : Nat → Except Halt Nat × Nat) (n k value state : Nat)
    (found : firstDone f n = some (k, (.ok value, state))) :
    swappedSearch f n = some (k, (.ok value, state)) := by
  simp only [swappedSearch, mapFound, found, Option.map_some, swapFailure]

theorem swappedSearch_refused : ¬ SearchContract swappedSearch := by
  intro contract
  have same := (contract_iff_reference swappedSearch).1 contract revertFailure 0
  change (some (0, (.error (.stuck "masked"), 0)) : Option (Nat × (Except Halt Nat × Nat))) =
    some (0, (.error (.revert [1, 2]), 0)) at same
  cases same

def forgeTimeout (r : Except Halt Nat × Nat) : Except Halt Nat × Nat := (.ok 7, r.2)

/-- Omitting the completion-status premise permits a timeout-to-success forgery. -/
theorem timeout_forgery_breaks_transport :
    firstDone (fun k => forgeTimeout (forever k)) 0 ≠
      mapFound forgeTimeout (firstDone forever 0) := by
  intro same
  cases same

#print axioms none_iff_unfinished_prefix
#print axioms firstDone_map
#print axioms swapFailure_preserves_done
#print axioms swappedSearch_preserves_success
#print axioms swappedSearch_refused
#print axioms timeout_forgery_breaks_transport
end Solidity.H62.AuditLanguage.SourceCompletionTransport
