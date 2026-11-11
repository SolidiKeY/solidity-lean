import Solidity.Examples.Tactics.Lifetime
import Solidity.Roadmap.V16.Specifications

/-!
A NEW consumer of a published nontrivial invariant and actual deployment/trace
witnesses. Test-only imports keep elaborators out of Roadmap/core consumers.
This identity-model transfer establishes no runtime/backend correspondence.
-/
namespace Solidity.Roadmap.V16.PublishedWitness
open Solidity.Lifetime
open Solidity.Examples.Tactics.Lifetime

/-- NEW backward reachability induction transports the existing proved
mutual-exclusion invariant; it is not the True smoke predicate. -/
theorem transferred_escrow_safety : Lifetime.AG model Safe :=
  reachable_invariant (M₁ := model) (M₂ := model) (fun s t => s = t) id
    (fun t ht => ⟨t, ht, rfl⟩)
    (fun h next => by cases h; exact ⟨_, next, rfl⟩)
    Safe Safe safeInvariant (fun _ _ eq hp => eq ▸ hp)

/-- A published successful deployment and payment trace inhabit the
transferred invariant; it is not vacuous reachability. -/
theorem inhabited_safe_reachable : ∃ s, Lifetime.Reachable model s ∧ Safe s := by
  obtain ⟨s, hs, _⟩ := paymentPossible.reachable
  exact ⟨s, hs, transferred_escrow_safety s hs⟩

/-- The invariant excludes an actual typed world with both flags set. -/
def bothFlags : Lifetime.World Escrow where
  storage := .cons (.prim true) (.cons (.prim true) .nil)
  net := []
  balance := ⟨0, rfl⟩
  address := ⟨9, rfl⟩
  timestamp := ⟨0, rfl⟩

theorem invariant_nontrivial : ¬ Safe bothFlags := by
  intro h
  change ¬ (_ ∧ _) at h
  exact h ⟨rfl, rfl⟩

/-- NEW target safety excludes this concrete bad world from reachability. -/
theorem bad_world_unreachable : ¬ Lifetime.Reachable model bothFlags :=
  fun h => invariant_nontrivial (transferred_escrow_safety bothFlags h)

#check transferred_escrow_safety
#check inhabited_safe_reachable
#check invariant_nontrivial
#check bad_world_unreachable
#print axioms transferred_escrow_safety
#print axioms inhabited_safe_reachable
#print axioms invariant_nontrivial
#print axioms bad_world_unreachable
end Solidity.Roadmap.V16.PublishedWitness
