import Solidity.Roadmap.V16.Specifications
import Solidity.Roadmap.V16.TransactionControls

/-! Application controls; actual existing Spec.sat and run, including exhaustion. -/
namespace Solidity.Roadmap.V16.SpecificationControls
open Solidity.Lifetime
open Solidity.Roadmap.V16.TransactionControls

def entryState : State contract [] := { start.observe with tx := callTx }
def nilOut : Out contract entryState.H [] := ⟨entryState, List.prefix_refl _⟩

theorem box_post_witness : Spec.sat nilOut.st (.tt : Spec contract []) :=
  spec_box_post (P := .nil) (o := nilOut) trivial rfl

theorem diamond_success_witness : ∃ o : Out contract entryState.H [],
    (Prog.nil : Prog contract [] []).run entryState = .ok o ∧ Spec.sat o.st (.tt : Spec contract []) :=
  spec_diamond_success (P := .nil) trivial (by intro h; cases h)

theorem diamond_commit_witness : ∃ o : Out contract entryState.H [],
    Lifetime.Step system start (.call false callTx) (World.ofState o.st) ∧
      Spec.sat o.st (.tt : Spec contract []) :=
  diamond_commit accepted trivial rfl (World.enter_zero start callTx rfl)
    trivial (by intro h; cases h)

/-- The approved diamond accepts exhaustion; it is not a commit witness. -/
theorem exhausted_diamond : Spec.sat entryState (.diamond (Prog.recBase : Prog contract [] []) .tt) := rfl

theorem exhausted_has_no_success : ∀ o : Out contract entryState.H [],
    (Prog.recBase : Prog contract [] []).run entryState ≠ .ok o := by
  intro o h
  cases h

/-- The premise required by NEW diamond success transport is impossible here. -/
theorem exhausted_not_eligible :
    ¬ ((Prog.recBase : Prog contract [] []).run entryState ≠ .error .exhausted) :=
  fun h => h rfl

/-- Inhabited smoke application of the full source-box/backward-reachability
consumer, with a proved identity step relation, not a target simulation oracle. -/
theorem invariant_transport_witness : Lifetime.AG system (fun _ => True) := by
  apply specification_invariant_transport (M₁ := system) (P := fun _ => True)
    (pre := fun _ => .tt) (post := fun _ => .tt)
    (R := fun s t => s = t) (event := id)
  · intros; trivial
  · intro a σ _
    cases a
    · change True
      trivial
    · change (THalt.revertWith [9]) ≠ .panic
      intro h
      cases h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro t ht; exact ⟨t, ht, rfl⟩
  · intro s t u a hst step
    subst t
    exact ⟨u, step, rfl⟩
  · intros; trivial
end Solidity.Roadmap.V16.SpecificationControls
