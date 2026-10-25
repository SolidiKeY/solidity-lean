import SolidityBridge.Loop
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
The loop's first-return map as a least fixed point in the complete lattice
of predicates. A well-founded variant is required only while the invariant
holds, so unreachable states need not decrease.
-/
namespace Solidity.TLoop

variable {α : Type} {body : α → TRes α} {c : α → TRes Bool}

def outcomeStep (body : α → TRes α) (c : α → TRes Bool) (Q : TRes α → Prop) :
    Set α →o Set α where
  toFun X := {σ | (∃ r, step body c σ = .inr r ∧ Q r) ∨
    ∃ τ, step body c σ = .inl τ ∧ τ ∈ X}
  monotone' := by
    intro X Y h σ hs
    rcases hs with hs | ⟨τ, ht, hX⟩
    · exact Or.inl hs
    · exact Or.inr ⟨τ, ht, h hX⟩

/-- Mathlib's order-theoretic least fixed point is exactly the successful
first-return outcomes satisfying the chosen postcondition. -/
theorem outcome_lfp_eq (Q : TRes α → Prop) :
    (outcomeStep body c Q).lfp = {σ | ∃ r, r ∈ (stepP body c).fix σ ∧ Q r} := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    intro σ hs
    rcases hs with ⟨r, hr, hQ⟩ | ⟨τ, ht, r, hr, hQ⟩
    · exact ⟨r, PFun.fix_stop (mem_stepP_inl.mpr hr), hQ⟩
    · exact ⟨r, PFun.mem_fix_iff.mpr (Or.inr ⟨τ, mem_stepP_inr.mpr ht, hr⟩), hQ⟩
  · rintro σ ⟨r, hr, hQ⟩
    refine PFun.fixInduction (C := fun s => s ∈ (outcomeStep body c Q).lfp) hr ?_
    intro s hs ih
    rw [← (outcomeStep body c Q).map_lfp]
    rcases PFun.mem_fix_iff.mp hs with hstop | ⟨t, ht, _⟩
    · exact Or.inl ⟨r, mem_stepP_inl.mp hstop, hQ⟩
    · exact Or.inr ⟨t, mem_stepP_inr.mp ht, ih t ht⟩

/-- An invariant and a decreasing well-founded variant establish membership
in the least fixed point, by `WellFounded.induction` and `OrderHom.map_lfp`.
No core loop invariant or termination theorem is used. -/
theorem mem_outcome_lfp_of_wellFounded {I : α → Prop} {Q : TRes α → Prop}
    {β : Type} {rel : β → β → Prop} (wf : WellFounded rel) (v : α → β)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ → rel (v τ) (v σ))
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : σ ∈ (outcomeStep body c Q).lfp := by
  have h : ∀ b s, v s = b → I s → s ∈ (outcomeStep body c Q).lfp := by
    intro b
    induction b using wf.induction with
    | h b ih =>
      intro s hv hs
      rw [← (outcomeStep body c Q).map_lfp]
      cases he : step body c s with
      | inr r => exact Or.inl ⟨r, he, stop s r hs he⟩
      | inl t =>
        exact Or.inr ⟨t, he, ih (v t) (hv ▸ decreases s t hs he) t rfl (keep s t hs he)⟩
  exact h (v σ) σ rfl hI

/-- Total correctness through the order-theoretic least fixed point. The
postcondition may reject all errors when successful termination is wanted. -/
theorem run_correct_of_wellFounded_on {I : α → Prop} {Q : TRes α → Prop}
    {β : Type} {rel : β → β → Prop} (wf : WellFounded rel) (v : α → β)
    (keep : ∀ σ τ, I σ → step body c σ = .inl τ → I τ)
    (decreases : ∀ σ τ, I σ → step body c σ = .inl τ → rel (v τ) (v σ))
    (stop : ∀ σ r, I σ → step body c σ = .inr r → Q r)
    {σ : α} (hI : I σ) : Q (run body c σ) := by
  have h : σ ∈ (outcomeStep body c Q).lfp :=
    mem_outcome_lfp_of_wellFounded wf v keep decreases stop hI
  rw [outcome_lfp_eq] at h
  obtain ⟨r, hr, hQ⟩ := h
  rw [run_eq_of_mem_fix hr]
  exact hQ

end Solidity.TLoop

/-- info: 'Solidity.TLoop.outcome_lfp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.TLoop.outcome_lfp_eq
/-- info: 'Solidity.TLoop.run_correct_of_wellFounded_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.TLoop.run_correct_of_wellFounded_on
