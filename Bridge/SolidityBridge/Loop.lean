import Solidity.Semantics.Run
import Cslib.Foundations.Semantics.ReductionSystem.Basic
import Mathlib.Data.PFun

/-!
# A loop's run, Mathlib's first-return map

`TLoop.run` (`Semantics/Run.lean`) runs a loop as a classical choice over
`TLoop.iterN`, the iterations counted out: the outcome of the first
iteration that is done, or `diverge` when none is.  That is Mathlib's
first-return map `PFun.fix` of one iteration, and the normal form of a
reduction system:

* `TLoop.stepP` is one iteration as a partial function `α →. TRes α ⊕ α`
  (done on the left, go on on the right, Mathlib's convention), and
  `TLoop.run_eq_fix`: the run is its `PFun.fix`, `diverge` where the fix is
  undefined;
* `TLoop.rs` is the loop as a CSLib `ReductionSystem` (a state reduces to
  the one its iteration goes on in), and `TLoop.run_cases`: a run ends as
  the reachable state that is done is done, or diverges with no such state.
-/

namespace Solidity

namespace TLoop

variable {α : Type} (body : α → TRes α) (c : α → TRes Bool)

/-- One iteration, Mathlib's way round: done on the left, go on on the
right. -/
def stepP : α →. TRes α ⊕ α := fun σ => Part.some (step body c σ).swap

/-- **The loop as a reduction system**: a state reduces to the state its
iteration goes on in. -/
def rs : ReductionSystem α where
  Red σ τ := step body c σ = .inl τ

variable {body c}

@[simp] theorem mem_stepP_inl {σ : α} {r : TRes α} :
    Sum.inl r ∈ stepP body c σ ↔ step body c σ = .inr r := by
  simp only [stepP, Part.mem_some_iff]
  cases step body c σ <;> simp

@[simp] theorem mem_stepP_inr {σ τ : α} :
    Sum.inr τ ∈ stepP body c σ ↔ step body c σ = .inl τ := by
  simp only [stepP, Part.mem_some_iff]
  cases step body c σ <;> simp [eq_comm]

/-- An iteration count that is done is in the first-return map. -/
theorem mem_fix_of_iterN {n : Nat} {σ : α} {r : TRes α} (h : iterN body c n σ = .inr r) :
    r ∈ (stepP body c).fix σ := by
  induction n generalizing σ with
  | zero => exact nomatch h
  | succ n ih =>
    simp only [iterN] at h
    cases hs : step body c σ with
    | inl τ =>
      rw [hs] at h
      exact PFun.mem_fix_iff.2 (.inr ⟨τ, mem_stepP_inr.2 hs, ih h⟩)
    | inr r' =>
      rw [hs] at h
      cases h
      exact PFun.fix_stop (mem_stepP_inl.2 hs)

/-- What the first-return map returns, some iteration count is done with. -/
theorem iterN_of_mem_fix {σ : α} {r : TRes α} (h : r ∈ (stepP body c).fix σ) :
    ∃ n, iterN body c n σ = .inr r := by
  refine PFun.fixInduction (C := fun σ => ∃ n, iterN body c n σ = .inr r) h ?_
  intro σ' hσ' ih
  rcases PFun.mem_fix_iff.1 hσ' with h1 | ⟨τ, hτ, _⟩
  · have hs := mem_stepP_inl.1 h1
    exact ⟨1, by simp only [iterN, hs]⟩
  · obtain ⟨n, hn⟩ := ih τ hτ
    have hs := mem_stepP_inr.1 hτ
    exact ⟨n + 1, by simp only [iterN, hs, hn]⟩

/-- `PFun.fix` of an iteration is the iterations counted out. -/
theorem mem_fix_iff {σ : α} {r : TRes α} :
    r ∈ (stepP body c).fix σ ↔ ∃ n, iterN body c n σ = .inr r :=
  ⟨iterN_of_mem_fix, fun ⟨_, h⟩ => mem_fix_of_iterN h⟩

/-- A loop ends as its first-return map returns. -/
theorem run_eq_of_mem_fix {σ : α} {r : TRes α} (h : r ∈ (stepP body c).fix σ) :
    run body c σ = r :=
  let ⟨_, hn⟩ := iterN_of_mem_fix h
  run_of_iterN hn

/-- A loop whose first-return map is undefined diverges. -/
theorem run_eq_diverge {σ : α} (h : ¬((stepP body c).fix σ).Dom) :
    run body c σ = .error .diverge := by
  unfold run
  rw [dif_neg]
  rintro ⟨r, n, hn⟩
  exact h (Part.dom_iff_mem.2 ⟨r, mem_fix_of_iterN hn⟩)

open Classical in
/-- **The run is Mathlib's first-return map** of one iteration, `diverge`
where it is undefined. -/
theorem run_eq_fix (σ : α) :
    run body c σ = ((stepP body c).fix σ).getOrElse (.error .diverge) := by
  by_cases h : ((stepP body c).fix σ).Dom
  · rw [Part.getOrElse_of_dom _ h]
    exact run_eq_of_mem_fix (Part.get_mem h)
  · rw [Part.getOrElse_of_not_dom _ h]
    exact run_eq_diverge h

/-! ## The loop as a reduction system -/

/-- A reduction is a step of the first-return map: both reach the same
outcome. -/
theorem fix_eq_of_mred {σ τ : α} (h : (rs body c).MRed σ τ) :
    (stepP body c).fix σ = (stepP body c).fix τ := by
  induction h with
  | refl => rfl
  | tail _ s ih => exact ih.trans (PFun.fix_fwd_eq (mem_stepP_inr.2 s))

/-- A loop ends as the state it reduces to is done. -/
theorem run_of_mred {σ τ : α} {r : TRes α} (h : (rs body c).MRed σ τ)
    (hs : step body c τ = .inr r) : run body c σ = r :=
  run_eq_of_mem_fix (by rw [fix_eq_of_mred h]; exact PFun.fix_stop (mem_stepP_inl.2 hs))

/-- What the first-return map returns, a reachable state is done with. -/
theorem exists_mred_of_mem_fix {σ : α} {r : TRes α} (h : r ∈ (stepP body c).fix σ) :
    ∃ τ, (rs body c).MRed σ τ ∧ step body c τ = .inr r := by
  refine PFun.fixInduction
    (C := fun σ => ∃ τ, (rs body c).MRed σ τ ∧ step body c τ = .inr r) h ?_
  intro σ' hσ' ih
  rcases PFun.mem_fix_iff.1 hσ' with h1 | ⟨τ, hτ, _⟩
  · exact ⟨σ', .refl, mem_stepP_inl.1 h1⟩
  · obtain ⟨υ, hυ, hs⟩ := ih τ hτ
    exact ⟨υ, Relation.ReflTransGen.head (mem_stepP_inr.1 hτ) hυ, hs⟩

/-- **A loop's run is its reduction system's normal form**: the outcome a
reachable state is done with (there is at most one, `iterN_done_unique`),
or `diverge` when every reachable state goes on. -/
theorem run_cases (σ : α) :
    (∃ τ, (rs body c).MRed σ τ ∧ step body c τ = .inr (run body c σ)) ∨
      (run body c σ = .error .diverge ∧
        ∀ τ, (rs body c).MRed σ τ → ∃ τ', (rs body c).Red τ τ') := by
  by_cases h : ((stepP body c).fix σ).Dom
  · left
    have hm := Part.get_mem h
    rw [run_eq_of_mem_fix hm]
    exact exists_mred_of_mem_fix hm
  · right
    refine ⟨run_eq_diverge h, fun τ hτ => ?_⟩
    cases hs : step body c τ with
    | inl τ' => exact ⟨τ', hs⟩
    | inr r =>
      exact absurd (Part.dom_iff_mem.2 ⟨r, by
        rw [fix_eq_of_mred hτ]; exact PFun.fix_stop (mem_stepP_inl.2 hs)⟩) h

/-- The loop's reduction system is deterministic. -/
theorem rs_deterministic {σ τ τ' : α} (h : (rs body c).Red σ τ) (h' : (rs body c).Red σ τ') :
    τ = τ' :=
  Sum.inl.inj (h.symm.trans h')

end TLoop

end Solidity
