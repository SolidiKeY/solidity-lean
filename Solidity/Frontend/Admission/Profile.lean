import Solidity.Frontend.Source

/-!
# Exact classification of extracted admission uses (G15 checkpoint 1)

These theorems concern the existing classifier, not completeness of the JSON
walker or agreement with source execution. In particular, rejection must not
silently truncate the uses following its first diagnostic. The public compiler
still needs certified extraction of every execution root and observation.
-/
namespace Solidity.Frontend.Source
open Solidity.Language

/-- Classification retains the entire ordered feature list, even on failure. -/
theorem ScopeScan.certify_features (uses : List Use) :
    (certify uses).features = uses.map Use.feature := by
  induction uses with
  | nil => rfl
  | cons u us ih =>
    simp only [certify]
    split
    · cases hs : certify us with
      | admitted fs hw =>
        simp only [hs, features] at ih ⊢
        exact congrArg (List.cons u.feature) ih
      | rejected fs d =>
        simp only [hs, features] at ih ⊢
        exact congrArg (List.cons u.feature) ih
    · rfl

/-- The existing classifier accepts exactly the policy's model/abstract uses.
This makes no assertion of implementation support for a modelled feature. -/
theorem ScopeScan.certify_iff (uses : List Use) :
    (certify uses).diagnostic? = none ↔ WithinProfile (uses.map Use.feature) := by
  induction uses with
  | nil =>
    constructor
    · exact fun _ _ h => nomatch h
    · exact fun _ => rfl
  | cons u us ih =>
    constructor
    · intro h
      have hw := within (certify (u :: us)) h
      rw [certify_features] at hw
      exact hw
    · intro hw
      have hu : u.feature.inProfile := hw u.feature (List.mem_cons_self ..)
      have ht : WithinProfile (us.map Use.feature) :=
        fun f hf => hw f (List.mem_cons_of_mem _ hf)
      have hd := ih.mpr ht
      simp only [certify]
      split
      · cases hs : certify us with
        | admitted fs hfs => rfl
        | rejected fs d =>
          simp only [hs, diagnostic?] at hd
          cases hd
      · next h => exact False.elim (h hu)

/-- A rejected classification has an actual out-of-profile use in its input. -/
theorem ScopeScan.certify_rejected_iff (uses : List Use) :
    (certify uses).diagnostic? ≠ none ↔
      ∃ u ∈ uses, ¬ u.feature.inProfile := by
  classical
  constructor
  · intro hn
    apply Classical.byContradiction
    intro he
    apply hn
    apply (certify_iff uses).mpr
    intro f hf
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hf
    apply Classical.byContradiction
    intro hf
    exact he ⟨u, hu, hf⟩
  · intro ⟨u, hu, hf⟩ hn
    have hw := (certify_iff uses).mp hn
    exact hf (hw u.feature (List.mem_map.mpr ⟨u, hu, rfl⟩))

/-- Combining scans preserves both operands' features, including failures. -/
theorem ScopeScan.append_features (a b : ScopeScan) :
    (a.append b).features = a.features ++ b.features := by
  cases a <;> cases b <;> rfl

/-- A failure in either root group cannot be hidden by concatenation. -/
theorem ScopeScan.append_iff (a b : ScopeScan) :
    (a.append b).diagnostic? = none ↔ a.diagnostic? = none ∧ b.diagnostic? = none := by
  cases a <;> cases b <;> simp only [append, diagnostic?, reduceCtorEq, false_and,
    and_false, and_self]

end Solidity.Frontend.Source
