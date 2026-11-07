import Solidity.Lowering.P9.BoundRecognizer

/-! Fuel completeness for the default-type component of the P9 recognizer.
This does not assert completeness of catalogueB or change evaluation horizons. -/
namespace Solidity.Source.Calls.Recognize
open Solidity.Source.Progress
variable {E : Env}

theorem zeroReadyB_complete {τ : STy} (ready : ZeroReady E τ) :
    zeroReadyB E τ = true := by
  cases ready with
  | value h => exact Bool.or_eq_true_iff.mpr (.inl h)
  | memory h =>
    cases h <;> exact Bool.or_eq_true_iff.mpr (.inr rfl)

theorem finiteDefaultB_step (n : Nat) {τ : STy}
    (accepted : finiteDefaultB E n τ = true) :
    finiteDefaultB E (n+1) τ = true := by
  induction n generalizing τ with
  | zero => exact Bool.or_eq_true_iff.mpr (.inl accepted)
  | succ n ih =>
    unfold finiteDefaultB at accepted ⊢
    rcases Bool.or_eq_true_iff.mp accepted with ready | shape
    · exact Bool.or_eq_true_iff.mpr (.inl ready)
    · apply Bool.or_eq_true_iff.mpr
      apply Or.inr
      split at shape
      · exact ih shape
      · exact List.all_eq_true.mpr (fun σ member =>
          ih (List.all_eq_true.mp shape σ member))
      · cases shape

theorem finiteDefaultB_mono {n m : Nat} {τ : STy} (order : n ≤ m)
    (accepted : finiteDefaultB E n τ = true) :
    finiteDefaultB E m τ = true := by
  induction order with
  | refl => exact accepted
  | step order ih => exact finiteDefaultB_step _ ih

theorem finiteDefaultsB_exists (types : List STy)
    (ready : ∀ τ ∈ types, ∃ n, finiteDefaultB E n τ = true) :
    ∃ n, types.all (finiteDefaultB E n) = true := by
  induction types with
  | nil => exact ⟨0,rfl⟩
  | cons τ types ih =>
    obtain ⟨a,head⟩ := ready τ (by simp only [List.mem_cons, true_or])
    obtain ⟨b,tail⟩ := ih (fun σ member =>
      ready σ (by simp only [List.mem_cons]; exact Or.inr member))
    refine ⟨max a b, List.all_eq_true.mpr ?_⟩
    intro σ member
    rcases List.mem_cons.mp member with same | rest
    · subst σ
      exact finiteDefaultB_mono (Nat.le_max_left _ _) head
    · exact finiteDefaultB_mono (Nat.le_max_right _ _) (List.all_eq_true.mp tail σ rest)

theorem finiteDefaultB_complete {τ : STy} (ready : FiniteDefault E τ) :
    ∃ n, finiteDefaultB E n τ = true := by
  induction ready with
  | ready h => exact ⟨0,zeroReadyB_complete h⟩
  | fixed m ready ih =>
    obtain ⟨n,accepted⟩ := ih
    exact ⟨n+1,Bool.or_eq_true_iff.mpr (.inr accepted)⟩
  | structNew dn fields ih =>
    obtain ⟨n,accepted⟩ := finiteDefaultsB_exists (E.layout.fields dn) ih
    exact ⟨n+1,Bool.or_eq_true_iff.mpr (.inr accepted)⟩

theorem finiteDefaultB_iff {τ : STy} :
    FiniteDefault E τ ↔ ∃ n, finiteDefaultB E n τ = true :=
  ⟨finiteDefaultB_complete, fun ⟨n,h⟩ => finiteDefaultB_sound n h⟩

/-- info: 'Solidity.Source.Calls.Recognize.zeroReadyB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroReadyB_complete
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultB_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultB_step
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultB_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultB_mono
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultsB_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultsB_exists
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultB_complete
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultB_iff
end Solidity.Source.Calls.Recognize
