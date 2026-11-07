import Solidity.Calculus.DecisionNumericBounds

/-! # Actual two-prefix numeric term translation
The two real pushQ operations supply both local atoms. This is a source
producer theorem, not a coverage premise or a completed Residue boundary.
-/
namespace Solidity.Decide

/-- Two intrinsic uint locals translate to exactly the two actual fresh atoms,
with the original source-derived node bound and no environment atoms. -/
theorem uintLinear_two_prefix_sourceBound {C : Contract}
    {t : Tm C [.val .uint, .val .uint] (.val .uint)} (h : t.UIntLinear) :
    ∃ l : LTm C (.val .uint),
      t.toLT (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some l ∧
      l.Num (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.condSimp = l ∧ l.nodes ≤ t.size := by
  rw [toLT_eq_toL_of_agree t _ (uintLinear_agrees h)]
  have hρ : ∀ i : Idx [.val .uint, .val .uint] (.val .uint),
      ∃ l : LTm C (.val .uint),
        (((SymS.init (C := C)).pushQ .uint).pushQ .uint).loc.get i = some l ∧
        l.Num (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
        (l.elim : LTm C (.val .uint)) = l ∧ l.nodes ≤ 1 := by
    intro i
    cases i with
    | here => exact ⟨.var 1, rfl, .var 1 (.inr rfl), rfl, Nat.le_refl 1⟩
    | there i =>
      cases i with
      | here => exact ⟨.var 0, rfl, .var 0 (.inl rfl), rfl, Nat.le_refl 1⟩
      | there i => cases i
  obtain ⟨l, hl, hn, he, hs⟩ := uintLinear_toL_sourceBound h _ hρ
  exact ⟨l, hl, hn, he, LTm.condSimp_of_conds l (numeric_no_conds hn), hs⟩

end Solidity.Decide
