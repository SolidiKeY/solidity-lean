import Solidity.Calculus.DecisionNumericLogic

/-! # Closed numeric leaf coverage
The zero-prefix case uses the existing numeric grammar and exact-route tests.
Source-to-leaf discovery remains a separate producer obligation.
-/
namespace Solidity.Decide

/-- Closed intrinsic terms have no local atoms to supply. -/
theorem uintLinear_ground_sourceBound {C : Contract}
    {t : Tm C [] (.val .uint)} (h : t.UIntLinear) :
    ∃ l : LTm C (.val .uint), t.toLT (SymS.init (C := C)) = some l ∧
      l.Num (fun _ => False) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.condSimp = l ∧ l.nodes ≤ t.size := by
  rw [toLT_eq_toL_of_agree t _ (uintLinear_agrees h)]
  have hρ : ∀ i : Idx [] (.val .uint), ∃ l : LTm C (.val .uint),
      (SymS.init (C := C)).loc.get i = some l ∧
      l.Num (fun _ => False) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.nodes ≤ 1 := by
    intro i
    cases i
  obtain ⟨l, hl, hn, he, hs⟩ := uintLinear_toL_sourceBound h _ hρ
  exact ⟨l, hl, hn, he, LTm.condSimp_of_conds l (numeric_no_conds hn), hs⟩

/-- A closed numeric body needs no artificial universal binder. -/
theorem LFml.UIntQF.ground_exact_tests {C : Contract} {ψ : LFml C}
    (h : ψ.UIntQF (fun _ => False) (fun _ => False)) (hn : ψ.nodes ≤ 511) :
    ψ.inExact = true ∧ ψ.exactBounded = true := by
  have hshape : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) :=
    source_body_shape (h.source false true)
  have hparse : (ψ.stripAll.2.src? true).isSome = true := by
    rw [hshape.2]
    exact h.parser true
  have hparams : ψ.parameters.all (fun q => decide (q ∈ ([] : List Parameter))) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    exact False.elim (h.parameters q hq)
  have hlift : ψ.liftCond condLiftFuel = ψ := by
    simpa only [LFml.condSimp_of_conds _ h.conds] using
      LFml.liftCond_condSimp_of_conds condLiftFuel ψ h.conds
  have hcut : ψ.cutAll = ψ := by simp only [LFml.cutAll, h.cut_identity]
  have hcond : ψ.condMax < condLiftFuel :=
    Nat.lt_of_le_of_lt h.condMax (by decide : 2 < condLiftFuel)
  constructor
  · simp only [LFml.inExact, hshape.1, hshape.2, hparse, hparams, hcond,
      decide_true, Bool.and_true]
    rfl
  · simp only [LFml.exactBounded, hlift, hshape.2, hcut, hn, decide_true, Bool.and_true]

/-- Actual leaf equality is explicit: this does not assume future source discovery. -/
theorem qfUIntGround_Covered_of_leaf {C : Contract} {φ : Fml C []} {ψ : LFml C}
    (h : ψ.UIntQF (fun _ => False) (fun _ => False)) (hn : ψ.nodes ≤ 511)
    (hl : leafOf? φ = some ψ) : φ.Covered = true := by
  obtain ⟨hi, hb⟩ := h.ground_exact_tests hn
  have hin : φ.inExact = true := by simpa only [Fml.inExact, hl] using hi
  have hbound : φ.exactBounded = true := by simpa only [Fml.exactBounded, hl] using hb
  simp only [Fml.Covered, Fml.CoveredA, hin, hbound, Bool.true_and, Bool.true_or]

end Solidity.Decide
