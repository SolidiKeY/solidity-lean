import Solidity.Lowering.P8.HelperPackets.MonetaryBounds.Laws

/-! Kernel boundary controls; these are not EVM execution tests. -/
namespace Solidity.Source.Monetary
open Solidity.Roadmap (Word)

theorem boundary_zero_fits : Fits (0) := by decide
theorem boundary_zero_checked : checkedWord (0) = some ⟨0, by decide⟩ := by decide
theorem boundary_zero_debit_zero : debit? (0) ⟨0, by decide⟩ = some (0) := by decide
theorem boundary_zero_credit_zero : credit? (0) ⟨0, by decide⟩ = some (0) := by decide
theorem boundary_zero_view : (wordView (0)).val = 0 := by decide

theorem boundary_max_fits : Fits (wordLimit - 1) := by decide
theorem boundary_max_checked : checkedWord (wordLimit - 1) = some ⟨wordLimit - 1, by decide⟩ := by decide
theorem boundary_max_debit_zero : debit? (wordLimit - 1) ⟨0, by decide⟩ = some (wordLimit - 1) := by decide
theorem boundary_max_credit_zero : credit? (wordLimit - 1) ⟨0, by decide⟩ = some (wordLimit - 1) := by decide
theorem boundary_max_view : (wordView (wordLimit - 1)).val = wordLimit - 1 := by decide

theorem boundary_limit_fits : ¬ Fits (wordLimit) := by decide
theorem boundary_limit_checked : checkedWord (wordLimit) = none := by decide
theorem boundary_limit_debit_zero : debit? (wordLimit) ⟨0, by decide⟩ = some (wordLimit) := by decide
theorem boundary_limit_credit_zero : credit? (wordLimit) ⟨0, by decide⟩ = none := by decide
theorem boundary_limit_view : (wordView (wordLimit)).val = 0 := by decide

theorem boundary_above_fits : ¬ Fits (wordLimit + 1) := by decide
theorem boundary_above_checked : checkedWord (wordLimit + 1) = none := by decide
theorem boundary_above_debit_zero : debit? (wordLimit + 1) ⟨0, by decide⟩ = some (wordLimit + 1) := by decide
theorem boundary_above_credit_zero : credit? (wordLimit + 1) ⟨0, by decide⟩ = none := by decide
theorem boundary_above_view : (wordView (wordLimit + 1)).val = 1 := by decide

theorem zero_unaffordable : debit? 0 ⟨1, by decide⟩ = none := by decide
theorem max_affordable : debit? (wordLimit - 1) ⟨wordLimit - 1, by decide⟩ = some 0 := by decide
theorem limit_affordable : debit? wordLimit ⟨wordLimit - 1, by decide⟩ = some 1 := by decide
theorem above_affordable : debit? (wordLimit + 1) ⟨wordLimit - 1, by decide⟩ = some 2 := by decide
theorem zero_credit_max : credit? 0 ⟨wordLimit - 1, by decide⟩ = some (wordLimit - 1) := by decide
theorem max_credit_refused : credit? (wordLimit - 1) ⟨1, by decide⟩ = none := by decide
theorem limit_credit_refused : credit? wordLimit ⟨1, by decide⟩ = none := by decide
theorem above_credit_refused : credit? (wordLimit + 1) ⟨1, by decide⟩ = none := by decide
/-- Positive nonzero round trips exercise both laws at the last Word. -/
theorem max_forward_roundtrip : debit? (wordLimit - 1) ⟨wordLimit - 1, by decide⟩ = some 0 :=
  credit_debit_roundtrip 0 ⟨wordLimit - 1, by decide⟩ (wordLimit - 1) zero_credit_max

theorem max_reverse_roundtrip : credit? 0 ⟨wordLimit - 1, by decide⟩ = some (wordLimit - 1) :=
  debit_credit_roundtrip (wordLimit - 1) ⟨wordLimit - 1, by decide⟩ 0 boundary_max_fits max_affordable

/-- Actual successful debit, followed by refused credit; Fits cannot be dropped. -/
theorem reverse_without_fits_counterexample :
    ¬ Fits wordLimit ∧ debit? wordLimit ⟨1, by decide⟩ = some (wordLimit - 1) ∧
      credit? (wordLimit - 1) ⟨1, by decide⟩ = none ∧
      credit? (wordLimit - 1) ⟨1, by decide⟩ ≠ some wordLimit := by decide

theorem above_reverse_counterexample :
    debit? (wordLimit + 1) ⟨1, by decide⟩ = some wordLimit ∧
      credit? wordLimit ⟨1, by decide⟩ = none := by decide

theorem checked_rejects_wrong_word : checkedWord 0 ≠ some (⟨1, by decide⟩ : Word) := by decide

theorem max_unaffordable : debit? (wordLimit - 2) ⟨wordLimit - 1, by decide⟩ = none := by decide

end Solidity.Source.Monetary
