import Solidity.KeySort
import Solidity.Syntax.CheckedExact

/-! Complete hypothesis tuples for the independent frozen lattice and checked
arithmetic interfaces. All arguments of each statement share one concrete input.
This module adds no compiler contract or replacement arithmetic semantics. -/
namespace Solidity.H62.AuditLanguage

/-- The base-sort argument and its exact premise coexist. -/
theorem sort_name_hypotheses : ∃ s : KeySort, s.isBase = true := by
  exact ⟨.bool, rfl⟩

/-- Two nontrivial lattice edges hold simultaneously on the same middle sort. -/
theorem sort_trans_hypotheses : ∃ a b c : KeySort,
    KeySort.le a b = true ∧ KeySort.le b c = true := by
  exact ⟨.bool, .prim, .any, rfl, rfl⟩

theorem sort_trans_client : KeySort.le .bool .any = true := by
  exact KeySort.le_trans (a := .bool) (b := .prim) (c := .any) rfl rfl

theorem emod_hypotheses : ∃ x M : Int, M ≤ x ∧ x < 2 * M := by
  exact ⟨130, 128, by decide, by decide⟩

theorem add_uint_hypotheses : ∃ M a b : Int,
    0 ≤ a ∧ a < M ∧ 0 ≤ b ∧ b < M := by
  exact ⟨256, 250, 7, by decide, by decide, by decide, by decide⟩

theorem mul_uint_hypotheses : ∃ M a b : Int,
    0 ≤ a ∧ a < M ∧ 0 ≤ b ∧ b < M := by
  exact ⟨256, 17, 16, by decide, by decide, by decide, by decide⟩

theorem add_int_hypotheses : ∃ M a _b : Int, -M ≤ a ∧ a < M := by
  exact ⟨128, 127, 1, by decide, by decide⟩

theorem sub_int_hypotheses : ∃ M a _b : Int, -M ≤ a ∧ a < M := by
  exact ⟨128, -128, 1, by decide, by decide⟩

theorem neg_int_hypotheses : ∃ M a : Int, -M ≤ a ∧ a < M := by
  exact ⟨128, -128, by decide, by decide⟩

theorem div_int_hypotheses : ∃ M a b : Int,
    0 < M ∧ (-M ≤ a ∧ a < M) ∧ b ≠ 0 := by
  exact ⟨128, -128, -1, by decide, ⟨by decide, by decide⟩, by decide⟩

theorem mul_int_hypotheses : ∃ M a b : Int,
    0 < M ∧ (-M ≤ a ∧ a < M) ∧ (-M ≤ b ∧ b < M) := by
  exact ⟨128, -128, -1, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- Import the frozen statement at a real overflow boundary. -/
theorem uint_add_overflow_client : ¬ ((250 : Int) ≤ (250 + 7) % 256) := by
  intro h
  have bounded : (250 : Int) + 7 < 256 :=
    (Checked.add_uint_exact (M := 256) (a := 250) (b := 7)
      (by decide) (by decide) (by decide) (by decide)).mp h
  exact (by decide : ¬ ((250 : Int) + 7 < 256)) bounded

#print axioms sort_trans_hypotheses
#print axioms sort_trans_client
#print axioms uint_add_overflow_client
end Solidity.H62.AuditLanguage
