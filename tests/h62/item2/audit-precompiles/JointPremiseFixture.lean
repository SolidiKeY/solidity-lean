import Solidity.Precompiles.Field

/-! Isolated simultaneous numeric constraints for the two generic MSM gas lemmas.
This imports only the unchanged buildable shared interface. It is NOT an imported
BLS statement witness and must not increase statement coverage before the BLS
producer receipt permits full original-type instantiation. -/
namespace H62.AuditPrecompiles

private theorem zero_table_getD (n i : Nat) :
    (List.replicate n 0).getD i 0 = 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- One table/cap/input-pair satisfies length, every adjacent constraint and k≤l together. -/
theorem msm_joint_premises_fixture : ∃ (table : List Nat) (cap k l : Nat),
    table.length = 128 ∧
    (∀ i < 128, (i + 1) * table.getD i cap ≤ (i + 2) * table.getD (i + 1) cap) ∧
    k ≤ l := by
  refine ⟨List.replicate 128 0, 0, 1, 2, List.length_replicate, ?_, by decide⟩
  intro i _
  simp only [zero_table_getD, Nat.mul_zero, Nat.le_refl]

#print axioms zero_table_getD
#print axioms msm_joint_premises_fixture
end H62.AuditPrecompiles
