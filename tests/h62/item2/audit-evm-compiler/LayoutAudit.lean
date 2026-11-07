import Solidity.Evm.Layout

/-! Exact simultaneous impossibility controls for frozen separation lemmas.
These are blockers for the universal witness requirement, not replacements for
that requirement and not evidence of a defective compiler correctness theorem. -/
namespace Solidity.H62.EvmCompilerAudit
open Evm Semantics

theorem occ_len_elem_no_joint_witness :
    ¬ ∃ (E : Ty) (s : Slot) (n : Nat), Occ E (.data s n) s := by
  rintro ⟨E, s, n, h⟩
  exact occ_len_elem h

theorem occ_entries_no_joint_witness :
    ¬ ∃ (V : Ty) (s x : Slot) (k₁ k₂ : Fin W), k₁ ≠ k₂ ∧
      Occ V (.hash k₁ s 0) x ∧ Occ V (.hash k₂ s 0) x := by
  rintro ⟨V, s, x, k₁, k₂, hne, h₁, h₂⟩
  exact occ_entries_disjoint hne h₁ h₂

theorem occ_elems_no_joint_witness :
    ¬ ∃ (E : Ty) (s x : Slot) (i j : Nat), i ≠ j ∧
      Occ E (.data s (i * size E)) x ∧ Occ E (.data s (j * size E)) x := by
  rintro ⟨E, s, x, i, j, hne, h₁, h₂⟩
  exact occ_elems_disjoint hne h₁ h₂

theorem occ_felems_no_joint_witness :
    ¬ ∃ (E : Ty) (s x : Slot) (i j : Nat), i ≠ j ∧
      Occ E (s.add (i * size E)) x ∧ Occ E (s.add (j * size E)) x := by
  rintro ⟨E, s, x, i, j, hne, h₁, h₂⟩
  exact occ_felems_disjoint hne h₁ h₂

theorem occ_members_no_joint_witness :
    ¬ ∃ (l : List (Name × Ty)) (s x : Slot) (f₁ f₂ : Name) (T₁ T₂ : Ty),
      lookupBy f₁ l = some T₁ ∧ lookupBy f₂ l = some T₂ ∧ f₁ ≠ f₂ ∧
      Occ T₁ (s.add (offsetIn l f₁)) x ∧ Occ T₂ (s.add (offsetIn l f₂)) x := by
  rintro ⟨l, s, x, f₁, f₂, T₁, T₂, h₁, h₂, hne, o₁, o₂⟩
  exact occ_members_disjoint h₁ h₂ hne o₁ o₂

/-- Each separated region can be inhabited, while their overlap cannot. -/
theorem individual_mapping_occupancies :
    (∃ x, Occ (.prim .uint) (.hash (wmod 0) (.root 0) 0) x) ∧
    (∃ x, Occ (.prim .uint) (.hash (wmod 1) (.root 0) 0) x) :=
  ⟨⟨_, .prim⟩, ⟨_, .prim⟩⟩

#print axioms occ_len_elem_no_joint_witness
#print axioms occ_entries_no_joint_witness
#print axioms occ_elems_no_joint_witness
#print axioms occ_felems_no_joint_witness
#print axioms occ_members_no_joint_witness
#print axioms individual_mapping_occupancies
end Solidity.H62.EvmCompilerAudit
