import Solidity.Storage.HashedSeparation

/-! Symbolic-location correspondence and alias controls. This test module is not registered. -/
namespace H62.LocationFixture
open Solidity.Storage

theorem child_ne_base (base : Loc) (i : Nat) : Loc.data base i ≠ base := by
  exact Solidity.Storage.Loc.data_ne_self base i

theorem grandchild_ne_base (base : Loc) (i j : Nat) :
    Loc.data (.data base i) j ≠ base := by
  exact Solidity.Storage.Loc.data_data_ne_self base i j

theorem base_ne_child (base : Loc) (i : Nat) : base ≠ Loc.data base i :=
  Ne.symm (child_ne_base base i)

theorem base_ne_grandchild (base : Loc) (i j : Nat) : base ≠ Loc.data (.data base i) j :=
  Ne.symm (grandchild_ne_base base i j)

-- Negative control: sibling separation needs an index inequality.
theorem same_index_is_equal (base : Loc) (i : Nat) : Loc.data base i = Loc.data base i := rfl

theorem distinct_indices (base : Loc) {i j : Nat} (h : i ≠ j) :
    Loc.data base i ≠ Loc.data base j := by
  intro same
  exact h (Loc.data.inj same).2

/-- Without word-separation assumptions distinct symbolic siblings can alias. -/
theorem sibling_word_alias (N : Nat) (H : Pre → Nat) (base : Loc) (hN : 0 < N) :
    Loc.data base 0 ≠ Loc.data base N ∧
      (Loc.data base 0).word N H = (Loc.data base N).word N H :=
  Loc.word_data_alias N H base hN

/-- An unconstrained hash can map a child and its root to the same word. -/
theorem child_word_alias : Loc.data (.root 0) 0 ≠ .root 0 ∧
    (Loc.data (.root 0) 0).word 1 (fun _ => 0) = (Loc.root 0).word 1 (fun _ => 0) := by
  exact ⟨child_ne_base (.root 0) 0, rfl⟩

#print axioms sibling_word_alias
#print axioms child_word_alias
#print axioms child_ne_base
#print axioms grandchild_ne_base
#print axioms distinct_indices
/-- info: 'Solidity.Storage.Loc.data_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.Loc.data_ne_self
/-- info: 'Solidity.Storage.Loc.data_data_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.Loc.data_data_ne_self
end H62.LocationFixture
