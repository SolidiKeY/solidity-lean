import Solidity.Storage.HashedSeparation

/-! Isolated symbolic-location fixture. This is not registered or integrated. -/
namespace H62.LocationFixture
open Solidity.Storage

theorem child_ne_base (base : Loc) (i : Nat) : Loc.data base i ≠ base := by
  intro h
  have hd : (Loc.data base i).depth = base.depth := congrArg Loc.depth h
  simp only [Loc.depth] at hd
  omega

theorem grandchild_ne_base (base : Loc) (i j : Nat) :
    Loc.data (.data base i) j ≠ base := by
  intro h
  have hd : (Loc.data (.data base i) j).depth = base.depth := congrArg Loc.depth h
  simp only [Loc.depth] at hd
  omega

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

#print axioms child_ne_base
#print axioms grandchild_ne_base
#print axioms distinct_indices
end H62.LocationFixture
