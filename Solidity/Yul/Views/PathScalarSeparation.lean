import Solidity.Yul.Views.PathScalarLengthCodec

namespace Solidity.Yul.Views

theorem PathScalarHeader.element_paths_ne {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i j : Nat) (different : i ≠ j) :
    (h.element fixed a i).path ≠ (h.element fixed a j).path := by
  intro same
  have steps := congrArg Source.SPath.steps same
  change root.steps ++ [Source.Step.index i] = root.steps ++ [Source.Step.index j] at steps
  exact different (Source.Step.index.inj ((List.cons.inj (List.append_cancel_left steps)).1))

theorem PathScalarHeader.elements_apart {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i j : Nat)
    (ib : i < 2^256) (jb : j < 2^256) (different : i ≠ j) : pathsApart (h.element fixed a i) (h.element fixed a j) := by
  by_cases quotient : i/h.perSlot = j/h.perSlot
  · have rem : i%h.perSlot ≠ j%h.perSlot := by
      intro same
      have one := Nat.mod_add_div i h.perSlot
      have two := Nat.mod_add_div j h.perSlot
      rw [quotient] at one
      exact different (by omega)
    change _ ∨ (i%h.perSlot)*h.byteWidth+h.byteWidth ≤ (j%h.perSlot)*h.byteWidth ∨
      (j%h.perSlot)*h.byteWidth+h.byteWidth ≤ (i%h.perSlot)*h.byteWidth
    rcases Nat.lt_or_gt_of_ne rem with lt | gt
    · apply Or.inr ∘ Or.inl
      calc
        _ = (i%h.perSlot+1)*h.byteWidth := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right h.byteWidth (by omega)
    · apply Or.inr ∘ Or.inr
      calc
        _ = (j%h.perSlot+1)*h.byteWidth := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right h.byteWidth (by omega)
  · apply Or.inl
    intro same
    have words := congrArg Fin.val same
    rw [h.element_word,h.element_word] at words
    exact quotient (Storage.Loc.off_eq_of_mod_eq (fixed.keccak_lt _)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ib) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) jb) words)

theorem PathScalarHeader.elements_separated {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) : finiteSeparated (h.elements fixed a n) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (List.nodup_range)
  intro i j im jm different
  exact ⟨h.element_paths_ne fixed a i j different,h.elements_apart fixed a i j
    (Nat.lt_trans (List.mem_range.mp im) n.isLt) (Nat.lt_trans (List.mem_range.mp jm) n.isLt) different⟩

/-- Region offset is the actual PACKED slot quotient, not the element index. -/
theorem PathScalarHeader.element_ne_registered {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i L : Nat) (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lb : L ≤ 2^256) (offset : i/h.perSlot < L)
    (preimage : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (r : Roadmap.Word) (registered : r.val ∈ roots) : (h.element fixed a i).slot ≠ r := by
  intro same
  have words := congrArg Fin.val same
  rw [h.element_word] at words
  exact regions.2 _ preimage r.val registered
    (Hash.covers_of_hit (fixedLayoutHash_lt fixed _) lb offset words)

end Solidity.Yul.Views
