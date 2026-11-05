import Solidity.Yul.Views.DynamicSeparation

namespace Solidity.Yul.Views

/-- The actual uint256 runtime length determines the finite inventory. There
is no extra traversal, owner-lmax, fuel or allocation cap. Construction may be
large; these mathematical laws do not claim a practical whole-store enumerator. -/
def DynamicHeader.elements {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) :=
  (List.range n.val).map (h.element fixed a)

theorem DynamicHeader.elements_member {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (c) :
    c ∈ h.elements fixed a n ↔ ∃ i, i < n.val ∧ h.element fixed a i = c := by
  simp only [elements,List.mem_map,List.mem_range]

theorem DynamicHeader.element_paths_ne {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i j : Nat) (different : i ≠ j) :
    (h.element fixed a i).path ≠ (h.element fixed a j).path := by
  intro same
  have steps := congrArg Source.SPath.steps same
  change [Source.Step.index i] = [Source.Step.index j] at steps
  exact different (Source.Step.index.inj ((List.cons.inj steps).1))

theorem DynamicHeader.elements_separated {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) :
    finiteSeparated (h.elements fixed a n) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (List.nodup_range)
  intro i j im jm different
  have ib := List.mem_range.mp im
  have jb := List.mem_range.mp jm
  exact ⟨h.element_paths_ne fixed a i j different,
    Or.inl (h.elements_distinct fixed a i j (Nat.lt_trans ib n.isLt) (Nat.lt_trans jb n.isLt) different)⟩

def DynamicHeader.inventory {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) :=
  h.registration a :: h.elements fixed a n

/-- The original per-run hash-region premises are retained. Separation of the
computed actual entries is a conclusion, not an assumed inverse/view law. -/
theorem DynamicHeader.inventory_separated {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (L : Nat)
    (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lb : L ≤ 2^256) (nb : n.val ≤ L)
    (preimage : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (registered : (h.registration a).slot.val ∈ roots) :
    finiteSeparated (h.inventory fixed a n) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro c member
    obtain ⟨i,ib,rfl⟩ := (h.elements_member fixed a n c).mp member
    constructor
    · intro same
      have steps := congrArg Source.SPath.steps same
      change [] = [Source.Step.index i] at steps
      cases steps
    · exact Or.inl (Ne.symm (h.element_ne_registered fixed a i L roots ps regions lb (Nat.lt_of_lt_of_le ib nb) preimage _ registered))
  · exact h.elements_separated fixed a n

theorem DynamicHeader.inventory_unchanged {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : finiteView (h.inventory fixed a n) s m) :
    finiteWriteback (h.inventory fixed a n) m s = some s := finiteWriteback_unchanged _ _ _ view

end Solidity.Yul.Views
