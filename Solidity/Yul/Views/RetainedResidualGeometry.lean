import Solidity.Yul.Views.ResidualMemoryWriteback

namespace Solidity.Yul.Views

theorem MixedHeapEntry.bytes_span_at {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (entry : MixedHeapEntry p) (root : Nat) (bytes : List UInt8)
    (found : h.get root=some ⟨.bytes .memory,Source.Data.bytes bytes⟩) (same : entry.id=root) :
    entry.image.span=32+bytes.length := by
  cases entry with
  | mk id ty data actual image =>
    dsimp only at same ⊢
    subst id
    have eq := Option.some.inj (found.symm.trans actual)
    cases eq
    exact image.bytes_span

/-- The window lies in this ACTUAL original allocation, past the CURRENT
live byte payload. Original occupancy/address/extent separation derives the
frame even after shrinking to zero; no capacity is inferred from a gap/free
pointer and no current shape falsely retains the old length. -/
theorem retained_byte_padding_disjoint {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (bytes : List UInt8)
    (found : h.get root=some ⟨.bytes .memory,Source.Data.bytes bytes⟩)
    (destination size : Nat) (afterLive : current.address root+32+bytes.length≤destination)
    (withinOwned : destination+size≤allocated.address root+(allocated.shape root).size) :
    ResidualWindowDisjoint current es destination size := by
  have present : (h.cells root).isSome := by change (h.get root).isSome=true; rw [found]; rfl
  intro entry member
  by_cases same : entry.id=root
  · have span := entry.bytes_span_at root bytes found same
    exact Or.inr (Or.inr (Or.inr (by rw [same,span]; omega)))
  · have other : (h.cells entry.id).isSome := by change (h.get entry.id).isSome=true; rw [entry.found]; rfl
    have separated := allocated.separate root entry.id (by rw [←history.occupancy root]; exact present)
      (by rw [←history.occupancy entry.id]; exact other) (Ne.symm same)
    have spanBound := Nat.le_trans (entry.image.fits current entry.id entry.found) (history.fits entry.id other)
    have addressRoot := congrFun history.addresses root
    have addressEntry := congrFun history.addresses entry.id
    rcases separated with left | right
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

end Solidity.Yul.Views
