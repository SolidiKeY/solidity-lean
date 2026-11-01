import Solidity.Yul.Views.PackedDynamicSeparation

namespace Solidity.Yul.Views

/-- Exact LIVE byte ownership from the actual length and documented field
coordinates, including unused full-slot and trailing partial-slot padding. -/
theorem PackedDynamicHeader.owns_byte_iff {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (q : Roadmap.Word) (b : Fin 32) :
    packedOwnsByte (h.elements fixed a n) q b = true ↔
      ∃ i, i<n.val ∧ (h.element fixed a i).slot=q ∧
        (i%h.perSlot)*h.byteWidth ≤ b.val ∧ b.val < (i%h.perSlot)*h.byteWidth+h.byteWidth := by
  rw [packedOwnsByte_iff]
  constructor
  · rintro ⟨c,member,same,lo,hi⟩
    obtain ⟨i,ib,rfl⟩ := (h.elements_member fixed a n c).mp member
    exact ⟨i,ib,same,lo,hi⟩
  · rintro ⟨i,ib,same,lo,hi⟩
    exact ⟨h.element fixed a i,(h.elements_member fixed a n _).mpr ⟨i,ib,rfl⟩,same,lo,hi⟩

theorem PackedDynamicHeader.element_noWrap {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat)
    (bound : fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i/h.perSlot < 2^256) :
    (h.element fixed a i).slot.val = fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i/h.perSlot := by
  rw [h.element_word,Nat.mod_eq_of_lt bound]

/-- All typed dynamic unsigned headers are enumerated by the same ordered
source root cursor. This is a supported-certificate inventory, not a claim
that arbitrary mappings/bytes/unknown metadata are represented. -/
theorem StorageDeclarations.unsigned_header_roots {E ds} (d : StorageDeclarations E ds) (cursor : Nat) :
    List.Sublist ((d.unsignedHeaders cursor).map Prod.fst) (ds.map Prod.fst) := by
  induction d generalizing cursor with
  | nil => exact .slnil
  | @cons root τ rest head tail ih =>
    cases head with
    | fixed fixed => exact List.Sublist.cons root (ih (fixed.endByte cursor))
    | uintArray => exact List.Sublist.cons₂ root (ih ((StorageDeclaration.uintArray (E := E)).endByte cursor))
    | packedUnsignedArray t u h => exact List.Sublist.cons₂ root (ih ((StorageDeclaration.packedUnsignedArray (E := E) t u h).endByte cursor))

theorem ComputedStorage.unsigned_headers_unique {E ds d active a} (r : @ComputedStorage E ds d active a) :
    (r.unsignedTrace.map Prod.fst).Nodup := (d.unsigned_header_roots _).nodup r.distinct

end Solidity.Yul.Views
