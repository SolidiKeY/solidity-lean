import Solidity.Yul.Views.PathIntSource

namespace Solidity.Yul.Views

theorem PathIntHeader.length_encode_value {E root t cursor} (h : PathIntHeader E root t cursor)
    (a : Roadmap.Address) (n : Roadmap.Word) : ((h.registration a).codec.encode (h.lengthValue n)).val = n.val := by
  have val := congrArg Fin.val (DeclPosition.registration_encode
    ((dynamicHeaderSeed E).position (roundSlot cursor)) root (path_integer_header_cell h.declared) a h.bounded
    (uintValueOfWord E.layout n))
  have reduced : ((h.registration a).codec.encode (h.lengthValue n)).val =
      (((dynamicHeaderSeed E).position (roundSlot cursor)).codec.encode (uintValueOfWord E.layout n)).val := by
    simpa only [PathIntHeader.registration,PathIntHeader.lengthValue] using val
  rw [reduced]
  change intPayload .u256 (n.val : Int) = n.val
  have nonnegative : ¬(n.val : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  simp only [intPayload,if_neg nonnegative,Int.toNat_natCast]

theorem PathIntHeader.offset {E root t cursor} (h : PathIntHeader E root t cursor) (a : Roadmap.Address) :
    (h.registration a).field.offset = 0 := by
  change ((dynamicHeaderSeed E).position (roundSlot cursor)).start%32 = 0
  rw [dynamic_header_start]
  exact (roundSlot_spec cursor).2.2

theorem PathIntHeader.width {E root t cursor} (h : PathIntHeader E root t cursor) (a : Roadmap.Address) :
    (h.registration a).field.width = 32 := rfl

theorem PathIntHeader.header_find_value {E root t cursor} (h : PathIntHeader E root t cursor)
    (a : Roadmap.Address) (n : Roadmap.Word) : ((h.registration a).field.findWord n).val = n.val := by
  change n.val / 256^((h.registration a).field.offset) % 256^((h.registration a).field.width) = n.val
  rw [h.offset,h.width]
  simp only [Nat.pow_zero,Nat.div_one]
  have power : 256^32 = 2^256 := by decide
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le n.isLt (Nat.le_of_eq power.symm))

theorem PathIntHeader.length_encode {E root t cursor} (h : PathIntHeader E root t cursor)
    (a : Roadmap.Address) (n : Roadmap.Word) :
    (h.registration a).codec.encode (h.lengthValue n) = (h.registration a).field.findWord n :=
  Fin.ext ((h.length_encode_value a n).trans (h.header_find_value a n).symm)

/-- Actual typed Source length read is derived FROM the computed codec view;
no caller supplies a finished read agreement or inverse theorem. -/
theorem PathIntHeader.view_length_cell {E root t cursor} (h : PathIntHeader E root t cursor)
    (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : scalarPathView (h.registration a).path (h.registration a).codec (h.registration a).slot s m) :
    s.read root = some (h.lengthValue (m (h.registration a).slot)) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have same := (h.registration a).codec.encode_injective (encoded.trans (h.length_encode a _).symm)
  rw [same] at read
  exact read

end Solidity.Yul.Views
