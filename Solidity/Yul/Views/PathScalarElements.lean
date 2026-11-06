import Solidity.Yul.Views.PathScalarHeader

namespace Solidity.Yul.Views

def PathScalarHeader.byteWidth {E root t cursor} (_ : PathScalarHeader E root t cursor) : Nat := (t.seed E.layout).field.width

def PathScalarHeader.perSlot {E root t cursor} (h : PathScalarHeader E root t cursor) : Nat := 32/h.byteWidth

theorem PathScalarHeader.width_bounds {E root t cursor} (h : PathScalarHeader E root t cursor) :
    0 < h.byteWidth ∧ h.byteWidth ≤ 32 := StorageWidth.bounds (D := E.layout) (t.seed E.layout).width

theorem PathScalarHeader.perSlot_positive {E root t cursor} (h : PathScalarHeader E root t cursor) : 0 < h.perSlot :=
  Nat.div_pos h.width_bounds.2 h.width_bounds.1

theorem PathScalarHeader.element_fits {E root t cursor} (h : PathScalarHeader E root t cursor) (i : Nat) :
    (i % h.perSlot)*h.byteWidth + h.byteWidth ≤ 32 := by
  have rem := Nat.mod_lt i h.perSlot_positive
  calc
    _ = (i % h.perSlot + 1)*h.byteWidth := by rw [Nat.add_mul,Nat.one_mul]
    _ ≤ h.perSlot*h.byteWidth := Nat.mul_le_mul_right h.byteWidth (by omega)
    _ ≤ 32 := Nat.div_mul_le_self 32 h.byteWidth

def PathScalarHeader.elementPath {E root t cursor} (_ : PathScalarHeader E root t cursor) (i : Nat) : Source.SPath := root.go (.index i)

theorem PathScalarHeader.element_type {E root t cursor} (h : PathScalarHeader E root t cursor) (i : Nat) :
    E.cellTy (h.elementPath i) = t.ty := by
  simp only [elementPath,Source.Env.cellTy,Source.Env.pathTy_go,h.declared,
    Option.bind_some,Source.Env.stepTy,Option.map_some,Option.getD_some,t.cell]


def PathScalarHeader.element {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) : ScalarPath E.layout (E.lay a) where
  path := h.elementPath i
  slot := physicalSlot (fixedLayoutHash fixed) (.data (.root (h.registration a).slot.val) (i/h.perSlot))
  field := ⟨(i%h.perSlot)*h.byteWidth,h.byteWidth,h.width_bounds.1,h.element_fits i⟩
  codec := Eq.mp (congrArg (fun τ => ScalarCodec E.layout τ ⟨(i%h.perSlot)*h.byteWidth,h.byteWidth,h.width_bounds.1,h.element_fits i⟩) (h.element_type i).symm)
    ((t.seed E.layout).codec.atOffset ((i%h.perSlot)*h.byteWidth) (h.element_fits i))
  width := Eq.mp (congrArg (fun τ => StorageWidth E.layout τ ((t.seed E.layout).field.width)) (h.element_type i).symm) (t.seed E.layout).width

theorem PathScalarHeader.element_word {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) :
    (h.element fixed a i).slot.val =
      (fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i/h.perSlot) % (2^256) := by
  change (fixedLayoutHash fixed (.data ((h.registration a).slot.val % (2^256)))+i/h.perSlot) % (2^256) = _
  rw [Nat.mod_eq_of_lt (h.registration a).slot.isLt]
  rfl

def PathScalarHeader.elements {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) := (List.range n.val).map (h.element fixed a)

theorem PathScalarHeader.elements_member {E root t cursor} (h : PathScalarHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (c) :
    c ∈ h.elements fixed a n ↔ ∃ i, i<n.val ∧ h.element fixed a i = c := by
  simp only [elements,List.mem_map,List.mem_range]

end Solidity.Yul.Views
