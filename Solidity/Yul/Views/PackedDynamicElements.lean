import Solidity.Yul.Views.PackedDynamicDeclarations

namespace Solidity.Yul.Views

def PackedDynamicHeader.byteWidth {E root t cursor} (_ : PackedDynamicHeader E root t cursor) : Nat := t.bits/8

def PackedDynamicHeader.perSlot {E root t cursor} (h : PackedDynamicHeader E root t cursor) : Nat := 32/h.byteWidth

theorem PackedDynamicHeader.width_bounds {E root t cursor} (h : PackedDynamicHeader E root t cursor) :
    0 < h.byteWidth ∧ h.byteWidth ≤ 32 := StorageWidth.bounds (D := E.layout) (StorageWidth.int t)

theorem PackedDynamicHeader.perSlot_positive {E root t cursor} (h : PackedDynamicHeader E root t cursor) : 0 < h.perSlot :=
  Nat.div_pos h.width_bounds.2 h.width_bounds.1

theorem PackedDynamicHeader.element_fits {E root t cursor} (h : PackedDynamicHeader E root t cursor) (i : Nat) :
    (i % h.perSlot)*h.byteWidth + h.byteWidth ≤ 32 := by
  have rem := Nat.mod_lt i h.perSlot_positive
  calc
    _ = (i % h.perSlot + 1)*h.byteWidth := by rw [Nat.add_mul,Nat.one_mul]
    _ ≤ h.perSlot*h.byteWidth := Nat.mul_le_mul_right h.byteWidth (by omega)
    _ ≤ 32 := Nat.div_mul_le_self 32 h.byteWidth

def PackedDynamicHeader.elementPath {E root t cursor} (_ : PackedDynamicHeader E root t cursor) (i : Nat) : Source.SPath := ⟨root,[.index i]⟩

theorem PackedDynamicHeader.element_type {E root t cursor} (h : PackedDynamicHeader E root t cursor) (i : Nat) :
    E.cellTy (h.elementPath i) = .int t := by
  simp only [elementPath,Source.Env.cellTy,Source.Env.pathTy,List.foldl_cons,List.foldl_nil,h.declared,
    Option.bind_some,Source.Env.stepTy,Option.map_some,Source.STy.cell,Source.STy.isValue,if_true,Option.getD_some]

def PackedDynamicHeader.element {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) : ScalarPath E.layout (E.lay a) where
  path := h.elementPath i
  slot := physicalSlot (fixedLayoutHash fixed) (.data (.root (h.registration a).slot.val) (i/h.perSlot))
  field := intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)
  codec := Eq.mp (congrArg (fun τ => ScalarCodec E.layout τ (intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i))) (h.element_type i).symm)
    (intCodec E.layout t ((i%h.perSlot)*h.byteWidth) (h.element_fits i))
  width := Eq.mp (congrArg (fun τ => StorageWidth E.layout τ (t.bits/8)) (h.element_type i).symm) (StorageWidth.int t)

theorem PackedDynamicHeader.element_word {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) :
    (h.element fixed a i).slot.val =
      (fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i/h.perSlot) % (2^256) := by
  change (fixedLayoutHash fixed (.data ((h.registration a).slot.val % (2^256)))+i/h.perSlot) % (2^256) = _
  rw [Nat.mod_eq_of_lt (h.registration a).slot.isLt]
  rfl

def PackedDynamicHeader.elements {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) := (List.range n.val).map (h.element fixed a)

theorem PackedDynamicHeader.elements_member {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (c) :
    c ∈ h.elements fixed a n ↔ ∃ i, i<n.val ∧ h.element fixed a i = c := by
  simp only [elements,List.mem_map,List.mem_range]

end Solidity.Yul.Views
