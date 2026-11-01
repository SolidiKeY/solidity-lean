import Solidity.Yul.Views.PackedDynamicRegions

namespace Solidity.Yul.Views

theorem PackedDynamicHeader.u256_perSlot {E root cursor} (h : PackedDynamicHeader E root .u256 cursor) : h.perSlot = 1 := by
  change 32 / (Source.IntTy.u256.bits/8) = 1
  decide

theorem typeTransport_rec {α : Type} (F : α → Type) {x y : α} (e : x=y) (v : F x) :
    Eq.mp (congrArg F e) v = e ▸ v := by cases e; rfl

def DynamicHeader.asPacked {E root cursor} (h : DynamicHeader E root cursor) : PackedDynamicHeader E root .u256 cursor :=
  ⟨rfl,h.declared,h.bounded⟩

theorem DynamicHeader.asPacked_registration {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    h.asPacked.registration a = h.registration a := rfl

theorem DynamicHeader.asPacked_perSlot {E root cursor} (h : DynamicHeader E root cursor) : h.asPacked.perSlot = 1 := by
  change 32 / (Source.IntTy.u256.bits/8) = 1
  decide

theorem DynamicHeader.asPacked_element {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) : h.asPacked.element fixed a i = h.element fixed a i := by
  let build (q : Roadmap.Word) (off : Nat) (fit : off+32≤32) : ScalarPath E.layout (E.lay a) :=
    ⟨h.elementPath i,q,intField .u256 off fit,
      Eq.mp (congrArg (fun τ => ScalarCodec E.layout τ (intField .u256 off fit)) (h.element_type i).symm) (intCodec E.layout .u256 off fit),
      Eq.mp (congrArg (fun τ => StorageWidth E.layout τ 32) (h.element_type i).symm) (StorageWidth.int .u256)⟩
  have normalize (q : Roadmap.Word) (off : Nat) (fit : off+32≤32)
      (slot : q=(h.element fixed a i).slot) (offset : off=0) : build q off fit = h.element fixed a i := by
    subst q
    subst off
    exact congrArg (fun codec : ScalarCodec E.layout (E.cellTy (h.elementPath i)) (intField .u256 0 fit) =>
      (⟨h.elementPath i,(h.element fixed a i).slot,intField .u256 0 fit,codec,
        Eq.mp (congrArg (fun τ => StorageWidth E.layout τ 32) (h.element_type i).symm) (StorageWidth.int .u256)⟩ : ScalarPath E.layout (E.lay a)))
      (typeTransport_rec (fun τ => ScalarCodec E.layout τ (intField .u256 0 fit)) (h.element_type i).symm (intCodec E.layout .u256 0 fit))
  apply normalize
  · change physicalSlot (fixedLayoutHash fixed) (.data (.root (h.asPacked.registration a).slot.val) (i/h.asPacked.perSlot)) = _
    rw [h.asPacked_perSlot,Nat.div_one,h.asPacked_registration]
    rfl
  · change (i%h.asPacked.perSlot)*h.asPacked.byteWidth=0
    rw [h.asPacked_perSlot,Nat.mod_one,Nat.zero_mul]

end Solidity.Yul.Views
