import Solidity.Yul.Views.DynamicInventory
import Solidity.Yul.Views.PackedResidualCodec

namespace Solidity.Yul.Views

/-- Concrete canonical preparation for the actual length cell and every live
uint256 element path. The SAME supplied raw map supplies all complementary
bytes/unknown slots. None is unsupported preparation, not a Yul verdict. -/
def DynamicHeader.inventoryWriteback {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  packedStoreWriteback (h.inventory fixed a n) m s

theorem DynamicHeader.inventory_reencode {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) (L : Nat)
    (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lb : L ≤ 2^256) (nb : n.val ≤ L)
    (preimage : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (registered : (h.registration a).slot.val ∈ roots)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : h.inventoryWriteback fixed a n m s = some (out,residual)) :
    finiteEncode (h.inventory fixed a n) out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _
    (h.inventory_separated fixed a n L roots ps regions lb nb preimage registered) step

theorem DynamicHeader.inventory_other {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : h.inventoryWriteback fixed a n m s = some (out,residual)) (q : Source.SPath)
    (notHeader : q ≠ ⟨root,[]⟩)
    (notElement : ∀ i < n.val, q ≠ h.elementPath i) : out.cell q = s.cell q := by
  apply packedStoreWriteback_other _ _ _ _ _ step q
  intro c member
  rcases List.mem_cons.mp member with same | element
  · subst c; exact notHeader
  · obtain ⟨i,ib,rfl⟩ := (h.elements_member fixed a n c).mp element
    exact notElement i ib

/-- The raw header itself chooses the complete live element inventory for this
new snapshot. This avoids assuming a caller-supplied length agrees with it. -/
def DynamicHeader.snapshotWriteback {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (m : SlotView)
    (s : Source.Storage E.layout (E.lay a)) :=
  h.inventoryWriteback fixed a (m (h.registration a).slot) m s

theorem DynamicHeader.snapshot_reencode {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (L : Nat)
    (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lb : L ≤ 2^256) (m : SlotView) (nb : (m (h.registration a).slot).val ≤ L)
    (preimage : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (registered : (h.registration a).slot.val ∈ roots)
    (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : h.snapshotWriteback fixed a m s = some (out,residual)) :
    finiteEncode (h.inventory fixed a (m (h.registration a).slot)) out residual = some m :=
  h.inventory_reencode fixed a _ L roots ps regions lb nb preimage registered m s out residual step

end Solidity.Yul.Views
