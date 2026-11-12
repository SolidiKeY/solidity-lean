import Solidity.Yul.Adapters.P6CopyPreparation

/-! Exact actions of prepared owned updates and unchanged siblings. These reuse
actual Source.heapPut/Heap.write; data equality is an intrinsic decoded payload
fact, not an assumed Source-run or physical-adequacy law. -/
namespace Solidity.Yul.Adapters.P6CopySource
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory

/-- Preparing an entry preserves its identity; exact dependent decoded data
therefore identifies the real Source action, in any current caller state. -/
theorem update_action {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (entry : MixedHeapEntry p) (m : ByteView) (u : OwnedInventoryUpdate allocated p)
    (prepared : update allocated p es entry m=some u)
    (data : Source.Data E.layout entry.ty) (same : HEq u.object.data data)
    (s : Source.EMState E Γ) :
    (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s=
      (Source.heapPut entry.id ⟨entry.ty,data⟩ : Source.EM E Γ Unit).run s := by
  have identity := update_entry allocated p es entry m u prepared
  cases u with
  | mk e object fits =>
    dsimp only at identity same ⊢
    subst entry
    rw [eq_of_heq same]

/-- A physically decoded sibling equal to its actual current Source cell makes
no administrative write change. None versus explicit cells is not normalized. -/
theorem unchanged_action {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (u : OwnedInventoryUpdate allocated p)
    (s : Source.EMState E Γ)
    (found : s.2.heap.get u.entry.id=some ⟨u.entry.ty,u.object.data⟩) :
    (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s=(.ok (),s) := by
  rw [heapPutConcrete_run s _ _ (heap_ty_of_get s.2.heap _ _ _ found),
    heap_write_unchanged s.2.heap _ _ _ found,withSourceHeap_unchanged]

end Solidity.Yul.Adapters.P6CopySource
