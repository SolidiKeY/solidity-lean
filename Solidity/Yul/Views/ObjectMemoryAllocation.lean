import Solidity.Yul.Views.AllocatedPhysicalMemory

namespace Solidity.Yul.Views

/-- The actual owner state after allocation, shared by success AND its genuine
nonmemory-type halt. This aliases the existing typed state, not a second state. -/
def objectAllocatedState {E Γ} (s : Source.EMState E Γ) {τ : Source.STy} (data : Source.Data E.layout τ) : Source.EMState E Γ :=
  withSourceHeap s (s.2.heap.alloc ⟨τ,data⟩).1

theorem objectAllocRef_run {E Γ} (s : Source.EMState E Γ) {τ : Source.STy} (data : Source.Data E.layout τ)
    (memory : τ.loc?=some .memory) :
    (Source.allocRef data).run s=(.ok (Source.Val.memRef memory s.2.heap.next),objectAllocatedState s data) := by
  unfold Source.allocRef Source.alloc
  simp only [Source.Hoare.run_bind,dif_pos memory]
  rfl

theorem objectAllocRef_halt {E Γ} (s : Source.EMState E Γ) {τ : Source.STy} (data : Source.Data E.layout τ)
    (notMemory : τ.loc?≠some .memory) :
    (Source.allocRef data).run s=(.error (.stuck "memory reference type"),objectAllocatedState s data) := by
  unfold Source.allocRef Source.alloc
  simp only [Source.Hoare.run_bind,dif_neg notMemory]
  rfl

theorem objectAllocRef_MemOK {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) {τ : Source.STy}
    (data : Source.Data E.layout τ) (memory : τ.loc?=some .memory)
    (top : Source.Data.Top (E := E) data) (inner : Source.Data.Inner (E := E) data)
    (valid : Source.DataOK E s.2.heap.ty data) (ok : Source.MemOK E H s) :
    Source.MemOK E H (objectAllocatedState s data) ∧
      (Source.Val.memRef memory s.2.heap.next).RefOK E (objectAllocatedState s data).2.heap.ty := by
  have safe := Source.allocRef_mem (H := H) (Γ := Γ) data memory top inner s ⟨ok,valid⟩
  rw [objectAllocRef_run s data memory] at safe
  exact safe

/-- Checked ordinary MEMORY object allocation encoder. The image is computed
from actual typed contents and actual allocated lookup. None is unsupported
physical preparation, never a source/Yul verdict or successful no-op. -/
def objectAllocationView {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (_memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val) (m : ByteView) : Option ByteView :=
  let q := heapAllocPlacement h p data shape shaped base free after fresh fits
  (prepareHeapImage q h.next τ data (Source.Heap.alloc_get h _)).map
    (fun image => image.encode (mstore m 64 free) base)

/-- Completeness comes from actual OLD-heap value ownership, declared member
support and actual Inner. No image/inverse/desired raw view is supplied. -/
theorem objectAllocationView_complete {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h) {τ : Source.STy}
    (data : Source.Data E.layout τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val) (m : ByteView)
    (supported : InventoryTypeSupported E τ) (inner : Source.Data.Inner (E := E) data)
    (valid : Source.DataOK E h.ty data) :
    (objectAllocationView h p data memory shape shaped base free after fresh fits m).isSome := by
  unfold objectAllocationView
  rw [Option.isSome_map]
  exact prepareHeapImage_supported _ _ _ _ (Source.Heap.alloc_get h _) supported inner
    (Source.DataOK.mono (Source.Heap.alloc_le h ⟨τ,data⟩) valid)

/-- Existing byte/string interfaces keep their exact encoder and guard behavior. -/
theorem objectAllocationView_bytes {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val) (m : ByteView) :
    objectAllocationView h p (heapByteData D string bs) (heapByteType_memory string) (.bytes bs.length)
      (heapByteData_shape D string bs) base free after fresh fits m=some (byteAllocationView bs base free fits m) := by
  cases string <;> rfl

end Solidity.Yul.Views
