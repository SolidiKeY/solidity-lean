import Solidity.Yul.Views.AbiUintArrayRun
import Solidity.Yul.Views.AllocatedObjectMemory

namespace Solidity.Yul.Views

def abiUintArrayShape (D : Source.Layout) (input : Roadmap.Bytes) (head : Nat) : MemoryShape :=
  .array true (abiUintValues D (abiArrayPayload input head) (abiArrayLength input head)).length

/-- Complete supported calldata-array producer connection: actual input
checks/decoded values/source result, every-original-H MemOK, computed output
inventory, whole raw reencoding, retained original allocation history and
exact unchanged writeback. Existing initial-view/geometry premises are real. -/
theorem abiUintArray_physical {E Γ} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (input : Roadmap.Bytes) (head : Nat)
    (header : abiArrayOffset input head+32≤input.length) (small : abiArrayLength input head<2^64)
    (payload : abiArrayOffset input head+32+32*abiArrayLength input head≤input.length)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+(abiUintArrayShape E.layout input head).size≤free.val)
    (m : ByteView) (ok : Source.MemOK E H s)
    (supportedOld : ∀ a σ d, s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (reads : ∀ e ∈ generatedHeapEntries p, e.image.Reads m (p.address e.id)) (reserved : ReservedOK m p.free) :
    let data := abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head)
    let shape := abiUintArrayShape E.layout input head
    let shaped : HasMemoryShape data shape := abiUintArrayData_shape _ _ _
    let currentAfter : p.free.val≤base := by rw [history.free]; exact after
    let currentFresh : ∀ a, (s.2.heap.cells a).isSome → p.address a≠base := fun a present => by
      rw [history.addresses]; exact fresh a (by rw [← history.occupancy a]; exact present)
    let q := retainedAllocationPlacement (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
    let nextOrigin := heapAllocPlacement origin allocated data shape shaped base free after fresh fits
    let nextHistory := retainAllocated (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
    let nextState := objectAllocatedState s data
    ∃ raw, objectAllocationView s.2.heap p data rfl shape shaped base free currentAfter currentFresh fits m=some raw ∧
      (Source.decodeArg input head (.array .memory (.int Source.IntTy.u256) none)).run s=
        (.ok (Source.Val.memRef rfl s.2.heap.next),nextState) ∧
      Source.MemOK E H nextState ∧ prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
      CoversMixedHeap (generatedHeapEntries q) ∧ ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      enumeratedMemoryWriteback nextState nextOrigin q nextHistory raw=.ok (some (.ok (),nextState)) ∧ ReservedOK raw free := by
  dsimp only
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,spare⟩ := retainedObjectAllocation_physical H s
    allocated p history (abiUintArrayData E.layout (abiArrayPayload input head) (abiArrayLength input head)) rfl
    (abiUintArrayShape E.layout input head) (abiUintArrayData_shape _ _ _)
    (abiUintArrayData_inner (E := E) _ _) (abiUintArrayData_valid E s.2.heap.ty _ _) (Or.inr True.intro)
    base free after fresh fits m ok supportedOld reads reserved
  exact ⟨raw,step,abiUintArray_run s input head header small payload,safe,ready,covers,distinct,same,source,spare⟩

end Solidity.Yul.Views
