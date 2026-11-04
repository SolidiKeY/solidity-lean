import Solidity.Yul.Views.ReferenceDelete

/-! Allocating reference deletion preserves prior allocation provenance. The
origin is extended by the actual new object; old retained capacities are not
replaced by current shrunken extents. New coordinates have explicit real bounds. -/
namespace Solidity.Yul.Views.ReferenceDeleteRetained

theorem strct {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (n root : Nat) (name : Source.DeclName) (string : Bool)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length)
    (updated : fields.setNth index.val (.val (Source.Val.memRef (heapByteType_memory string) s.2.heap.next))=.ok next)
    (base free : Roadmap.Word) (after : allocated.free.val≤base.val)
    (fresh : ∀ a,(origin.cells a).isSome → allocated.address a≠base.val)
    (fits : base.val+(MemoryShape.bytes 0).size≤free.val)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let data := heapByteData E.layout string []
    let shape := heapByteData_shape E.layout string []
    let currentAfter : p.free.val≤base.val := by rw [prior.free];exact after
    let currentFresh : ∀ a,(s.2.heap.cells a).isSome → p.address a≠base.val := fun a present => by
      rw [prior.addresses];exact fresh a (by rw [←prior.occupancy a];exact present)
    let nextOrigin := heapAllocPlacement origin allocated data (.bytes 0) shape base.val free after fresh fits
    ∃ (raw : ByteView) (out : Source.EMState E Γ) (q : Placement out.2.heap),
      objectAllocationView s.2.heap p data (heapByteType_memory string) (.bytes 0) shape
        base.val free currentAfter currentFresh fits memory=some raw ∧
      q.address=(fun id => if id=s.2.heap.next then base.val else p.address id) ∧ q.free=free ∧
      (Source.deleteLoc F (n+2) (.mem (τ:=heapByteType string) root index.val)).run s=(.ok (),out) ∧
      Source.MemOK E H out ∧
      let patch := mstore raw (p.address root+index.val*32) base
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ history : RetainedAllocation nextOrigin q,
        enumeratedMemoryWriteback out nextOrigin q history patch=.ok (some (.ok (),out)) ∧ ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let data := heapByteData E.layout string []
  let shape := heapByteData_shape E.layout string []
  have newSupport : InventoryTypeSupported E (heapByteType string) := by cases string <;> trivial
  have inner : Source.Data.Inner (E:=E) data := by cases string <;> trivial
  have valid := heapByteData_OK E s.2.heap.ty string []
  have currentAfter : p.free.val≤base.val := by rw [prior.free];exact after
  have currentFresh : ∀ a,(s.2.heap.cells a).isSome → p.address a≠base.val := by
    intro a present
    rw [prior.addresses]
    exact fresh a (by rw [←prior.occupancy a];exact present)
  let state := objectAllocatedState s data
  let a := retainedAllocationPlacement allocated p prior data (.bytes 0) shape base.val free after fresh fits
  let nextOrigin := heapAllocPlacement origin allocated data (.bytes 0) shape base.val free after fresh fits
  have nextHistory := retainAllocated allocated p prior data (.bytes 0) shape base.val free after fresh fits
  obtain ⟨raw,step,allocationRun,safe,readyNew,coverage,nodup,fullAllocated,writebackAllocated,reservedAllocated⟩ :=
    retainedObjectAllocation_physical H s allocated p prior data (heapByteType_memory string) (.bytes 0) shape inner valid
      newSupport base.val free after fresh fits memory ok supported oldReads reserved
  have extension : ∀ id σ,s.2.heap.ty id=some σ → state.2.heap.ty id=some σ ∧ a.address id=p.address id :=
    heapAlloc_owned_extension s.2.heap p data (.bytes 0) shape base.val free currentAfter currentFresh fits
  have rootType := heap_ty_of_get s.2.heap root _ _ found
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have different := occupied_ne_next s.2.heap root present
  have allocatedFound : state.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩ :=
    (Source.Heap.alloc_other s.2.heap _ different).trans found
  have fieldsEncoded := encoded.forward a extension
  have childType : state.2.heap.ty s.2.heap.next=some (heapByteType string) :=
    heap_ty_of_get _ _ _ _ (Source.Heap.alloc_get s.2.heap _)
  have pointerWord : ownedPointerWord a s.2.heap.next (heapByteType string) childType=base := by
    apply Fin.ext
    change (if s.2.heap.next=s.2.heap.next then base.val else p.address s.2.heap.next)=base.val
    rw [if_pos rfl]
  have pointerEncoded : MemoryElement a (Source.Val.memRef (heapByteType_memory string) s.2.heap.next) base := by
    rw [←pointerWord]
    exact .pointer (heapByteType_memory string) _ _ childType rfl
  have ready := ownerMemOK_prepares_inventory H s p ok supported
  have allocatedReads : ∀ e∈generatedHeapEntries a,e.image.Reads raw (a.address e.id) := by
    intro e _
    exact objectAllocationView_image_reads s.2.heap p data (heapByteType_memory string) (.bytes 0) shape
      base.val free currentAfter currentFresh fits _ ready memory raw oldReads step e
  have support := heapAlloc_inventory_supported s.2.heap data newSupport supported
  have current := StructWordHeap.whole H state a safe support F (n+2) root name fields next words fieldsEncoded
    allocatedFound index (Source.Val.memRef (heapByteType_memory string) s.2.heap.next) base pointerEncoded updated
    raw allocatedReads reservedAllocated
  have retained := StructWordRetained.whole H state nextOrigin a nextHistory safe support F (n+2) root name
    fields next words fieldsEncoded allocatedFound index (Source.Val.memRef (heapByteType_memory string) s.2.heap.next)
    base pointerEncoded updated raw allocatedReads reservedAllocated
  let out := withSourceHeap state (state.2.heap.write root (.struct next) (heap_ty_of_get _ _ _ _ allocatedFound))
  let q := structWrittenPlacement state.2.heap a root name fields next allocatedFound
  have sourceRun : (Source.deleteLoc F (n+2) (.mem (τ:=heapByteType string) root index.val)).run s=(.ok (),out) := by
    rw [ReferenceDelete.source s F n root index.val string]
    exact current.1
  have sameAddress := (extension root _ rootType).2
  have full := current.2.2.2.1
  have wb := retained.2.2.2
  have reservedOut := current.2.2.2.2.2
  rw [sameAddress] at full wb reservedOut
  exact ⟨raw,out,q,step,rfl,rfl,sourceRun,current.2.1,full,
    StructWordRetained.history state.2.heap nextOrigin a nextHistory root name fields next allocatedFound,wb,reservedOut⟩
end Solidity.Yul.Views.ReferenceDeleteRetained
