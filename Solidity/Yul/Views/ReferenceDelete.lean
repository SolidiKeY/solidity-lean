import Solidity.Yul.Views.MemoryDelete

/-! Actual bytes/string reference deletion allocates its empty default before
writing the new pointer. One incremental allocation map feeds the field store;
old and new image reads are derived rather than assumed final agreements. -/
namespace Solidity.Yul.Views.ReferenceDelete

theorem source {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (n root index : Nat) (string : Bool) :
    (Source.deleteLoc F (n+2) (.mem (τ:=heapByteType string) root index)).run s=
    (Source.writeLoc F (n+2) (.mem root index)
      (Source.Val.memRef (heapByteType_memory string) s.2.heap.next)).run
      (objectAllocatedState s (heapByteData E.layout string [])) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases string <;> rfl

/-- Construct allocation, updated pointer encoding and whole-map/Source
writeback for the actual reference deletion, without a supplied final view. -/
theorem strct {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (done : ComputedPlacement.prepare s.2.heap=.ok p) (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (n root : Nat) (name : Source.DeclName) (string : Bool)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length)
    (updated : fields.setNth index.val (.val (Source.Val.memRef (heapByteType_memory string) s.2.heap.next))=.ok next)
    (bound : p.free.val+max 1 (MemoryShape.bytes 0).size<2^256)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    ∃ (raw : ByteView) (after : Source.EMState E Γ) (q : Placement after.2.heap),
      ComputedAllocationWrite.prepare s.2.heap p done (heapByteData E.layout string []) (.bytes 0)
        (by cases string <;> rfl) bound memory=some raw ∧
      q.address=(fun id => if id=s.2.heap.next then p.free.val else p.address id) ∧
      q.free.val=p.free.val+max 1 (MemoryShape.bytes 0).size ∧
      (Source.deleteLoc F (n+2) (.mem (τ:=heapByteType string) root index.val)).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧
      let patch := mstore raw (p.address root+index.val*32) p.free
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ allocated : Placement (objectAllocatedState s (heapByteData E.layout string [])).2.heap,
        ∃ history : RetainedAllocation allocated q,
          enumeratedMemoryWriteback after allocated q history patch=.ok (some (.ok (),after)) ∧
          ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  let data := heapByteData E.layout string []
  have shape : ComputedPlacement.objectShape data=some (.bytes 0) := by cases string <;> rfl
  have newSupport : InventoryTypeSupported E (heapByteType string) := by cases string <;> trivial
  have inner : Source.Data.Inner (E:=E) data := by cases string <;> trivial
  have valid := heapByteData_OK E s.2.heap.ty string []
  obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
    (ComputedAllocationWrite.complete s.2.heap p done data (.bytes 0) shape bound memory newSupport inner valid)
  let allocated := objectAllocatedState s data
  let a := ComputedAllocationWrite.placement s.2.heap p done data (.bytes 0) shape bound
  have ready := ownerMemOK_prepares_inventory H s p ok supported
  have allocation := ComputedAllocationWrite.sound H s p done data (.bytes 0) shape bound memory raw step
    ok inner valid newSupport supported oldReads
  have safe : Source.MemOK E H allocated := allocation.2.1
  have extension : ∀ id σ,s.2.heap.ty id=some σ → allocated.2.heap.ty id=some σ ∧ a.address id=p.address id :=
    heapAlloc_owned_extension s.2.heap p data (.bytes 0) (ComputedPlacement.objectShape_sound data _ shape)
      p.free.val (ComputedAllocationWrite.nextFree p (.bytes 0) bound) (Nat.le_refl _)
      (ComputedAllocationWrite.computed_fresh s.2.heap p done) (by dsimp [ComputedAllocationWrite.nextFree];omega)
  have rootType := heap_ty_of_get s.2.heap root _ _ found
  have oldPresent : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have different := occupied_ne_next s.2.heap root oldPresent
  have allocatedFound : allocated.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩ :=
    (Source.Heap.alloc_other s.2.heap _ different).trans found
  have fieldsEncoded := encoded.forward a extension
  have childType : allocated.2.heap.ty s.2.heap.next=some (heapByteType string) :=
    heap_ty_of_get _ _ _ _ (Source.Heap.alloc_get s.2.heap _)
  have pointerWord : ownedPointerWord a s.2.heap.next (heapByteType string) childType=p.free := by
    apply Fin.ext
    change (if s.2.heap.next=s.2.heap.next then p.free.val else p.address s.2.heap.next)=p.free.val
    rw [if_pos rfl]
  have pointerEncoded : MemoryElement a (Source.Val.memRef (heapByteType_memory string) s.2.heap.next) p.free := by
    rw [←pointerWord]
    exact .pointer (heapByteType_memory string) _ _ childType rfl
  have allocatedReads : ∀ e∈generatedHeapEntries a,e.image.Reads raw (a.address e.id) := by
    intro e _
    exact objectAllocationView_image_reads s.2.heap p data (ComputedPlacement.objectShape_memory data _ shape)
      (.bytes 0) (ComputedPlacement.objectShape_sound data _ shape) p.free.val
      (ComputedAllocationWrite.nextFree p (.bytes 0) bound) (Nat.le_refl _)
      (ComputedAllocationWrite.computed_fresh s.2.heap p done) (by dsimp [ComputedAllocationWrite.nextFree];omega)
      _ ready memory raw oldReads step e
  have allocatedReserved : ReservedOK raw a.free := ComputedAllocationWrite.reserved s.2.heap p done data
    (.bytes 0) shape bound memory raw step reserved
  have support := heapAlloc_inventory_supported s.2.heap data newSupport supported
  have current := StructWordHeap.whole H allocated a safe support F (n+2) root name fields next words fieldsEncoded
    allocatedFound index (Source.Val.memRef (heapByteType_memory string) s.2.heap.next) p.free pointerEncoded updated
    raw allocatedReads allocatedReserved
  have retained := StructWordRetained.whole H allocated a a (retainInitial _ _) safe support F (n+2) root name
    fields next words fieldsEncoded allocatedFound index (Source.Val.memRef (heapByteType_memory string) s.2.heap.next)
    p.free pointerEncoded updated raw allocatedReads allocatedReserved
  let after := withSourceHeap allocated (allocated.2.heap.write root (.struct next) (heap_ty_of_get _ _ _ _ allocatedFound))
  let q := structWrittenPlacement allocated.2.heap a root name fields next allocatedFound
  have sourceRun : (Source.deleteLoc F (n+2) (.mem (τ:=heapByteType string) root index.val)).run s=(.ok (),after) := by
    rw [source s F n root index.val string]
    exact current.1
  have sameAddress := (extension root _ rootType).2
  have full := current.2.2.2.1
  have wb := retained.2.2.2
  have reservedAfter := current.2.2.2.2.2
  rw [sameAddress] at full wb reservedAfter
  exact ⟨raw,after,q,step,rfl,rfl,sourceRun,current.2.1,full,a,
    StructWordRetained.history allocated.2.heap a a (retainInitial _ _) root name fields next allocatedFound,wb,reservedAfter⟩
end Solidity.Yul.Views.ReferenceDelete
