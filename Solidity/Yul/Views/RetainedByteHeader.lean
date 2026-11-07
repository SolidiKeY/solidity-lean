import Solidity.Yul.Views.RetainedArrayHeader

/-! Bytes/string header changes decode their payload from the same complete
input map. Retained origin capacity justifies resized ownership; all refreshed
heap reads and whole Source writeback are derived, including dormant bytes. -/
namespace Solidity.Yul.Views.RetainedByteHeader

theorem payload (memory : ByteView) (base : Nat) (length : Roadmap.Word) :
    readBytes (mstore memory base length) (base+32) length.val=readBytes memory (base+32) length.val := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply readBytes_congr_on
  intro i _
  apply mstore_outside
  omega

theorem decoded (D : Source.Layout) (string : Bool) (memory : ByteView) (base : Nat) (length : Roadmap.Word) :
    decodeHeapByte D string (mstore memory base length) base=
      heapByteData D string (readBytes memory (base+32) length.val) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [decodeHeapByte_data,mload_mstore,payload]

theorem shape (D : Source.Layout) (string : Bool) (memory : ByteView) (base : Nat) (length : Roadmap.Word) :
    HasMemoryShape (heapByteData D string (readBytes memory (base+32) length.val)) (.bytes length.val) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have actual := heapByteData_shape D string (readBytes memory (base+32) length.val)
  simpa only [readBytes,List.length_map,List.length_range] using actual

def placement {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (root : Nat) (string : Bool) (old : List UInt8)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string old⟩)
    (memory : ByteView) (length : Roadmap.Word)
    (capacity : (MemoryShape.bytes length.val).size≤(allocated.shape root).size) :=
  retainedWritePlacement allocated p prior root
    (heapByteData D string (readBytes memory (p.address root+32) length.val))
    (heap_ty_of_get h root _ _ found) (.bytes length.val) (shape D string memory (p.address root) length) capacity

theorem history {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (root : Nat) (string : Bool) (old : List UInt8)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string old⟩)
    (memory : ByteView) (length : Roadmap.Word)
    (capacity : (MemoryShape.bytes length.val).size≤(allocated.shape root).size) :
    RetainedAllocation allocated (placement h allocated p prior root string old found memory length capacity) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact retainWritten allocated p prior root _ _ (.bytes length.val) (shape D string memory (p.address root) length) capacity

theorem reads {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (string : Bool) (old : List UInt8)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string old⟩)
    (memory : ByteView) (length : Roadmap.Word)
    (capacity : (MemoryShape.bytes length.val).size≤(allocated.shape root).size)
    (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (e : MixedHeapEntry (placement h allocated p prior root string old found memory length capacity)) :
    e.image.Reads (mstore memory (p.address root) length)
      ((placement h allocated p prior root string old found memory length capacity).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let bytes := readBytes memory (p.address root+32) length.val
  let data := heapByteData D string bytes
  let ht := heap_ty_of_get h root _ _ found
  let q := placement h allocated p prior root string old found memory length capacity
  let patch := mstore memory (p.address root) length
  have size : bytes.length=length.val := by simp only [bytes,readBytes,List.length_map,List.length_range]
  have bound : bytes.length<2^256 := by rw [size];exact length.isLt
  let image : MemoryImage q data := by
    cases string
    · exact .bytes bytes bound
    · exact .string bytes bound
  have newReads : image.Reads patch (p.address root) := by
    have header : (mload patch (p.address root)).val=bytes.length :=
      (congrArg Fin.val (mload_mstore memory (p.address root) length)).trans size.symm
    have tail : readBytes patch (p.address root+32) bytes.length=bytes := by
      rw [size]
      exact payload memory (p.address root) length
    cases string <;> exact ⟨header,tail⟩
  have newFound : (h.write root data ht).get root=some ⟨_,data⟩ := Source.Heap.write_get h root _ ht
  rcases e with ⟨a,σ,d,eFound,eImage⟩
  by_cases same : a=root
  · subst a
    have dataEq := Option.some.inj (newFound.symm.trans eFound)
    cases dataEq
    exact (image.reads_unique eImage patch (p.address root)).mp newReads
  · have oldFound : h.get a=some ⟨σ,d⟩ := by
      rw [←Source.Heap.write_other h same data ht]
      exact eFound
    have extension : ∀ a σ,(h.write root data ht).ty a=some σ → h.ty a=some σ ∧ p.address a=q.address a := by
      intro a σ owned
      rw [Source.Heap.write_ty] at owned
      exact ⟨owned,rfl⟩
    have oldImageReads := mixedImage_reads_of_coverage p es coverage memory oldReads
      (⟨a,σ,d,oldFound,eImage.forward p extension⟩ : MixedHeapEntry p)
    have unchanged : eImage.Reads memory (q.address a) := (eImage.forward_reads p extension memory _).mp oldImageReads
    have rootPresent : (h.cells root).isSome := by change (h.get root).isSome=true;rw [found];rfl
    have present : (h.cells a).isSome := by change (h.get a).isSome=true;rw [oldFound];rfl
    have separate := p.separate root a rootPresent present (Ne.symm same)
    have fit := eImage.fits q a eFound
    have otherShape : q.shape a=p.shape a := by
      change (if a=root then MemoryShape.bytes length.val else p.shape a)=p.shape a
      rw [if_neg same]
    rw [otherShape] at fit
    have headerFits : 32≤(p.shape root).size := by
      have live := byte_shape_live_bound old.length
      rw [←heapByte_placement_shape h p root string old found] at live
      omega
    apply eImage.reads_congr patch memory (q.address a) _ unchanged
    intro byte small
    change mstore memory (p.address root) length (p.address a+byte)=memory (p.address a+byte)
    apply mstore_outside
    rcases separate with before | after <;> omega

theorem whole {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (root : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (memory : ByteView) (length : Roadmap.Word)
    (capacity : (MemoryShape.bytes length.val).size≤(allocated.shape root).size)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id)) (reserved : ReservedOK memory p.free) :
    let data := heapByteData E.layout string (readBytes memory (p.address root+32) length.val)
    let out : Source.EMState E Γ := withSourceHeap s (s.2.heap.write root data (heap_ty_of_get s.2.heap root _ _ found))
    let q : Placement out.2.heap := placement s.2.heap allocated p prior root string old found memory length capacity
    let lineage := history s.2.heap allocated p prior root string old found memory length capacity
    let patch := mstore memory (p.address root) length
    retainedByteStateWriteback s allocated p prior root string old found patch=some out ∧
      (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) ∧ Source.MemOK E H out ∧ q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback out allocated q lineage patch=.ok (some (.ok (),out)) ∧ ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let bytes := readBytes memory (p.address root+32) length.val
  let data := heapByteData E.layout string bytes
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let out := withSourceHeap s (s.2.heap.write root data ht)
  let q := placement s.2.heap allocated p prior root string old found memory length capacity
  let lineage := history s.2.heap allocated p prior root string old found memory length capacity
  let patch := mstore memory (p.address root) length
  have prepare : retainedByteStateWriteback s allocated p prior root string old found patch=some out := by
    unfold retainedByteStateWriteback retainedByteWriteback
    rw [show mload patch (p.address root)=length from mload_mstore _ _ _,if_pos capacity,decoded]
    rfl
  have sourceRun : (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) := heapPutConcrete_run s root data ht
  have safe := heapByte_write_MemOK E H s root string bytes ht ok
  have support := heapWrite_inventory_supported s.2.heap root data ht supported
  have ready := ownerMemOK_prepares_inventory H s p ok supported
  have coverage := (prepareHeapInventory_ok p _ ready).2.1
  have nextReady := ownerMemOK_prepares_inventory H out q safe support
  have full : encodeMixedHeap q (generatedHeapEntries q) patch=patch :=
    encodeMixedHeap_unchanged q _ patch (fun e _ => reads s.2.heap allocated p prior _ coverage root string old found memory length capacity oldReads e)
  have wb := enumeratedMemory_unchanged out allocated q lineage patch support _ nextReady
  rw [full] at wb
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have start := p.starts root present
  have reservedOut : ReservedOK patch q.free := by
    constructor
    · exact (congrArg Fin.val (mload_congr patch memory 64 (fun byte =>
        mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)))).trans reserved.1
    · intro byte
      change mstore memory _ length (96+byte.val)=0
      rw [mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)]
      exact reserved.2 byte
  exact ⟨prepare,sourceRun,safe,rfl,rfl,full,wb,reservedOut⟩
end Solidity.Yul.Views.RetainedByteHeader
