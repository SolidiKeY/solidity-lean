import Solidity.Yul.Views.StructWordRetained

/-! Actual memory-byte location writes and their one-byte physical patch.
The source object retains its bytes/string type and exact length; existing
codecs and placement bounds provide the header and whole payload agreement. -/
namespace Solidity.Yul.Views.ByteElementStore

theorem payload (bytes : List UInt8) (index : Fin bytes.length) (value : UInt8)
    (memory : ByteView) (base : Nat) (reads : readBytes memory base bytes.length=bytes) :
    readBytes (saveByte memory (base+index.val) value) base bytes.length=bytes.set index.val value := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range,List.length_set]
  · intro i hi hj
    simp only [readBytes,List.getElem_map,List.getElem_range,List.getElem_set]
    by_cases same : index.val=i
    · subst i
      rw [if_pos rfl,find_saveByte]
    · rw [if_neg same,find_saveByte_other _ _ (by omega)]
      have observed :=  congrArg (fun bs => bs[i]?) reads
      have bound : i<bytes.length := by simpa only [List.length_set] using hj
      have eq : some (memory (base+i))=some bytes[i] := by
        simpa only [readBytes,List.getElem?_map,List.getElem?_range bound,Option.map_some,
          List.getElem?_eq_getElem bound] using observed
      exact Option.some.inj eq

theorem header (memory : ByteView) (base index : Nat) (value : UInt8) :
    mload (saveByte memory (base+32+index) value) base=mload memory base := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply mload_congr
  intro byte
  apply find_saveByte_other
  have small := byte.isLt
  omega

theorem source {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat)
    (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) :
    (Source.writeLoc F horizon (.memByte root index.val)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)).run s=
    (Source.heapPut root ⟨heapByteType string,heapByteData E.layout string (bytes.set index.val value)⟩).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases string <;> rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s root _ found]
  all_goals
    dsimp only [heapByteType,heapByteData]
    rw [if_pos index.isLt]
    rfl

/-- The original placement choices remain valid after the actual byte write. -/
def placement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat)
    (string : Bool) (bytes : List UInt8)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) :
    Placement (h.write root (heapByteData D string (bytes.set index.val value)) (heap_ty_of_get h root _ _ found)) :=
  heapWritePlacement h p root _ _ (by
    rw [heapByte_placement_shape h p root string bytes found]
    have shape := heapByteData_shape D string (bytes.set index.val value)
    simpa only [List.length_set] using shape)

theorem source_run {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat)
    (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) :
    (Source.writeLoc F horizon (.memByte root index.val)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)).run s=
    (.ok (),withSourceHeap s (s.2.heap.write root (heapByteData E.layout string (bytes.set index.val value))
      (heap_ty_of_get _ _ _ _ found))) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [source s F horizon root string bytes found index value]
  exact heapPutConcrete_run s root _ (heap_ty_of_get _ _ _ _ found)

/-- All objects read the actual patched map after the checked byte write. -/
theorem reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (string : Bool) (bytes : List UInt8)
    (found : h.get root=some ⟨heapByteType string,heapByteData D string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) (memory : ByteView)
    (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (e : MixedHeapEntry (placement h p root string bytes found index value)) :
    e.image.Reads (saveByte memory (p.address root+32+index.val) value)
      ((placement h p root string bytes found index value).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let ht := heap_ty_of_get h root _ _ found
  let q := placement h p root string bytes found index value
  let patch := saveByte memory (p.address root+32+index.val) value
  have bound := heapByte_length_bound h p root string bytes found
  let oldImage : MemoryImage p (heapByteData D string bytes) := by
    cases string
    · exact .bytes bytes bound
    · exact .string bytes bound
  have initial := mixedImage_reads_of_coverage p es coverage memory oldReads
    (⟨root,_,_,found,oldImage⟩ : MixedHeapEntry p)
  have parts : (mload memory (p.address root)).val=bytes.length ∧
      readBytes memory (p.address root+32) bytes.length=bytes := by cases string <;> exact initial
  have nextBound : (bytes.set index.val value).length<2^256 := by simpa only [List.length_set] using bound
  let image : MemoryImage q (heapByteData D string (bytes.set index.val value)) := by
    cases string
    · exact .bytes _ nextBound
    · exact .string _ nextBound
  have newReads : image.Reads patch (p.address root) := by
    have head := congrArg Fin.val (header memory (p.address root) index.val value)
    have tail := payload bytes index value memory (p.address root+32) parts.2
    cases string <;> exact ⟨by simpa only [List.length_set] using head.trans parts.1,
      by simpa only [List.length_set] using tail⟩
  have newFound : (h.write root (heapByteData D string (bytes.set index.val value)) ht).get root=
      some ⟨_,heapByteData D string (bytes.set index.val value)⟩ := Source.Heap.write_get h root _ ht
  rcases e with ⟨a,σ,data,eFound,eImage⟩
  by_cases same : a=root
  · subst a
    have dataEq := Option.some.inj (newFound.symm.trans eFound)
    cases dataEq
    exact (image.reads_unique eImage patch (p.address root)).mp newReads
  · have oldFound : h.get a=some ⟨σ,data⟩ := by
      rw [←Source.Heap.write_other h same (heapByteData D string (bytes.set index.val value)) ht]
      exact eFound
    have extension : ∀ a σ,(h.write root (heapByteData D string (bytes.set index.val value)) ht).ty a=some σ →
        h.ty a=some σ ∧ p.address a=q.address a := by
      intro a σ owned
      rw [Source.Heap.write_ty] at owned
      exact ⟨owned,rfl⟩
    have oldImageReads := mixedImage_reads_of_coverage p es coverage memory oldReads
      (⟨a,σ,data,oldFound,eImage.forward p extension⟩ : MixedHeapEntry p)
    have unchanged : eImage.Reads memory (q.address a) :=
      (eImage.forward_reads p extension memory _).mp oldImageReads
    have rootPresent : (h.cells root).isSome := by change (h.get root).isSome=true;rw [found];rfl
    have present : (h.cells a).isSome := by change (h.get a).isSome=true;rw [oldFound];rfl
    have separate := p.separate root a rootPresent present (Ne.symm same)
    have fit := eImage.fits q a eFound
    change eImage.span≤(p.shape a).size at fit
    have extent := byte_shape_live_bound bytes.length
    rw [←heapByte_placement_shape h p root string bytes found] at extent
    apply eImage.reads_congr patch memory (q.address a) _ unchanged
    intro byte small
    change saveByte memory (p.address root+32+index.val) value (p.address a+byte)=memory (p.address a+byte)
    apply find_saveByte_other
    have inside := index.isLt
    rcases separate with before | after <;> omega

/-- Actual source success, complete map reconstruction, and unchanged whole
Source writeback use the original supplied allocation lineage. -/
theorem whole {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (value : UInt8) (memory : ByteView)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let ht := heap_ty_of_get s.2.heap root _ _ found
    let data := heapByteData E.layout string (bytes.set index.val value)
    let after := withSourceHeap s (s.2.heap.write root data ht)
    let q := placement s.2.heap p root string bytes found index value
    let patch := saveByte memory (p.address root+32+index.val) value
    (Source.writeLoc F horizon (.memByte root index.val)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [value] rfl)).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback after allocated q history patch=.ok (some (.ok (),after)) ∧
        ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let data := heapByteData E.layout string (bytes.set index.val value)
  let after := withSourceHeap s (s.2.heap.write root data ht)
  let q := placement s.2.heap p root string bytes found index value
  let patch := saveByte memory (p.address root+32+index.val) value
  have safe := heapByte_write_MemOK E H s root string (bytes.set index.val value) ht ok
  have nextSupport : ∀ a σ d,after.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
    intro a σ d actual
    change (s.2.heap.write root data ht).get a=some ⟨σ,d⟩ at actual
    by_cases same : a=root
    · subst a
      rw [Source.Heap.write_get] at actual
      cases actual
      cases string <;> trivial
    · rw [Source.Heap.write_other s.2.heap same] at actual
      exact supported a σ d actual
  have coverage := (prepareHeapInventory_ok p _ (ownerMemOK_prepares_inventory H s p ok supported)).2.1
  have wholeMap : encodeMixedHeap q (generatedHeapEntries q) patch=patch :=
    encodeMixedHeap_unchanged q _ patch (fun e _ => reads s.2.heap p _ coverage root string bytes found
      index value memory oldReads e)
  have shape : HasMemoryShape data (p.shape root) := by
    rw [heapByte_placement_shape s.2.heap p root string bytes found]
    simpa only [List.length_set] using heapByteData_shape E.layout string (bytes.set index.val value)
  have history : RetainedAllocation allocated q := retainSameShapeWrite allocated p prior root data ht shape
  have ready := ownerMemOK_prepares_inventory H after q safe nextSupport
  have writeback := enumeratedMemory_unchanged after allocated q history patch nextSupport _ ready
  rw [wholeMap] at writeback
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have start := p.starts root present
  have validReserved : ReservedOK patch q.free := by
    constructor
    · exact (congrArg Fin.val (mload_congr patch memory 64 (fun byte =>
        find_saveByte_other _ _ (by have small:=byte.isLt;omega)))).trans reserved.1
    · intro byte
      change saveByte memory _ value (96+byte.val)=0
      rw [find_saveByte_other _ _ (by have small:=byte.isLt;omega)]
      exact reserved.2 byte
  exact ⟨source_run s F horizon root string bytes found index value,safe,wholeMap,history,writeback,validReserved⟩
end Solidity.Yul.Views.ByteElementStore
