import Solidity.Yul.Views.ReferenceDeleteRetained

/-! Whole-heap refresh after a checked retained dynamic-array header patch.
Canonical words are read from the same complete raw map, including dormant
payload. This is preparation/heapPut transport, not new source length syntax. -/
namespace Solidity.Yul.Views.RetainedArrayHeader

theorem payload (memory : ByteView) (base : Nat) (length : Roadmap.Word)
    (words : Fin length.val → Roadmap.Word)
    (reads : ∀ i,mload memory (base+32+i.val*32)=words i) :
    ∀ i,mload (mstore memory base length) (base+32+i.val*32)=words i := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro i
  rw [mload_congr _ memory _ (fun byte => mstore_outside _ _ _ _ (by have small:=byte.isLt;omega))]
  exact reads i

theorem reencode (memory : ByteView) (base : Nat) (length : Roadmap.Word)
    (words : Fin length.val → Roadmap.Word)
    (reads : ∀ i,mload memory (base+32+i.val*32)=words i) :
    let patch := mstore memory base length
    dynamicUintView length.val length.isLt words patch base=patch := by
  first | (simp only;done) | decide | omega | rfl | skip
  let patch := mstore memory base length
  have tail : (fun i : Fin length.val => mload patch (base+32+i.val*32))=words :=
    funext (payload memory base length words reads)
  have raw := decodeDynamicUint_reencode patch base
  rw [show mload patch base=length from mload_mstore _ _ _] at raw
  rw [tail] at raw
  exact raw

theorem reads {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root=some ⟨_,dynamicMemberData D τ n old⟩)
    (length : Roadmap.Word) (values : Fin length.val → Source.Val D τ) (words : Fin length.val → Roadmap.Word)
    (encoded : ∀ i,MemoryElement p (values i) (words i))
    (capacity : (MemoryShape.array true length.val).size≤(allocated.shape root).size)
    (memory : ByteView) (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (tail : ∀ i,mload memory (p.address root+32+i.val*32)=words i)
    (e : MixedHeapEntry (retainedMemberArrayPlacement allocated p prior root τ n old found length.val values capacity)) :
    e.image.Reads (mstore memory (p.address root) length)
      ((retainedMemberArrayPlacement allocated p prior root τ n old found length.val values capacity).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let ht := heap_ty_of_get h root _ _ found
  let q := retainedMemberArrayPlacement allocated p prior root τ n old found length.val values capacity
  let patch := mstore memory (p.address root) length
  have types : (h.write root (dynamicMemberData D τ length.val values) ht).ty=h.ty :=
    funext (fun a => Source.Heap.write_ty h root a _ ht)
  have nextEncoded : ∀ i,MemoryElement q (values i) (words i) := fun i => (encoded i).transport q types rfl
  have newFound : (h.write root (dynamicMemberData D τ length.val values) ht).get root=
      some ⟨_,dynamicMemberData D τ length.val values⟩ := Source.Heap.write_get h root _ ht
  let image := memoryArrayImage q root (n:=none) length.val (fun _ eq => nomatch eq) values words nextEncoded newFound
  have imageEq : image.encode patch (p.address root)=dynamicUintView length.val length.isLt words patch (p.address root) := rfl
  have newReads := image.encode_reads patch (p.address root)
  rw [imageEq,reencode memory (p.address root) length words tail] at newReads
  rcases e with ⟨a,σ,data,eFound,eImage⟩
  by_cases same : a=root
  · subst a
    have dataEq := Option.some.inj (newFound.symm.trans eFound)
    cases dataEq
    exact (image.reads_unique eImage patch (p.address root)).mp newReads
  · have oldFound : h.get a=some ⟨σ,data⟩ := by
      rw [←Source.Heap.write_other h same (dynamicMemberData D τ length.val values) ht]
      exact eFound
    have extension : ∀ a σ,(h.write root (dynamicMemberData D τ length.val values) ht).ty a=some σ →
        h.ty a=some σ ∧ p.address a=q.address a := by
      intro a σ owned
      rw [types] at owned
      exact ⟨owned,rfl⟩
    have oldImageReads := mixedImage_reads_of_coverage p es coverage memory oldReads
      (⟨a,σ,data,oldFound,eImage.forward p extension⟩ : MixedHeapEntry p)
    have unchanged : eImage.Reads memory (q.address a) :=
      (eImage.forward_reads p extension memory _).mp oldImageReads
    have rootPresent : (h.cells root).isSome := by change (h.get root).isSome=true;rw [found];rfl
    have present : (h.cells a).isSome := by change (h.get a).isSome=true;rw [oldFound];rfl
    have separate := p.separate root a rootPresent present (Ne.symm same)
    have fit := eImage.fits q a eFound
    have shapeOther : q.shape a=p.shape a := by
      change (if a=root then MemoryShape.array true length.val else p.shape a)=p.shape a
      rw [if_neg same]
    rw [shapeOther] at fit
    have headerFits : 32≤(p.shape root).size := by
      rw [memberArray_shape h p root τ none n (fun _ eq => nomatch eq) old found]
      change 32≤32+n*32
      omega
    apply eImage.reads_congr patch memory (q.address a) _ unchanged
    intro byte small
    change mstore memory (p.address root) length (p.address a+byte)=memory (p.address a+byte)
    apply mstore_outside
    rcases separate with before | after <;> omega

/-- Complete Source preparation and whole-map/writeback transport are derived
for any checked length within the genuine retained original allocation. -/
theorem whole {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (root : Nat) (τ : Source.STy) (elementType : ExtendedMemberType E.layout τ)
    (n : Nat) (old : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get root=some ⟨_,dynamicMemberData E.layout τ n old⟩)
    (length : Roadmap.Word) (values : Fin length.val → Source.Val E.layout τ) (words : Fin length.val → Roadmap.Word)
    (encoded : ∀ i,MemoryElement p (values i) (words i))
    (capacity : (MemoryShape.array true length.val).size≤(allocated.shape root).size)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (tail : ∀ i,mload memory (p.address root+32+i.val*32)=words i) (reserved : ReservedOK memory p.free) :
    let data := dynamicMemberData E.layout τ length.val values
    let out : Source.EMState E Γ := withSourceHeap s (s.2.heap.write root data (heap_ty_of_get s.2.heap root _ _ found))
    let q : Placement out.2.heap := retainedMemberArrayPlacement (h:=s.2.heap) allocated p prior root τ n old found length.val values capacity
    let history := retainedMemberArray_history allocated p prior root τ n old found length.val values capacity
    let patch := mstore memory (p.address root) length
    canonicalRetainedState s allocated p prior (generatedHeapEntries p) root τ patch=some (.ok (),out) ∧
      (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) ∧ Source.MemOK E H out ∧
      q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback out allocated q history patch=.ok (some (.ok (),out)) ∧ ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let data := dynamicMemberData E.layout τ length.val values
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let out := withSourceHeap s (s.2.heap.write root data ht)
  let q := retainedMemberArrayPlacement allocated p prior root τ n old found length.val values capacity
  let history := retainedMemberArray_history allocated p prior root τ n old found length.val values capacity
  let patch := mstore memory (p.address root) length
  have ready := ownerMemOK_prepares_inventory H s p ok supported
  have coverage := (prepareHeapInventory_ok p _ ready).2.1
  have decoded := decodeCanonicalArray_reads p _ coverage τ elementType length.val values words encoded patch
    (p.address root+32) (payload memory (p.address root) length words tail)
  have sourceRun : (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) :=
    memberArrayHeapPut_run s root τ none length.val (fun _ eq => nomatch eq) values ht
  have prepared : canonicalRetainedState s allocated p prior (generatedHeapEntries p) root τ patch=some (.ok (),out) := by
    unfold canonicalRetainedState
    rw [show mload patch (p.address root)=length from mload_mstore _ _ _,if_pos capacity,decoded]
    exact congrArg some sourceRun
  have safe : Source.MemOK E H out := canonicalRetainedState_MemOK E H s allocated p prior _ root τ patch (.ok (),out) prepared ok
  have nextSupport := heapWrite_inventory_supported s.2.heap root data ht supported
  have newReady := ownerMemOK_prepares_inventory H out q safe nextSupport
  have full : encodeMixedHeap q (generatedHeapEntries q) patch=patch :=
    encodeMixedHeap_unchanged q _ patch (fun e _ => reads s.2.heap allocated p prior _ coverage root τ n old found
      length values words encoded capacity memory oldReads tail e)
  have wb := enumeratedMemory_unchanged out allocated q history patch nextSupport _ newReady
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
  exact ⟨prepared,sourceRun,safe,rfl,rfl,full,wb,reservedOut⟩
end Solidity.Yul.Views.RetainedArrayHeader
