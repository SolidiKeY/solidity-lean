import Solidity.Yul.Views.ArrayWordStore

/-! Every typed image after a same-type array word update reads the actual
patched map. The changed array uses the new codec word; all other objects use
real region separation and typed ownership transport. No final view law is an
input, and no shared-zero/interior or dirty-owned extension is asserted. -/
namespace Solidity.Yul.Views.ArrayWordHeap
open ArrayWordStore

theorem reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x,k=some x → x=n)
    (old : Fin n → Source.Val D τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : h.get root=some ⟨_,memberArrayData D τ k n hl old⟩)
    (index : Fin n) (value : Source.Val D τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (memory : ByteView) (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (e : MixedHeapEntry (memberArrayWrittenPlacement h p root τ k n hl old (replace old index value) found)) :
    e.image.Reads (mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word)
      ((memberArrayWrittenPlacement h p root τ k n hl old (replace old index value) found).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let nextValues := replace old index value
  let nextWords := replace words index word
  let ht := heap_ty_of_get h root _ _ found
  let q := memberArrayWrittenPlacement h p root τ k n hl old nextValues found
  let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
  have types : (h.write root (memberArrayData D τ k n hl nextValues) ht).ty=h.ty :=
    funext (fun a => Source.Heap.write_ty h root a _ ht)
  have nextEncoded : ∀ j,MemoryElement q (nextValues j) (nextWords j) := by
    intro j
    have before : MemoryElement p (nextValues j) (nextWords j) := by
      dsimp only [nextValues,nextWords,replace]
      split
      · exact newEncoded
      · exact encoded j
    exact before.transport q types rfl
  have newFound : (h.write root (memberArrayData D τ k n hl nextValues) ht).get root=
      some ⟨_,memberArrayData D τ k n hl nextValues⟩ := Source.Heap.write_get h root _ ht
  let oldImage := memoryArrayImage p root n hl old words encoded found
  have initial := mixedImage_reads_of_coverage p es coverage memory oldReads
    (⟨root,_,_,found,oldImage⟩ : MixedHeapEntry p)
  have bound := (memberArray_placement_bounds h p root τ k n hl old found).1
  have parts := inventory_array_reads k n hl bound words memory (p.address root) initial
  let image := memoryArrayImage q root n hl nextValues nextWords nextEncoded newFound
  have imageEq : image.encode patch (p.address root)=memberArrayView k n bound nextWords patch (p.address root) := by
    cases k <;> rfl
  have newReads := image.encode_reads patch (p.address root)
  rw [imageEq,ArrayWordStore.reencode k n bound memory (p.address root) words parts.1 parts.2 index word] at newReads
  rcases e with ⟨a,σ,data,eFound,eImage⟩
  by_cases same : a=root
  · subst a
    have dataEq := Option.some.inj (newFound.symm.trans eFound)
    cases dataEq
    exact (image.reads_unique eImage patch (p.address root)).mp newReads
  · have oldFound : h.get a=some ⟨σ,data⟩ := by
      rw [←Source.Heap.write_other h same (memberArrayData D τ k n hl nextValues) ht]
      exact eFound
    have extension : ∀ a σ,(h.write root (memberArrayData D τ k n hl nextValues) ht).ty a=some σ →
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
    change eImage.span≤(p.shape a).size at fit
    have wordFits : p.address root+arrayPayloadOffset k+index.val*32+32≤p.address root+(p.shape root).size := by
      rw [memberArray_shape h p root τ k n hl old found]
      change _≤p.address root+((if k.isNone then 32 else 0)+n*32)
      unfold arrayPayloadOffset
      have inside := index.isLt
      omega
    apply eImage.reads_congr patch memory (q.address a) _ unchanged
    intro byte small
    change mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word (p.address a+byte)=memory (p.address a+byte)
    apply mstore_outside
    rcases separate with before | after <;> omega
/-- Complete changed-map reconstruction and unchanged whole Source writeback
are derived for the actual member write, not assumed as output agreements. -/
theorem whole {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x,k=some x → x=n) (old : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (index : Fin n) (value : Source.Val E.layout τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let values := replace old index value
    let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) (heap_ty_of_get _ _ _ _ found))
    let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
    let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) patch=.ok (some (.ok (),after)) ∧
      ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let values := replace old index value
  let newWords := replace words index word
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) ht)
  let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
  let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
  have newEnc : ∀ j,MemoryElement p (values j) (newWords j) := by
    intro j
    dsimp only [values,newWords,replace]
    split
    · exact newEncoded
    · exact encoded j
  have run : (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) := by
    rw [ArrayWordStore.source s F horizon root τ k n hl old found index value,
      memberArrayHeapPut_run s root τ k n hl values ht]
  have safe := memberArrayHeapPut_MemOK E H s p root τ k n hl values newWords newEnc ok
  rw [memberArrayHeapPut_run s root τ k n hl values ht] at safe
  have nextSupport : ∀ a σ d,after.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
    intro a σ d actual
    change (s.2.heap.write root (memberArrayData E.layout τ k n hl values) ht).get a=some ⟨σ,d⟩ at actual
    by_cases same : a=root
    · subst a
      rw [Source.Heap.write_get] at actual
      cases actual
      exact supported root _ _ found
    · rw [Source.Heap.write_other s.2.heap same] at actual
      exact supported a σ d actual
  have before := ownerMemOK_prepares_inventory H s p ok supported
  have coverage := (prepareHeapInventory_ok p _ before).2.1
  have ready := ownerMemOK_prepares_inventory H after q safe nextSupport
  have wholeMap : encodeMixedHeap q (generatedHeapEntries q) patch=patch :=
    encodeMixedHeap_unchanged q _ patch (fun e _ => reads s.2.heap p _ coverage root τ k n hl old words encoded
      found index value word newEncoded memory oldReads e)
  have unchanged := enumeratedMemory_unchanged after q q (retainInitial _ _) patch nextSupport _ ready
  rw [wholeMap] at unchanged
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true;rw [found];rfl
  have start := p.starts root present
  have validReserved : ReservedOK patch q.free := by
    constructor
    · exact (congrArg Fin.val (mload_congr patch memory 64 (fun byte =>
        mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)))).trans reserved.1
    · intro byte
      change mstore memory _ word (96+byte.val)=0
      rw [mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)]
      exact reserved.2 byte
  exact ⟨run,safe,(prepareHeapInventory_ok q _ ready).2.1,wholeMap,unchanged,validReserved⟩
end Solidity.Yul.Views.ArrayWordHeap
