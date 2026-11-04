import Solidity.Yul.Views.StructWordStore

/-! Whole-heap reads after an actual typed struct-field word update. Changed
fields use the existing canonical codecs; other objects retain their exact
bytes by placement separation. No output image agreement is assumed. -/
namespace Solidity.Yul.Views.StructWordHeap

theorem reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList D (D.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : h.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length) {τ : Source.STy} (value : Source.Val D τ) (word : Roadmap.Word)
    (newEncoded : MemoryElement p value word) (updated : fields.setNth index.val (.val value)=.ok next)
    (memory : ByteView) (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (e : MixedHeapEntry (structWrittenPlacement h p root name fields next found)) :
    e.image.Reads (mstore memory (p.address root+index.val*32) word)
      ((structWrittenPlacement h p root name fields next found).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let ht := heap_ty_of_get h root _ _ found
  let q := structWrittenPlacement h p root name fields next found
  let patch := mstore memory (p.address root+index.val*32) word
  have types : (h.write root (.struct next) ht).ty=h.ty :=
    funext (fun a => Source.Heap.write_ty h root a _ ht)
  have nextEncoded : MemoryFields q next (words.set index.val word) :=
    (StructWordStore.fields_update encoded index.val value word newEncoded updated).transport q types rfl
  have newFound : (h.write root (.struct next) ht).get root=some ⟨_,.struct next⟩ :=
    Source.Heap.write_get h root _ ht
  let oldImage : MemoryImage p (.struct (l:=.memory) fields) := .words _ words (.strct fields words encoded)
  have initial := mixedImage_reads_of_coverage p es coverage memory oldReads
    (⟨root,_,_,found,oldImage⟩ : MixedHeapEntry p)
  let image : MemoryImage q (.struct (l:=.memory) next) :=
    .words _ (words.set index.val word) (.strct next _ nextEncoded)
  have imageEq : image.encode patch (p.address root)=wordListView (words.set index.val word) patch (p.address root) := rfl
  have newReads := image.encode_reads patch (p.address root)
  rw [imageEq,StructWordStore.reencode words index word memory (p.address root) initial] at newReads
  rcases e with ⟨a,σ,data,eFound,eImage⟩
  by_cases same : a=root
  · subst a
    have dataEq := Option.some.inj (newFound.symm.trans eFound)
    cases dataEq
    exact (image.reads_unique eImage patch (p.address root)).mp newReads
  · have oldFound : h.get a=some ⟨σ,data⟩ := by
      rw [←Source.Heap.write_other h same (.struct next) ht]
      exact eFound
    have extension : ∀ a σ,(h.write root (.struct next) ht).ty a=some σ →
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
    have extent := structFields_extent h p root name fields fields found words encoded
    have wordFits : p.address root+index.val*32+32≤p.address root+(p.shape root).size := by
      have inside := index.isLt
      omega
    apply eImage.reads_congr patch memory (q.address a) _ unchanged
    intro byte small
    change mstore memory (p.address root+index.val*32) word (p.address a+byte)=memory (p.address a+byte)
    apply mstore_outside
    rcases separate with before | after <;> omega
/-- The actual typed field write produces a complete reconstructed map and
an unchanged whole administrative Source state on canonical writeback. -/
theorem whole {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length) {τ : Source.STy} (value : Source.Val E.layout τ) (word : Roadmap.Word)
    (newEncoded : MemoryElement p value word) (updated : fields.setNth index.val (.val value)=.ok next)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := withSourceHeap s (s.2.heap.write root (.struct next) (heap_ty_of_get _ _ _ _ found))
    let q := structWrittenPlacement s.2.heap p root name fields next found
    let patch := mstore memory (p.address root+index.val*32) word
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) patch=.ok (some (.ok (),after)) ∧
      ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let after := withSourceHeap s (s.2.heap.write root (.struct next) ht)
  let q := structWrittenPlacement s.2.heap p root name fields next found
  let patch := mstore memory (p.address root+index.val*32) word
  have run : (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) := by
    rw [StructWordStore.source s F horizon root name fields next found index.val value updated,
      structHeapPut_run s root name next ht]
  have before := ownerMemOK_prepares_inventory H s p ok supported
  have coverage := (prepareHeapInventory_ok p _ before).2.1
  let oldImage : MemoryImage p (.struct (l:=.memory) fields) := .words _ words (.strct fields words encoded)
  have initial := mixedImage_reads_of_coverage p _ coverage memory oldReads
    (⟨root,_,_,found,oldImage⟩ : MixedHeapEntry p)
  have selected := StructWordStore.writeback s p _ coverage F horizon root name fields next words encoded
    (supported root _ _ found) found index value word newEncoded updated memory initial
  rw [run] at selected
  have safe : Source.MemOK E H after :=
    canonicalStructState_MemOK E H s p _ root name patch (.ok (),after) selected ok
  have nextSupport : ∀ a σ d,after.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
    intro a σ d actual
    change (s.2.heap.write root (.struct next) ht).get a=some ⟨σ,d⟩ at actual
    by_cases same : a=root
    · subst a
      rw [Source.Heap.write_get] at actual
      cases actual
      exact supported root _ _ found
    · rw [Source.Heap.write_other s.2.heap same] at actual
      exact supported a σ d actual
  have ready := ownerMemOK_prepares_inventory H after q safe nextSupport
  have wholeMap : encodeMixedHeap q (generatedHeapEntries q) patch=patch :=
    encodeMixedHeap_unchanged q _ patch (fun e _ => reads s.2.heap p _ coverage root name fields next words encoded
      found index value word newEncoded updated memory oldReads e)
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
end Solidity.Yul.Views.StructWordHeap
