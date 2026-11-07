import Solidity.Yul.Views.ByteElementStore

/-! Actual memory deletion runs the owner zeroVal before the write. These
adapters retain default availability, horizon/type failures and canonical
physical codecs; reference defaults that allocate are not treated as scalars. -/
namespace Solidity.Yul.Views.MemoryDelete
open ArrayWordStore

theorem member {E Γ τ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root index : Nat)
    (value : Source.Val E.layout τ) (computed : Source.Val.default E.layout τ=some value) :
    (Source.deleteLoc F (horizon+1) (.mem (τ:=τ) root index)).run s=
      (Source.writeLoc F (horizon+1) (.mem root index) value).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (do let value ← Source.zeroVal (horizon+1) τ
             Source.writeLoc F (horizon+1) (.mem root index) value).run s=_
  rw [Source.zeroVal,computed]
  rfl

theorem byte {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root index : Nat) :
    (Source.deleteLoc F (horizon+1) (.memByte root index)).run s=
      (Source.writeLoc F (horizon+1) (.memByte root index)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0] rfl)).run s := by rfl

theorem timeout {E Γ τ} (s : Source.EMState E Γ) (F : Source.Fr) (root index : Nat) :
    (Source.deleteLoc F 0 (.mem (τ:=τ) root index)).run s=(.error .timeout,s) := by rfl

theorem array {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x,k=some x → x=n) (old : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (index : Fin n) (value : Source.Val E.layout τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (computed : Source.Val.default E.layout τ=some value)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let values := replace old index value
    let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) (heap_ty_of_get _ _ _ _ found))
    let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
    let nextHistory := ArrayWordRetained.history s.2.heap allocated p prior root τ k n hl old values found
    let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
    (Source.deleteLoc F (horizon+1) (.mem (τ:=τ) root index.val)).run s=(.ok (),after) ∧
      RetainedAllocation allocated q ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after allocated q nextHistory patch=.ok (some (.ok (),after)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [member s F horizon root index.val value computed]
  exact ArrayWordRetained.whole H s allocated p prior ok supported F (horizon+1) root τ k n hl old words encoded found
    index value word newEncoded memory oldReads reserved

theorem strct {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length) {τ : Source.STy} (value : Source.Val E.layout τ) (word : Roadmap.Word)
    (newEncoded : MemoryElement p value word)
    (computed : Source.Val.default E.layout τ=some value) (updated : fields.setNth index.val (.val value)=.ok next)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := withSourceHeap s (s.2.heap.write root (.struct next) (heap_ty_of_get _ _ _ _ found))
    let q := structWrittenPlacement s.2.heap p root name fields next found
    let nextHistory := StructWordRetained.history s.2.heap allocated p prior root name fields next found
    let patch := mstore memory (p.address root+index.val*32) word
    (Source.deleteLoc F (horizon+1) (.mem (τ:=τ) root index.val)).run s=(.ok (),after) ∧
      RetainedAllocation allocated q ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after allocated q nextHistory patch=.ok (some (.ok (),after)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [member s F horizon root index.val value computed]
  exact StructWordRetained.whole H s allocated p prior ok supported F (horizon+1) root name fields next words encoded found
    index value word newEncoded updated memory oldReads reserved

theorem bytes {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (index : Fin bytes.length) (memory : ByteView)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let ht := heap_ty_of_get s.2.heap root _ _ found
    let data := heapByteData E.layout string (bytes.set index.val 0)
    let after := withSourceHeap s (s.2.heap.write root data ht)
    let q := ByteElementStore.placement s.2.heap p root string bytes found index 0
    let patch := saveByte memory (p.address root+32+index.val) 0
    (Source.deleteLoc F (horizon+1) (.memByte root index.val)).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback after allocated q history patch=.ok (some (.ok (),after)) ∧
        ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [byte s F horizon root index.val]
  exact ByteElementStore.whole H s allocated p prior ok supported F (horizon+1) root string bytes found index 0 memory oldReads reserved
end Solidity.Yul.Views.MemoryDelete
