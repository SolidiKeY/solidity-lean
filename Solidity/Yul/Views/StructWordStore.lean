import Solidity.Yul.Views.ArrayWordRetained

/-! Actual typed struct field replacement and its raw word store. The owner's
setNth computation retains field-type checks; existing canonical codecs retain
scalar and pointer interpretation. No final image/view or inverse law is input. -/
namespace Solidity.Yul.Views.StructWordStore

theorem fields_update {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {types : List Source.STy} {fields next : Source.DataList D types} {words : List Roadmap.Word}
    (encoded : MemoryFields p fields words) (index : Nat) {τ : Source.STy}
    (value : Source.Val D τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (updated : fields.setNth index (.val value)=.ok next) : MemoryFields p next (words.set index word) := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction encoded generalizing index with
  | nil =>
    simp only [Source.DataList.setNth,Source.stuck] at updated
    cases updated
  | @cons headTy tailTypes old oldWord oldEncoded rest restWords restEncoded ih =>
    cases index with
    | zero =>
      by_cases same : τ=headTy
      · subst headTy
        simp only [Source.DataList.setNth] at updated
        cases updated
        exact .cons value word newEncoded rest restWords restEncoded
      · simp only [Source.DataList.setNth,dif_neg same,Source.stuck] at updated
        cases updated
    | succ index =>
      simp only [Source.DataList.setNth] at updated
      cases actual : rest.setNth index (.val value) with
      | error error => rw [actual] at updated;cases updated
      | ok fields =>
        rw [actual] at updated
        cases updated
        exact .cons old oldWord oldEncoded fields (restWords.set index word) (ih index actual)

theorem word_reads (words : List Roadmap.Word) (index : Fin words.length) (word : Roadmap.Word)
    (memory : ByteView) (base : Nat)
    (oldReads : ∀ i w,words[i]?=some w → mload memory (base+i*32)=w) :
    ∀ i w,(words.set index.val word)[i]?=some w →
      mload (mstore memory (base+index.val*32) word) (base+i*32)=w := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro i w found
  by_cases same : i=index.val
  · subst i
    rw [List.getElem?_set_self index.isLt] at found
    cases found
    exact mload_mstore memory _ word
  · rw [List.getElem?_set_ne (Ne.symm same)] at found
    rw [mload_congr _ memory _ (fun byte => mstore_outside _ _ _ _ (by have small:=byte.isLt;omega))]
    exact oldReads i w found

theorem source {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList E.layout (E.layout.fields name))
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Nat) {τ : Source.STy} (value : Source.Val E.layout τ)
    (updated : fields.setNth index (.val value)=.ok next) :
    (Source.writeLoc F horizon (.mem root index) value).run s=
      (Source.heapPut root ⟨.struct .memory name,.struct next⟩).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (Source.memSet root index value).run s=_
  rw [Source.memSet,Source.Hoare.run_bind,heapObj_known s root _ found]
  dsimp only
  have lifted : (Source.EM.lift (E:=E) (Γ:=Γ) (fields.setNth index (.val value))).run s=(.ok next,s) := by
    unfold Source.EM.lift
    rw [updated]
    rfl
  rw [Source.Hoare.run_bind,lifted]

theorem writeback {E Γ} (s : Source.EMState E Γ) (p : Placement s.2.heap) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (F : Source.Fr) (horizon root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words) (supported : ∀ τ∈E.layout.fields name,ExtendedMemberType E.layout τ)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length) {τ : Source.STy} (value : Source.Val E.layout τ) (word : Roadmap.Word)
    (newEncoded : MemoryElement p value word) (updated : fields.setNth index.val (.val value)=.ok next)
    (memory : ByteView) (oldReads : ∀ i w,words[i]?=some w → mload memory (p.address root+i*32)=w) :
    canonicalStructState s p es root name (mstore memory (p.address root+index.val*32) word)=
      some ((Source.writeLoc F horizon (.mem root index.val) value).run s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have nextEncoded := fields_update encoded index.val value word newEncoded updated
  unfold canonicalStructState
  rw [decodeCanonicalFields_reads p es coverage nextEncoded supported _ _ (word_reads words index word memory _ oldReads)]
  simp only [Option.map_some]
  rw [source s F horizon root name fields next found index.val value updated]

theorem reencode (words : List Roadmap.Word) (index : Fin words.length) (word : Roadmap.Word)
    (memory : ByteView) (base : Nat)
    (oldReads : ∀ i w,words[i]?=some w → mload memory (base+i*32)=w) :
    let patch := mstore memory (base+index.val*32) word
    wordListView (words.set index.val word) patch base=patch := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact wordList_unchanged _ _ _ (word_reads words index word memory base oldReads)
end Solidity.Yul.Views.StructWordStore
