import Solidity.Yul.Views.CanonicalRetained

/-! Transport existing intrinsic images and actual owned candidates after a
same-type heap write. Addresses/types, not stale child contents, determine a
pointer word. No replacement state, assumed inverse or new semantic profile. -/
namespace Solidity.Yul.Views

theorem MemoryElement.transport {D : Source.Layout} {h h' : Source.Heap D}
    {p : Placement h} (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τ : Source.STy} {v : Source.Val D τ} {w : Roadmap.Word} (e : MemoryElement p v w) : MemoryElement q v w := by
  cases e with
  | scalar v w read => exact .scalar v w read
  | pointer loc a σ owned shape =>
    have ht : h'.ty a = some σ := by rw [types]; exact owned
    have eq : ownedPointerWord q a σ ht = ownedPointerWord p a σ owned := Fin.ext (congrFun addresses a)
    rw [← eq]
    exact .pointer loc a σ ht shape

theorem MemoryFields.transport {D : Source.Layout} {h h' : Source.Heap D}
    {p : Placement h} (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws) : MemoryFields q fs ws := by
  induction e with
  | nil => exact .nil
  | cons v w encoded fs ws rest ih => exact .cons v w (encoded.transport q types addresses) fs ws ih

theorem MemoryObjectWords.transport {D : Source.Layout} {h h' : Source.Heap D}
    {p : Placement h} (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τ : Source.STy} {d : Source.Data D τ} {ws : List Roadmap.Word} (e : MemoryObjectWords p d ws) : MemoryObjectWords q d ws := by
  cases e with
  | value v w encoded => exact .value v w (encoded.transport q types addresses)
  | array n hl bound vs ws encoded => exact .array n hl bound vs ws (fun i => (encoded i).transport q types addresses)
  | strct fs ws encoded => exact .strct fs ws (encoded.transport q types addresses)

def MemoryImage.transport {D : Source.Layout} {h h' : Source.Heap D}
    {p : Placement h} (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) : MemoryImage q d := by
  cases image with
  | bytes bs bound => exact .bytes bs bound
  | string bs bound => exact .string bs bound
  | words d ws encoded => exact .words d ws (encoded.transport q types addresses)

theorem MemoryImage.transport_encode {D : Source.Layout} {h h' : Source.Heap D}
    {p : Placement h} (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat) :
    (image.transport q types addresses).encode m base = image.encode m base := by cases image <;> rfl

/-- Refresh the actual written entry, transport every unchanged child's image.
The supplied image is concrete constructor evidence, not an inverse/read law. -/
def refreshMixedEntry {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (e : MixedHeapEntry p) : MixedHeapEntry q :=
  if same : e.id = root then
    ⟨root, τ, d, Source.Heap.write_get h root d ht, image⟩
  else
    ⟨e.id, e.ty, e.data, (Source.Heap.write_other h same d ht).trans e.found,
      e.image.transport q (funext (fun a => Source.Heap.write_ty h root a d ht)) addresses⟩

theorem refreshMixedEntry_id {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (e : MixedHeapEntry p) : (refreshMixedEntry p root d ht q addresses image e).id = e.id := by
  unfold refreshMixedEntry
  split
  · exact ‹e.id = root›.symm
  · rfl

theorem refreshMixedEntry_ty {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (e : MixedHeapEntry p) : (refreshMixedEntry p root d ht q addresses image e).ty = e.ty := by
  unfold refreshMixedEntry
  split
  · rename_i same
    exact Option.some.inj (ht.symm.trans (same ▸ heap_ty_of_get h e.id e.ty e.data e.found))
  · rfl

def refreshMixedEntries {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) : List (MixedHeapEntry q) :=
  es.map (refreshMixedEntry p root d ht q addresses image)

theorem refreshMixedEntries_coverage {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) :
    CoversMixedHeap (refreshMixedEntries p root d ht q addresses image es) := by
  intro a present
  obtain ⟨e, member, same⟩ := coverage a (by rwa [heap_write_occupancy] at present)
  exact ⟨_, List.mem_map.mpr ⟨e, member, rfl⟩, (refreshMixedEntry_id p root d ht q addresses image e).trans same⟩

/-- Exact pointer decoder equality, including missing candidates/None. -/
theorem decodeMemoryPointer_refresh {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data D σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) (τ : Source.STy)
    (loc : τ.loc? = some .memory) (word : Roadmap.Word) :
    decodeMemoryPointer q (refreshMixedEntries p root d ht q addresses image es) τ loc word = decodeMemoryPointer p es τ loc word := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have pred : pointerCandidate τ word (refreshMixedEntry p root d ht q addresses image e) = pointerCandidate τ word e := by
      unfold pointerCandidate
      rw [refreshMixedEntry_ty, refreshMixedEntry_id, addresses]
    simp only [decodeMemoryPointer] at ih ⊢
    change (List.find? (pointerCandidate τ word) (refreshMixedEntry p root d ht q addresses image e :: refreshMixedEntries p root d ht q addresses image es)).map _ = _
    simp only [List.find?_cons, pred]
    cases yes : pointerCandidate τ word e
    · simpa only [yes, Bool.false_eq_true, if_false] using ih
    · simp only [Option.map_some, refreshMixedEntry_id]

theorem decodeExtended_refresh {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data D σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) (τ : Source.STy) (word : Roadmap.Word) :
    decodeExtendedMemoryMember q (refreshMixedEntries p root d ht q addresses image es) τ word = decodeExtendedMemoryMember p es τ word := by
  unfold decodeExtendedMemoryMember
  cases scalar : decodeCanonicalScalar D τ word with
  | some v => rfl
  | none =>
    simp only [decodeMemoryMember]
    split
    · exact decodeMemoryPointer_refresh p root d ht q addresses image es τ _ word
    · rfl

theorem decodeCanonicalArray_refresh {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data D σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) (τ : Source.STy) (n : Nat) (m : ByteView) (base : Nat) :
    decodeCanonicalArray q (refreshMixedEntries p root d ht q addresses image es) τ n m base = decodeCanonicalArray p es τ n m base := by
  unfold decodeCanonicalArray
  have eq : decodeExtendedMemoryMember q (refreshMixedEntries p root d ht q addresses image es) τ = decodeExtendedMemoryMember p es τ :=
    funext (decodeExtended_refresh p root d ht q addresses image es τ)
  rw [eq]

theorem decodeCanonicalFields_refresh {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data D σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) (τs : List Source.STy) (m : ByteView) (base : Nat) :
    decodeCanonicalFields q (refreshMixedEntries p root d ht q addresses image es) τs m base = decodeCanonicalFields p es τs m base := by
  unfold decodeCanonicalFields
  have eq : decodeExtendedMemoryMember q (refreshMixedEntries p root d ht q addresses image es) = decodeExtendedMemoryMember p es :=
    funext (fun τ => funext (decodeExtended_refresh p root d ht q addresses image es τ))
  rw [eq]

theorem refreshMixedEntries_ids {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address)
    (image : MemoryImage q d) (es : List (MixedHeapEntry p)) :
    (refreshMixedEntries p root d ht q addresses image es).map MixedHeapEntry.id = es.map MixedHeapEntry.id := by
  simp only [refreshMixedEntries, List.map_map]
  congr 1
  funext e
  exact refreshMixedEntry_id p root d ht q addresses image e

end Solidity.Yul.Views
