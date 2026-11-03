import Solidity.Yul.Views.InventoryObject

namespace Solidity.Yul.Views

theorem snapshotArray_refresh {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data E.layout σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address) (image : MemoryImage q d)
    (es : List (MixedHeapEntry p)) (l : Source.DataLoc) (τ : Source.STy) (k : Option Nat) (m : ByteView) (base : Nat) :
    snapshotArray q (refreshMixedEntries p root d ht q addresses image es) l τ k m base =
      (snapshotArray p es l τ k m base).map (InventoryObject.transport q (funext (fun a => Source.Heap.write_ty h root a d ht)) addresses) := by
  unfold snapshotArray
  dsimp only
  by_cases bound : arrayLengthChoice k m base < 2^256
  · simp only [dif_pos bound]
    have stable := decodeCanonicalArray_refresh p root d ht q addresses image es τ (arrayLengthChoice k m base) m (base+arrayPayloadOffset k)
    by_cases dec : decodeCanonicalArray p es τ (arrayLengthChoice k m base) m (base+arrayPayloadOffset k) = none
    · rw [Option.pmap_none' (stable.trans dec),Option.pmap_none' dec]; rfl
    · obtain ⟨values,yes⟩ := Option.ne_none_iff_exists'.mp dec
      rw [Option.pmap_some' (stable.trans yes),Option.pmap_some' yes,Option.map_some]; rfl
  · simp only [dif_neg bound,Option.map_none]

theorem snapshotStruct_refresh {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data E.layout σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address) (image : MemoryImage q d)
    (es : List (MixedHeapEntry p)) (l : Source.DataLoc) (name : Source.DeclName) (m : ByteView) (base : Nat) :
    snapshotStruct q (refreshMixedEntries p root d ht q addresses image es) l name m base =
      (snapshotStruct p es l name m base).map (InventoryObject.transport q (funext (fun a => Source.Heap.write_ty h root a d ht)) addresses) := by
  unfold snapshotStruct
  have stable := decodeCanonicalFields_refresh p root d ht q addresses image es (E.layout.fields name) m base
  by_cases dec : decodeCanonicalFields p es (E.layout.fields name) m base = none
  · rw [Option.pmap_none' (stable.trans dec),Option.pmap_none' dec]; rfl
  · obtain ⟨fs,yes⟩ := Option.ne_none_iff_exists'.mp dec
    rw [Option.pmap_some' (stable.trans yes),Option.pmap_some' yes,Option.map_some]; rfl

theorem decodeInventoryObject_refresh {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (root : Nat) {σ : Source.STy} (d : Source.Data E.layout σ) (ht : h.ty root = some σ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address) (image : MemoryImage q d)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat) :
    decodeInventoryObject q (refreshMixedEntries p root d ht q addresses image es) τ m base =
      (decodeInventoryObject p es τ m base).map (InventoryObject.transport q (funext (fun a => Source.Heap.write_ty h root a d ht)) addresses) := by
  cases τ with
  | bytes l => cases l <;> rfl
  | string l => cases l <;> rfl
  | array l τ k => exact snapshotArray_refresh p root d ht q addresses image es l τ k m base
  | struct l name => exact snapshotStruct_refresh p root d ht q addresses image es l name m base
  | _ => rfl

theorem MemoryImage.transport_trans {E : Source.Env} {h h' h'' : Source.Heap E.layout}
    {p : Placement h} (q : Placement h') (r : Placement h'')
    (t1 : h'.ty = h.ty) (a1 : q.address = p.address) (t2 : h''.ty = h'.ty) (a2 : r.address = q.address)
    {τ : Source.STy} {d : Source.Data E.layout τ} (image : MemoryImage p d) :
    (image.transport q t1 a1).transport r t2 a2 = image.transport r (t2.trans t1) (a2.trans a1) := by
  cases image <;> rfl

/-- Internal context transport fact. Its decoder premise is instantiated by
concrete refresh laws at each step, never an opaque read/inverse assumption. -/
theorem decodeInventoryObject_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w, decodeExtendedMemoryMember q qs τ w = decodeExtendedMemoryMember p es τ w)
    (τ : Source.STy) (m : ByteView) (base : Nat) :
    decodeInventoryObject q qs τ m base = (decodeInventoryObject p es τ m base).map (InventoryObject.transport q types addresses) := by
  have fields (τs : List Source.STy) : decodeCanonicalFields q qs τs m base = decodeCanonicalFields p es τs m base := by
    unfold decodeCanonicalFields
    rw [show decodeExtendedMemoryMember q qs = decodeExtendedMemoryMember p es from funext (fun υ => funext (members υ))]
  cases τ with
  | bytes l => cases l <;> rfl
  | string l => cases l <;> rfl
  | array l υ k =>
    change snapshotArray q qs l υ k m base = (snapshotArray p es l υ k m base).map _
    unfold snapshotArray
    dsimp only
    by_cases bound : arrayLengthChoice k m base < 2^256
    · simp only [dif_pos bound]
      have stable : decodeCanonicalArray q qs υ (arrayLengthChoice k m base) m (base+arrayPayloadOffset k) =
          decodeCanonicalArray p es υ (arrayLengthChoice k m base) m (base+arrayPayloadOffset k) := by
        unfold decodeCanonicalArray
        rw [show decodeExtendedMemoryMember q qs υ = decodeExtendedMemoryMember p es υ from funext (members υ)]
      by_cases no : decodeCanonicalArray p es υ (arrayLengthChoice k m base) m (base+arrayPayloadOffset k) = none
      · rw [Option.pmap_none' (stable.trans no),Option.pmap_none' no]; rfl
      · obtain ⟨vs,yes⟩ := Option.ne_none_iff_exists'.mp no
        rw [Option.pmap_some' (stable.trans yes),Option.pmap_some' yes,Option.map_some]; rfl
    · simp only [dif_neg bound,Option.map_none]
  | struct l name =>
    change snapshotStruct q qs l name m base = (snapshotStruct p es l name m base).map _
    unfold snapshotStruct
    by_cases no : decodeCanonicalFields p es (E.layout.fields name) m base = none
    · rw [Option.pmap_none' ((fields _).trans no),Option.pmap_none' no]; rfl
    · obtain ⟨fs,yes⟩ := Option.ne_none_iff_exists'.mp no
      rw [Option.pmap_some' ((fields _).trans yes),Option.pmap_some' yes,Option.map_some]; rfl
  | _ => rfl

theorem snapshotArray_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (l : Source.DataLoc) (τ : Source.STy) (k : Option Nat) (m : ByteView) (base : Nat) (o : InventoryObject p (.array l τ k))
    (decoded : snapshotArray p es l τ k m base = some o) : o.image.encode m base = m := by
  unfold snapshotArray at decoded
  dsimp only at decoded
  split at decoded
  · obtain ⟨values,valid,dec,same⟩ := Option.pmap_eq_some_iff.mp decoded
    subst o
    change wordListView ((if k.isNone then [⟨arrayLengthChoice k m base,_⟩] else []) ++ List.ofFn
      (fun i : Fin (arrayLengthChoice k m base) => mload m (base+arrayPayloadOffset k+i.val*32))) m base = m
    cases k with
    | none =>
      change dynamicUintView (mload m base).val _ (fun i => mload m (base+32+i.val*32)) m base = m
      exact arraySnapshot_reencode none _ _ m base rfl
    | some size => exact decodeStaticUint_reencode size m base
  · cases decoded

theorem snapshotStruct_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (l : Source.DataLoc) (name : Source.DeclName) (m : ByteView) (base : Nat) (o : InventoryObject p (.struct l name))
    (decoded : snapshotStruct p es l name m base = some o) : o.image.encode m base = m := by
  obtain ⟨fs,valid,dec,same⟩ := Option.pmap_eq_some_iff.mp decoded
  subst o
  exact decodeStaticUint_reencode (E.layout.fields name).length m base

theorem decodeInventoryObject_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat) (o : InventoryObject p τ)
    (decoded : decodeInventoryObject p es τ m base = some o) : o.image.encode m base = m := by
  cases τ with
  | bytes l => cases l with
    | memory => cases decoded; exact bytesObject_decode_reencode m base
    | storage | calldata => cases decoded
  | string l => cases l with
    | memory => cases decoded; exact bytesObject_decode_reencode m base
    | storage | calldata => cases decoded
  | array l τ k => exact snapshotArray_raw p es l τ k m base o decoded
  | struct l name => exact snapshotStruct_raw p es l name m base o decoded
  | _ => cases decoded

end Solidity.Yul.Views
