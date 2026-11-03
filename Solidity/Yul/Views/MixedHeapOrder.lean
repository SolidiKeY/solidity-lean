import Solidity.Yul.Views.MemoryImageOrder
import Solidity.Yul.Views.HeapEnumerationLaws

/-! Whole physical heap encoding is independent of the order of distinct actual
root entries. Separation comes from the existing Placement and image bounds,
not from caller-supplied byte regions. Pointer aliases do not duplicate roots.
This is an encoder law; actual Source update permutations remain the separate
existing InventoryOrder theorem. -/
namespace Solidity.Yul.Views

theorem mixedEntry_encode_commute {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e f : MixedHeapEntry p) (different : e.id≠f.id) (m : ByteView) :
    f.image.encode (e.image.encode m (p.address e.id)) (p.address f.id)=
      e.image.encode (f.image.encode m (p.address f.id)) (p.address e.id) := by
  have present (x : MixedHeapEntry p) : (h.cells x.id).isSome := by
    change (h.get x.id).isSome=true
    rw [x.found]
    rfl
  have separate := p.separate e.id f.id (present e) (present f) different
  have eb := e.image.fits p e.id e.found
  have fb := f.image.fits p f.id f.found
  exact e.image.disjoint_commute f.image m _ _ (by omega)

theorem encodeMixedHeap_append {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es fs : List (MixedHeapEntry p)) (m : ByteView) :
    encodeMixedHeap p (es++fs) m=encodeMixedHeap p es (encodeMixedHeap p fs m) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.image.encode (encodeMixedHeap p (es++fs) m) _=_
    rw [ih]
    rfl

/-- Arbitrary finite permutation, with no root-count cap. Distinct logical root
IDs derive real physical separation even when pointer words alias a child. -/
theorem encodeMixedHeap_perm {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {es fs : List (MixedHeapEntry p)} (perm : es.Perm fs)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    encodeMixedHeap p es m=encodeMixedHeap p fs m := by
  induction perm with
  | nil => rfl
  | cons e perm ih =>
    change e.image.encode (encodeMixedHeap p _ m) _=e.image.encode (encodeMixedHeap p _ m) _
    rw [ih (List.nodup_cons.mp distinct).2]
  | swap e f rest =>
    have no := (List.nodup_cons.mp distinct).1
    have different : e.id≠f.id := fun eq=>no (List.mem_cons.mpr (Or.inl eq.symm))
    exact mixedEntry_encode_commute p e f different (encodeMixedHeap p rest m)
  | trans one two ih1 ih2 =>
    exact (ih1 distinct).trans (ih2 ((one.map MixedHeapEntry.id).nodup distinct))

/-- Re-encoding an already encoded inventory is exact over the WHOLE byte map,
including untouched residual bytes. No decoder inverse is supplied. -/
theorem encodeMixedHeap_idempotent {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    encodeMixedHeap p es (encodeMixedHeap p es m)=encodeMixedHeap p es m :=
  encodeMixedHeap_unchanged p es _ (encodeMixedHeap_reads p es distinct m)

/-- Every byte at or beyond the actual free extent is residual for ANY typed
entry inventory. The region fact is derived from Placement and image bounds. -/
theorem encodeMixedHeap_after_free {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (m : ByteView) (i : Nat) (beyond : p.free.val≤i) :
    encodeMixedHeap p es m i=m i := by
  apply encodeMixedHeap_residual p es m i
  intro e member
  have present : (h.cells e.id).isSome := by
    change (h.get e.id).isSome=true
    rw [e.found]
    rfl
  have span := e.image.fits p e.id e.found
  have ends := p.ends e.id present
  exact Or.inr (by omega)

/-- Any permutation of the COMPUTED complete inventory has actual whole-source
unchanged writeback. Completeness is obtained from the original owner MemOK
and concrete codec profile, not a supplied inventory/inverse/output-view law. -/
theorem generated_permuted_writeback {E : Source.Env} {Γ : Source.RCtx}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (es : List (MixedHeapEntry p)) (perm : es.Perm (generatedHeapEntries p)) (m : ByteView) :
    enumeratedMemoryWriteback s p p (retainInitial _ _) (encodeMixedHeap p es m)=.ok (some (.ok (),s)) := by
  have distinct := (perm.symm.map MixedHeapEntry.id).nodup (generatedHeapEntries_nodup p)
  rw [encodeMixedHeap_perm p perm distinct m]
  exact enumeratedMemory_unchanged s p p (retainInitial _ _) m supported _
    (ownerMemOK_prepares_inventory H s p ok supported)

end Solidity.Yul.Views
