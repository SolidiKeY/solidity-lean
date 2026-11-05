import Solidity.Yul.Views.FixedNominalInventory

/-! Exact nominal snapshot reencoding and actual whole-source writeback laws. -/
namespace Solidity.Yul.Views.FixedNominalInventory

theorem snapshot_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (name : Source.DeclName) (k : Option Nat) (m : ByteView) (base : Nat)
    (o : InventoryObject p (.array .memory (.udvt name) k))
    (prepared : snapshot p name k m base = some o) : o.image.encode m base = m := by
  unfold snapshot at prepared
  dsimp only at prepared
  split at prepared
  · split at prepared
    · obtain ⟨values,valid,decoded,same⟩ := Option.pmap_eq_some_iff.mp prepared
      subst o
      change wordListView ((if k.isNone then [⟨arrayLengthChoice k m base,_⟩] else []) ++ List.ofFn
        (fun i : Fin (arrayLengthChoice k m base) => mload m (base+arrayPayloadOffset k+i.val*32))) m base = m
      cases k with
      | none =>
        change dynamicUintView (mload m base).val _ (fun i => mload m (base+32+i.val*32)) m base = m
        exact arraySnapshot_reencode none _ _ m base rfl
      | some size => exact decodeStaticUint_reencode size m base
    · cases prepared
  · cases prepared

theorem snapshot_encode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (bound : n<2^256)
    (old : Fin n → Source.Val E.layout (.udvt name)) (m : ByteView) (base : Nat)
    (declared : NominalMemory.declaredUDVT E name=true)
    (supported : FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name))
    (header : arrayLengthChoice k m base=n)
    (encoded : ∀ i,(old i).word=some (mload m (base+arrayPayloadOffset k+i.val*32))) :
    (snapshot p name k m base).map InventoryObject.data =
      some (memberArrayData E.layout (.udvt name) k n hl old) := by
  first
  | solve | simp only [snapshot,declared,header]
  | solve | decide
  | solve | omega
  | solve | rfl
  | cases header
    unfold snapshot
    simp only [declared,↓reduceIte]
    rw [dif_pos bound,Option.pmap_some' (FixedNominalMemory.array_decode_encode E.layout name supported _ m _ old encoded)]
    rfl

theorem decode_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat)
    (o : InventoryObject p τ) (prepared : decode p es τ m base=some o) :
    o.image.encode m base=m := by
  unfold decode at prepared
  split at prepared <;> first
    | exact snapshot_raw p _ _ m base o prepared
    | exact FixedInventory.decode_raw p es _ m base o prepared

theorem update_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (e : MixedHeapEntry p) (m : ByteView) (u : OwnedInventoryUpdate allocated p)
    (prepared : update allocated p es e m=some u) :
    u.object.image.encode m (p.address u.entry.id)=m := by
  unfold update at prepared
  cases dec : decode p es e.ty m (p.address e.id) with
  | none => rw [dec] at prepared; cases prepared
  | some o =>
    rw [dec] at prepared
    change (if fits : o.shape.size ≤ (allocated.shape e.id).size then some ⟨e,o,fits⟩ else none)=some u at prepared
    split at prepared
    · cases prepared; exact decode_raw p es e.ty m _ o dec
    · cases prepared

theorem updates_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p))
    (prepared : updates allocated p es entries m=some us) :
    ∀ u ∈ us, u.object.image.encode m (p.address u.entry.id)=m := by
  induction entries generalizing us with
  | nil => cases prepared; intro u member; cases member
  | cons e entries ih =>
    unfold updates at prepared
    cases one : update allocated p es e m with
    | none => rw [one] at prepared; cases prepared
    | some u =>
      cases tail : updates allocated p es entries m with
      | none => rw [one,tail] at prepared; cases prepared
      | some rest =>
        rw [one,tail] at prepared
        cases prepared
        intro v member
        rcases List.mem_cons.mp member with same | later
        · subst v; exact update_raw allocated p es e m u one
        · exact ih rest tail v later

theorem reencode_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p))
    (prepared : updates allocated p es entries m=some us) : reencodeInventory us m=m := by
  have all := updates_raw allocated p es entries m us prepared
  clear prepared
  induction us with
  | nil => rfl
  | cons u rest ih =>
    rw [reencodeInventory,ih (fun v member => all v (List.mem_cons_of_mem _ member))]
    exact all u List.mem_cons_self

theorem writeback_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (prepared : writeback s allocated p history es m = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp prepared
  subst result
  exact runInventoryUpdates_MemOK us H s (fun u _ => u.object.image.dataOK) ok

end Solidity.Yul.Views.FixedNominalInventory
