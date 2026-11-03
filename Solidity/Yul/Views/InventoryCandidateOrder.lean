import Solidity.Yul.Views.InventoryDecodeOrder

/-! Candidate lookup order is immaterial for actual typed owned entries:
Placement uniqueness forces every match for one pointer word to name the same
logical object. This does not manufacture missing ownership or accept interior
pointers. Candidate permutations then compose with real visit-order transport. -/
namespace Solidity.Yul.Views

theorem decodeMemoryPointer_perm {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs) (τ : Source.STy)
    (loc : τ.loc?=some .memory) (word : Roadmap.Word) :
    decodeMemoryPointer p es τ loc word=decodeMemoryPointer p fs τ loc word := by
  have present (e : MixedHeapEntry p) : (h.cells e.id).isSome := by
    change (h.get e.id).isSome=true
    rw [e.found]
    rfl
  unfold decodeMemoryPointer
  cases first : es.find? (pointerCandidate τ word) with
  | none =>
    have second : fs.find? (pointerCandidate τ word)=none := by
      apply List.find?_eq_none.mpr
      intro e member
      exact (List.find?_eq_none.mp first) e (perm.mem_iff.mpr member)
    rw [second]
  | some e =>
    have member := List.mem_of_find?_eq_some first
    have yes := List.find?_some first
    cases second : fs.find? (pointerCandidate τ word) with
    | none => exact False.elim ((List.find?_eq_none.mp second) e (perm.mem_iff.mp member) yes)
    | some f =>
      have other := List.find?_some second
      have ep : e.ty.memShape=τ.memShape ∧ p.address e.id=word.val := of_decide_eq_true yes
      have fp : f.ty.memShape=τ.memShape ∧ p.address f.id=word.val := of_decide_eq_true other
      have ids := p.distinct e.id f.id (present e) (present f) (ep.2.trans fp.2.symm)
      simp only [Option.map_some,ids]

theorem decodeMemoryMember_perm {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs) (τ : Source.STy) (word : Roadmap.Word) :
    decodeMemoryMember p es τ word=decodeMemoryMember p fs τ word := by
  unfold decodeMemoryMember
  split
  · exact decodeMemoryPointer_perm p es fs perm τ _ word
  · rfl

theorem decodeExtendedMemoryMember_perm {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs) (τ : Source.STy) (word : Roadmap.Word) :
    decodeExtendedMemoryMember p es τ word=decodeExtendedMemoryMember p fs τ word := by
  unfold decodeExtendedMemoryMember
  cases scalar : decodeCanonicalScalar D τ word with
  | none => exact decodeMemoryMember_perm p es fs perm τ word
  | some v => rfl

theorem decodeInventoryObject_candidates {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs) (τ : Source.STy) (m : ByteView) (base : Nat) :
    decodeInventoryObject p es τ m base=decodeInventoryObject p fs τ m base := by
  have transport := decodeInventoryObject_transport p p rfl rfl fs es
    (fun τ w=>decodeExtendedMemoryMember_perm p es fs perm τ w) τ m base
  have identity : InventoryObject.transport p rfl rfl (τ:=τ)=id := by
    funext o
    rcases o with ⟨data,shape,shaped,image⟩
    cases image <;> rfl
  rw [identity,Option.map_id] at transport
  exact transport

theorem decodeInventoryUpdate_candidates {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es fs : List (MixedHeapEntry p))
    (perm : es.Perm fs) (e : MixedHeapEntry p) (m : ByteView) :
    decodeInventoryUpdate allocated p es e m=decodeInventoryUpdate allocated p fs e m := by
  unfold decodeInventoryUpdate
  rw [decodeInventoryObject_candidates p es fs perm]

theorem decodeInventoryUpdates_candidates {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es fs : List (MixedHeapEntry p))
    (perm : es.Perm fs) (entries : List (MixedHeapEntry p)) (m : ByteView) :
    decodeInventoryUpdates allocated p es entries m=decodeInventoryUpdates allocated p fs entries m := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    rw [decodeInventoryUpdates,decodeInventoryUpdates,
      decodeInventoryUpdate_candidates allocated p es fs perm e m,ih]

/-- Reorder BOTH candidates and visits at the actual existing entrypoint.
Exact Option equality retains unsupported preparation; complete Source equality
uses genuine distinct roots and derives all candidate decoder agreements. -/
theorem inventoryStateWriteback_perm {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    inventoryStateWriteback s allocated p history es m=inventoryStateWriteback s allocated p history fs m := by
  unfold inventoryStateWriteback
  rw [decodeInventoryUpdates_candidates allocated p es fs perm es m]
  exact decodedInventory_runs_perm allocated p fs perm distinct m s rfl
/-- The actual sequential implementation may reorder its INITIAL candidates
and visit roots together; every subsequent dependent refresh is still real. -/
theorem inventoryStateWriteback_sequential_candidates_perm {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es fs : List (MixedHeapEntry p)) (perm : es.Perm fs)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    inventoryStateWriteback s allocated p history es m=
      (sequentialInventory allocated p history fs s.2.heap p history rfl fs m).map
        (fun realized=>((.ok () : Except Source.Halt Unit),withSourceHeap s realized.heap)) :=
  (inventoryStateWriteback_perm s allocated p history es fs perm distinct m).trans
    (inventoryStateWriteback_sequential s allocated p history fs m)
end Solidity.Yul.Views

