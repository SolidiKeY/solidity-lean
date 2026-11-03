import Solidity.Yul.Views.NominalMemory

/-! Canonical nominal dynamic arrays within their actual retained allocation.
Current shapes describe current data; original capacity and full-region ownership
come from RetainedAllocation, never gaps or a free pointer. Unsupported decoding
is preparation None, not source/Yul failure, cleaning or deallocation. -/
namespace Solidity.Yul.Views.NominalMemory

def retainedState {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (_history : RetainedAllocation allocated current) (root : Nat) (name : Source.DeclName)
    (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if declaredUDVT E name then
    if (MemoryShape.array true (mload m (current.address root)).val).size ≤ (allocated.shape root).size then
      (decodeArray E.layout name (mload m (current.address root)).val m (current.address root+32)).map
        (fun values => (Source.heapPut root ⟨_,dynamicMemberData E.layout (.udvt name) _ values⟩).run s)
    else none
  else none

/-- Real old typed contents force successful source writeback after preparation;
capacity and decoded values are derived from that actual preparation. -/
theorem retainedState_write {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (history : RetainedAllocation allocated current) (root : Nat) (name : Source.DeclName)
    (n : Nat) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,dynamicMemberData E.layout (.udvt name) n old⟩)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : retainedState s allocated current history root name m=some result) :
    ∃ values : Fin (mload m (current.address root)).val → Source.Val E.layout (.udvt name),
      (MemoryShape.array true (mload m (current.address root)).val).size ≤ (allocated.shape root).size ∧
      decodeArray E.layout name (mload m (current.address root)).val m (current.address root+32)=some values ∧
      result=(.ok (),withSourceHeap s (s.2.heap.write root
        (dynamicMemberData E.layout (.udvt name) _ values) (heap_ty_of_get s.2.heap root _ _ found))) := by
  unfold retainedState at step
  split at step
  · split at step
    · rename_i capacity
      obtain ⟨values,decoded,same⟩ := Option.map_eq_some_iff.mp step
      unfold dynamicMemberData at same
      rw [memberArrayHeapPut_run s root (.udvt name) none _ (fun _ h => nomatch h) values
        (heap_ty_of_get s.2.heap root _ _ found)] at same
      exact ⟨values,capacity,decoded,same.symm⟩
    · cases step
  · cases step

/-- Current shape follows the new length while the real original retained
region survives, including tail words no longer in the current live payload. -/
theorem retainedState_placement {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (history : RetainedAllocation allocated current) (root : Nat) (name : Source.DeclName)
    (n : Nat) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,dynamicMemberData E.layout (.udvt name) n old⟩)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : retainedState s allocated current history root name m=some result) :
    (∃ q : Placement result.2.2.heap, RetainedAllocation allocated q ∧
      q.address=current.address ∧ q.free=current.free ∧
      q.shape root=.array true (mload m (current.address root)).val ∧
      ∀ a,a≠root → q.shape a=current.shape a) ∧
    result.2.2.heap.ty=s.2.heap.ty ∧ result.2.2.heap.next=s.2.heap.next ∧
    ∀ a,a≠root → result.2.2.heap.get a=s.2.heap.get a := by
  obtain ⟨values,capacity,decoded,same⟩ := retainedState_write s allocated current history root name n old found m result step
  subst result
  refine ⟨⟨retainedMemberArrayPlacement allocated current history root (.udvt name) n old found _ values capacity,
    retainedMemberArray_history allocated current history root (.udvt name) n old found _ values capacity,
    rfl,rfl,?_,?_⟩,?_,rfl,?_⟩
  · simp only [retainedMemberArrayPlacement,retainedWritePlacement,retainedGeometryWritePlacement,if_true]
  · intro a ha
    simp only [retainedMemberArrayPlacement,retainedWritePlacement,retainedGeometryWritePlacement,if_neg ha]
  · exact funext (fun a => Source.Heap.write_ty s.2.heap root a
      (dynamicMemberData E.layout (.udvt name) _ values) (heap_ty_of_get s.2.heap root _ _ found))
  · intro a ha
    exact Source.Heap.write_other s.2.heap ha (dynamicMemberData E.layout (.udvt name) _ values)
      (heap_ty_of_get s.2.heap root _ _ found)

/-- Every original heap typing survives the complete actual source outcome,
including an actual type-error halt. Preparation None remains separate. -/
theorem retainedState_MemOK (E : Source.Env) {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (current : Placement s.2.heap) (history : RetainedAllocation allocated current)
    (root : Nat) (name : Source.DeclName) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : retainedState s allocated current history root name m=some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold retainedState at step
  split at step
  · split at step
    · obtain ⟨values,decoded,same⟩ := Option.map_eq_some_iff.mp step
      subst result
      exact memberArrayHeapPut_MemOK E H s current root (.udvt name) none _
        (fun _ h => nomatch h) values _
        (fun i => .scalar _ _ (array_word E.layout name _ m _ values decoded i)) ok
    · cases step
  · cases step

/-- Unchanged canonical snapshots preserve the entire administrative source
state. Current capacity is derived from the actual retained history. -/
theorem retainedState_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (history : RetainedAllocation allocated current) (root : Nat) (name : Source.DeclName)
    (n : Nat) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,dynamicMemberData E.layout (.udvt name) n old⟩)
    (m : ByteView) (declared : declaredUDVT E name=true)
    (supported : CanonicalScalarType E.layout (E.layout.underlying name))
    (header : (mload m (current.address root)).val=n)
    (encoded : ∀ i,(old i).word=some (mload m (current.address root+32+i.val*32))) :
    retainedState s allocated current history root name m=some (.ok (),s) := by
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome=true; rw [found]; rfl
  have capacity := history.fits root present
  rw [memberArray_shape s.2.heap current root (.udvt name) none n _ old found] at capacity
  change (MemoryShape.array true n).size ≤ (allocated.shape root).size at capacity
  subst n
  unfold retainedState
  simp only [declared,↓reduceIte]
  rw [if_pos capacity,array_decode_encode E.layout name supported _ m _ old encoded]
  simp only [Option.map_some]
  unfold dynamicMemberData
  rw [memberArrayHeapPut_run s root (.udvt name) none _ (fun _ h => nomatch h) old (heap_ty_of_get s.2.heap root _ _ found)]
  have sameHeap := heap_write_unchanged s.2.heap root _ _ found
  unfold dynamicMemberData at sameHeap
  rw [sameHeap,withSourceHeap_unchanged]

end Solidity.Yul.Views.NominalMemory
