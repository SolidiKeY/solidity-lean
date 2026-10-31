import Solidity.Yul.Views.JointPlacement

namespace Solidity.Yul.Views

/-- Retained capacity comes ONLY from the supplied actual allocation lineage.
The new header, including zero/regrowth, is decoded without an arbitrary cap. -/
def canonicalJointRetainedState {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (_history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (a : Nat) (name : Source.DeclName) (b : Nat) (τ : Source.STy) (reverse : Bool) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if (MemoryShape.array true (mload m (p.address b)).val).size ≤ (allocated.shape b).size then
    canonicalJointState s p es a name b τ none (mload m (p.address b)).val (fun _ eq => nomatch eq) reverse m
  else none

theorem canonicalJointRetained_header {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (a : Nat) (name : Source.DeclName) (b : Nat) (τ : Source.STy) (reverse : Bool) (m : ByteView)
    (n : Nat) (header : (mload m (p.address b)).val = n)
    (capacity : (MemoryShape.array true n).size ≤ (allocated.shape b).size) :
    canonicalJointRetainedState s allocated p history es a name b τ reverse m =
      canonicalJointState s p es a name b τ none n (fun _ e => nomatch e) reverse m := by
  unfold canonicalJointRetainedState
  simp only [header, if_pos capacity]

theorem canonicalJointRetained_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (a : Nat) (name : Source.DeclName) (b : Nat) (τ : Source.STy) (reverse : Bool) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : canonicalJointRetainedState s allocated p history es a name b τ reverse m = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold canonicalJointRetainedState at step
  split at step
  · exact canonicalJoint_MemOK H s p es a name b τ none _ _ reverse m result step ok
  · cases step

theorem canonicalJointRetained_order {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (a : Nat) (name : Source.DeclName) (b : Nat) (τ : Source.STy)
    (ha : s.2.heap.ty a = some (.struct .memory name)) (hb : s.2.heap.ty b = some (.array .memory τ none))
    (distinct : a ≠ b) (m : ByteView) :
    canonicalJointRetainedState s allocated p history es a name b τ false m = canonicalJointRetainedState s allocated p history es a name b τ true m := by
  unfold canonicalJointRetainedState
  split
  · exact canonicalJoint_order s p es a name b τ none _ _ ha hb distinct m
  · rfl

/-- Construct the exact current shape, retained full original extents, actual
updated images and complete candidate inventory after the TWO writes. -/
theorem canonicalJointRetained_geometry {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (a : Nat) (name : Source.DeclName) (oldfs fs : Source.DataList E.layout (E.layout.fields name))
    (fa : h.get a = some ⟨.struct .memory name,.struct oldfs⟩)
    (b : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val E.layout τ)
    (fb : h.get b = some ⟨_,dynamicMemberData E.layout τ n old⟩) (distinct : a ≠ b)
    (m : ByteView) (df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) = some fs)
    (values : Fin (mload m (p.address b)).val → Source.Val E.layout τ)
    (da : decodeCanonicalArray p es τ _ m (p.address b + 32) = some values)
    (capacity : (MemoryShape.array true (mload m (p.address b)).val).size ≤ (allocated.shape b).size) :
    let out := pairWrittenHeap h a (.struct fs) (heap_ty_of_get h a _ _ fa) b
      (dynamicMemberData E.layout τ _ values) (heap_ty_of_get h b _ _ fb)
    ∃ q : Placement out, RetainedAllocation allocated q ∧ q.address = p.address ∧ q.free = p.free ∧
      q.shape b = .array true (mload m (p.address b)).val ∧
      (∀ c, c ≠ b → q.shape c = p.shape c) ∧
      ∃ entries : List (MixedHeapEntry q), CoversMixedHeap entries ∧
        ∀ υ w, decodeExtendedMemoryMember q entries υ w = decodeExtendedMemoryMember p es υ w := by
  obtain ⟨ws, fields, reads⟩ := decodeCanonicalFields_representation p es _ m _ fs df
  let ha := heap_ty_of_get h a _ _ fa
  let sx := struct_shape_write h p a name oldfs fs fa
  let p1 := heapWritePlacement h p a (.struct fs) ha sx
  have history1 : RetainedAllocation allocated p1 := retainSameShapeWrite allocated p history a (.struct fs) ha sx
  have fb1 : (h.write a (.struct fs) ha).get b = some ⟨_,dynamicMemberData E.layout τ n old⟩ :=
    (Source.Heap.write_other h (Ne.symm distinct) (.struct fs) ha).trans fb
  let size := (mload m (p.address b)).val
  let p2 := retainedMemberArrayPlacement allocated p1 history1 b τ n old fb1 size values capacity
  have history2 : RetainedAllocation allocated p2 := retainedMemberArray_history allocated p1 history1 b τ n old fb1 size values capacity
  have types1 : (h.write a (.struct fs) ha).ty = h.ty := funext (fun c => Source.Heap.write_ty h a c (.struct fs) ha)
  have types2 : (pairWrittenHeap h a (.struct fs) ha b (dynamicMemberData E.layout τ size values) (heap_ty_of_get h b _ _ fb)).ty = h.ty :=
    (pairWritten_preserves h a (.struct fs) ha b _ (heap_ty_of_get h b _ _ fb)).1
  let ix : MemoryImage p1 (.struct (l := .memory) fs) := .words _ ws (.strct fs ws (fields.transport p1 types1 rfl))
  let es1 := refreshMixedEntries p a (.struct fs) ha p1 rfl ix es
  let iy : MemoryImage p2 (dynamicMemberData E.layout τ size values) := .words _ _
    (.array (n := none) size (fun _ eq => nomatch eq) (mload m (p.address b)).isLt values
      (fun i => mload m (p.address b + 32 + i.val * 32))
      (fun i => (decodeCanonicalArray_sound p es τ size m _ values da i).transport p2 types2 rfl))
  let es2 := refreshMixedEntries p1 b (dynamicMemberData E.layout τ size values) _ p2 rfl iy es1
  refine ⟨p2, history2, rfl, rfl, ?_, ?_, es2, ?_, ?_⟩
  · change (if b = b then MemoryShape.array true size else p.shape b) = _
    rw [if_pos rfl]
  · intro c cb
    change (if c = b then MemoryShape.array true size else p.shape c) = _
    rw [if_neg cb]
  · exact refreshMixedEntries_coverage _ _ _ _ _ _ _ _ (refreshMixedEntries_coverage p a (.struct fs) ha p1 rfl ix es coverage)
  · intro υ w
    unfold es2 es1
    rw [decodeExtended_refresh, decodeExtended_refresh]

end Solidity.Yul.Views
