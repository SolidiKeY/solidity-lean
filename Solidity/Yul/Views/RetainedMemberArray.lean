import Solidity.Yul.Views.MemberArray

/-! Actual retained ordinary allocations for canonical array-member families.
The original allocated region remains owned through typed write lineage; the
CURRENT shape always reflects the decoded current length. No gap/free-derived
capacity, decoder cap, dirty cleanup, or full-Yul writeback claim. -/
namespace Solidity.Yul.Views

def dynamicMemberData (D : Source.Layout) (τ : Source.STy) (n : Nat) (values : Fin n → Source.Val D τ) :=
  memberArrayData D τ none n (fun _ e => nomatch e) values

def retainedMemberArrayHeap {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (_history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (MemoryShape.array true (mload m (current.address root)).val).size ≤ (allocated.shape root).size then
    (decodeArrayMembers current es τ (mload m (current.address root)).val m (current.address root + 32)).map
      (fun values => h.write root (dynamicMemberData D τ _ values) (heap_ty_of_get h root _ _ found))
  else none

def retainedMemberArrayState {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (_history : RetainedAllocation allocated current) (es : List (MixedHeapEntry current))
    (root : Nat) (τ : Source.STy) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if (MemoryShape.array true (mload m (current.address root)).val).size ≤ (allocated.shape root).size then
    (decodeArrayMembers current es τ (mload m (current.address root)).val m (current.address root + 32)).map
      (fun values => (Source.heapPut root ⟨_, dynamicMemberData E.layout τ _ values⟩).run s)
  else none

def retainedMemberArrayPlacement {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩)
    (k : Nat) (values : Fin k → Source.Val D τ) (capacity : (MemoryShape.array true k).size ≤ (allocated.shape root).size) :
    Placement (h.write root (dynamicMemberData D τ k values) (heap_ty_of_get h root _ _ found)) :=
  retainedWritePlacement allocated current history root _ _ (.array true k) (.array _ _ _) capacity

theorem retainedMemberArray_history {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩)
    (k : Nat) (values : Fin k → Source.Val D τ) (capacity : (MemoryShape.array true k).size ≤ (allocated.shape root).size) :
    RetainedAllocation allocated (retainedMemberArrayPlacement allocated current history root τ n old found k values capacity) :=
  retainWritten allocated current history root _ _ (.array true k) (.array _ _ _) capacity

theorem retainedMemberArray_success {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩) (m : ByteView) (out : Source.Heap D)
    (step : retainedMemberArrayHeap h allocated current history es root τ n old found m = some out) :
    (MemoryShape.array true (mload m (current.address root)).val).size ≤ (allocated.shape root).size ∧
    ∃ values, decodeArrayMembers current es τ (mload m (current.address root)).val m (current.address root + 32) = some values ∧
      out = h.write root (dynamicMemberData D τ _ values) (heap_ty_of_get h root _ _ found) := by
  unfold retainedMemberArrayHeap at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    exact ⟨‹_›, values, decoded, same.symm⟩
  · cases step

theorem retainedMemberArray_result {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩) (m : ByteView) (out : Source.Heap D)
    (step : retainedMemberArrayHeap h allocated current history es root τ n old found m = some out) :
    ∃ q : Placement out, RetainedAllocation allocated q ∧ q.address = current.address ∧ q.free = current.free ∧
      q.shape root = .array true (mload m (current.address root)).val ∧ ∀ a, a ≠ root → q.shape a = current.shape a := by
  obtain ⟨capacity, values, decoded, same⟩ := retainedMemberArray_success h allocated current history es root τ n old found m out step
  subst out
  refine ⟨retainedMemberArrayPlacement allocated current history root τ n old found _ values capacity,
    retainedMemberArray_history allocated current history root τ n old found _ values capacity, rfl, rfl, ?_, ?_⟩
  · simp only [retainedMemberArrayPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_true]
  · intro a ha
    simp only [retainedMemberArrayPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_neg ha]

theorem retainedMemberArray_preservation {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy) (n : Nat) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩) (m : ByteView) (out : Source.Heap D)
    (step : retainedMemberArrayHeap h allocated current history es root τ n old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ (∀ a, h.next ≤ a → out.cells a = none) ∧ ∀ a, a ≠ root → out.get a = h.get a := by
  obtain ⟨capacity, values, decoded, same⟩ := retainedMemberArray_success h allocated current history es root τ n old found m out step
  subst out
  exact ⟨funext (fun a => Source.Heap.write_ty _ _ a _ _), rfl,
    fun a ha => (h.write root _ _).bounded a ha, fun a ha => Source.Heap.write_other _ ha _ _⟩

theorem retainedMemberArray_MemOK (E : Source.Env) {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (history : RetainedAllocation allocated current) (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : retainedMemberArrayState s allocated current history es root τ m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold retainedMemberArrayState at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    subst result
    exact memberArrayHeapPut_MemOK E H s current root τ none _ _ values _
      (decodeArrayMembers_sound current es τ _ m _ values decoded) ok
  · cases step

theorem retainedMemberArray_encode {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (old : Fin n → Source.Val D τ) (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩)
    (k : Nat) (bound : k < 2 ^ 256) (values : Fin k → Source.Val D τ) (words : Fin k → Roadmap.Word)
    (encoded : ∀ i, MemoryElement current (values i) (words i)) (capacity : (MemoryShape.array true k).size ≤ (allocated.shape root).size)
    (m : ByteView) : retainedMemberArrayHeap h allocated current history es root τ n old found (dynamicUintView k bound words m (current.address root)) =
      some (h.write root (dynamicMemberData D τ k values) (heap_ty_of_get h root _ _ found)) := by
  unfold retainedMemberArrayHeap
  rw [dynamicUint_header]
  simp only [if_pos capacity]
  rw [decodeArrayMembers_reads current es coverage τ supported k values words encoded _ _ (dynamicUint_element k bound words m (current.address root))]
  rfl

theorem retainedMemberArray_unchanged {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (old : Fin n → Source.Val D τ) (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩)
    (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement current (old i) (words i)) (m : ByteView)
    (header : (mload m (current.address root)).val = n) (reads : ∀ i, mload m (current.address root + 32 + i.val * 32) = words i) :
    retainedMemberArrayHeap h allocated current history es root τ n old found m = some h := by
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have capacity := history.fits root present
  rw [memberArray_shape h current root τ none n _ old found] at capacity
  change (MemoryShape.array true n).size ≤ (allocated.shape root).size at capacity
  subst n
  unfold retainedMemberArrayHeap
  rw [if_pos capacity, decodeArrayMembers_reads current es coverage τ supported _ old words encoded _ _ reads]
  simp only [Option.map_some, heap_write_unchanged h root _ _ found]

theorem retainedMemberArrayState_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (old : Fin n → Source.Val E.layout τ) (found : s.2.heap.get root = some ⟨_, dynamicMemberData E.layout τ n old⟩)
    (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement current (old i) (words i)) (m : ByteView)
    (header : (mload m (current.address root)).val = n) (reads : ∀ i, mload m (current.address root + 32 + i.val * 32) = words i) :
    retainedMemberArrayState s allocated current history es root τ m = some (.ok (), s) := by
  have present : (s.2.heap.cells root).isSome := by change (s.2.heap.get root).isSome = true; rw [found]; rfl
  have capacity := history.fits root present
  rw [memberArray_shape s.2.heap current root τ none n _ old found] at capacity
  change (MemoryShape.array true n).size ≤ (allocated.shape root).size at capacity
  subst n
  unfold retainedMemberArrayState
  rw [if_pos capacity, decodeArrayMembers_reads current es coverage τ supported _ old words encoded _ _ reads]
  simp only [Option.map_some]
  unfold dynamicMemberData at found ⊢
  rw [memberArrayHeapPut_run s root τ none _ _ old (heap_ty_of_get s.2.heap root _ _ found),
    heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

theorem retainedMemberArray_other_region {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (root other : Nat) (hr : (h.cells root).isSome) (ho : (h.cells other).isSome) (distinct : root ≠ other)
    (k : Nat) (bound : k < 2 ^ 256) (words : Fin k → Roadmap.Word)
    (capacity : (MemoryShape.array true k).size ≤ (allocated.shape root).size) (m : ByteView) (off : Nat) (inside : off < (allocated.shape other).size) :
    dynamicUintView k bound words m (current.address root) (current.address other + off) = m (current.address other + off) := by
  have sep := (retainedByte_full_separation allocated current history root other hr ho distinct).2.2
  change 32 + k * 32 ≤ (allocated.shape root).size at capacity
  apply dynamicUint_residual
  omega

theorem retainedMemberArray_raw_reencode (m : ByteView) (base : Nat) :
    dynamicUintView (mload m base).val (mload m base).isLt (fun i => mload m (base + 32 + i.val * 32)) m base = m :=
  decodeDynamicUint_reencode m base

end Solidity.Yul.Views
