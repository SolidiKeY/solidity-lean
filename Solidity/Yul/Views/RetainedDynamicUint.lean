import Solidity.Yul.Views.DynamicUintMemory
import Solidity.Yul.Views.RetainedAllocation

/-! Dynamic full-width array resizing against an actual retained allocation.
Current shape changes; original ownership is retained by typed write lineage. -/
namespace Solidity.Yul.Views

def retainedDynamicUintWriteback {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (_r : RetainedAllocation allocated current)
    (a : Nat) (n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), dynamicUintData D n old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (MemoryShape.array true (mload m (current.address a)).val).size ≤ (allocated.shape a).size then
    some (h.write a (decodeDynamicUint D m (current.address a)) (heap_ty_of_get h a _ _ found))
  else none

theorem retainedDynamicUint_success {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedDynamicUintWriteback h allocated current r a n old found m = some out) :
    (MemoryShape.array true (mload m (current.address a)).val).size ≤ (allocated.shape a).size ∧
    out = h.write a (decodeDynamicUint D m (current.address a)) (heap_ty_of_get h a _ _ found) := by
  unfold retainedDynamicUintWriteback at e
  split at e
  · exact ⟨‹_›, (Option.some.inj e).symm⟩
  · cases e

def retainedDynamicUintResultPlacement {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedDynamicUintWriteback h allocated current r a n old found m = some out) : Placement out :=
  (retainedDynamicUint_success h allocated current r a n old found m out e).2.symm ▸
    retainedWritePlacement allocated current r a _ _ (.array true (mload m (current.address a)).val)
      (HasMemoryShape.array _ _ _)
      (retainedDynamicUint_success h allocated current r a n old found m out e).1

theorem retainedDynamicUint_result_history {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedDynamicUintWriteback h allocated current r a n old found m = some out) :
    RetainedAllocation allocated (retainedDynamicUintResultPlacement h allocated current r a n old found m out e) := by
  have he := (retainedDynamicUint_success h allocated current r a n old found m out e).2
  subst out
  exact retainWritten allocated current r a _ _ (.array true (mload m (current.address a)).val)
    (HasMemoryShape.array _ _ _)
    (retainedDynamicUint_success h allocated current r a n old found m _ e).1

theorem retainedDynamicUint_preservation {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedDynamicUintWriteback h allocated current r a n old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ (∀ b, h.next ≤ b → out.cells b = none) ∧
    (∀ b, b ≠ a → out.get b = h.get b) ∧
    out.get a = some ⟨(.array .memory (.int Source.IntTy.u256) none), decodeDynamicUint D m (current.address a)⟩ := by
  rw [(retainedDynamicUint_success h allocated current r a n old found m out e).2]
  exact ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl,
    fun b hb => (h.write a _ _).bounded b hb,
    fun b hb => Source.Heap.write_other _ hb _ _, Source.Heap.write_get _ _ _ _⟩


theorem retainedDynamicUint_encode {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (k : Nat) (bound : k < 2 ^ 256) (words : Fin k → Roadmap.Word)
    (capacity : (MemoryShape.array true k).size ≤ (allocated.shape a).size) (m : ByteView) :
    retainedDynamicUintWriteback h allocated current r a n old found (dynamicUintView k bound words m (current.address a)) =
      some (h.write a (dynamicUintData D k words) (heap_ty_of_get h a _ _ found)) := by
  simp only [retainedDynamicUintWriteback, dynamicUint_header, if_pos capacity]
  rw [decodeDynamicUint_encode]

theorem retainedDynamicUint_compat {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a n : Nat) (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (step : dynamicUintWriteback h current a n old found m = some out) :
    retainedDynamicUintWriteback h allocated current r a n old found m = some out := by
  have e := dynamicUintWriteback_success h current a n old found m out step
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have capacity := r.fits a present
  rw [dynamicUint_shape h current a n old found, ← e.1] at capacity
  simp only [retainedDynamicUintWriteback, if_pos capacity]
  rw [e.2]

theorem retainedDynamicUint_unchanged {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a n : Nat) (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (m : ByteView) (header : (mload m (current.address a)).val = n)
    (reads : ∀ i, mload m (current.address a + 32 + i.val * 32) = old i) :
    retainedDynamicUintWriteback h allocated current r a n old found m = some h :=
  retainedDynamicUint_compat h allocated current r a n old found m h
    (dynamicUintWriteback_unchanged h current a n old found m header reads)

def retainedDynamicUintStateWriteback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (r : RetainedAllocation allocated current) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, dynamicUintData E.layout n old⟩) (m : ByteView) : Option (Source.EMState E Γ) :=
  (retainedDynamicUintWriteback s.2.heap allocated current r a n old found m).map (withSourceHeap s)

theorem retainedDynamicUintState_MemOK (E : Source.Env) {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s out : Source.EMState E Γ) (allocated : Placement origin)
    (current : Placement s.2.heap) (r : RetainedAllocation allocated current)
    (a n : Nat) (old : Fin n → Roadmap.Word) (found : s.2.heap.get a = some ⟨_, dynamicUintData E.layout n old⟩)
    (m : ByteView) (step : retainedDynamicUintStateWriteback s allocated current r a n old found m = some out)
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨heap, wrote, same⟩ := Option.map_eq_some_iff.mp step
  subst out
  rw [(retainedDynamicUint_success s.2.heap allocated current r a n old found m heap wrote).2]
  exact dynamicUint_write_MemOK E H s a _ _ _ ok

theorem retainedDynamicUint_choices {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a n : Nat) (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (step : retainedDynamicUintWriteback h allocated current r a n old found m = some out) :
    let q := retainedDynamicUintResultPlacement h allocated current r a n old found m out step
    q.address = current.address ∧ q.free = current.free ∧ q.shape a = .array true (mload m (current.address a)).val ∧
      ∀ b, b ≠ a → q.shape b = current.shape b := by
  have he := (retainedDynamicUint_success h allocated current r a n old found m out step).2
  subst out
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [retainedDynamicUintResultPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_true]
  · intro b hb
    simp only [retainedDynamicUintResultPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_neg hb]

theorem retainedDynamicUint_other_region {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a b : Nat) (ha : (h.cells a).isSome) (hb : (h.cells b).isSome) (distinct : a ≠ b)
    (k : Nat) (bound : k < 2 ^ 256) (words : Fin k → Roadmap.Word)
    (capacity : (MemoryShape.array true k).size ≤ (allocated.shape a).size)
    (m : ByteView) (off : Nat) (hoff : off < (allocated.shape b).size) :
    dynamicUintView k bound words m (current.address a) (current.address b + off) = m (current.address b + off) := by
  have sep := (retainedByte_full_separation allocated current r a b ha hb distinct).2.2
  apply dynamicUint_residual
  change 32 + k * 32 ≤ (allocated.shape a).size at capacity
  omega

end Solidity.Yul.Views
