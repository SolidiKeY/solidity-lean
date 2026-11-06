import Solidity.Yul.Views.StaticUintMemory

/-! Dynamic uint256 objects, with actual length header and word elements.
The fixed-length API keeps its header guard; retained resizing is separate.
No artificial decoder/length/fuel bound or dirty-bit cleanup. -/
namespace Solidity.Yul.Views

def dynamicUintData (D : Source.Layout) (n : Nat) (words : Fin n → Roadmap.Word) :
    Source.Data D (.array .memory (.int Source.IntTy.u256) none) :=
  .array n (fun _ e => nomatch e) (fun i => .val (uintValueOfWord D (words i)))

def dynamicUintView (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word)
    (m : ByteView) (base : Nat) : ByteView :=
  mstore (wordListView (List.ofFn words) m (base + 32)) base ⟨n, bound⟩

def decodeDynamicUint (D : Source.Layout) (m : ByteView) (base : Nat) :=
  dynamicUintData D (mload m base).val (fun i => mload m (base + 32 + i.val * 32))

theorem dynamicUint_header (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat) :
    mload (dynamicUintView n bound words m base) base = ⟨n, bound⟩ := mload_mstore _ _ _

theorem dynamicUint_element (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView)
    (base : Nat) (i : Fin n) : mload (dynamicUintView n bound words m base) (base + 32 + i.val * 32) = words i := by
  unfold dynamicUintView
  rw [mload_congr _ (wordListView (List.ofFn words) m (base + 32)) _
    (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
  apply wordList_read
  rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
  simp only [List.getElem_ofFn]

theorem decodeDynamicUint_encode (D : Source.Layout) (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word)
    (m : ByteView) (base : Nat) : decodeDynamicUint D (dynamicUintView n bound words m base) base = dynamicUintData D n words := by
  unfold decodeDynamicUint
  rw [dynamicUint_header]
  apply congrArg (dynamicUintData D n)
  funext i
  exact dynamicUint_element n bound words m base i

theorem decodeDynamicUint_reencode (m : ByteView) (base : Nat) :
    dynamicUintView (mload m base).val (mload m base).isLt
      (fun i => mload m (base + 32 + i.val * 32)) m base = m := by
  unfold dynamicUintView
  rw [decodeStaticUint_reencode]
  exact mstore_mload m base

theorem dynamicUint_residual (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView)
    (base pos : Nat) (outside : pos < base ∨ base + 32 + n * 32 ≤ pos) : dynamicUintView n bound words m base pos = m pos := by
  rw [dynamicUintView, mstore_outside _ _ _ _ (by omega)]
  apply wordList_residual
  simp only [List.length_ofFn]
  omega

theorem dynamicUint_reserved (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView)
    (base : Nat) (free : Roadmap.Word) (start : 128 ≤ base) (reserved : ReservedOK m free) :
    ReservedOK (dynamicUintView n bound words m base) free := by
  constructor
  · have eq := mload_congr (dynamicUintView n bound words m base) m 64 (fun i => dynamicUint_residual _ _ _ _ _ _ (Or.inl (by have hi := i.isLt; omega)))
    exact (congrArg Fin.val eq).trans reserved.1
  · intro i
    rw [dynamicUint_residual _ _ _ _ _ _ (Or.inl (by have hi := i.isLt; omega))]
    exact reserved.2 i

theorem dynamicUint_shape {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩) : p.shape a = .array true n := by
  have shape := p.typed a _ _ found
  generalize he : p.shape a = sh at shape
  cases shape
  rfl

def dynamicUintWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (mload m (p.address a)).val = n then
    some (h.write a (decodeDynamicUint D m (p.address a)) (heap_ty_of_get h a _ _ found)) else none

theorem dynamicUintWriteback_success {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (m : ByteView) (out : Source.Heap D) (step : dynamicUintWriteback h p a n old found m = some out) :
    (mload m (p.address a)).val = n ∧ out = h.write a (decodeDynamicUint D m (p.address a)) (heap_ty_of_get h a _ _ found) := by
  unfold dynamicUintWriteback at step
  split at step
  · exact ⟨‹_›, (Option.some.inj step).symm⟩
  · cases step

theorem dynamicUintWriteback_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old words : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (bound : n < 2 ^ 256) (m : ByteView) :
    dynamicUintWriteback h p a n old found (dynamicUintView n bound words m (p.address a)) =
      some (h.write a (dynamicUintData D n words) (heap_ty_of_get h a _ _ found)) := by
  simp only [dynamicUintWriteback, dynamicUint_header, if_true]
  rw [decodeDynamicUint_encode]

theorem dynamicUintWriteback_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩)
    (m : ByteView) (header : (mload m (p.address a)).val = n)
    (reads : ∀ i, mload m (p.address a + 32 + i.val * 32) = old i) : dynamicUintWriteback h p a n old found m = some h := by
  have same : decodeDynamicUint D m (p.address a) = dynamicUintData D n old := by
    unfold decodeDynamicUint
    rw [header]
    apply congrArg (dynamicUintData D n)
    funext i
    exact reads i
  simp only [dynamicUintWriteback, if_pos header]
  rw [same, heap_write_unchanged h a _ _ found]

def dynamicUintWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = n) :
    Placement (h.write a (decodeDynamicUint D m (p.address a)) (heap_ty_of_get h a _ _ found)) :=
  heapWritePlacement h p a _ _ (by
    rw [dynamicUint_shape h p a n old found, ← header]
    exact .array _ _ _)

theorem dynamicUint_write_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (a n : Nat) (words : Fin n → Roadmap.Word)
    (typed : s.2.heap.ty a = some (.array .memory (.int Source.IntTy.u256) none)) (ok : Source.MemOK E H s) :
    Source.MemOK E H (withSourceHeap s (s.2.heap.write a (dynamicUintData E.layout n words) typed)) := by
  have types : (s.2.heap.write a (dynamicUintData E.layout n words) typed).ty = s.2.heap.ty :=
    funext (fun b => Source.Heap.write_ty _ _ b _ _)
  have valid : Source.DataOK E s.2.heap.ty (dynamicUintData E.layout n words) := .array (fun _ => .val trivial)
  refine ⟨⟨⟨Source.HeapOK.write ok.1.1.heap typed valid, ?_⟩, ?_⟩,
    Source.HeapShaped.write ok.2.1 typed trivial, Source.HeapInner.write ok.2.2 typed (fun i => ⟨uintValueOfWord E.layout (words i), rfl⟩)⟩
  · change H.Le (s.2.heap.write a (dynamicUintData E.layout n words) typed).ty
    rw [types]; exact ok.1.1.le
  · change Source.LocalsOK E (s.2.heap.write a (dynamicUintData E.layout n words) typed).ty s.1
    rw [types]; exact ok.1.2

def dynamicUintStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, dynamicUintData E.layout n old⟩) (m : ByteView) : Option (Source.EMState E Γ) :=
  (dynamicUintWriteback s.2.heap p a n old found m).map (withSourceHeap s)

theorem dynamicUintState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s out : Source.EMState E Γ) (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, dynamicUintData E.layout n old⟩) (m : ByteView)
    (step : dynamicUintStateWriteback s p a n old found m = some out) (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨heap, wrote, same⟩ := Option.map_eq_some_iff.mp step
  subst out
  rw [(dynamicUintWriteback_success s.2.heap p a n old found m heap wrote).2]
  exact dynamicUint_write_MemOK E H s a _ _ _ ok

theorem dynamicUintState_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, dynamicUintData E.layout n old⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = n) (reads : ∀ i, mload m (p.address a + 32 + i.val * 32) = old i) :
    dynamicUintStateWriteback s p a n old found m = some s := by
  unfold dynamicUintStateWriteback
  rw [dynamicUintWriteback_unchanged s.2.heap p a n old found m header reads]
  exact congrArg some (withSourceHeap_unchanged s)

theorem dynamicUint_placement_bounds {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, dynamicUintData D n old⟩) :
    n < 2 ^ 256 ∧ p.address a + 32 + n * 32 ≤ p.free.val := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have ends := p.ends a present
  rw [dynamicUint_shape h p a n old found] at ends
  change p.address a + (32 + n * 32) ≤ p.free.val at ends
  have free := p.free.isLt
  constructor <;> omega

/-- Every serialized byte inside the exact word window depends only on words. -/
theorem wordList_inside (ws : List Roadmap.Word) (m other : ByteView) (base pos : Nat)
    (inside : base ≤ pos ∧ pos < base + ws.length * 32) : wordListView ws m base pos = wordListView ws other base pos := by
  induction ws generalizing base with
  | nil => simp only [List.length_nil, Nat.zero_mul, Nat.add_zero] at inside; omega
  | cons w ws ih =>
    by_cases head : pos < base + 32
    · simp only [wordListView, mstore, dif_pos (And.intro inside.1 head)]
    · change mstore (wordListView ws m (base + 32)) base w pos = mstore (wordListView ws other (base + 32)) base w pos
      rw [mstore_outside _ _ _ _ (by omega), mstore_outside _ _ _ _ (by omega)]
      apply ih
      simp only [List.length_cons] at inside
      omega

theorem wordList_disjoint_commute (xs ys : List Roadmap.Word) (m : ByteView) (a b : Nat)
    (separate : a + xs.length * 32 ≤ b ∨ b + ys.length * 32 ≤ a) :
    wordListView ys (wordListView xs m a) b = wordListView xs (wordListView ys m b) a := by
  funext pos
  by_cases x : a ≤ pos ∧ pos < a + xs.length * 32
  · rw [wordList_residual ys _ b pos (by omega)]
    exact wordList_inside xs _ _ a pos x
  · rw [wordList_residual xs _ a pos (by omega)]
    by_cases y : b ≤ pos ∧ pos < b + ys.length * 32
    · exact wordList_inside ys _ _ b pos y
    · rw [wordList_residual ys _ b pos (by omega), wordList_residual ys _ b pos (by omega), wordList_residual xs _ a pos (by omega)]

theorem dynamicUint_disjoint_commute (nx ny : Nat) (hx : nx < 2 ^ 256) (hy : ny < 2 ^ 256)
    (xs : Fin nx → Roadmap.Word) (ys : Fin ny → Roadmap.Word) (m : ByteView) (a b : Nat)
    (separate : a + 32 + nx * 32 ≤ b ∨ b + 32 + ny * 32 ≤ a) :
    dynamicUintView ny hy ys (dynamicUintView nx hx xs m a) b =
      dynamicUintView nx hx xs (dynamicUintView ny hy ys m b) a := by
  apply wordList_disjoint_commute (⟨nx, hx⟩ :: List.ofFn xs) (⟨ny, hy⟩ :: List.ofFn ys) m a b
  simp only [List.length_cons, List.length_ofFn]
  omega

end Solidity.Yul.Views
