import Solidity.Yul.Views.MixedMemoryMemOK

/-! Full-width static uint256 arrays: every raw word has an exact typed source
value. No truncation/dirty cleanup, decoder cap or allocation change occurs.
This selected component does not define arbitrary assembly writeback. -/
namespace Solidity.Yul.Views

def uintValueOfWord (D : Source.Layout) (w : Roadmap.Word) : Source.Val D (.int Source.IntTy.u256) :=
  .int w.val (by
    have bound := w.isLt
    change 0 ≤ (w.val : Int) ∧ (w.val : Int) ≤ (2 ^ 256 : Nat) - 1
    omega)

theorem uintValueOfWord_word (D : Source.Layout) (w : Roadmap.Word) :
    (uintValueOfWord D w).word = some w := by
  have bound : (w.val : Int) < (2 ^ 256 : Nat) := Int.ofNat_lt.mpr w.isLt
  have nonnegative : 0 ≤ (w.val : Int) := Int.natCast_nonneg _
  simp only [uintValueOfWord, Source.Val.word, Source.intWord, Int.emod_eq_of_lt nonnegative bound, Int.toNat_natCast]
  apply congrArg some
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

def staticUintData (D : Source.Layout) (n : Nat) (words : Fin n → Roadmap.Word) :
    Source.Data D (.array .memory (.int Source.IntTy.u256) (some n)) :=
  .array n (fun _ e => (Option.some.inj e).symm) (fun i => .val (uintValueOfWord D (words i)))

def decodeStaticUint (D : Source.Layout) (n : Nat) (m : ByteView) (base : Nat) :=
  staticUintData D n (fun i => mload m (base + i.val * 32))

theorem staticUintData_words {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) :
    MemoryObjectWords p (staticUintData D n words) (List.ofFn words) := by
  exact MemoryObjectWords.array n _ bound (fun i => uintValueOfWord D (words i)) words
    (fun i => .scalar _ _ (uintValueOfWord_word D (words i)))

theorem decodeStaticUint_encode (D : Source.Layout) (n : Nat) (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat) :
    decodeStaticUint D n (wordListView (List.ofFn words) m base) base = staticUintData D n words := by
  apply congrArg (staticUintData D n)
  funext i
  apply wordList_read
  rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
  simp only [List.getElem_ofFn]

theorem decodeStaticUint_reencode (n : Nat) (m : ByteView) (base : Nat) :
    wordListView (List.ofFn (fun i : Fin n => mload m (base + i.val * 32))) m base = m := by
  apply wordList_unchanged
  intro i w found
  have hi : i < n := by
    apply Nat.lt_of_not_le
    intro no
    rw [List.getElem?_eq_none (by simp only [List.length_ofFn]; exact no)] at found
    cases found
  rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact hi), List.getElem_ofFn] at found
  exact Option.some.inj found

def staticUintWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩)
    (m : ByteView) : Source.Heap D :=
  h.write a (decodeStaticUint D n m (p.address a)) (heap_ty_of_get h a _ _ found)

theorem staticUintWriteback_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old words : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩)
    (m : ByteView) :
    staticUintWriteback h p a n old found (wordListView (List.ofFn words) m (p.address a)) =
      h.write a (staticUintData D n words) (heap_ty_of_get h a _ _ found) := by
  unfold staticUintWriteback
  rw [decodeStaticUint_encode]

theorem staticUintWriteback_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩)
    (m : ByteView) (reads : ∀ i, mload m (p.address a + i.val * 32) = old i) :
    staticUintWriteback h p a n old found m = h := by
  have same : decodeStaticUint D n m (p.address a) = staticUintData D n old := by
    apply congrArg (staticUintData D n)
    funext i
    exact reads i
  unfold staticUintWriteback
  rw [same]
  exact heap_write_unchanged h a _ _ found

theorem staticUintWriteback_other {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a b n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩)
    (m : ByteView) (other : b ≠ a) : (staticUintWriteback h p a n old found m).get b = h.get b :=
  Source.Heap.write_other h other _ _

theorem staticUintWriteback_types {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩) (m : ByteView) :
    (staticUintWriteback h p a n old found m).ty = h.ty ∧
    (staticUintWriteback h p a n old found m).next = h.next ∧
    ∀ b, h.next ≤ b → (staticUintWriteback h p a n old found m).cells b = none :=
  ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl, fun b hb => (staticUintWriteback h p a n old found m).bounded b hb⟩

theorem staticUint_shape {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩) :
    p.shape a = .array false n := by
  have shape := p.typed a _ _ found
  generalize he : p.shape a = sh at shape
  cases shape
  rfl

def staticUintWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩) (m : ByteView) :
    Placement (staticUintWriteback h p a n old found m) :=
  heapWritePlacement h p a _ _ (by rw [staticUint_shape h p a n old found]; exact .array n _ _)

theorem staticUint_placement_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩) (m : ByteView) :
    let q := staticUintWrittenPlacement h p a n old found m
    q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free := ⟨rfl, rfl, rfl⟩

def staticUintStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, staticUintData E.layout n old⟩) (m : ByteView) : Source.EMState E Γ :=
  withSourceHeap s (staticUintWriteback s.2.heap p a n old found m)

theorem staticUintState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, staticUintData E.layout n old⟩) (m : ByteView)
    (ok : Source.MemOK E H s) : Source.MemOK E H (staticUintStateWriteback s p a n old found m) := by
  have ht := heap_ty_of_get s.2.heap a _ _ found
  have types := (staticUintWriteback_types s.2.heap p a n old found m).1
  have valid : Source.DataOK E s.2.heap.ty (decodeStaticUint E.layout n m (p.address a)) :=
    .array (fun _ => .val trivial)
  refine ⟨⟨⟨Source.HeapOK.write ok.1.1.heap ht valid, ?_⟩, ?_⟩,
    Source.HeapShaped.write ok.2.1 ht trivial, Source.HeapInner.write ok.2.2 ht ?_⟩
  · change H.Le (staticUintWriteback s.2.heap p a n old found m).ty
    rw [types]
    exact ok.1.1.le
  · change Source.LocalsOK E (staticUintWriteback s.2.heap p a n old found m).ty s.1
    rw [types]
    exact ok.1.2
  · exact fun i => ⟨uintValueOfWord E.layout (mload m (p.address a + i.val * 32)), rfl⟩

theorem staticUintState_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a n : Nat) (old : Fin n → Roadmap.Word)
    (found : s.2.heap.get a = some ⟨_, staticUintData E.layout n old⟩) (m : ByteView)
    (reads : ∀ i, mload m (p.address a + i.val * 32) = old i) : staticUintStateWriteback s p a n old found m = s := by
  unfold staticUintStateWriteback
  rw [staticUintWriteback_unchanged s.2.heap p a n old found m reads]
  exact withSourceHeap_unchanged s

theorem staticUint_word_fits {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a n : Nat)
    (old : Fin n → Roadmap.Word) (found : h.get a = some ⟨_, staticUintData D n old⟩) (i : Fin n) :
    p.address a + i.val * 32 + 32 ≤ p.free.val := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have ends := p.ends a present
  rw [staticUint_shape h p a n old found] at ends
  have bound := i.isLt
  simp only [MemoryShape.size] at ends
  omega

theorem mstore_disjoint_commute (m : ByteView) (a b : Nat) (x y : Roadmap.Word)
    (separate : a + 32 ≤ b ∨ b + 32 ≤ a) : mstore (mstore m a x) b y = mstore (mstore m b y) a x := by
  funext i
  by_cases atA : a ≤ i ∧ i < a + 32
  · have notB : ¬ (b ≤ i ∧ i < b + 32) := by omega
    simp only [mstore, dif_pos atA, dif_neg notB]
  · by_cases atB : b ≤ i ∧ i < b + 32
    · simp only [mstore, dif_neg atA, dif_pos atB]
    · simp only [mstore, dif_neg atA, dif_neg atB]

end Solidity.Yul.Views
