import Solidity.Yul.Views.AggregateWriteback
import Solidity.Yul.Views.RetainedAllocation

/-! Ordinary canonical bool/u256/owned-reference array components over actual
Source.Val/Data. Parameter-only Nat recursion, no decoder/fuel/length cap.
Children remain real separate heap objects; aliases are not inline copies.
None is unsupported preparation, not a Yul refusal/no-op/dirty-word policy. -/
namespace Solidity.Yul.Views

def decodeArrayMembers {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) : (n : Nat) → ByteView → Nat → Option (Fin n → Source.Val D τ)
  | 0, _, _ => some Fin.elim0
  | n + 1, m, base => do
    let head ← decodeMemoryMember p es τ (mload m base)
    let tail ← decodeArrayMembers p es τ n m (base + 32)
    pure (Fin.cases head tail)

theorem decodeArrayMembers_sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (n : Nat) (m : ByteView) (base : Nat)
    (values : Fin n → Source.Val E.layout τ) (decoded : decodeArrayMembers p es τ n m base = some values) :
    ∀ i, MemoryElement p (values i) (mload m (base + i.val * 32)) := by
  induction n generalizing base with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    unfold decodeArrayMembers at decoded
    cases dh : decodeMemoryMember p es τ (mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : decodeArrayMembers p es τ n m (base + 32) with
      | none => rw [dh, dt] at decoded; cases decoded
      | some tail =>
        rw [dh, dt] at decoded
        cases decoded
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero, Fin.val_zero, Nat.zero_mul, Nat.add_zero] using
            (decodeMemoryMember_sound p es τ _ head dh).2
        · have eq : base + j.succ.val * 32 = base + 32 + j.val * 32 := by simp only [Fin.val_succ]; omega
          simpa only [Fin.cases_succ, eq] using ih (base + 32) tail dt j

/-- Composition of actual per-cell decoder results; no inverse law is assumed. -/
theorem decodeArrayMembers_of_decodes {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (n : Nat) (m : ByteView) (base : Nat)
    (values : Fin n → Source.Val D τ)
    (decodes : ∀ i, decodeMemoryMember p es τ (mload m (base + i.val * 32)) = some (values i)) :
    decodeArrayMembers p es τ n m base = some values := by
  induction n generalizing base with
  | zero =>
    have same : values = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [same]
    rfl
  | succ n ih =>
    have head : decodeMemoryMember p es τ (mload m base) = some (values 0) := decodes 0
    have tail := ih (base + 32) (fun i => values i.succ) (by
      intro i
      have eq : base + i.succ.val * 32 = base + 32 + i.val * 32 := by simp only [Fin.val_succ]; omega
      simpa only [eq] using decodes i.succ)
    have same : Fin.cases (values 0) (fun i => values i.succ) = values := by funext i; exact Fin.cases rfl (fun _ => rfl) i
    simp only [decodeArrayMembers, head, tail]
    exact congrArg some same

theorem decodeArrayMembers_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (values : Fin n → Source.Val D τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ i, MemoryElement p (values i) (words i)) (m : ByteView) (base : Nat)
    (reads : ∀ i, mload m (base + i.val * 32) = words i) : decodeArrayMembers p es τ n m base = some values := by
  induction n generalizing base with
  | zero =>
    have same : values = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [same]
    rfl
  | succ n ih =>
    have head : decodeMemoryMember p es τ (mload m base) = some (values 0) := by
      rw [show mload m base = words 0 from reads 0]
      exact decodeMemoryMember_encode p es coverage τ supported _ _ (encoded 0)
    have tail := ih (fun i => values i.succ) (fun i => words i.succ) (fun i => encoded i.succ) (base + 32) (by
      intro i
      have eq : base + i.succ.val * 32 = base + 32 + i.val * 32 := by simp only [Fin.val_succ]; omega
      simpa only [eq] using reads i.succ)
    have same : Fin.cases (values 0) (fun i => values i.succ) = values := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [decodeArrayMembers, head, tail]
    exact congrArg some same

theorem decodeArrayMembers_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (values : Fin n → Source.Val D τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ i, MemoryElement p (values i) (words i)) (m : ByteView) (base : Nat) :
    decodeArrayMembers p es τ n (wordListView (List.ofFn words) m base) base = some values := by
  apply decodeArrayMembers_reads p es coverage τ supported n values words encoded
  intro i
  apply wordList_read
  rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
  simp only [List.getElem_ofFn]

def memberArrayData (D : Source.Layout) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ m, k = some m → m = n) (values : Fin n → Source.Val D τ) : Source.Data D (.array .memory τ k) :=
  .array n hl (fun i => .val (values i))

def arrayPayloadOffset (k : Option Nat) : Nat := if k.isNone then 32 else 0

def arrayLengthChoice (k : Option Nat) (m : ByteView) (base : Nat) : Nat := k.getD (mload m base).val

def memberArrayHeapWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ m, k = some m → m = n)
    (old : Fin n → Source.Val D τ) (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if arrayLengthChoice k m (p.address root) = n then
    (decodeArrayMembers p es τ n m (p.address root + arrayPayloadOffset k)).map
      (fun values => h.write root (memberArrayData D τ k n hl values) (heap_ty_of_get h root _ _ found))
  else none

def memberArrayStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ m, k = some m → m = n) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if arrayLengthChoice k m (p.address root) = n then
    (decodeArrayMembers p es τ n m (p.address root + arrayPayloadOffset k)).map
      (fun values => (Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩).run s)
  else none

def memberArrayView (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat) : ByteView :=
  if k.isNone then dynamicUintView n bound words m base else wordListView (List.ofFn words) m base

theorem memberArrayView_length (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat) :
    arrayLengthChoice k (memberArrayView k n bound words m base) base = n := by
  cases k with
  | none => exact congrArg Fin.val (dynamicUint_header n bound words m base)
  | some x => exact hl x rfl

theorem memberArrayView_element (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat) (i : Fin n) :
    mload (memberArrayView k n bound words m base) (base + arrayPayloadOffset k + i.val * 32) = words i := by
  cases k with
  | none => exact dynamicUint_element n bound words m base i
  | some x =>
    apply wordList_read
    rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getElem_ofFn]

theorem memberArrayView_reencode (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256) (m : ByteView) (base : Nat)
    (header : arrayLengthChoice k m base = n) :
    memberArrayView k n bound (fun i => mload m (base + arrayPayloadOffset k + i.val * 32)) m base = m := by
  cases k with
  | none =>
    change (mload m base).val = n at header
    subst n
    exact decodeDynamicUint_reencode m base
  | some x => exact decodeStaticUint_reencode n m base

theorem memberArrayView_residual (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (m : ByteView) (base pos : Nat)
    (outside : pos < base ∨ base + arrayPayloadOffset k + n * 32 ≤ pos) :
    memberArrayView k n bound words m base pos = m pos := by
  cases k with
  | none => exact dynamicUint_residual n bound words m base pos outside
  | some x =>
    apply wordList_residual
    simpa only [List.length_ofFn, arrayPayloadOffset, Option.isNone_some,
      Bool.false_eq_true, ite_false, Nat.add_zero] using outside

theorem memberArrayHeap_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (old values : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement p (values i) (words i)) (m : ByteView) :
    memberArrayHeapWriteback h p es root τ k n hl old found (memberArrayView k n bound words m (p.address root)) =
      some (h.write root (memberArrayData D τ k n hl values) (heap_ty_of_get h root _ _ found)) := by
  unfold memberArrayHeapWriteback
  rw [memberArrayView_length k n hl, if_pos rfl,
    decodeArrayMembers_reads p es coverage τ supported n values words encoded _ _ (memberArrayView_element k n bound words m (p.address root))]
  rfl

theorem memberArray_shape {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) : p.shape root = .array k.isNone n := by
  have shape := p.typed root _ _ found
  generalize eq : p.shape root = sh at shape
  cases shape
  rfl

def memberArrayWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old values : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) :
    Placement (h.write root (memberArrayData D τ k n hl values) (heap_ty_of_get h root _ _ found)) :=
  heapWritePlacement h p root _ _ (by rw [memberArray_shape h p root τ k n hl old found]; exact .array _ _ _)

theorem memberArrayHeap_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (words : Fin n → Roadmap.Word)
    (encoded : ∀ i, MemoryElement p (old i) (words i)) (m : ByteView) (header : arrayLengthChoice k m (p.address root) = n)
    (reads : ∀ i, mload m (p.address root + arrayPayloadOffset k + i.val * 32) = words i) :
    memberArrayHeapWriteback h p es root τ k n hl old found m = some h := by
  unfold memberArrayHeapWriteback
  rw [if_pos header, decodeArrayMembers_reads p es coverage τ supported n old words encoded _ _ reads]
  simp only [Option.map_some, heap_write_unchanged h root _ _ found]

theorem memberArrayHeap_preservation {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) (out : Source.Heap D)
    (step : memberArrayHeapWriteback h p es root τ k n hl old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ (∀ a, h.next ≤ a → out.cells a = none) ∧ ∀ a, a ≠ root → out.get a = h.get a := by
  unfold memberArrayHeapWriteback at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    subst out
    exact ⟨funext (fun a => Source.Heap.write_ty _ _ a _ _), rfl,
      fun a ha => (h.write root _ _).bounded a ha, fun a ha => Source.Heap.write_other _ ha _ _⟩
  · cases step

theorem memberArrayHeapPut_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (values : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement p (values i) (words i))
    (ok : Source.MemOK E H s) :
    Source.MemOK E H ((Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩ : Source.EM E Γ Unit).run s).2 := by
  have valid : Source.DataOK E s.2.heap.ty (memberArrayData E.layout τ k n hl values) := .array (fun i => .val (encoded i).refOK)
  have one := Source.heapPut_ok (E := E) (Γ := Γ) (H := H) root ⟨_, memberArrayData E.layout τ k n hl values⟩ s ⟨ok.1, valid⟩
  have two := Source.heapPut_top (E := E) (Γ := Γ) root ⟨_, memberArrayData E.layout τ k n hl values⟩ s ⟨ok.2.1, trivial⟩
  have three := Source.heapPut_inner (E := E) (Γ := Γ) root ⟨_, memberArrayData E.layout τ k n hl values⟩ s ⟨ok.2.2, fun i => ⟨values i, rfl⟩⟩
  cases run : (Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩ : Source.EM E Γ Unit).run s with
  | mk result out =>
    cases result with
    | ok value => exact ⟨by simpa only [run] using one, by simpa only [run] using two, by simpa only [run] using three⟩
    | error e =>
      have em : Source.EMOK E H out ∧ (Source.NotStuck e ∨ out.2.heap.ty root ≠ some (.array .memory τ k)) := by simpa only [run] using one
      exact ⟨em.1, by simpa only [run] using two, by simpa only [run] using three⟩

theorem memberArrayState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : memberArrayStateWriteback s p es root τ k n hl m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold memberArrayStateWriteback at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    subst result
    exact memberArrayHeapPut_MemOK E H s p root τ k n hl values _ (decodeArrayMembers_sound p es τ n m _ values decoded) ok
  · cases step

theorem memberArrayHeapPut_run {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (values : Fin n → Source.Val E.layout τ)
    (typed : s.2.heap.ty root = some (.array .memory τ k)) :
    (Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩ : Source.EM E Γ Unit).run s =
      (.ok (), withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) typed)) := by
  rcases s with ⟨locals, state⟩
  unfold Source.heapPut
  rw [Source.Hoare.run_bind]
  change (if ht : state.heap.ty root = some (.array .memory τ k) then
    Source.EM.setSt { state with heap := state.heap.write root (memberArrayData E.layout τ k n hl values) ht } else
    Source.EM.halt (.stuck "memory write type")).run ⟨locals, state⟩ = _
  rw [dif_pos typed]
  rfl

theorem memberArrayState_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get root = some ⟨_, memberArrayData E.layout τ k n hl old⟩) (words : Fin n → Roadmap.Word)
    (encoded : ∀ i, MemoryElement p (old i) (words i)) (m : ByteView) (header : arrayLengthChoice k m (p.address root) = n)
    (reads : ∀ i, mload m (p.address root + arrayPayloadOffset k + i.val * 32) = words i) :
    memberArrayStateWriteback s p es root τ k n hl m = some (.ok (), s) := by
  unfold memberArrayStateWriteback
  rw [if_pos header, decodeArrayMembers_reads p es coverage τ supported n old words encoded _ _ reads]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_run s root τ k n hl old (heap_ty_of_get s.2.heap root _ _ found),
    heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

def memberArrayResultPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) (out : Source.Heap D)
    (step : memberArrayHeapWriteback h p es root τ k n hl old found m = some out) : Placement out := by
  unfold memberArrayHeapWriteback at step
  split at step
  · cases decoded : decodeArrayMembers p es τ n m (p.address root + arrayPayloadOffset k) with
    | none => rw [decoded] at step; cases step
    | some values =>
      rw [decoded] at step
      have same := Option.some.inj step
      subst out
      exact memberArrayWrittenPlacement h p root τ k n hl old values found
  · cases step

theorem memberArray_placement_bounds {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) :
    n < 2 ^ 256 ∧ p.address root + arrayPayloadOffset k + n * 32 ≤ p.free.val := by
  have bound := array_length_from_placement p root n hl _ found
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have ends := p.ends root present
  rw [memberArray_shape h p root τ k n hl old found] at ends
  change p.address root + ((if k.isNone then 32 else 0) + n * 32) ≤ p.free.val at ends
  exact ⟨bound, by unfold arrayPayloadOffset; omega⟩

theorem decodedArray_representation {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (bound : n < 2 ^ 256)
    (m : ByteView) (base : Nat) (values : Fin n → Source.Val E.layout τ)
    (decoded : decodeArrayMembers p es τ n m (base + arrayPayloadOffset k) = some values) :
    MemoryObjectWords p (memberArrayData E.layout τ k n hl values)
      ((if k.isNone then [⟨n, bound⟩] else []) ++ List.ofFn (fun i : Fin n => mload m (base + arrayPayloadOffset k + i.val * 32))) :=
  .array n hl bound values _ (decodeArrayMembers_sound p es τ n m _ values decoded)

theorem memberArray_reserved {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (root : Nat)
    (present : (h.cells root).isSome) (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (m : ByteView) (reserved : ReservedOK m p.free) :
    ReservedOK (memberArrayView k n bound words m (p.address root)) p.free := by
  have start := p.starts root present
  constructor
  · have eq := mload_congr (memberArrayView k n bound words m (p.address root)) m 64
      (fun i => memberArrayView_residual k n bound words m _ _ (Or.inl (by have hi := i.isLt; omega)))
    exact (congrArg Fin.val eq).trans reserved.1
  · intro i
    rw [memberArrayView_residual k n bound words m _ _ (Or.inl (by have hi := i.isLt; omega))]
    exact reserved.2 i

theorem memberArrayHeapPut_error {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (values : Fin n → Source.Val E.layout τ)
    (wrong : s.2.heap.ty root ≠ some (.array .memory τ k)) :
    (Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩ : Source.EM E Γ Unit).run s =
      (.error (.stuck "memory write type"), s) := by
  rcases s with ⟨locals, state⟩
  unfold Source.heapPut
  rw [Source.Hoare.run_bind]
  change (if ht : state.heap.ty root = some (.array .memory τ k) then
    Source.EM.setSt { state with heap := state.heap.write root (memberArrayData E.layout τ k n hl values) ht } else
    Source.EM.halt (.stuck "memory write type")).run ⟨locals, state⟩ = _
  rw [dif_neg wrong]
  rfl

theorem memberArray_other_region {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (τ : Source.STy)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (other : Nat) (owned : (h.cells other).isSome)
    (distinct : root ≠ other) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word) (m : ByteView)
    (off : Nat) (inside : off < (p.shape other).size) :
    memberArrayView k n bound words m (p.address root) (p.address other + off) = m (p.address other + off) := by
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have sep := p.separate root other present owned distinct
  have extent : arrayPayloadOffset k + n * 32 = (p.shape root).size := by
    rw [memberArray_shape h p root τ k n hl old found]
    rfl
  apply memberArrayView_residual
  omega

end Solidity.Yul.Views
