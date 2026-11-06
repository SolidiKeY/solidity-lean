import Solidity.Yul.Views.MemoryScalarCodec
import Solidity.Yul.Views.RetainedMemberArray

/-! Canonical scalar extension ADAPTER. The original memory decoder/arrays/
struct APIs stay unchanged. Concrete scalar inversion composes with existing
pointer ownership, actual Data/Heap.write/heapPut, Placement and retained laws.
No assumed inverse/read/safety/result fields or new source state/IR. -/
namespace Solidity.Yul.Views

def ExtendedMemberType (D : Source.Layout) (τ : Source.STy) : Prop := OrdinaryMemberType τ ∨ CanonicalScalarType D τ

theorem CanonicalScalarType.no_memory {D : Source.Layout} {τ : Source.STy} (supported : CanonicalScalarType D τ) : τ.loc? ≠ some .memory := by
  cases τ <;> simp only [CanonicalScalarType] at supported <;> try cases supported
  all_goals simp only [Source.STy.loc?]
  all_goals (intro eq; cases eq)

theorem memoryScalarCandidate_memory_none (D : Source.Layout) (τ : Source.STy) (loc : τ.loc? = some .memory) (word : Roadmap.Word) :
    memoryScalarCandidate D τ word = none := by
  cases τ <;> simp only [Source.STy.loc?] at loc <;> try cases loc
  all_goals rfl

def decodeExtendedMemoryMember {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (word : Roadmap.Word) : Option (Source.Val D τ) :=
  match decodeCanonicalScalar D τ word with
  | some v => some v
  | none => decodeMemoryMember p es τ word

theorem decodeExtendedMemoryMember_sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (word : Roadmap.Word) (v : Source.Val E.layout τ)
    (decoded : decodeExtendedMemoryMember p es τ word = some v) : Source.Val.RefOK E h.ty v ∧ MemoryElement p v word := by
  unfold decodeExtendedMemoryMember at decoded
  cases scalar : decodeCanonicalScalar E.layout τ word with
  | none => rw [scalar] at decoded; exact decodeMemoryMember_sound p es τ word v decoded
  | some x =>
    rw [scalar] at decoded
    cases decoded
    exact ⟨decodeCanonicalScalar_refOK E h.ty τ word v scalar, .scalar v word (decodeCanonicalScalar_word E.layout τ word v scalar)⟩

theorem decodeExtendedScalar_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (supported : CanonicalScalarType D τ) (v : Source.Val D τ) (word : Roadmap.Word)
    (encoded : MemoryElement p v word) : decodeExtendedMemoryMember p es τ word = some v := by
  have read : v.word = some word := by
    cases encoded with
    | scalar _ _ read => exact read
    | pointer loc _ _ _ _ => exact False.elim (supported.no_memory loc)
  unfold decodeExtendedMemoryMember
  rw [decodeCanonicalScalar_encode D τ supported v word read]

theorem decodeExtendedMemoryMember_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy) (supported : ExtendedMemberType D τ)
    (v : Source.Val D τ) (word : Roadmap.Word) (encoded : MemoryElement p v word) : decodeExtendedMemoryMember p es τ word = some v := by
  rcases supported with old | scalar
  · rcases old with eq | eq | loc
    · subst τ; exact decodeExtendedScalar_encode p es .bool trivial v word encoded
    · subst τ; exact decodeExtendedScalar_encode p es (.int Source.IntTy.u256) trivial v word encoded
    · unfold decodeExtendedMemoryMember decodeCanonicalScalar
      rw [memoryScalarCandidate_memory_none D τ loc word]
      exact decodeMemoryMember_encode p es coverage τ (Or.inr (Or.inr loc)) v word encoded
  · exact decodeExtendedScalar_encode p es τ scalar v word encoded

/-- Ordinary Nat recursion over a CONCRETE word decoder callback, no law fields. -/
def decodeArrayWith {D : Source.Layout} {τ : Source.STy} (decode : Roadmap.Word → Option (Source.Val D τ)) :
    (n : Nat) → ByteView → Nat → Option (Fin n → Source.Val D τ)
  | 0, _, _ => some Fin.elim0
  | n + 1, m, base => do
    let head ← decode (mload m base)
    let tail ← decodeArrayWith decode n m (base + 32)
    pure (Fin.cases head tail)

theorem decodeArrayWith_legacy {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (n : Nat) (m : ByteView) (base : Nat) :
    decodeArrayWith (decodeMemoryMember p es τ) n m base = decodeArrayMembers p es τ n m base := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp only [decodeArrayWith, decodeArrayMembers, ih]

theorem decodeArrayWith_of_decodes {D : Source.Layout} {τ : Source.STy} (decode : Roadmap.Word → Option (Source.Val D τ))
    (n : Nat) (m : ByteView) (base : Nat) (values : Fin n → Source.Val D τ)
    (decodes : ∀ i, decode (mload m (base + i.val * 32)) = some (values i)) : decodeArrayWith decode n m base = some values := by
  induction n generalizing base with
  | zero =>
    have same : values = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [same]; rfl
  | succ n ih =>
    have head : decode (mload m base) = some (values 0) := decodes 0
    have tail := ih (base + 32) (fun i => values i.succ) (by
      intro i
      have eq : base + i.succ.val * 32 = base + 32 + i.val * 32 := by simp only [Fin.val_succ]; omega
      simpa only [eq] using decodes i.succ)
    have same : Fin.cases (values 0) (fun i => values i.succ) = values := by funext i; exact Fin.cases rfl (fun _ => rfl) i
    simp only [decodeArrayWith, head, tail]
    exact congrArg some same

def decodeCanonicalArray {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p)) (τ : Source.STy) :=
  decodeArrayWith (decodeExtendedMemoryMember p es τ)

theorem decodeCanonicalArray_sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (n : Nat) (m : ByteView) (base : Nat) (values : Fin n → Source.Val E.layout τ)
    (decoded : decodeCanonicalArray p es τ n m base = some values) : ∀ i, MemoryElement p (values i) (mload m (base + i.val * 32)) := by
  induction n generalizing base with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    change (do let head ← decodeExtendedMemoryMember p es τ (mload m base); let tail ← decodeCanonicalArray p es τ n m (base + 32); pure (Fin.cases head tail)) = some values at decoded
    cases dh : decodeExtendedMemoryMember p es τ (mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : decodeCanonicalArray p es τ n m (base + 32) with
      | none => rw [dh, dt] at decoded; cases decoded
      | some tail =>
        rw [dh, dt] at decoded
        cases decoded
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero, Fin.val_zero, Nat.zero_mul, Nat.add_zero] using (decodeExtendedMemoryMember_sound p es τ _ head dh).2
        · have eq : base + j.succ.val * 32 = base + 32 + j.val * 32 := by simp only [Fin.val_succ]; omega
          simpa only [Fin.cases_succ, eq] using ih _ tail dt j

theorem decodeCanonicalArray_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (τ : Source.STy) (supported : ExtendedMemberType D τ) (n : Nat)
    (values : Fin n → Source.Val D τ) (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement p (values i) (words i))
    (m : ByteView) (base : Nat) (reads : ∀ i, mload m (base + i.val * 32) = words i) : decodeCanonicalArray p es τ n m base = some values := by
  induction n generalizing base with
  | zero =>
    have same : values = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [same]; rfl
  | succ n ih =>
    have head : decodeExtendedMemoryMember p es τ (mload m base) = some (values 0) := by
      rw [show mload m base = words 0 from reads 0]
      exact decodeExtendedMemoryMember_encode p es coverage τ supported _ _ (encoded 0)
    have tail := ih (fun i => values i.succ) (fun i => words i.succ) (fun i => encoded i.succ) (base + 32) (by
      intro i
      have eq : base + i.succ.val * 32 = base + 32 + i.val * 32 := by simp only [Fin.val_succ]; omega
      simpa only [eq] using reads i.succ)
    have same : Fin.cases (values 0) (fun i => values i.succ) = values := by funext i; exact Fin.cases rfl (fun _ => rfl) i
    change (do let head ← decodeExtendedMemoryMember p es τ (mload m base); let tail ← decodeCanonicalArray p es τ n m (base + 32); pure (Fin.cases head tail)) = some values
    simp only [head, tail]
    exact congrArg some same

/-- The same declared-field fold with a concrete decoder callback. -/
def decodeFieldsWith {D : Source.Layout} (decode : (τ : Source.STy) → Roadmap.Word → Option (Source.Val D τ)) :
    (τs : List Source.STy) → ByteView → Nat → Option (Source.DataList D τs)
  | [], _, _ => some .nil
  | τ :: τs, m, base => do
    let head ← decode τ (mload m base)
    let tail ← decodeFieldsWith decode τs m (base + 32)
    pure (Source.DataList.cons (Source.Data.val head) tail)

theorem decodeFieldsWith_legacy {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (τs : List Source.STy) (m : ByteView) (base : Nat) :
    decodeFieldsWith (decodeMemoryMember p es) τs m base = decodeMemoryFields p es τs m base := by
  induction τs generalizing base with
  | nil => rfl
  | cons τ τs ih => simp only [decodeFieldsWith, decodeMemoryFields, ih]

def decodeCanonicalFields {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p)) :=
  decodeFieldsWith (decodeExtendedMemoryMember p es)

theorem decodeCanonicalFields_representation {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τs : List Source.STy) (m : ByteView) (base : Nat) (fs : Source.DataList E.layout τs)
    (decoded : decodeCanonicalFields p es τs m base = some fs) :
    ∃ ws, MemoryFields p fs ws ∧ ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w := by
  induction τs generalizing base with
  | nil => cases decoded; exact ⟨[], .nil, fun i w found => by cases i <;> cases found⟩
  | cons τ τs ih =>
    change (do let head ← decodeExtendedMemoryMember p es τ (mload m base); let tail ← decodeCanonicalFields p es τs m (base + 32); pure (Source.DataList.cons (Source.Data.val head) tail)) = some fs at decoded
    cases dh : decodeExtendedMemoryMember p es τ (mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : decodeCanonicalFields p es τs m (base + 32) with
      | none => rw [dh, dt] at decoded; cases decoded
      | some tail =>
        rw [dh, dt] at decoded
        cases decoded
        obtain ⟨ws, fields, reads⟩ := ih _ tail dt
        refine ⟨mload m base :: ws, .cons head _ (decodeExtendedMemoryMember_sound p es τ _ head dh).2 tail ws fields, ?_⟩
        intro i w found
        cases i with
        | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Option.some.inj found
        | succ i =>
          have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
          rw [eq]; exact reads i w found

theorem decodeCanonicalFields_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word}
    (fields : MemoryFields p fs ws) (supported : ∀ τ ∈ τs, ExtendedMemberType D τ) (m : ByteView) (base : Nat)
    (reads : ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w) : decodeCanonicalFields p es τs m base = some fs := by
  induction fields generalizing base with
  | nil => rfl
  | @cons τ τs v w encoded fs ws rest ih =>
    have head := reads 0 w rfl
    simp only [Nat.zero_mul, Nat.add_zero] at head
    have tail : decodeCanonicalFields p es τs m (base + 32) = some fs := by
      apply ih (fun σ hs => supported σ (List.mem_cons_of_mem _ hs))
      intro i word found
      have read := reads (i + 1) word found
      have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
      rwa [eq] at read
    change (do let head ← decodeExtendedMemoryMember p es τ (mload m base); let tail ← decodeCanonicalFields p es τs m (base + 32); pure (Source.DataList.cons (Source.Data.val head) tail)) = some (Source.DataList.cons (Source.Data.val v) fs)
    simp only [head, decodeExtendedMemoryMember_encode p es coverage τ (supported τ List.mem_cons_self) v w encoded, tail]
    rfl

def canonicalArrayHeap {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (old : Fin n → Source.Val D τ) (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if arrayLengthChoice k m (p.address root) = n then
    (decodeCanonicalArray p es τ n m (p.address root + arrayPayloadOffset k)).map
      (fun values => h.write root (memberArrayData D τ k n hl values) (heap_ty_of_get h root _ _ found)) else none

def canonicalArrayState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (p : Placement s.2.heap) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if arrayLengthChoice k m (p.address root) = n then
    (decodeCanonicalArray p es τ n m (p.address root + arrayPayloadOffset k)).map
      (fun values => (Source.heapPut root ⟨_, memberArrayData E.layout τ k n hl values⟩).run s) else none

theorem canonicalArrayState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : canonicalArrayState s p es root τ k n hl m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold canonicalArrayState at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    subst result
    exact memberArrayHeapPut_MemOK E H s p root τ k n hl values _ (decodeCanonicalArray_sound p es τ n m _ values decoded) ok
  · cases step

theorem canonicalArray_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy)
    (supported : ExtendedMemberType E.layout τ) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (old : Fin n → Source.Val E.layout τ) (found : s.2.heap.get root = some ⟨_, memberArrayData E.layout τ k n hl old⟩)
    (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement p (old i) (words i)) (m : ByteView)
    (header : arrayLengthChoice k m (p.address root) = n) (reads : ∀ i, mload m (p.address root + arrayPayloadOffset k + i.val * 32) = words i) :
    canonicalArrayState s p es root τ k n hl m = some (.ok (), s) := by
  unfold canonicalArrayState
  rw [if_pos header, decodeCanonicalArray_reads p es coverage τ supported n old words encoded _ _ reads]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_run s root τ k n hl old (heap_ty_of_get s.2.heap root _ _ found), heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

theorem canonicalArray_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : ExtendedMemberType D τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (old values : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (encoded : ∀ i, MemoryElement p (values i) (words i)) (m : ByteView) :
    canonicalArrayHeap h p es root τ k n hl old found (memberArrayView k n bound words m (p.address root)) =
      some (h.write root (memberArrayData D τ k n hl values) (heap_ty_of_get h root _ _ found)) := by
  unfold canonicalArrayHeap
  rw [memberArrayView_length k n hl, if_pos rfl, decodeCanonicalArray_reads p es coverage τ supported n values words encoded _ _ (memberArrayView_element k n bound words m (p.address root))]
  rfl

theorem canonicalArray_result {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) (out : Source.Heap D)
    (step : canonicalArrayHeap h p es root τ k n hl old found m = some out) :
    (∃ q : Placement out, q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free) ∧
      out.ty = h.ty ∧ out.next = h.next ∧ (∀ a, h.next ≤ a → out.cells a = none) ∧ ∀ a, a ≠ root → out.get a = h.get a := by
  unfold canonicalArrayHeap at step
  split at step
  · obtain ⟨values, decoded, same⟩ := Option.map_eq_some_iff.mp step
    subst out
    exact ⟨⟨memberArrayWrittenPlacement h p root τ k n hl old values found, rfl, rfl, rfl⟩,
      funext (fun a => Source.Heap.write_ty _ _ a _ _), rfl, fun a ha => (h.write root _ _).bounded a ha, fun a ha => Source.Heap.write_other _ ha _ _⟩
  · cases step

def canonicalStructHeap {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) : Option (Source.Heap D) :=
  (decodeCanonicalFields p es (D.fields name) m (p.address root)).map
    (fun fs => h.write root (.struct fs) (heap_ty_of_get h root _ _ found))

def canonicalStructState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (decodeCanonicalFields p es (E.layout.fields name) m (p.address root)).map (fun fs => (Source.heapPut root ⟨.struct .memory name, .struct fs⟩).run s)

theorem canonicalStructState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ) (step : canonicalStructState s p es root name m = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst result
  obtain ⟨ws, fields, reads⟩ := decodeCanonicalFields_representation p es _ m (p.address root) fs decoded
  have valid : Source.DataOK E s.2.heap.ty (Source.Data.struct (l := .memory) fs) := .struct fields.dataOK
  have one := Source.heapPut_ok (E := E) (Γ := Γ) (H := H) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.1, valid⟩
  have two := Source.heapPut_top (E := E) (Γ := Γ) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.2.1, trivial⟩
  have three := Source.heapPut_inner (E := E) (Γ := Γ) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.2.2, fields.allVal⟩
  cases run : (Source.heapPut root ⟨.struct .memory name, .struct fs⟩ : Source.EM E Γ Unit).run s with
  | mk outcome out =>
    cases outcome with
    | ok value => exact ⟨by simpa only [run] using one, by simpa only [run] using two, by simpa only [run] using three⟩
    | error e =>
      have em : Source.EMOK E H out ∧ (Source.NotStuck e ∨ out.2.heap.ty root ≠ some (.struct .memory name)) := by simpa only [run] using one
      exact ⟨em.1, by simpa only [run] using two, by simpa only [run] using three⟩

theorem canonicalStruct_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName) (old fs : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (ws : List Roadmap.Word) (fields : MemoryFields p fs ws)
    (supported : ∀ τ ∈ D.fields name, ExtendedMemberType D τ) (m : ByteView) :
    canonicalStructHeap h p es root name old found (wordListView ws m (p.address root)) =
      some (h.write root (.struct fs) (heap_ty_of_get h root _ _ found)) := by
  unfold canonicalStructHeap
  rw [decodeCanonicalFields_reads p es coverage fields supported _ _ (fun i w found => wordList_read ws m (p.address root) i w found)]
  rfl

theorem canonicalStruct_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName)
    (old : Source.DataList E.layout (E.layout.fields name)) (found : s.2.heap.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p old ws) (supported : ∀ τ ∈ E.layout.fields name, ExtendedMemberType E.layout τ)
    (m : ByteView) (reads : ∀ i w, ws[i]? = some w → mload m (p.address root + i * 32) = w) :
    canonicalStructState s p es root name m = some (.ok (), s) := by
  unfold canonicalStructState
  rw [decodeCanonicalFields_reads p es coverage fields supported _ _ reads]
  simp only [Option.map_some]
  rw [structHeapPut_run s root name old (heap_ty_of_get s.2.heap root _ _ found), heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

theorem canonicalStruct_result {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) (out : Source.Heap D)
    (step : canonicalStructHeap h p es root name old found m = some out) :
    (∃ q : Placement out, q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free) ∧
      out.ty = h.ty ∧ out.next = h.next ∧ (∀ a, h.next ≤ a → out.cells a = none) ∧ ∀ a, a ≠ root → out.get a = h.get a := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst out
  exact ⟨⟨structWrittenPlacement h p root name old fs found, rfl, rfl, rfl⟩,
    funext (fun a => Source.Heap.write_ty _ _ a _ _), rfl, fun a ha => (h.write root _ _).bounded a ha, fun a ha => Source.Heap.write_other _ ha _ _⟩

theorem canonicalFields_raw_reencode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τs : List Source.STy) (m : ByteView) (base : Nat) (fs : Source.DataList E.layout τs)
    (decoded : decodeCanonicalFields p es τs m base = some fs) : ∃ ws, MemoryFields p fs ws ∧ wordListView ws m base = m := by
  obtain ⟨ws, fields, reads⟩ := decodeCanonicalFields_representation p es τs m base fs decoded
  exact ⟨ws, fields, wordList_unchanged ws m base reads⟩

theorem canonicalArrayHeap_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (τ : Source.STy) (supported : ExtendedMemberType D τ)
    (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (words : Fin n → Roadmap.Word)
    (encoded : ∀ i, MemoryElement p (old i) (words i)) (m : ByteView) (header : arrayLengthChoice k m (p.address root) = n)
    (reads : ∀ i, mload m (p.address root + arrayPayloadOffset k + i.val * 32) = words i) : canonicalArrayHeap h p es root τ k n hl old found m = some h := by
  unfold canonicalArrayHeap
  rw [if_pos header, decodeCanonicalArray_reads p es coverage τ supported n old words encoded _ _ reads]
  simp only [Option.map_some, heap_write_unchanged h root _ _ found]

theorem canonicalStructHeap_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (ws : List Roadmap.Word) (fields : MemoryFields p old ws)
    (supported : ∀ τ ∈ D.fields name, ExtendedMemberType D τ) (m : ByteView)
    (reads : ∀ i w, ws[i]? = some w → mload m (p.address root + i * 32) = w) : canonicalStructHeap h p es root name old found m = some h := by
  unfold canonicalStructHeap
  rw [decodeCanonicalFields_reads p es coverage fields supported _ _ reads]
  simp only [Option.map_some, heap_write_unchanged h root _ _ found]

end Solidity.Yul.Views
