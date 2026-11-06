import Solidity.Yul.Views.DynamicUintMemory
import Solidity.Yul.Views.PointerMemory

/-! Constructive simultaneous ordinary struct-member decoding over ACTUAL
Source.DataList, declared types and owned pointer candidates. Canonical bool,
full-width uint256 and memory-reference members are supported components.
None is unsupported preparation, never a Yul refusal/no-op/dirty-bit policy.
Recursion is on the ordinary list of declared member types, not an indexed
source data matcher. No duplicate state/IR or assumed inverse/safety laws. -/
namespace Solidity.Yul.Views

def decodeMemoryMember {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (word : Roadmap.Word) : Option (Source.Val D τ) :=
  if loc : τ.loc? = some .memory then decodeMemoryPointer p es τ loc word else
    match τ with
    | .bool => if word = 0 then some (.bool false) else if word = 1 then some (.bool true) else none
    | .int t => if eq : t = Source.IntTy.u256 then some (eq.symm ▸ uintValueOfWord D word) else none
    | _ => none

theorem decodeMemoryMember_sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (word : Roadmap.Word) (v : Source.Val E.layout τ)
    (decoded : decodeMemoryMember p es τ word = some v) : Source.Val.RefOK E h.ty v ∧ MemoryElement p v word := by
  unfold decodeMemoryMember at decoded
  split at decoded
  · have sound := decodeMemoryPointer_sound p es τ _ word v decoded
    obtain ⟨e, member, raw, same⟩ := sound.2
    subst v
    have owned := heap_ty_of_get h e.id e.ty e.data e.found
    have shape : e.ty.memShape = τ.memShape := by
      obtain ⟨σ, eq, shape⟩ := sound.1
      have same := Option.some.inj (owned.symm.trans eq)
      subst σ
      exact shape
    have bits : ownedPointerWord p e.id e.ty owned = word := Fin.ext raw
    rw [← bits]
    exact ⟨sound.1, .pointer _ e.id e.ty owned shape⟩
  · cases τ <;> try cases decoded
    case bool =>
      dsimp only at decoded
      split at decoded
      · subst word; cases decoded; exact ⟨trivial, .scalar _ _ rfl⟩
      · split at decoded
        · subst word; cases decoded; exact ⟨trivial, .scalar _ _ rfl⟩
        · cases decoded
    case int =>
      rename_i t noLoc
      dsimp only at decoded
      split at decoded
      · subst t; cases decoded; exact ⟨trivial, .scalar _ _ (uintValueOfWord_word _ _)⟩
      · cases decoded

theorem uintValueOfWord_inverse {D : Source.Layout} (v : Source.Val D (.int Source.IntTy.u256))
    (word : Roadmap.Word) (encoded : v.word = some word) : uintValueOfWord D word = v := by
  cases v with
  | int n range =>
    have bounds : 0 ≤ n ∧ n < (2 ^ 256 : Nat) := by
      change 0 ≤ n ∧ n ≤ (2 ^ 256 : Nat) - 1 at range
      omega
    have small : n.toNat < 2 ^ 256 := by omega
    change some (Source.intWord n) = some word at encoded
    have val := congrArg Fin.val (Option.some.inj encoded)
    change (n % (2 ^ 256 : Nat)).toNat % 2 ^ 256 = word.val at val
    rw [Int.emod_eq_of_lt bounds.1 bounds.2, Nat.mod_eq_of_lt small] at val
    have eq : (word.val : Int) = n := by omega
    unfold uintValueOfWord
    cases eq
    rfl
  | memRef loc _ | storRef loc _ | cdRef loc _ => cases loc

/-- Concrete supported member TYPES; this does not rename the Yul fragment. -/
def OrdinaryMemberType (τ : Source.STy) : Prop :=
  τ = .bool ∨ τ = .int Source.IntTy.u256 ∨ τ.loc? = some .memory

theorem decodeMemoryMember_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy)
    (supported : OrdinaryMemberType τ) (v : Source.Val D τ) (word : Roadmap.Word)
    (encoded : MemoryElement p v word) : decodeMemoryMember p es τ word = some v := by
  cases encoded with
  | pointer loc a σ owned shape =>
    simp only [decodeMemoryMember, dif_pos loc]
    exact decodeMemoryPointer_encode p es coverage τ loc a σ owned shape
  | scalar v w read =>
    rcases supported with eq | eq | loc
    · subst τ
      cases v with
      | bool b =>
        cases b
        · have raw : word = 0 := (Option.some.inj read).symm
          subst word
          rfl
        · have raw : word = 1 := (Option.some.inj read).symm
          subst word
          rfl
      | memRef loc _ | storRef loc _ | cdRef loc _ => cases loc
    · subst τ
      unfold decodeMemoryMember
      simp only [Source.STy.loc?, reduceCtorEq]
      exact congrArg some (uintValueOfWord_inverse v word read)
    · cases v <;> simp only [Source.STy.loc?] at loc <;> first | cases loc | cases read

def decodeMemoryFields {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) : (τs : List Source.STy) → ByteView → Nat → Option (Source.DataList D τs)
  | [], _, _ => some .nil
  | τ :: τs, m, base => do
    let v ← decodeMemoryMember p es τ (mload m base)
    let rest ← decodeMemoryFields p es τs m (base + 32)
    pure (.cons (.val v) rest)

theorem decodeMemoryFields_ok {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τs : List Source.STy) (m : ByteView) (base : Nat)
    (fs : Source.DataList E.layout τs) (decoded : decodeMemoryFields p es τs m base = some fs) : Source.DataListOK E h.ty fs := by
  induction τs generalizing base with
  | nil => cases decoded; exact .nil
  | cons τ τs ih =>
    unfold decodeMemoryFields at decoded
    cases dv : decodeMemoryMember p es τ (mload m base) with
    | none => rw [dv] at decoded; cases decoded
    | some v =>
      cases dr : decodeMemoryFields p es τs m (base + 32) with
      | none => rw [dv, dr] at decoded; cases decoded
      | some rest =>
        rw [dv, dr] at decoded
        cases decoded
        exact .cons (.val (decodeMemoryMember_sound p es τ _ v dv).1) (ih _ rest dr)

theorem decodeMemoryFields_reads {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word}
    (fields : MemoryFields p fs ws) (supported : ∀ τ ∈ τs, OrdinaryMemberType τ)
    (m : ByteView) (base : Nat) (reads : ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w) :
    decodeMemoryFields p es τs m base = some fs := by
  induction fields generalizing base with
  | nil => rfl
  | @cons τ τs v w encoded fs ws rest ih =>
    have head := reads 0 w rfl
    simp only [Nat.zero_mul, Nat.add_zero] at head
    have tail : decodeMemoryFields p es τs m (base + 32) = some fs := by
      apply ih (fun σ hs => supported σ (List.mem_cons_of_mem _ hs))
      intro i word found
      have read := reads (i + 1) word found
      have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
      rwa [eq] at read
    simp only [decodeMemoryFields, head, decodeMemoryMember_encode p es coverage τ (supported τ List.mem_cons_self) v w encoded,
      tail]
    rfl

theorem decodeMemoryFields_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word}
    (fields : MemoryFields p fs ws) (supported : ∀ τ ∈ τs, OrdinaryMemberType τ) (m : ByteView) (base : Nat) :
    decodeMemoryFields p es τs (wordListView ws m base) base = some fs :=
  decodeMemoryFields_reads p es coverage fields supported _ _ (fun i w found => wordList_read ws m base i w found)

theorem decodeMemoryFields_representation {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τs : List Source.STy) (m : ByteView) (base : Nat)
    (fs : Source.DataList E.layout τs) (decoded : decodeMemoryFields p es τs m base = some fs) :
    ∃ ws, MemoryFields p fs ws ∧ (∀ i w, ws[i]? = some w → mload m (base + i * 32) = w) := by
  induction τs generalizing base with
  | nil => cases decoded; exact ⟨[], .nil, fun i w found => by cases i <;> cases found⟩
  | cons τ τs ih =>
    unfold decodeMemoryFields at decoded
    cases dv : decodeMemoryMember p es τ (mload m base) with
    | none => rw [dv] at decoded; cases decoded
    | some v =>
      cases dr : decodeMemoryFields p es τs m (base + 32) with
      | none => rw [dv, dr] at decoded; cases decoded
      | some rest =>
        rw [dv, dr] at decoded
        cases decoded
        obtain ⟨ws, fields, reads⟩ := ih _ rest dr
        refine ⟨mload m base :: ws, .cons v _ (decodeMemoryMember_sound p es τ _ v dv).2 rest ws fields, ?_⟩
        intro i w found
        cases i with
        | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Option.some.inj found
        | succ i =>
          have eq : base + (i + 1) * 32 = base + 32 + i * 32 := by omega
          rw [eq]
          exact reads i w found

def structHeapWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) : Option (Source.Heap D) :=
  (decodeMemoryFields p es (D.fields name) m (p.address root)).map
    (fun fs => h.write root (.struct fs) (heap_ty_of_get h root _ _ found))

theorem structHeapWriteback_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (ws : List Roadmap.Word) (fields : MemoryFields p old ws)
    (supported : ∀ τ ∈ D.fields name, OrdinaryMemberType τ) (m : ByteView)
    (reads : ∀ i w, ws[i]? = some w → mload m (p.address root + i * 32) = w) : structHeapWriteback h p es root name old found m = some h := by
  unfold structHeapWriteback
  rw [decodeMemoryFields_reads p es coverage fields supported m (p.address root) reads]
  simp only [Option.map_some, heap_write_unchanged h root _ _ found]

def structWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get root = some ⟨.struct .memory name, .struct old⟩) :
    Placement (h.write root (.struct fs) (heap_ty_of_get h root _ _ found)) :=
  heapWritePlacement h p root _ _ (by
    have shape := p.typed root _ _ found
    generalize he : p.shape root = sh at shape
    cases shape
    exact .strct fs)

def structStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (decodeMemoryFields p es (E.layout.fields name) m (p.address root)).map
    (fun fs => (Source.heapPut root ⟨.struct .memory name, .struct fs⟩).run s)

theorem structStateWriteback_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : structStateWriteback s p es root name m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst result
  obtain ⟨ws, fields, reads⟩ := decodeMemoryFields_representation p es _ m (p.address root) fs decoded
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

theorem decodedStruct_raw_reencode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (name : Source.DeclName) (m : ByteView) (base : Nat) (fs : Source.DataList E.layout (E.layout.fields name))
    (decoded : decodeMemoryFields p es (E.layout.fields name) m base = some fs) :
    ∃ ws, MemoryFields p fs ws ∧ wordListView ws m base = m := by
  obtain ⟨ws, fields, reads⟩ := decodeMemoryFields_representation p es _ m base fs decoded
  exact ⟨ws, fields, wordList_unchanged ws m base reads⟩

theorem structHeapWriteback_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName) (old fs : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (ws : List Roadmap.Word) (fields : MemoryFields p fs ws)
    (supported : ∀ τ ∈ D.fields name, OrdinaryMemberType τ) (m : ByteView) :
    structHeapWriteback h p es root name old found (wordListView ws m (p.address root)) =
      some (h.write root (.struct fs) (heap_ty_of_get h root _ _ found)) := by
  unfold structHeapWriteback
  rw [decodeMemoryFields_encode p es coverage fields supported]
  rfl

theorem structHeapWriteback_preservation {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) (out : Source.Heap D)
    (step : structHeapWriteback h p es root name old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ (∀ b, h.next ≤ b → out.cells b = none) ∧
    ∀ b, b ≠ root → out.get b = h.get b := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst out
  exact ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl,
    fun b hb => (h.write root _ _).bounded b hb, fun b hb => Source.Heap.write_other _ hb _ _⟩

theorem structWrittenPlacement_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get root = some ⟨.struct .memory name, .struct old⟩) :
    let q := structWrittenPlacement h p root name old fs found
    q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free := ⟨rfl, rfl, rfl⟩

theorem structHeapPut_run {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (root : Nat)
    (name : Source.DeclName) (fs : Source.DataList E.layout (E.layout.fields name))
    (typed : s.2.heap.ty root = some (.struct .memory name)) :
    (Source.heapPut root ⟨.struct .memory name, .struct fs⟩ : Source.EM E Γ Unit).run s =
      (.ok (), withSourceHeap s (s.2.heap.write root (.struct fs) typed)) := by
  rcases s with ⟨locals, state⟩
  unfold Source.heapPut
  rw [Source.Hoare.run_bind]
  change (if ht : state.heap.ty root = some (.struct .memory name) then
    Source.EM.setSt { state with heap := state.heap.write root (.struct fs) ht } else
    Source.EM.halt (.stuck "memory write type")).run ⟨locals, state⟩ = _
  rw [dif_pos typed]
  rfl

theorem structStateWriteback_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (root : Nat) (name : Source.DeclName) (old : Source.DataList E.layout (E.layout.fields name))
    (found : s.2.heap.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p old ws)
    (supported : ∀ τ ∈ E.layout.fields name, OrdinaryMemberType τ) (m : ByteView)
    (reads : ∀ i w, ws[i]? = some w → mload m (p.address root + i * 32) = w) :
    structStateWriteback s p es root name m = some (.ok (), s) := by
  unfold structStateWriteback
  rw [decodeMemoryFields_reads p es coverage fields supported m (p.address root) reads]
  simp only [Option.map_some]
  rw [structHeapPut_run s root name old (heap_ty_of_get s.2.heap root _ _ found),
    heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

def structHeapWriteback_resultPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) (out : Source.Heap D)
    (step : structHeapWriteback h p es root name old found m = some out) : Placement out := by
  cases decoded : decodeMemoryFields p es (D.fields name) m (p.address root) with
  | none =>
    unfold structHeapWriteback at step
    rw [decoded] at step
    cases step
  | some fs =>
    unfold structHeapWriteback at step
    rw [decoded] at step
    have same := Option.some.inj step
    subst out
    exact structWrittenPlacement h p root name old fs found

theorem decodedStruct_source_word {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (name : Source.DeclName) (m : ByteView) (base : Nat) (fs : Source.DataList E.layout (E.layout.fields name))
    (decoded : decodeMemoryFields p es (E.layout.fields name) m base = some fs)
    (off : Nat) (word : Roadmap.Word) (read : ObjectWord p.address (Source.Data.struct (l := .memory) fs) off word) :
    mload m (base + off) = word := by
  obtain ⟨ws, fields, reads⟩ := decodeMemoryFields_representation p es _ m base fs decoded
  have object : MemoryObjectWords p (Source.Data.struct (l := .memory) fs) ws := .strct fs ws fields
  obtain ⟨i, nth, eq⟩ := object.read off word read
  rw [eq]
  exact reads i word nth

theorem structFields_extent {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p fs ws) : ws.length * 32 = (p.shape root).size := by
  have length := fields.length
  rw [length]
  have shape := p.typed root _ _ found
  generalize eq : p.shape root = sh at shape
  cases shape
  rfl

theorem structFields_other_region {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p fs ws) (other : Nat) (owned : (h.cells other).isSome)
    (distinct : root ≠ other) (m : ByteView) (off : Nat) (inside : off < (p.shape other).size) :
    wordListView ws m (p.address root) (p.address other + off) = m (p.address other + off) := by
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have sep := p.separate root other present owned distinct
  have extent := structFields_extent h p root name old fs found ws fields
  apply wordList_residual
  omega

theorem structFields_reserved {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (root : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (_fields : MemoryFields p fs ws) (m : ByteView) (reserved : ReservedOK m p.free) :
    ReservedOK (wordListView ws m (p.address root)) p.free := by
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have start := p.starts root present
  constructor
  · have eq := mload_congr (wordListView ws m (p.address root)) m 64
      (fun i => wordList_residual ws m (p.address root) (64 + i.val) (Or.inl (by have hi := i.isLt; omega)))
    exact (congrArg Fin.val eq).trans reserved.1
  · intro i
    rw [wordList_residual ws m (p.address root) (96 + i.val) (Or.inl (by have hi := i.isLt; omega))]
    exact reserved.2 i

end Solidity.Yul.Views
