import Solidity.Calculus.Close

/-!
# The memory the updates allocate, kept symbolically

`sol_decide`'s target language (`Calculus/Decide.lean`) reads every value
in the state a formula starts in.  Memory needs no tree of writes there:
`TestSuite` has no memory parameter, so every object a leaf reads was
allocated by an update of the leaf itself, at the identity the state's
`nextId` gives, and each slot holds a word computed by a term of the
initial state, or a reference to another such object.  The updates are run
on that heap as they are pushed in (`Fml.toL`), and a read becomes the term
the slot holds.

* **Identities.**  The `k`-th object the updates allocate is the concrete
  identity `nextId + k` of the initial state: allocation writes at `nextId`
  and moves it (`State.alloc`), overwriting what was there, so no heap
  premise is needed and two allocations are apart by their offsets.
* **Objects** (`SObj`): a struct or an array of slots, a slot a word as a
  term or the offset of an object (`SMV`), laid out as the interpreter's
  `MObj` is, so that a read or a write is the same list operation on both
  sides (`lookupBy`, `setBy`, `List.set`): `SObj.conc` maps one to the other.
* **Defaults** come from the structural `dfltT?` (fuel, no well-founded
  recursion the kernel would have to unfold), proved equal to
  `defaultForTy` (`dfltT?_eq`); an allocation is the interpreter's
  `copyStToM` run on the symbolic heap (`sallocV`, `sallocV_rel`).
* **The relation** (`MemRel`): the heap holds each object at its identity
  and `nextId` is past them; every word term of the heap returns.

The leaves are a type parameter: the reads, the writes at an index and the
guards that make them exact are built from `LTerm`s in `Decide.lean`.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

variable {α : Type}

/-! ## Symbolic objects -/

/-- A slot of an object the updates allocated: a word, as the term that
computes it, or the `k`-th object allocated. -/
inductive SMV (α : Type) where
  | val (t : α)
  | ref (k : Nat)
  deriving Inhabited, Repr

/-- An object the updates allocated, laid out as `MObj`. -/
inductive SObj (α : Type) where
  | struct (fs : List (Name × SMV α))
  | array (es : List (SMV α)) (fx : Bool)
  deriving Inhabited, Repr

/-- The objects the updates allocated, the `k`-th at offset `k`. -/
abbrev SMem (α : Type) := List (SObj α)

/-- The concrete slot: the word the term returns (a junk `0` where it
halts, which `SMV.Ok` rules out), or the identity `b + k`. -/
def SMV.conc (ev : α → Res Value) (b : Nat) : SMV α → MVal
  | .val t =>
    match ev t with
    | .ok v => v.toMVal
    | .error _ => .int 0
  | .ref k => .ref (b + k)

/-- The concrete object. -/
def SObj.conc (ev : α → Res Value) (b : Nat) : SObj α → MObj
  | .struct fs => .struct (fs.map fun p => (p.1, p.2.conc ev b))
  | .array es fx => .array (es.map (SMV.conc ev b)) fx

/-- The slot's term returns. -/
def SMV.Ok (ev : α → Res Value) : SMV α → Prop
  | .val t => ∃ v, ev t = .ok v
  | .ref _ => True

/-- Every word term of the object returns. -/
def SObj.Ok (ev : α → Res Value) : SObj α → Prop
  | .struct fs => ∀ p ∈ fs, p.2.Ok ev
  | .array es _ => ∀ s ∈ es, s.Ok ev

/-- `τ`'s heap holds the objects `M`, the `k`-th at `b + k`, and allocates
past them. -/
structure MemRel (ev : α → Res Value) (b : Nat) (M : SMem α) (τ : State) : Prop where
  next : τ.nextId = b + M.length
  obj : ∀ k (hk : k < M.length), τ.getObj (b + k) = .ok ((M[k]'hk).conc ev b)
  ok : ∀ o ∈ M, o.Ok ev

/-- The relation reads the heap and `nextId` only. -/
theorem MemRel.of_heap {ev : α → Res Value} {b : Nat} {M : SMem α} {τ τ' : State}
    (h : MemRel ev b M τ) (hh : τ'.heap = τ.heap) (hn : τ'.nextId = τ.nextId) :
    MemRel ev b M τ' :=
  ⟨hn.trans h.next, fun k hk => by
    simp only [State.getObj, hh]; exact h.obj k hk, h.ok⟩

/-- The word terms of a slot. -/
def SMV.leaves : SMV α → List α
  | .val t => [t]
  | .ref _ => []

/-- The word terms of an object. -/
def SObj.leaves : SObj α → List α
  | .struct fs => fs.flatMap fun p => p.2.leaves
  | .array es _ => es.flatMap SMV.leaves

theorem SMV.conc_congr {ev ev' : α → Res Value} {b : Nat} :
    (s : SMV α) → (∀ t ∈ s.leaves, ev' t = ev t) → s.conc ev' b = s.conc ev b
  | .val t, h => by simp only [SMV.conc, h t (List.mem_singleton_self t)]
  | .ref _, _ => rfl

theorem SMV.ok_congr {ev ev' : α → Res Value} :
    (s : SMV α) → (∀ t ∈ s.leaves, ev' t = ev t) → (s.Ok ev' ↔ s.Ok ev)
  | .val t, h => by simp only [SMV.Ok, h t (List.mem_singleton_self t)]
  | .ref _, _ => Iff.rfl

theorem SObj.conc_congr {ev ev' : α → Res Value} {b : Nat} :
    (o : SObj α) → (∀ t ∈ o.leaves, ev' t = ev t) → o.conc ev' b = o.conc ev b
  | .struct fs, h => by
    simp only [SObj.conc, SObj.leaves, List.mem_flatMap] at h ⊢
    congr 1
    exact List.map_congr_left fun p hp => by
      rw [SMV.conc_congr p.2 fun t ht => h t ⟨p, hp, ht⟩]
  | .array es fx, h => by
    simp only [SObj.conc, SObj.leaves, List.mem_flatMap] at h ⊢
    congr 1
    exact List.map_congr_left fun s hs => SMV.conc_congr s fun t ht => h t ⟨s, hs, ht⟩

theorem SObj.ok_congr {ev ev' : α → Res Value} :
    (o : SObj α) → (∀ t ∈ o.leaves, ev' t = ev t) → (o.Ok ev' ↔ o.Ok ev)
  | .struct fs, h => by
    simp only [SObj.leaves, List.mem_flatMap] at h
    simp only [SObj.Ok]
    exact forall_congr' fun p => imp_congr_right fun hp =>
      SMV.ok_congr p.2 fun t ht => h t ⟨p, hp, ht⟩
  | .array es fx, h => by
    simp only [SObj.leaves, List.mem_flatMap] at h
    simp only [SObj.Ok]
    exact forall_congr' fun s => imp_congr_right fun hs =>
      SMV.ok_congr s fun t ht => h t ⟨s, hs, ht⟩

/-- The relation for another reading of the word terms that agrees with
this one on them: a quantified local the heap's terms do not read. -/
theorem MemRel.congr {ev ev' : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) (he : ∀ o ∈ M, ∀ t ∈ o.leaves, ev' t = ev t) : MemRel ev' b M τ :=
  ⟨h.next, fun k hk => by
    rw [SObj.conc_congr _ (he _ (List.getElem_mem hk))]; exact h.obj k hk,
    fun o ho => (SObj.ok_congr o (he o ho)).2 (h.ok o ho)⟩

/-- No object yet: `nextId` as it is. -/
theorem MemRel.empty (ev : α → Res Value) (τ : State) : MemRel ev τ.nextId [] τ :=
  ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _), fun _ ho => nomatch ho⟩

/-- A word of a returning term. -/
theorem SMV.conc_val {ev : α → Res Value} {b : Nat} {t : α} {v : Value} (h : ev t = .ok v) :
    (SMV.val t).conc ev b = v.toMVal := by
  simp only [SMV.conc, h]

/-! ## Lists of pairs -/

theorem lookupBy_map_conc {β γ : Type} (g : β → γ) (f : Name) :
    (fs : List (Name × β)) →
      lookupBy f (fs.map fun p => (p.1, g p.2)) = (lookupBy f fs).map g
  | [] => rfl
  | (n, x) :: rest => by
    simp only [List.map_cons, lookupBy]
    split
    · rfl
    · exact lookupBy_map_conc g f rest

theorem setBy_map_conc {β γ : Type} (g : β → γ) (f : Name) (s : β) :
    (fs : List (Name × β)) →
      (setBy f s fs).map (fun p => (p.1, g p.2)) = setBy f (g s) (fs.map fun p => (p.1, g p.2))
  | [] => rfl
  | (n, x) :: rest => by
    simp only [setBy, List.map_cons]
    split
    · rfl
    · simp only [List.map_cons, setBy_map_conc g f s rest]

theorem mem_setBy_name {β : Type} {f : Name} {s : β} :
    (fs : List (Name × β)) → ∀ p ∈ setBy f s fs, p = (f, s) ∨ p ∈ fs
  | [], p, hp => by
    simp only [setBy, List.mem_cons, List.not_mem_nil, or_false] at hp
    exact .inl hp
  | (n, x) :: rest, p, hp => by
    simp only [setBy] at hp
    split at hp
    · simp only [List.mem_cons] at hp
      rcases hp with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at hp
      rcases hp with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases mem_setBy_name rest p h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_cons_of_mem _ h')

theorem lookupBy_mem_name {β : Type} {f : Name} {x : β} :
    (fs : List (Name × β)) → lookupBy f fs = some x → (f, x) ∈ fs
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (n, y) :: rest, h => by
    simp only [lookupBy] at h
    split at h
    · rename_i hn
      cases h
      subst hn
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupBy_mem_name rest h)

/-! ## Writes on both sides -/

/-- Setting an object in the heap: the concrete `setObj` at its identity. -/
theorem MemRel.set {ev : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) {k : Nat} (_hk : k < M.length) (o : SObj α) (ho : o.Ok ev) :
    MemRel ev b (M.set k o) (τ.setObj (b + k) (o.conc ev b)) := by
  refine ⟨by simp only [State.setObj, List.length_set]; exact h.next, fun j hj => ?_,
    fun o' ho' => ?_⟩
  · have hj' : j < M.length := by simpa only [List.length_set] using hj
    simp only [State.getObj, State.setObj, List.getElem_set]
    by_cases hjk : k = j
    · subst hjk
      simp only [lookupBy_setBy_self, ↓reduceIte]
    · rw [lookupBy_setBy_ne (by omega), if_neg hjk]
      exact h.obj j hj'
  · rcases List.mem_or_eq_of_mem_set ho' with h' | h'
    · exact h.ok o' h'
    · exact h' ▸ ho

/-- Allocating an object: the concrete `alloc`, at the next identity. -/
theorem MemRel.alloc {ev : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) (o : SObj α) (ho : o.Ok ev) :
    (τ.alloc (o.conc ev b)).2 = b + M.length ∧
      MemRel ev b (M ++ [o]) (τ.alloc (o.conc ev b)).1 := by
  have hn : (τ.alloc (o.conc ev b)).1.nextId = b + (M ++ [o]).length := by
    simp only [State.alloc, List.length_append, List.length_singleton, h.next]
    omega
  refine ⟨h.next, ⟨hn, fun j hj => ?_, fun o' ho' => ?_⟩⟩
  · simp only [List.length_append, List.length_singleton] at hj
    simp only [State.getObj, State.alloc, h.next]
    by_cases hjk : j = M.length
    · subst hjk
      simp only [lookupBy_setBy_self, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_singleton]
    · have hj' : j < M.length := by omega
      rw [lookupBy_setBy_ne (by omega), List.getElem_append_left hj']
      exact h.obj j hj'
  · rcases List.mem_append.1 ho' with h' | h'
    · exact h.ok o' h'
    · rw [List.mem_singleton] at h'
      exact h' ▸ ho

/-- A member written: the concrete `memWriteField`. -/
theorem MemRel.writeField {ev : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) {k : Nat} (hk : k < M.length) {fs : List (Name × SMV α)}
    (hfs : M[k] = .struct fs) (f : Name) {s : SMV α} (hs : s.Ok ev) :
    memWriteField τ (b + k) f (s.conc ev b) =
      .ok (τ.setObj (b + k) ((SObj.struct (setBy f s fs)).conc ev b)) ∧
    MemRel ev b (M.set k (.struct (setBy f s fs))) (τ.setObj (b + k)
      ((SObj.struct (setBy f s fs)).conc ev b)) := by
  refine ⟨?_, h.set hk _ ?_⟩
  · simp only [memWriteField, h.obj k hk, hfs, SObj.conc, bind, Except.bind,
      setBy_map_conc (SMV.conc ev b)]
  · intro p hp
    rcases mem_setBy_name fs p hp with h' | h'
    · exact h' ▸ hs
    · have hO : (SObj.struct fs).Ok ev := hfs ▸ h.ok _ (List.getElem_mem hk)
      exact hO p h'

/-- An element written at an index in range: the concrete `memWriteIndex`. -/
theorem MemRel.writeIndex {ev : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) {k : Nat} (hk : k < M.length) {es : List (SMV α)} {fx : Bool}
    (hes : M[k] = .array es fx) {i : Int} (hi : 0 ≤ i ∧ i.toNat < es.length) {s : SMV α}
    (hs : s.Ok ev) :
    memWriteIndex τ (b + k) i (s.conc ev b) =
      .ok (τ.setObj (b + k) ((SObj.array (es.set i.toNat s) fx).conc ev b)) ∧
    MemRel ev b (M.set k (.array (es.set i.toNat s) fx)) (τ.setObj (b + k)
      ((SObj.array (es.set i.toNat s) fx).conc ev b)) := by
  refine ⟨?_, h.set hk _ ?_⟩
  · have hi' : 0 ≤ i ∧ i.toNat < (es.map (SMV.conc ev b)).length := by
      simpa only [List.length_map] using hi
    simp only [memWriteIndex, h.obj k hk, hes, SObj.conc, bind, Except.bind, if_pos hi',
      List.map_set]
  · intro s' hs'
    rcases List.mem_or_eq_of_mem_set hs' with h' | h'
    · have hO : (SObj.array es fx).Ok ev := hes ▸ h.ok _ (List.getElem_mem hk)
      exact hO s' h'
    · exact h' ▸ hs

/-- An index out of range reverts. -/
theorem MemRel.writeIndex_out {ev : α → Res Value} {b : Nat} {M : SMem α} {τ : State}
    (h : MemRel ev b M τ) {k : Nat} (hk : k < M.length) {es : List (SMV α)} {fx : Bool}
    (hes : M[k] = .array es fx) {i : Int} (hi : ¬ (0 ≤ i ∧ i.toNat < es.length)) (mv : MVal) :
    memWriteIndex τ (b + k) i mv = .error .revert := by
  have hi' : ¬ (0 ≤ i ∧ i.toNat < (es.map (SMV.conc ev b)).length) := by
    simpa only [List.length_map] using hi
  simp only [memWriteIndex, h.obj k hk, hes, SObj.conc, bind, Except.bind, if_neg hi']

/-! ## Defaults by structural recursion -/

/-- `defaultForTy`, by structural recursion on a depth bound (`none` where it
runs out), so that the kernel evaluates it. -/
def dfltT? : Nat → Ty → Option SVal
  | _, .prim .bool => some (.bool false)
  | _, .prim .uint => some (.int 0)
  | _, .prim .int => some (.int 0)
  | 0, .ref _ => none
  | n + 1, .ref (.struct s) =>
    ((structDef s).mapM fun p => (dfltT? n p.2).map fun v => (p.1, v)).map .struct
  | _ + 1, .ref (.array _) => some (.array [] [] false)
  | n + 1, .ref (.fixed E k) => (dfltT? n E).map fun v => .array (List.replicate k v) [] true
  | n + 1, .ref (.mapping _ V) => (dfltT? n V).map (.map [])

theorem dfltFs_eq {n : Nat} (ih : ∀ T v, dfltT? n T = some v → v = defaultForTy T) :
    (l : List (Name × Ty)) → ∀ {fs : List (Name × SVal)},
      l.mapM (fun p => (dfltT? n p.2).map fun v => (p.1, v)) = some fs → fs = defaultForFields l
  | [], fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rw [defaultForFields]
  | (f, T) :: rest, fs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨_, ⟨v, hv, rfl⟩, fs', hfs', rfl⟩ := h
    rw [defaultForFields, ih T v hv, dfltFs_eq ih rest hfs']

/-- The structural default is the interpreter's. -/
theorem dfltT?_eq : (n : Nat) → ∀ (T : Ty) {v : SVal}, dfltT? n T = some v → v = defaultForTy T
  | n, .prim .bool, v, h | n, .prim .uint, v, h | n, .prim .int, v, h => by
    cases n <;> simp only [dfltT?, Option.some.injEq] at h <;> subst h <;> rw [defaultForTy]
  | 0, .ref _, v, h => by simp only [dfltT?, reduceCtorEq] at h
  | n + 1, .ref (.struct s), v, h => by
    simp only [dfltT?, Option.map_eq_some_iff] at h
    obtain ⟨fs, hfs, rfl⟩ := h
    rw [defaultForTy, dfltFs_eq (dfltT?_eq n) _ hfs]
  | n + 1, .ref (.array _), v, h => by
    simp only [dfltT?, Option.some.injEq] at h
    subst h; rw [defaultForTy]
  | n + 1, .ref (.fixed E k), v, h => by
    simp only [dfltT?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    rw [defaultForTy, dfltT?_eq n E hd]
  | n + 1, .ref (.mapping _ V), v, h => by
    simp only [dfltT?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    rw [defaultForTy, dfltT?_eq n V hd]

/-- The depth bound the closer uses: every struct of `structDef` nests less
deep (a default past it is `none`, and the allocation is left alone). -/
def dfltFuel : Nat := 8

/-! ## Allocation on both sides -/

mutual

/-- `copyStToM` on the symbolic heap: a copy of the storage value `v`,
its words as literals (`lit`), each struct and array a new object after its
members. -/
def sallocV (lit : Value → α) (M : SMem α) : SVal → Option (SMem α × SMV α)
  | .prim p => some (M, .val (lit p))
  | .struct fs =>
    match sallocFs lit M fs with
    | some (M', mfs) => some (M' ++ [.struct mfs], .ref M'.length)
    | none => none
  | .array es _ fx =>
    match sallocEs lit M es with
    | some (M', mes) => some (M' ++ [.array mes fx], .ref M'.length)
    | none => none
  | .map _ _ => none

def sallocFs (lit : Value → α) (M : SMem α) :
    List (Name × SVal) → Option (SMem α × List (Name × SMV α))
  | [] => some (M, [])
  | (n, v) :: rest =>
    match sallocV lit M v with
    | some (M₁, s) =>
      match sallocFs lit M₁ rest with
      | some (M₂, ss) => some (M₂, (n, s) :: ss)
      | none => none
    | none => none

def sallocEs (lit : Value → α) (M : SMem α) : List SVal → Option (SMem α × List (SMV α))
  | [] => some (M, [])
  | v :: rest =>
    match sallocV lit M v with
    | some (M₁, s) =>
      match sallocEs lit M₁ rest with
      | some (M₂, ss) => some (M₂, s :: ss)
      | none => none
    | none => none

end

section Alloc

variable {ev : α → Res Value} {lit : Value → α} (hlit : ∀ v, ev (lit v) = .ok v) {b : Nat}
include hlit

mutual

/-- **An allocation, symbolically and concretely**: the copy lands on the
objects `sallocV` lists, at the identities their offsets give. -/
theorem sallocV_rel : (v : SVal) → ∀ {M M' : SMem α} {s : SMV α} {τ : State},
    MemRel ev b M τ → sallocV lit M v = some (M', s) →
      s.Ok ev ∧ ∃ τ', copyStToM τ v = .ok (τ', s.conc ev b) ∧ MemRel ev b M' τ'
  | .prim p, M, M', s, τ, h, hs => by
    simp only [sallocV, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨⟨p, hlit p⟩, τ, ?_, h⟩
    cases p <;> simp only [copyStToM, SMV.conc, hlit, Value.toMVal]
  | .struct fs, M, M', s, τ, h, hs => by
    simp only [sallocV] at hs
    split at hs
    · rename_i M₁ mfs hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hok, τ₁, h₁, hr⟩ := sallocFs_rel fs h hf
      obtain ⟨hid, hr'⟩ := hr.alloc (.struct mfs) hok
      refine ⟨trivial, _, ?_, hr'⟩
      simp only [copyStToM, h₁, bind, Except.bind, SMV.conc, ← hid, SObj.conc]
    · simp only [reduceCtorEq] at hs
  | .array es sh fx, M, M', s, τ, h, hs => by
    simp only [sallocV] at hs
    split at hs
    · rename_i M₁ mes he
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hok, τ₁, h₁, hr⟩ := sallocEs_rel es h he
      obtain ⟨hid, hr'⟩ := hr.alloc (.array mes fx) hok
      refine ⟨trivial, _, ?_, hr'⟩
      simp only [copyStToM, h₁, bind, Except.bind, SMV.conc, ← hid, SObj.conc]
    · simp only [reduceCtorEq] at hs
  | .map _ _, _, _, _, _, _, hs => by simp only [sallocV, reduceCtorEq] at hs

theorem sallocFs_rel : (fs : List (Name × SVal)) → ∀ {M M' : SMem α}
    {mfs : List (Name × SMV α)} {τ : State},
    MemRel ev b M τ → sallocFs lit M fs = some (M', mfs) →
      (∀ p ∈ mfs, p.2.Ok ev) ∧ ∃ τ', copyStFields τ fs =
        .ok (τ', mfs.map fun p => (p.1, p.2.conc ev b)) ∧ MemRel ev b M' τ'
  | [], M, M', mfs, τ, h, hs => by
    simp only [sallocFs, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨(fun _ hp => nomatch hp), τ, rfl, h⟩
  | (n, v) :: rest, M, M', mfs, τ, h, hs => by
    simp only [sallocFs] at hs
    split at hs
    · rename_i M₁ s hv
      split at hs
      · rename_i M₂ ss hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨hok₁, τ₁, h₁, hr₁⟩ := sallocV_rel v h hv
        obtain ⟨hok₂, τ₂, h₂, hr₂⟩ := sallocFs_rel rest hr₁ hr
        refine ⟨fun p hp => ?_, τ₂, ?_, hr₂⟩
        · rcases List.mem_cons.1 hp with hp | hp
          · exact hp ▸ hok₁
          · exact hok₂ p hp
        · simp only [copyStFields, h₁, h₂, bind, Except.bind, List.map_cons]
      · simp only [reduceCtorEq] at hs
    · simp only [reduceCtorEq] at hs

theorem sallocEs_rel : (es : List SVal) → ∀ {M M' : SMem α} {mes : List (SMV α)} {τ : State},
    MemRel ev b M τ → sallocEs lit M es = some (M', mes) →
      (∀ s ∈ mes, s.Ok ev) ∧ ∃ τ', copyStElems τ es =
        .ok (τ', mes.map (SMV.conc ev b)) ∧ MemRel ev b M' τ'
  | [], M, M', mes, τ, h, hs => by
    simp only [sallocEs, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨(fun _ hp => nomatch hp), τ, rfl, h⟩
  | v :: rest, M, M', mes, τ, h, hs => by
    simp only [sallocEs] at hs
    split at hs
    · rename_i M₁ s hv
      split at hs
      · rename_i M₂ ss hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨hok₁, τ₁, h₁, hr₁⟩ := sallocV_rel v h hv
        obtain ⟨hok₂, τ₂, h₂, hr₂⟩ := sallocEs_rel rest hr₁ hr
        refine ⟨fun p hp => ?_, τ₂, ?_, hr₂⟩
        · rcases List.mem_cons.1 hp with hp | hp
          · exact hp ▸ hok₁
          · exact hok₂ p hp
        · simp only [copyStElems, h₁, h₂, bind, Except.bind, List.map_cons]
      · simp only [reduceCtorEq] at hs
    · simp only [reduceCtorEq] at hs

end

end Alloc

/-- The default `R` allocated, and the offset of its top object:
`addM(memory, R)` and `freshId(addM(memory, R))`. -/
def sallocR (lit : Value → α) (M : SMem α) (R : RefTy) : Option (SMem α × Nat) :=
  match dfltT? dfltFuel (.ref R) with
  | some v =>
    match sallocV lit M v with
    | some (M', .ref k) => some (M', k)
    | _ => none
  | none => none

/-- `new R(n)`'s value, `newArrVal`, with the structural default. -/
def newArrS (R : RefTy) (n : Int) : Option SVal :=
  match R with
  | .array E => (dfltT? dfltFuel E).map fun d => .array (List.replicate n.toNat d) [] false
  | R => dfltT? dfltFuel (.ref R)

theorem newArrS_eq {R : RefTy} {n : Int} {v : SVal} (h : newArrS R n = some v) :
    v = newArrVal R n := by
  cases R with
  | array E =>
    simp only [newArrS, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    rw [newArrVal, dfltT?_eq _ _ hd]
  | struct _ | fixed _ _ | mapping _ _ =>
    simp only [newArrS] at h
    rw [dfltT?_eq _ _ h]
    rfl

/-- The copy `new R(n)` allocates, and the offset of its top object:
`copySt(memory, newArr(R, n))` and its `freshId`. -/
def sallocNew (lit : Value → α) (M : SMem α) (R : RefTy) (n : Int) : Option (SMem α × Nat) :=
  match newArrS R n with
  | some v =>
    match sallocV lit M v with
    | some (M', .ref k) => some (M', k)
    | _ => none
  | none => none

section Alloc

variable {ev : α → Res Value} {lit : Value → α} (hlit : ∀ v, ev (lit v) = .ok v) {b : Nat}
include hlit

/-- `allocDefault` on both sides. -/
theorem sallocR_rel {M M' : SMem α} {R : RefTy} {k : Nat} {τ : State} (h : MemRel ev b M τ)
    (hs : sallocR lit M R = some (M', k)) :
    ∃ τ', allocDefault τ R = .ok (τ', b + k) ∧ MemRel ev b M' τ' := by
  unfold sallocR at hs
  split at hs
  · rename_i v hv
    split at hs
    · rename_i M₁ k₁ ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨-, τ', h₁, hr⟩ := sallocV_rel hlit v h ha
      refine ⟨τ', ?_, hr⟩
      rw [dfltT?_eq _ _ hv] at h₁
      simp only [allocDefault, defaultForRef, h₁, SMV.conc]
    · simp only [reduceCtorEq] at hs
  · simp only [reduceCtorEq] at hs

/-- `copyStToM` of `new R(n)`'s value on both sides. -/
theorem sallocNew_rel {M M' : SMem α} {R : RefTy} {n : Int} {k : Nat} {τ : State}
    (h : MemRel ev b M τ) (hs : sallocNew lit M R n = some (M', k)) :
    ∃ τ', copyStToM τ (newArrVal R n) = .ok (τ', .ref (b + k)) ∧ MemRel ev b M' τ' := by
  unfold sallocNew at hs
  split at hs
  · rename_i v hv
    split at hs
    · rename_i M₁ k₁ ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨-, τ', h₁, hr⟩ := sallocV_rel hlit v h ha
      rw [newArrS_eq hv] at h₁
      exact ⟨τ', h₁, hr⟩
    · simp only [reduceCtorEq] at hs
  · simp only [reduceCtorEq] at hs

end Alloc

end Decide

end Solidity
