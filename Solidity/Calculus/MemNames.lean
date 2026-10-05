import Solidity.Calculus.ReadWrite
import Solidity.Theory.Terms

/-!
# Memory objects named by their birth

The interpreter facts the memory closer's clauses rest on.  solkey names a
memory object by its root and a path, `idC(freshIdp, flds)`, and its read
taclets (`memoryRules.key`, `structMemoryRules.key`) never look at a heap:
two names are the same object exactly when they are the same name.  The
interpreter gives every object a number instead, so this module proves that
the numbers a copy allocates behave as names do.

* **A copy is a tree** (`Owned`).  `copyStToM` allocates the children first
  and the root last, each child a copy of its own, so every object a path
  from the root reaches lies in the interval of counters the copy used
  (`copyStToM_interval`), and two paths that reach one object are one path
  (`copyStToM_resolve_inj`).  Two allocations use disjoint intervals; so a
  write at `x.a.v` leaves `x.b.v` and every other root's objects alone.
* **A name is fixed at its birth** (`Birth`, `Births.eval`).  A name denotes
  `Theory.Memory.resolveFrom` in the heap the allocation left, as KeY's
  `\unique idC` does, whatever is written later; a reference written later
  is seen through the slot it is written to, never by renaming
  (`birth_slot`).
* **A copy reads as its source** (`copyStToM_readPath`, `copyMToSt_readPath`):
  a path through the copy into memory reads the copy of what `findLive`
  reads in storage, and a path through a view of memory as storage reads
  the copy of what memory holds there.  A length is not a slot of memory, so
  `.field "length"` is answered apart (`copyStToM_lenPath`, `copyMToSt_arrLen`).
* **What halting changes** (Lean only; KeY's functions are total).
  `copyMToSt` halts on a cycle: it succeeds where every reference points to
  an older object of the interval (`DescFrom`, `copyMToSt_ok_desc`), which a
  copy into memory leaves and a write of an older reference keeps.
  `copyStToM` halts on a mapping: it succeeds on a canonical value of a type
  with none (`copyStToM_ok_noMap`); and a copy out of memory holds no
  mapping (`copyMToSt_noMap`).
-/

namespace Solidity

namespace MemNames

open Semantics SemanticsProperties
open Theory.Memory (resolveFrom step)

/-! ## Lists and heaps -/

theorem lookupBy_index {κ α : Type} [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → ∃ i : Nat, l[i]? = some (k, v)
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k', v') :: rest, h => by
    simp only [lookupBy] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨0, by simp only [hk, List.getElem?_cons_zero]⟩
    · obtain ⟨i, hi⟩ := lookupBy_index h
      exact ⟨i + 1, by simpa only [List.getElem?_cons_succ] using hi⟩

theorem lookupBy_mem_keys {κ α : Type} [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v → k ∈ l.map Prod.fst
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k', v') :: rest, h => by
    simp only [lookupBy] at h
    split at h
    · rename_i hk
      simp only [hk, List.map_cons, List.mem_cons, true_or]
    · simp only [List.map_cons, List.mem_cons, lookupBy_mem_keys h, or_true]

theorem mem_setBy {κ α : Type} [DecidableEq κ] {k : κ} {v : α} {x : κ × α} :
    ∀ {l : List (κ × α)}, x ∈ setBy k v l → x = (k, v) ∨ x ∈ l
  | [], h => by simp only [setBy, List.mem_cons, List.not_mem_nil, or_false] at h; exact .inl h
  | (k', v') :: rest, h => by
    simp only [setBy] at h
    split at h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact .inr (.inl h)
      · rcases mem_setBy h with h | h
        · exact .inl h
        · exact .inr (.inr h)

theorem resolveFrom_cons {h : List (Nat × MObj)} {n m : Nat} {a : Seg} {rest : List Seg} :
    resolveFrom h n (a :: rest) = some m ↔ ∃ c, step h n a = some c ∧ resolveFrom h c rest = some m := by
  simp only [resolveFrom]
  cases step h n a with
  | none => simp only [reduceCtorEq, false_and, exists_false]
  | some c => simp only [Option.some.injEq, exists_eq_left']

theorem resolveFrom_append (h : List (Nat × MObj)) :
    ∀ (n : Nat) (p q : List Seg), resolveFrom h n (p ++ q) = (resolveFrom h n p).bind (resolveFrom h · q)
  | n, [], q => by simp only [List.nil_append, resolveFrom, Option.bind_some]
  | n, a :: p, q => by
    simp only [List.cons_append, resolveFrom]
    cases step h n a with
    | none => rfl
    | some c => exact resolveFrom_append h c p q

theorem step_struct {h : List (Nat × MObj)} {n c : Nat} {fs : List (Name × MVal)} {a : Seg}
    (hobj : lookupBy n h = some (.struct fs)) (hs : step h n a = some c) :
    ∃ f, a = .field f ∧ lookupBy f fs = some (.ref c) := by
  cases a with
  | field f =>
    simp only [step, hobj] at hs
    split at hs
    · rename_i m hm
      cases hs
      exact ⟨f, rfl, hm⟩
    · cases hs
  | «at» i => simp only [step, hobj, reduceCtorEq] at hs

theorem step_array {h : List (Nat × MObj)} {n c : Nat} {es : List MVal} {fx : Bool} {a : Seg}
    (hobj : lookupBy n h = some (.array es fx)) (hs : step h n a = some c) :
    ∃ k, a = .at k ∧ 0 ≤ k ∧ es[k.toNat]? = some (.ref c) := by
  cases a with
  | field f => simp only [step, hobj, reduceCtorEq] at hs
  | «at» k =>
    simp only [step, hobj] at hs
    split at hs
    · rename_i hb
      split at hs
      · rename_i m hm
        cases hs
        exact ⟨k, rfl, hb.1, by simp only [List.getElem?_eq_getElem hb.2, ← hm, List.get_eq_getElem]⟩
      · cases hs
    · cases hs

/-- A step of a path is a read of a reference slot. -/
theorem step_iff_readAddr (τ : State) (m m' : Nat) (a : Seg) :
    step τ.heap m a = some m' ↔ readAddr τ (.ofSeg m a) = .ok (.ref m') := by
  cases a with
  | field f =>
    simp only [step, Addr.ofSeg, readAddr, State.getObj]
    cases lookupBy m τ.heap with
    | none => simp only [reduceCtorEq, bind, Except.bind]
    | some obj =>
      cases obj with
      | array es fx => simp only [reduceCtorEq, bind, Except.bind]
      | struct fs =>
        simp only [bind, Except.bind]
        cases lookupBy f fs with
        | none => simp only [reduceCtorEq]
        | some v =>
          cases v with
          | prim p => simp only [reduceCtorEq, pure, Except.pure, Except.ok.injEq]
          | ref r => simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq, MVal.ref.injEq]
  | «at» k =>
    simp only [step, Addr.ofSeg, readAddr, State.getObj]
    cases lookupBy m τ.heap with
    | none => simp only [reduceCtorEq, bind, Except.bind]
    | some obj =>
      cases obj with
      | struct fs => simp only [reduceCtorEq, bind, Except.bind]
      | array es fx =>
        simp only [bind, Except.bind]
        by_cases hb : 0 ≤ k ∧ k.toNat < es.length
        · simp only [hb, and_self, dite_true, pure, Except.pure]
          cases es.get ⟨k.toNat, hb.2⟩ with
          | prim p => simp only [reduceCtorEq, Except.ok.injEq]
          | ref r => simp only [Option.some.injEq, Except.ok.injEq, MVal.ref.injEq]
        · simp only [hb, dite_false, reduceCtorEq]

/-! ## The inversions of a copy into memory -/

theorem copyStToM_struct_inv {σ τ : State} {fs : List (Name × SVal)} {mv : MVal}
    (h : copyStToM σ (.struct fs) = .ok (τ, mv)) :
    ∃ τ₁ mfs, copyStFields σ fs = .ok (τ₁, mfs) ∧ τ = (τ₁.alloc (.struct mfs)).1 ∧
      mv = .ref τ₁.nextId := by
  rw [copyStToM] at h
  cases hf : copyStFields σ fs with
  | error e => rw [hf] at h; exact absurd h (by simp only [bind, Except.bind, reduceCtorEq, not_false_eq_true])
  | ok tf =>
    obtain ⟨τ₁, mfs⟩ := tf
    rw [hf] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
    exact ⟨τ₁, mfs, rfl, h.1.symm, h.2.symm⟩

theorem copyStToM_array_inv {σ τ : State} {es sh : List SVal} {fx : Bool} {mv : MVal}
    (h : copyStToM σ (.array es sh fx) = .ok (τ, mv)) :
    ∃ τ₁ mes, copyStElems σ es = .ok (τ₁, mes) ∧ τ = (τ₁.alloc (.array mes fx)).1 ∧
      mv = .ref τ₁.nextId := by
  rw [copyStToM] at h
  cases he : copyStElems σ es with
  | error e => rw [he] at h; exact absurd h (by simp only [bind, Except.bind, reduceCtorEq, not_false_eq_true])
  | ok te =>
    obtain ⟨τ₁, mes⟩ := te
    rw [he] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, State.alloc] at h
    exact ⟨τ₁, mes, rfl, h.1.symm, h.2.symm⟩

theorem copyStToM_prim_inv {σ τ : State} {p : PrimVal} {mv : MVal}
    (h : copyStToM σ (.prim p) = .ok (τ, mv)) : τ = σ ∧ mv = .prim p := by
  cases p <;> simp only [copyStToM, Except.ok.injEq, Prod.mk.injEq] at h <;>
    exact ⟨h.1.symm, h.2.symm⟩

theorem copyStToM_map_inv {σ τ : State} {e : List (Int × SVal)} {d : SVal} {mv : MVal}
    (h : copyStToM σ (.map e d) = .ok (τ, mv)) : False := by
  simp only [copyStToM, reduceCtorEq] at h

theorem copyStFields_nil_inv {σ τ : State} {mfs : List (Name × MVal)}
    (h : copyStFields σ [] = .ok (τ, mfs)) : τ = σ ∧ mfs = [] := by
  simp only [copyStFields, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem copyStFields_cons_inv {σ τ : State} {n : Name} {v : SVal} {rest : List (Name × SVal)}
    {mfs : List (Name × MVal)} (h : copyStFields σ ((n, v) :: rest) = .ok (τ, mfs)) :
    ∃ σ₁ mv mrest, copyStToM σ v = .ok (σ₁, mv) ∧ copyStFields σ₁ rest = .ok (τ, mrest) ∧
      mfs = (n, mv) :: mrest := by
  rw [copyStFields] at h
  cases h1 : copyStToM σ v with
  | error e => simp only [h1, bind, Except.bind, reduceCtorEq] at h
  | ok p =>
    obtain ⟨σ₁, mv⟩ := p
    cases h2 : copyStFields σ₁ rest with
    | error e => simp only [h1, h2, bind, Except.bind, reduceCtorEq] at h
    | ok q =>
      obtain ⟨σ₂, mrest⟩ := q
      simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ₁, mv, mrest, rfl, h2, rfl⟩

theorem copyStElems_nil_inv {σ τ : State} {mes : List MVal}
    (h : copyStElems σ [] = .ok (τ, mes)) : τ = σ ∧ mes = [] := by
  simp only [copyStElems, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem copyStElems_cons_inv {σ τ : State} {v : SVal} {rest : List SVal} {mes : List MVal}
    (h : copyStElems σ (v :: rest) = .ok (τ, mes)) :
    ∃ σ₁ mv mrest, copyStToM σ v = .ok (σ₁, mv) ∧ copyStElems σ₁ rest = .ok (τ, mrest) ∧
      mes = mv :: mrest := by
  rw [copyStElems] at h
  cases h1 : copyStToM σ v with
  | error e => simp only [h1, bind, Except.bind, reduceCtorEq] at h
  | ok p =>
    obtain ⟨σ₁, mv⟩ := p
    cases h2 : copyStElems σ₁ rest with
    | error e => simp only [h1, h2, bind, Except.bind, reduceCtorEq] at h
    | ok q =>
      obtain ⟨σ₂, mrest⟩ := q
      simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ₁, mv, mrest, rfl, h2, rfl⟩

/-- The object an allocation wrote, in any heap extending the one it left. -/
theorem alloc_ext {τ₁ τ τ' : State} {obj : MObj} (hτ : τ = (τ₁.alloc obj).1) (hx : τ.HeapExt τ') :
    lookupBy τ₁.nextId τ'.heap = some obj ∧ τ₁.HeapExt τ' ∧ τ.nextId = τ₁.nextId + 1 := by
  subst hτ
  refine ⟨?_, (State.HeapExt.alloc τ₁ obj).trans hx, rfl⟩
  rw [hx.2 τ₁.nextId (Nat.lt_succ_self _)]
  exact lookupBy_setBy_self _ _ _

/-! ## A copy is a tree -/

/-- `mv` names a tree of objects of the heap `h` in `[lo, hi)`: every object
a path from it reaches is in the interval, and two paths that reach one
object are one path.  A primitive names none. -/
def Owned (h : List (Nat × MObj)) (lo hi : Nat) : MVal → Prop
  | .prim _ => True
  | .ref c => (∀ p m, resolveFrom h c p = some m → lo ≤ m ∧ m < hi) ∧
      (∀ p q m, resolveFrom h c p = some m → resolveFrom h c q = some m → p = q)

theorem Owned.ref_iff {h : List (Nat × MObj)} {lo hi c : Nat} :
    Owned h lo hi (.ref c) ↔ (∀ p m, resolveFrom h c p = some m → lo ≤ m ∧ m < hi) ∧
      (∀ p q m, resolveFrom h c p = some m → resolveFrom h c q = some m → p = q) := Iff.rfl

/-- The slots of one object, each a tree in its own interval, the intervals
in order: what a list copy leaves. -/
inductive Chain (h : List (Nat × MObj)) : Nat → Nat → List MVal → Prop
  | nil (lo : Nat) : Chain h lo lo []
  | cons {lo mid hi : Nat} {mv : MVal} {rest : List MVal} :
      lo ≤ mid → Owned h lo mid mv → Chain h mid hi rest → Chain h lo hi (mv :: rest)

theorem Chain.le {h : List (Nat × MObj)} {lo hi : Nat} {l : List MVal} (hc : Chain h lo hi l) :
    lo ≤ hi := by
  induction hc with
  | nil => exact Nat.le_refl _
  | cons hlm _ _ ih => exact Nat.le_trans hlm ih

theorem Chain.get {h : List (Nat × MObj)} {lo hi : Nat} {l : List MVal} (hc : Chain h lo hi l) :
    ∀ {i : Nat} {mv : MVal}, l[i]? = some mv → ∃ x y, lo ≤ x ∧ x ≤ y ∧ y ≤ hi ∧ Owned h x y mv := by
  induction hc with
  | nil => intro i mv hi; simp only [List.getElem?_nil, reduceCtorEq] at hi
  | cons hlm ho hr ih =>
    intro i mv hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, _, Nat.le_refl _, hlm, hr.le, ho⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨x, y, hx, hxy, hy, ho'⟩ := ih hi
      exact ⟨x, y, Nat.le_trans hlm hx, hxy, hy, ho'⟩

/-- Two slots of a chain name trees that share no object. -/
theorem Chain.apart {h : List (Nat × MObj)} {lo hi : Nat} {l : List MVal} (hc : Chain h lo hi l) :
    ∀ {i j c₁ c₂ m : Nat} {p q : List Seg}, i ≠ j → l[i]? = some (.ref c₁) → l[j]? = some (.ref c₂) →
      resolveFrom h c₁ p = some m → resolveFrom h c₂ q = some m → False := by
  induction hc with
  | nil => intro i j c₁ c₂ m p q _ hi; simp only [List.getElem?_nil, reduceCtorEq] at hi
  | cons hlm ho hr ih =>
    intro i j c₁ c₂ m p q hij hi hj hp hq
    cases i with
    | zero =>
      cases j with
      | zero => exact hij rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [List.getElem?_cons_succ] at hj
        obtain ⟨x, y, hx, -, -, ho'⟩ := hr.get hj
        have h1 := (Owned.ref_iff.1 ho).1 p m hp
        have h2 := (Owned.ref_iff.1 ho').1 q m hq
        omega
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨x, y, hx, -, -, ho'⟩ := hr.get hi
        have h1 := (Owned.ref_iff.1 ho).1 q m hq
        have h2 := (Owned.ref_iff.1 ho').1 p m hp
        omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact ih (fun e => hij (congrArg Nat.succ e)) hi hj hp hq

/-- An object whose slots form a chain below it is the root of a tree: each
step from it goes to one slot (`P a i`), and one slot is one step. -/
theorem owned_node {h : List (Nat × MObj)} {n lo : Nat} {l : List MVal} (P : Seg → Nat → Prop)
    (hstep : ∀ a c, step h n a = some c → ∃ i, l[i]? = some (.ref c) ∧ P a i)
    (hP : ∀ a b i, P a i → P b i → a = b) (hc : Chain h lo n l) :
    Owned h lo (n + 1) (.ref n) := by
  have below : ∀ a rest m, resolveFrom h n (a :: rest) = some m →
      ∃ i c, l[i]? = some (.ref c) ∧ P a i ∧ resolveFrom h c rest = some m ∧ lo ≤ m ∧ m < n := by
    intro a rest m hm
    obtain ⟨c, hs, hr⟩ := resolveFrom_cons.1 hm
    obtain ⟨i, hi, hPi⟩ := hstep a c hs
    obtain ⟨x, y, hx, -, hy, ho⟩ := hc.get hi
    have := (Owned.ref_iff.1 ho).1 rest m hr
    exact ⟨i, c, hi, hPi, hr, by omega, by omega⟩
  refine ⟨fun p m hm => ?_, fun p q m hp hq => ?_⟩
  · cases p with
    | nil =>
      simp only [resolveFrom, Option.some.injEq] at hm
      subst hm
      have := hc.le
      omega
    | cons a rest =>
      obtain ⟨_, _, _, _, _, h1, h2⟩ := below a rest m hm
      omega
  · cases p with
    | nil =>
      cases q with
      | nil => rfl
      | cons b q =>
        simp only [resolveFrom, Option.some.injEq] at hp
        subst hp
        obtain ⟨_, _, _, _, _, _, h2⟩ := below b q _ hq
        omega
    | cons a p =>
      cases q with
      | nil =>
        simp only [resolveFrom, Option.some.injEq] at hq
        subst hq
        obtain ⟨_, _, _, _, _, _, h2⟩ := below a p _ hp
        omega
      | cons b q =>
        obtain ⟨i, c, hi, hPa, hrp, -, -⟩ := below a p m hp
        obtain ⟨j, c', hj, hPb, hrq, -, -⟩ := below b q m hq
        by_cases hij : i = j
        · subst hij
          rw [hi] at hj
          simp only [Option.some.injEq, MVal.ref.injEq] at hj
          subst hj
          obtain ⟨x, y, -, -, -, ho⟩ := hc.get hi
          rw [hP a b i hPa hPb, (Owned.ref_iff.1 ho).2 p q m hrp hrq]
        · exact (hc.apart hij hi hj hrp hrq).elim

theorem owned_struct {h : List (Nat × MObj)} {n lo : Nat} {fs : List (Name × MVal)}
    (hobj : lookupBy n h = some (.struct fs)) (hc : Chain h lo n (fs.map Prod.snd)) :
    Owned h lo (n + 1) (.ref n) := by
  refine owned_node (fun a i => ∃ f, a = .field f ∧ (fs[i]?).map Prod.fst = some f) ?_ ?_ hc
  · intro a c hs
    obtain ⟨f, rfl, hf⟩ := step_struct hobj hs
    obtain ⟨i, hi⟩ := lookupBy_index hf
    exact ⟨i, by simp only [List.getElem?_map, hi, Option.map_some], f, rfl,
      by simp only [hi, Option.map_some]⟩
  · rintro a b i ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    rw [hf] at hg
    simp only [Option.some.injEq] at hg
    rw [hg]

theorem owned_array {h : List (Nat × MObj)} {n lo : Nat} {es : List MVal} {fx : Bool}
    (hobj : lookupBy n h = some (.array es fx)) (hc : Chain h lo n es) :
    Owned h lo (n + 1) (.ref n) := by
  refine owned_node (fun a i => ∃ k, a = .at k ∧ 0 ≤ k ∧ k.toNat = i) ?_ ?_ hc
  · intro a c hs
    obtain ⟨k, rfl, hk, he⟩ := step_array hobj hs
    exact ⟨k.toNat, he, k, rfl, hk, rfl⟩
  · rintro a b i ⟨k, rfl, hk, hki⟩ ⟨k', rfl, hk', hki'⟩
    have : k = k' := by omega
    rw [this]

mutual

/-- **A copy into memory is a tree** of objects in the counters it used. -/
theorem copyStToM_owned (τ' : State) (σ : State) (v : SVal) :
    ∀ τ mv, copyStToM σ v = .ok (τ, mv) → τ.HeapExt τ' →
      Owned τ'.heap σ.nextId τ.nextId mv := by
  intro τ mv h hx
  cases v with
  | prim p => obtain ⟨-, rfl⟩ := copyStToM_prim_inv h; trivial
  | map e d => exact (copyStToM_map_inv h).elim
  | struct fs =>
    obtain ⟨τ₁, mfs, hf, hτ, rfl⟩ := copyStToM_struct_inv h
    obtain ⟨hobj, hx₁, hn⟩ := alloc_ext hτ hx
    rw [hn]
    exact owned_struct hobj (copyStFields_chain τ' σ fs τ₁ mfs hf hx₁)
  | array es sh fx =>
    obtain ⟨τ₁, mes, he, hτ, rfl⟩ := copyStToM_array_inv h
    obtain ⟨hobj, hx₁, hn⟩ := alloc_ext hτ hx
    rw [hn]
    exact owned_array hobj (copyStElems_chain τ' σ es τ₁ mes he hx₁)

theorem copyStFields_chain (τ' : State) (σ : State) (fs : List (Name × SVal)) :
    ∀ τ mfs, copyStFields σ fs = .ok (τ, mfs) → τ.HeapExt τ' →
      Chain τ'.heap σ.nextId τ.nextId (mfs.map Prod.snd) := by
  intro τ mfs h hx
  cases fs with
  | nil =>
    obtain ⟨rfl, rfl⟩ := copyStFields_nil_inv h
    exact .nil _
  | cons fv rest =>
    obtain ⟨n, v⟩ := fv
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStFields_cons_inv h
    have hx₁ : σ₁.HeapExt τ' := (copyStFields_heapExt σ₁ rest τ mrest h2).trans hx
    exact .cons (copyStToM_nextId σ v σ₁ mv h1) (copyStToM_owned τ' σ v σ₁ mv h1 hx₁)
      (copyStFields_chain τ' σ₁ rest τ mrest h2 hx)

theorem copyStElems_chain (τ' : State) (σ : State) (es : List SVal) :
    ∀ τ mes, copyStElems σ es = .ok (τ, mes) → τ.HeapExt τ' →
      Chain τ'.heap σ.nextId τ.nextId mes := by
  intro τ mes h hx
  cases es with
  | nil =>
    obtain ⟨rfl, rfl⟩ := copyStElems_nil_inv h
    exact .nil _
  | cons v rest =>
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStElems_cons_inv h
    have hx₁ : σ₁.HeapExt τ' := (copyStElems_heapExt σ₁ rest τ mrest h2).trans hx
    exact .cons (copyStToM_nextId σ v σ₁ mv h1) (copyStToM_owned τ' σ v σ₁ mv h1 hx₁)
      (copyStElems_chain τ' σ₁ rest τ mrest h2 hx)

end

/-- **Every object a copy's root reaches** is one the copy allocated: KeY's
`newFromAdd`/`newFromWrite`, where a fresh root is apart from every older
object and so from every other root. -/
theorem copyStToM_interval {σ τ τ' : State} {v : SVal} {n : Nat}
    (h : copyStToM σ v = .ok (τ, .ref n)) (hx : τ.HeapExt τ') {p : List Seg} {m : Nat}
    (hm : resolveFrom τ'.heap n p = some m) : σ.nextId ≤ m ∧ m < τ.nextId :=
  (Owned.ref_iff.1 (copyStToM_owned τ' σ v τ _ h hx)).1 p m hm

/-- **Two paths from a copy's root** that reach one object are one path: a
write at `x.a.v` is apart from a read at `x.b.v`. -/
theorem copyStToM_resolve_inj {σ τ τ' : State} {v : SVal} {n : Nat}
    (h : copyStToM σ v = .ok (τ, .ref n)) (hx : τ.HeapExt τ') {p q : List Seg} {m : Nat}
    (hp : resolveFrom τ'.heap n p = some m) (hq : resolveFrom τ'.heap n q = some m) : p = q :=
  (Owned.ref_iff.1 (copyStToM_owned τ' σ v τ _ h hx)).2 p q m hp hq

/-! ## A copy into memory reads as its source -/

/-- `mv` is a copy into memory of `v`, made into a heap `τ` extends. -/
def CopiedTo (τ : State) (v : SVal) (mv : MVal) : Prop :=
  ∃ σ₁ σ₂, copyStToM σ₁ v = .ok (σ₂, mv) ∧ σ₂.HeapExt τ

theorem CopiedTo.ext {τ τ' : State} {v : SVal} {mv : MVal} (h : CopiedTo τ v mv)
    (hx : τ.HeapExt τ') : CopiedTo τ' v mv := by
  obtain ⟨σ₁, σ₂, hc, hx₂⟩ := h
  exact ⟨σ₁, σ₂, hc, hx₂.trans hx⟩

/-- The members of a struct copy, name by name. -/
theorem copyStFields_lookupBy : ∀ {σ τ : State} {fs : List (Name × SVal)} {mfs : List (Name × MVal)},
    copyStFields σ fs = .ok (τ, mfs) → ∀ f : Name,
      (lookupBy f fs = none ∧ lookupBy f mfs = none) ∨
      ∃ v mv, lookupBy f fs = some v ∧ lookupBy f mfs = some mv ∧ CopiedTo τ v mv
  | σ, τ, [], mfs, h, f => by
    obtain ⟨rfl, rfl⟩ := copyStFields_nil_inv h
    exact .inl ⟨rfl, rfl⟩
  | σ, τ, (n, v) :: rest, mfs, h, f => by
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStFields_cons_inv h
    by_cases hf : f = n
    · subst hf
      simp only [lookupBy, if_true]
      exact .inr ⟨v, mv, rfl, rfl, σ, σ₁, h1, copyStFields_heapExt σ₁ rest τ mrest h2⟩
    · simp only [lookupBy, hf, if_false]
      exact copyStFields_lookupBy h2 f

/-- The elements of an array copy, index by index. -/
theorem copyStElems_getElem : ∀ {σ τ : State} {es : List SVal} {mes : List MVal},
    copyStElems σ es = .ok (τ, mes) → mes.length = es.length ∧
      ∀ (i : Nat) v mv, es[i]? = some v → mes[i]? = some mv → CopiedTo τ v mv
  | σ, τ, [], mes, h => by
    obtain ⟨rfl, rfl⟩ := copyStElems_nil_inv h
    exact ⟨rfl, fun i v mv hv _ => by simp only [List.getElem?_nil, reduceCtorEq] at hv⟩
  | σ, τ, v :: rest, mes, h => by
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStElems_cons_inv h
    obtain ⟨hlen, hget⟩ := copyStElems_getElem h2
    refine ⟨by simp only [List.length_cons, hlen], fun i v' mv' hv hmv => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hmv
      subst hv hmv
      exact ⟨σ, σ₁, h1, copyStElems_heapExt σ₁ rest τ mrest h2⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv hmv
      exact hget i v' mv' hv hmv

theorem readAddr_field_struct {τ : State} {n : Nat} {fs : List (Name × MVal)} (f : Name)
    (hobj : lookupBy n τ.heap = some (.struct fs)) :
    readAddr τ (.memoryField n f) =
      match lookupBy f fs with | some v => .ok v | none => .error .stuck := by
  simp only [readAddr, State.getObj, hobj, bind, Except.bind]
  cases lookupBy f fs <;> rfl

theorem readAddr_index_struct {τ : State} {n : Nat} {fs : List (Name × MVal)} (k : Int)
    (hobj : lookupBy n τ.heap = some (.struct fs)) :
    readAddr τ (.memoryIndex n k) = .error .stuck := by
  simp only [readAddr, State.getObj, hobj, bind, Except.bind]

theorem readAddr_field_array {τ : State} {n : Nat} {es : List MVal} {fx : Bool} (f : Name)
    (hobj : lookupBy n τ.heap = some (.array es fx)) :
    readAddr τ (.memoryField n f) = .error .stuck := by
  simp only [readAddr, State.getObj, hobj, bind, Except.bind]

theorem readAddr_index_array {τ : State} {n : Nat} {es : List MVal} {fx : Bool} (k : Int)
    (hobj : lookupBy n τ.heap = some (.array es fx)) :
    readAddr τ (.memoryIndex n k) =
      if h : 0 ≤ k ∧ k.toNat < es.length then .ok es[k.toNat] else .error .revert := by
  simp only [readAddr, State.getObj, hobj, bind, Except.bind, List.get_eq_getElem]
  split <;> rfl

theorem findLive_array_field {es sh : List SVal} {fx : Bool} {f : Name} {rest : List Seg}
    (hf : f ≠ "length") : (SVal.array es sh fx).findLive (.field f :: rest) = .error .stuck := by
  simp only [SVal.findLive]

theorem findLive_array_at {es sh : List SVal} {fx : Bool} {k : Int} {rest : List Seg} :
    (SVal.array es sh fx).findLive (.at k :: rest) =
      if h : 0 ≤ k ∧ k.toNat < es.length then es[k.toNat].findLive rest else .error .revert := by
  simp only [SVal.findLive, List.get_eq_getElem]

/-- **A path through a copy into memory**: what it reads is the copy of what
`findLive` reads in the storage value copied (KeY's `readFromCopyToStorage`),
and every path `findLive` reads that asks no `length` reads in memory. -/
theorem copiedTo_readPath : (p : List Seg) → ∀ {τ' : State} {v : SVal} {mv : MVal},
    CopiedTo τ' v mv →
    (∀ mv', mv.readPath τ' p = .ok mv' → ∃ v', v.findLive p = .ok v' ∧ CopiedTo τ' v' mv') ∧
    ((∀ s ∈ p, s ≠ .field "length") → ∀ v', v.findLive p = .ok v' →
      ∃ mv', mv.readPath τ' p = .ok mv' ∧ CopiedTo τ' v' mv')
  | [], τ', v, mv, hc => by
    refine ⟨fun mv' h => ?_, fun _ v' h => ?_⟩
    · simp only [MVal.readPath, Except.ok.injEq] at h
      subst h
      exact ⟨v, SVal.findLive_nil v, hc⟩
    · simp only [SVal.findLive_nil, Except.ok.injEq] at h
      subst h
      exact ⟨mv, by cases mv <;> rfl, hc⟩
  | s :: rest, τ', v, mv, ⟨σ, τ, h, hx⟩ => by
    cases v with
    | prim pv =>
      obtain ⟨rfl, rfl⟩ := copyStToM_prim_inv h
      refine ⟨fun mv' h' => ?_, fun _ v' h' => ?_⟩
      · simp only [MVal.readPath, reduceCtorEq] at h'
      · cases s <;> simp only [SVal.findLive, reduceCtorEq] at h'
    | map e d => exact (copyStToM_map_inv h).elim
    | struct fs =>
      obtain ⟨τ₁, mfs, hf, hτ, rfl⟩ := copyStToM_struct_inv h
      obtain ⟨hobj, hx₁, -⟩ := alloc_ext hτ hx
      cases s with
      | «at» k =>
        refine ⟨fun mv' h' => ?_, fun _ v' h' => ?_⟩
        · simp only [MVal.readPath, Addr.ofSeg, readAddr_index_struct k hobj, bind, Except.bind,
            reduceCtorEq] at h'
        · simp only [SVal.findLive, reduceCtorEq] at h'
      | field f =>
        have hr := readAddr_field_struct f hobj
        rcases copyStFields_lookupBy hf f with ⟨h1, h2⟩ | ⟨v₁, mv₁, h1, h2, hc₁⟩
        · refine ⟨fun mv' h' => ?_, fun _ v' h' => ?_⟩
          · simp only [MVal.readPath, Addr.ofSeg, hr, h2, bind, Except.bind, reduceCtorEq] at h'
          · simp only [SVal.findLive, h1, reduceCtorEq] at h'
        · have ih := copiedTo_readPath rest (hc₁.ext hx₁)
          refine ⟨fun mv' h' => ?_, fun hp v' h' => ?_⟩
          · simp only [MVal.readPath, Addr.ofSeg, hr, h2, Res.ok_bind'] at h'
            obtain ⟨v', hv', hc'⟩ := ih.1 mv' h'
            exact ⟨v', by simp only [SVal.findLive, h1, hv'], hc'⟩
          · simp only [SVal.findLive, h1] at h'
            obtain ⟨mv', hmv', hc'⟩ :=
              ih.2 (fun s hs => hp s (List.mem_cons_of_mem _ hs)) v' h'
            exact ⟨mv', by simp only [MVal.readPath, Addr.ofSeg, hr, h2, Res.ok_bind', hmv'], hc'⟩
    | array es sh fx =>
      obtain ⟨τ₁, mes, he, hτ, rfl⟩ := copyStToM_array_inv h
      obtain ⟨hobj, hx₁, -⟩ := alloc_ext hτ hx
      obtain ⟨hlen, hget⟩ := copyStElems_getElem he
      cases s with
      | field f =>
        refine ⟨fun mv' h' => ?_, fun hp v' h' => ?_⟩
        · simp only [MVal.readPath, Addr.ofSeg, readAddr_field_array f hobj, bind, Except.bind,
            reduceCtorEq] at h'
        · have hf : f ≠ "length" := fun e => hp _ List.mem_cons_self (by rw [e])
          simp only [findLive_array_field hf, reduceCtorEq] at h'
      | «at» k =>
        have hr := readAddr_index_array k hobj
        by_cases hb : 0 ≤ k ∧ k.toNat < es.length
        · have hb' : 0 ≤ k ∧ k.toNat < mes.length := ⟨hb.1, by rw [hlen]; exact hb.2⟩
          have hc₁ : CopiedTo τ₁ es[k.toNat] mes[k.toNat] :=
            hget k.toNat _ _ (List.getElem?_eq_getElem hb.2) (List.getElem?_eq_getElem hb'.2)
          have ih := copiedTo_readPath rest (hc₁.ext hx₁)
          refine ⟨fun mv' h' => ?_, fun hp v' h' => ?_⟩
          · simp only [MVal.readPath, Addr.ofSeg, hr, hb', and_self, dite_true, Res.ok_bind'] at h'
            obtain ⟨v', hv', hc'⟩ := ih.1 mv' h'
            exact ⟨v', by simp only [findLive_array_at, hb, and_self, dite_true, hv'], hc'⟩
          · simp only [findLive_array_at, hb, and_self, dite_true] at h'
            obtain ⟨mv', hmv', hc'⟩ :=
              ih.2 (fun s hs => hp s (List.mem_cons_of_mem _ hs)) v' h'
            exact ⟨mv', by simp only [MVal.readPath, Addr.ofSeg, hr, hb', and_self, dite_true,
              Res.ok_bind', hmv'], hc'⟩
        · have hb' : ¬ (0 ≤ k ∧ k.toNat < mes.length) := by rw [hlen]; exact hb
          refine ⟨fun mv' h' => ?_, fun _ v' h' => ?_⟩
          · simp only [MVal.readPath, Addr.ofSeg, hr, hb', dite_false, bind, Except.bind,
              reduceCtorEq] at h'
          · simp only [findLive_array_at, hb, dite_false, reduceCtorEq] at h'

/-- `copiedTo_readPath` at the copy itself. -/
theorem copyStToM_readPath (p : List Seg) {σ τ τ' : State} {v : SVal} {mv : MVal}
    (h : copyStToM σ v = .ok (τ, mv)) (hx : τ.HeapExt τ') :
    (∀ mv', mv.readPath τ' p = .ok mv' → ∃ v', v.findLive p = .ok v' ∧ CopiedTo τ' v' mv') ∧
    ((∀ s ∈ p, s ≠ .field "length") → ∀ v', v.findLive p = .ok v' →
      ∃ mv', mv.readPath τ' p = .ok mv' ∧ CopiedTo τ' v' mv') :=
  copiedTo_readPath p ⟨σ, τ, h, hx⟩

/-- A slot below a path through a copy: the copy of what `findLive` reads one
segment further. -/
theorem copyStToM_readSlot {σ τ τ' : State} {v : SVal} {mv mv' : MVal} {p : List Seg} {m : Nat}
    {s : Seg} (h : copyStToM σ v = .ok (τ, mv)) (hx : τ.HeapExt τ')
    (hm : mv.readPath τ' p = .ok (.ref m)) (hs : readAddr τ' (.ofSeg m s) = .ok mv') :
    ∃ v', v.findLive (p ++ [s]) = .ok v' ∧ CopiedTo τ' v' mv' := by
  refine (copyStToM_readPath (p ++ [s]) h hx).1 mv' ?_
  rw [MVal.readPath_snoc, hm, Res.ok_bind']
  exact hs

/-- The object a copy's reference names: a struct for a struct, an array as
long as the array's live part for an array. -/
theorem copiedTo_ref_obj {τ' : State} {v : SVal} {m : Nat} (hc : CopiedTo τ' v (.ref m)) :
    (∃ fs mfs, v = .struct fs ∧ lookupBy m τ'.heap = some (.struct mfs)) ∨
    (∃ es sh fx mes, v = .array es sh fx ∧ lookupBy m τ'.heap = some (.array mes fx) ∧
      mes.length = es.length) := by
  obtain ⟨σ, τ, h, hx⟩ := hc
  cases v with
  | prim pv => obtain ⟨-, h⟩ := copyStToM_prim_inv h; cases h
  | map e d => exact (copyStToM_map_inv h).elim
  | struct fs =>
    obtain ⟨τ₁, mfs, -, hτ, hm⟩ := copyStToM_struct_inv h
    cases hm
    exact .inl ⟨fs, mfs, rfl, (alloc_ext hτ hx).1⟩
  | array es sh fx =>
    obtain ⟨τ₁, mes, he, hτ, hm⟩ := copyStToM_array_inv h
    cases hm
    exact .inr ⟨es, sh, fx, mes, rfl, (alloc_ext hτ hx).1, (copyStElems_getElem he).1⟩

/-- The length of a copy into memory is the live length of the source. -/
theorem copiedTo_len {τ' : State} {v : SVal} {m : Nat} (hc : CopiedTo τ' v (.ref m)) :
    memArrayLen τ' m = Close.arrLen v := by
  rcases copiedTo_ref_obj hc with ⟨fs, mfs, rfl, hobj⟩ | ⟨es, sh, fx, mes, rfl, hobj, hlen⟩
  · simp only [memArrayLen, State.getObj, hobj, bind, Except.bind, Close.arrLen]
  · simp only [memArrayLen, State.getObj, hobj, bind, Except.bind, Close.arrLen, hlen, pure,
      Except.pure]

/-- **The length below a path through a copy** (`findDefinitionSize` on a
copy): the live length `findLive` reads there in storage. -/
theorem copyStToM_lenPath {σ τ τ' : State} {v : SVal} {mv : MVal} {p : List Seg} {m : Nat}
    (h : copyStToM σ v = .ok (τ, mv)) (hx : τ.HeapExt τ') (hm : mv.readPath τ' p = .ok (.ref m)) :
    memArrayLen τ' m = (v.findLive p >>= Close.arrLen) := by
  obtain ⟨v', hv', hc⟩ := (copyStToM_readPath p h hx).1 _ hm
  rw [hv', Res.ok_bind']
  exact copiedTo_len hc

/-! ### `new T[](n)` -/

theorem newArrVal_findLive_at (E : Ty) (n k : Int) :
    (newArrVal (.array E) n).findLive [.at k] =
      if 0 ≤ k ∧ k < n then .ok (defaultForTy E) else .error .revert := by
  simp only [newArrVal, findLive_array_at, List.length_replicate, List.getElem_replicate,
    SVal.findLive_nil]
  by_cases hb : 0 ≤ k ∧ k < n
  · have hb' : 0 ≤ k ∧ k.toNat < n.toNat := ⟨hb.1, by omega⟩
    simp only [hb', and_self, dite_true, hb, if_true]
  · have hb' : ¬ (0 ≤ k ∧ k.toNat < n.toNat) := by omega
    simp only [hb', dite_false, hb, if_false]

/-- The length of `new T[](n)` is `n` (KeY's `memoryArrayFreshAlloc`, which
writes it at `size`). -/
theorem copyStToM_newArr_len {σ τ τ' : State} {E : Ty} {n : Int} {m : Nat}
    (h : copyStToM σ (newArrVal (.array E) n) = .ok (τ, .ref m)) (hx : τ.HeapExt τ') :
    memArrayLen τ' m = .ok (.int n.toNat) := by
  rw [copiedTo_len ⟨σ, τ, h, hx⟩]
  simp only [newArrVal, Close.arrLen, List.length_replicate]

/-- An element of `new T[](n)`: in range, a copy of `T`'s default
(`initElement`); out of range, no slot. -/
theorem copyStToM_newArr_at {σ τ τ' : State} {E : Ty} {n : Int} {m : Nat} (k : Int)
    (h : copyStToM σ (newArrVal (.array E) n) = .ok (τ, .ref m)) (hx : τ.HeapExt τ') :
    (∀ mv', readAddr τ' (.memoryIndex m k) = .ok mv' →
      0 ≤ k ∧ k < n ∧ CopiedTo τ' (defaultForTy E) mv') ∧
    (0 ≤ k → k < n → ∃ mv', readAddr τ' (.memoryIndex m k) = .ok mv' ∧
      CopiedTo τ' (defaultForTy E) mv') := by
  have hp := copyStToM_readPath [.at k] h hx
  have hrd : ∀ mv', (MVal.ref m).readPath τ' [.at k] = .ok mv' ↔
      readAddr τ' (.memoryIndex m k) = .ok mv' := by
    intro mv'
    simp only [MVal.readPath, Addr.ofSeg]
    cases readAddr τ' (.memoryIndex m k) <;> rfl
  refine ⟨fun mv' hr => ?_, fun hk hn => ?_⟩
  · obtain ⟨v', hv', hc⟩ := hp.1 mv' ((hrd mv').2 hr)
    rw [newArrVal_findLive_at] at hv'
    by_cases hb : 0 ≤ k ∧ k < n
    · simp only [hb, and_self, if_true, Except.ok.injEq] at hv'
      subst hv'
      exact ⟨hb.1, hb.2, hc⟩
    · simp only [hb, if_false, reduceCtorEq] at hv'
  · have hl : ∀ s ∈ [Seg.at k], s ≠ .field "length" := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      exact fun e => nomatch e
    obtain ⟨mv', hmv', hc⟩ := hp.2 hl (defaultForTy E)
      (by rw [newArrVal_findLive_at]; simp only [hk, hn, and_self, if_true])
    exact ⟨mv', (hrd mv').1 hmv', hc⟩

/-! ## A view of memory as storage reads as memory -/

theorem copyMToSt_ref_inv {σ : State} {rem : List Nat} {id : Nat} {v : SVal}
    (h : copyMToSt σ rem (.ref id) = .ok v) : id ∈ rem ∧
    ((∃ fs sfs, lookupBy id σ.heap = some (.struct fs) ∧
        copyMFields σ (rem.erase id) fs = .ok sfs ∧ v = .struct sfs) ∨
      (∃ es fx ses, lookupBy id σ.heap = some (.array es fx) ∧
        copyMElems σ (rem.erase id) es = .ok ses ∧ v = .array ses [] fx)) := by
  rw [copyMToSt.eq_def] at h
  simp only at h
  split at h
  · rename_i hmem
    refine ⟨hmem, ?_⟩
    cases hg : lookupBy id σ.heap with
    | none => simp only [State.getObj, hg, reduceCtorEq] at h
    | some obj =>
      cases obj with
      | struct fs =>
        cases hc : copyMFields σ (rem.erase id) fs with
        | error e => simp only [State.getObj, hg, hc, bind, Except.bind, reduceCtorEq] at h
        | ok sfs =>
          simp only [State.getObj, hg, hc, bind, Except.bind, Except.ok.injEq] at h
          exact .inl ⟨fs, sfs, rfl, hc, h.symm⟩
      | array es fx =>
        cases hc : copyMElems σ (rem.erase id) es with
        | error e => simp only [State.getObj, hg, hc, bind, Except.bind, reduceCtorEq] at h
        | ok ses =>
          simp only [State.getObj, hg, hc, bind, Except.bind, Except.ok.injEq] at h
          exact .inr ⟨es, fx, ses, rfl, hc, h.symm⟩
  · simp only [reduceCtorEq] at h

theorem copyMToSt_ref_struct {σ : State} {rem : List Nat} {id : Nat} {fs : List (Name × MVal)}
    {sfs : List (Name × SVal)} (hmem : id ∈ rem) (hg : lookupBy id σ.heap = some (.struct fs))
    (hc : copyMFields σ (rem.erase id) fs = .ok sfs) :
    copyMToSt σ rem (.ref id) = .ok (.struct sfs) := by
  rw [copyMToSt.eq_def]
  simp only [hmem, dite_true, State.getObj, hg, hc, bind, Except.bind]

theorem copyMToSt_ref_array {σ : State} {rem : List Nat} {id : Nat} {es : List MVal} {fx : Bool}
    {ses : List SVal} (hmem : id ∈ rem) (hg : lookupBy id σ.heap = some (.array es fx))
    (hc : copyMElems σ (rem.erase id) es = .ok ses) :
    copyMToSt σ rem (.ref id) = .ok (.array ses [] fx) := by
  rw [copyMToSt.eq_def]
  simp only [hmem, dite_true, State.getObj, hg, hc, bind, Except.bind]

theorem copyMFields_cons_inv {σ : State} {rem : List Nat} {n : Name} {mv : MVal}
    {rest : List (Name × MVal)} {sfs : List (Name × SVal)}
    (h : copyMFields σ rem ((n, mv) :: rest) = .ok sfs) :
    ∃ w srest, copyMToSt σ rem mv = .ok w ∧ copyMFields σ rem rest = .ok srest ∧
      sfs = (n, w) :: srest := by
  rw [copyMFields] at h
  cases h1 : copyMToSt σ rem mv with
  | error e => simp only [h1, bind, Except.bind, reduceCtorEq] at h
  | ok w =>
    cases h2 : copyMFields σ rem rest with
    | error e => simp only [h1, h2, bind, Except.bind, reduceCtorEq] at h
    | ok srest =>
      simp only [h1, h2, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨w, srest, rfl, rfl, h.symm⟩

theorem copyMElems_cons_inv {σ : State} {rem : List Nat} {mv : MVal} {rest : List MVal}
    {ses : List SVal} (h : copyMElems σ rem (mv :: rest) = .ok ses) :
    ∃ w srest, copyMToSt σ rem mv = .ok w ∧ copyMElems σ rem rest = .ok srest ∧
      ses = w :: srest := by
  rw [copyMElems] at h
  cases h1 : copyMToSt σ rem mv with
  | error e => simp only [h1, bind, Except.bind, reduceCtorEq] at h
  | ok w =>
    cases h2 : copyMElems σ rem rest with
    | error e => simp only [h1, h2, bind, Except.bind, reduceCtorEq] at h
    | ok srest =>
      simp only [h1, h2, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨w, srest, rfl, rfl, h.symm⟩

/-- The members of a struct copied out of memory, name by name. -/
theorem copyMFields_lookupBy {σ : State} {rem : List Nat} :
    ∀ {fs : List (Name × MVal)} {sfs : List (Name × SVal)},
      copyMFields σ rem fs = .ok sfs → ∀ f : Name,
      (lookupBy f fs = none ∧ lookupBy f sfs = none) ∨
      ∃ mv w, lookupBy f fs = some mv ∧ lookupBy f sfs = some w ∧ copyMToSt σ rem mv = .ok w
  | [], sfs, h, f => by
    rw [copyMFields, Except.ok.injEq] at h
    subst h
    exact .inl ⟨rfl, rfl⟩
  | (n, mv) :: rest, sfs, h, f => by
    obtain ⟨w, srest, h1, h2, rfl⟩ := copyMFields_cons_inv h
    by_cases hf : f = n
    · subst hf
      simp only [lookupBy, if_true]
      exact .inr ⟨mv, w, rfl, rfl, h1⟩
    · simp only [lookupBy, hf, if_false]
      exact copyMFields_lookupBy h2 f

/-- The elements of an array copied out of memory, index by index. -/
theorem copyMElems_getElem {σ : State} {rem : List Nat} :
    ∀ {es : List MVal} {ses : List SVal}, copyMElems σ rem es = .ok ses →
      ses.length = es.length ∧
      ∀ (i : Nat) mv w, es[i]? = some mv → ses[i]? = some w → copyMToSt σ rem mv = .ok w
  | [], ses, h => by
    rw [copyMElems, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i mv w hv _ => by simp only [List.getElem?_nil, reduceCtorEq] at hv⟩
  | mv :: rest, ses, h => by
    obtain ⟨w, srest, h1, h2, rfl⟩ := copyMElems_cons_inv h
    obtain ⟨hlen, hget⟩ := copyMElems_getElem h2
    refine ⟨by simp only [List.length_cons, hlen], fun i mv' w' hv hw => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hw
      subst hv hw
      exact h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv hw
      exact hget i mv' w' hv hw

theorem find_array_at {es sh : List SVal} {fx : Bool} {k : Int} {rest : List Seg} :
    (SVal.array es sh fx).find (.at k :: rest) =
      if h : 0 ≤ k ∧ k.toNat < (es ++ sh).length then (es ++ sh)[k.toNat].find rest
      else .error .revert := by
  simp only [SVal.find, List.get_eq_getElem]

theorem find_array_field {es sh : List SVal} {fx : Bool} {f : Name} {rest : List Seg}
    (hf : f ≠ "length") : (SVal.array es sh fx).find (.field f :: rest) = .error .stuck := by
  simp only [SVal.find]

/-- **A path through a view of memory as storage** (KeY's `findOnCopy` and
`selectOnCopyMem*`): `find` on a copy out of memory reads the copy of the
slot the same path reads in memory, for a path that asks no `length`. -/
theorem copyMToSt_readPath (σ : State) : (p : List Seg) → (∀ s ∈ p, s ≠ .field "length") →
    ∀ {rem : List Nat} {mv : MVal} {v : SVal}, copyMToSt σ rem mv = .ok v →
    (∀ w, v.find p = .ok w → ∃ mv' rem', mv.readPath σ p = .ok mv' ∧ copyMToSt σ rem' mv' = .ok w) ∧
    (∀ mv', mv.readPath σ p = .ok mv' → ∃ w rem', v.find p = .ok w ∧ copyMToSt σ rem' mv' = .ok w)
  | [], _, rem, mv, v, h => by
    refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
    · rw [SVal.find_nil, Except.ok.injEq] at hw
      subst hw
      exact ⟨mv, rem, by cases mv <;> rfl, h⟩
    · simp only [MVal.readPath, Except.ok.injEq] at hmv
      subst hmv
      exact ⟨v, rem, SVal.find_nil v, h⟩
  | s :: rest, hp, rem, mv, v, h => by
    have hp' : ∀ s ∈ rest, s ≠ .field "length" := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    cases mv with
    | prim pv =>
      rw [Close.copyMToSt_prim, Except.ok.injEq] at h
      subst h
      refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
      · cases s <;> simp only [SVal.find, reduceCtorEq] at hw
      · simp only [MVal.readPath, reduceCtorEq] at hmv
    | ref id =>
      obtain ⟨-, ⟨fs, sfs, hg, hc, rfl⟩ | ⟨es, fx, ses, hg, hc, rfl⟩⟩ := copyMToSt_ref_inv h
      · cases s with
        | «at» k =>
          refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
          · simp only [SVal.find, reduceCtorEq] at hw
          · simp only [MVal.readPath, Addr.ofSeg, readAddr_index_struct k hg, bind, Except.bind,
              reduceCtorEq] at hmv
        | field f =>
          have hr := readAddr_field_struct (τ := σ) f hg
          rcases copyMFields_lookupBy hc f with ⟨h1, h2⟩ | ⟨mv₁, w₁, h1, h2, hc₁⟩
          · refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
            · simp only [SVal.find, h2, reduceCtorEq] at hw
            · simp only [MVal.readPath, Addr.ofSeg, hr, h1, bind, Except.bind, reduceCtorEq] at hmv
          · have ih := copyMToSt_readPath σ rest hp' hc₁
            refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
            · simp only [SVal.find, h2] at hw
              obtain ⟨mv', rem', hmv', hc'⟩ := ih.1 w hw
              exact ⟨mv', rem', by simp only [MVal.readPath, Addr.ofSeg, hr, h1, Res.ok_bind', hmv'],
                hc'⟩
            · simp only [MVal.readPath, Addr.ofSeg, hr, h1, Res.ok_bind'] at hmv
              obtain ⟨w, rem', hw, hc'⟩ := ih.2 mv' hmv
              exact ⟨w, rem', by simp only [SVal.find, h2, hw], hc'⟩
      · obtain ⟨hlen, hget⟩ := copyMElems_getElem hc
        cases s with
        | field f =>
          have hf : f ≠ "length" := fun e => hp _ List.mem_cons_self (by rw [e])
          refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
          · simp only [find_array_field hf, reduceCtorEq] at hw
          · simp only [MVal.readPath, Addr.ofSeg, readAddr_field_array f hg, bind, Except.bind,
              reduceCtorEq] at hmv
        | «at» k =>
          have hr := readAddr_index_array (τ := σ) k hg
          by_cases hb : 0 ≤ k ∧ k.toNat < es.length
          · have hb' : 0 ≤ k ∧ k.toNat < ses.length := by
              rw [hlen]; exact hb
            have hc₁ : copyMToSt σ (rem.erase id) es[k.toNat] = .ok ses[k.toNat] :=
              hget k.toNat _ _ (List.getElem?_eq_getElem hb.2)
                (List.getElem?_eq_getElem (by rw [hlen]; exact hb.2))
            have ih := copyMToSt_readPath σ rest hp' hc₁
            refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
            · simp only [find_array_at, List.append_nil, hb', and_self, dite_true] at hw
              obtain ⟨mv', rem', hmv', hc'⟩ := ih.1 w hw
              exact ⟨mv', rem', by simp only [MVal.readPath, Addr.ofSeg, hr, hb, and_self,
                dite_true, Res.ok_bind', hmv'], hc'⟩
            · simp only [MVal.readPath, Addr.ofSeg, hr, hb, and_self, dite_true,
                Res.ok_bind'] at hmv
              obtain ⟨w, rem', hw, hc'⟩ := ih.2 mv' hmv
              exact ⟨w, rem', by simp only [find_array_at, List.append_nil, hb', and_self,
                dite_true, hw], hc'⟩
          · have hb' : ¬ (0 ≤ k ∧ k.toNat < ses.length) := by
              rw [hlen]; exact hb
            refine ⟨fun w hw => ?_, fun mv' hmv => ?_⟩
            · simp only [find_array_at, List.append_nil, hb', dite_false, reduceCtorEq] at hw
            · simp only [MVal.readPath, Addr.ofSeg, hr, hb, dite_false, bind, Except.bind,
                reduceCtorEq] at hmv

/-- The length of a view of an array is the memory array's
(`selectOnCopyMemPrim` at `size`). -/
theorem copyMToSt_arrLen {σ : State} {rem : List Nat} {m : Nat} {w : SVal}
    (h : copyMToSt σ rem (.ref m) = .ok w) : Close.arrLen w = memArrayLen σ m := by
  obtain ⟨-, ⟨fs, sfs, hg, -, rfl⟩ | ⟨es, fx, ses, hg, hc, rfl⟩⟩ := copyMToSt_ref_inv h
  · simp only [Close.arrLen, memArrayLen, State.getObj, hg, bind, Except.bind]
  · simp only [Close.arrLen, memArrayLen, State.getObj, hg, bind, Except.bind, pure, Except.pure,
      (copyMElems_getElem hc).1]

/-! ### What a copy out of memory holds -/

/-- `v` is a copy out of memory, from some slot and some set of identities
still unvisited. -/
def IsCopy (σ : State) (v : SVal) : Prop := ∃ rem mv, copyMToSt σ rem mv = .ok v

theorem IsCopy.prim (σ : State) (pv : PrimVal) : IsCopy σ (.prim pv) :=
  ⟨[], .prim pv, Close.copyMToSt_prim σ [] pv⟩

theorem IsCopy.not_map {σ : State} {e : List (Int × SVal)} {d : SVal} :
    ¬ IsCopy σ (.map e d) := by
  rintro ⟨rem, mv, h⟩
  cases mv with
  | prim pv => rw [Close.copyMToSt_prim, Except.ok.injEq] at h; cases h
  | ref id =>
    obtain ⟨-, ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩⟩ := copyMToSt_ref_inv h <;> cases h

theorem IsCopy.inv {σ : State} {v : SVal} (h : IsCopy σ v) :
    (∃ pv, v = .prim pv) ∨
    (∃ sfs, v = .struct sfs ∧ ∀ f w, lookupBy f sfs = some w → IsCopy σ w) ∨
    (∃ ses fx, v = .array ses [] fx ∧ ∀ (i : Nat) w, ses[i]? = some w → IsCopy σ w) := by
  obtain ⟨rem, mv, h⟩ := h
  cases mv with
  | prim pv => rw [Close.copyMToSt_prim, Except.ok.injEq] at h; exact .inl ⟨pv, h.symm⟩
  | ref id =>
    obtain ⟨-, ⟨fs, sfs, -, hc, rfl⟩ | ⟨es, fx, ses, -, hc, rfl⟩⟩ := copyMToSt_ref_inv h
    · refine .inr (.inl ⟨sfs, rfl, fun f w hw => ?_⟩)
      rcases copyMFields_lookupBy hc f with ⟨-, h2⟩ | ⟨mv₁, w₁, -, h2, hc₁⟩
      · rw [h2] at hw; cases hw
      · rw [h2, Option.some.injEq] at hw
        subst hw
        exact ⟨_, _, hc₁⟩
    · refine .inr (.inr ⟨ses, fx, rfl, fun i w hw => ?_⟩)
      obtain ⟨hlen, hget⟩ := copyMElems_getElem hc
      have hi : i < es.length := by
        rw [← hlen]
        exact (List.getElem?_eq_some_iff.1 hw).1
      exact ⟨_, _, hget i _ w (List.getElem?_eq_getElem hi) hw⟩

theorem int_find_isCopy {σ : State} (k : Int) : ∀ (p : List Seg) (w : SVal),
    (SVal.int k).find p = .ok w → IsCopy σ w
  | [], w, h => by rw [SVal.find_nil, Except.ok.injEq] at h; subst h; exact IsCopy.prim σ _
  | s :: _, w, h => by cases s <;> simp only [SVal.find, reduceCtorEq] at h

/-- What `find` reads in a copy out of memory is a copy out of memory. -/
theorem IsCopy.find {σ : State} : ∀ (p : List Seg) {v w : SVal}, IsCopy σ v → v.find p = .ok w →
    IsCopy σ w
  | [], v, w, hv, h => by rw [SVal.find_nil, Except.ok.injEq] at h; subst h; exact hv
  | s :: rest, v, w, hv, h => by
    rcases hv.inv with ⟨pv, rfl⟩ | ⟨sfs, rfl, hm⟩ | ⟨ses, fx, rfl, he⟩
    · cases s <;> simp only [SVal.find, reduceCtorEq] at h
    · cases s with
      | «at» k => simp only [SVal.find, reduceCtorEq] at h
      | field f =>
        simp only [SVal.find] at h
        split at h
        · rename_i w₁ hw₁
          exact IsCopy.find rest (hm f w₁ hw₁) h
        · cases h
    · cases s with
      | «at» k =>
        rw [find_array_at] at h
        split at h
        · rename_i hb
          refine IsCopy.find rest (he k.toNat _ ?_) h
          simp only [List.append_nil] at hb ⊢
          exact List.getElem?_eq_getElem hb.2
        · cases h
      | field f =>
        by_cases hf : f = "length"
        · subst hf
          simp only [SVal.find] at h
          split at h
          · cases h
          · exact int_find_isCopy _ rest w h
        · simp only [find_array_field hf, reduceCtorEq] at h

/-- **A copy out of memory holds no mapping**, at any path (Lean only: KeY's
`copyMem` view has no mapping to read). -/
theorem copyMToSt_noMap {σ : State} {rem : List Nat} {mv : MVal} {v : SVal}
    (h : copyMToSt σ rem mv = .ok v) (p : List Seg) {w : SVal} (hw : v.find p = .ok w)
    (e : List (Int × SVal)) (d : SVal) : w ≠ .map e d := by
  rintro rfl
  exact IsCopy.not_map (IsCopy.find p ⟨rem, mv, h⟩ hw)

theorem int_findLive_eq (k : Int) : ∀ p : List Seg, (SVal.int k).findLive p = (SVal.int k).find p
  | [] => rfl
  | s :: _ => by cases s <;> simp only [SVal.find, SVal.findLive]

/-- A copy out of memory has no slots past its length, so `findLive` and
`find` read it alike. -/
theorem IsCopy.findLive_eq {σ : State} : ∀ (p : List Seg) {v : SVal}, IsCopy σ v →
    v.findLive p = v.find p
  | [], v, _ => by rw [SVal.findLive_nil, SVal.find_nil]
  | s :: rest, v, hv => by
    rcases hv.inv with ⟨pv, rfl⟩ | ⟨sfs, rfl, hm⟩ | ⟨ses, fx, rfl, he⟩
    · cases s <;> simp only [SVal.find, SVal.findLive]
    · cases s with
      | «at» k => simp only [SVal.find, SVal.findLive]
      | field f =>
        simp only [SVal.find, SVal.findLive]
        split
        · rename_i w₁ hw₁
          exact IsCopy.findLive_eq rest (hm f w₁ hw₁)
        · rfl
    · cases s with
      | «at» k =>
        rw [find_array_at, findLive_array_at]
        simp only [List.append_nil]
        split
        · rename_i hb
          exact IsCopy.findLive_eq rest (he k.toNat _ (List.getElem?_eq_getElem hb.2))
        · rfl
      | field f =>
        by_cases hf : f = "length"
        · subst hf
          simp only [SVal.find, SVal.findLive]
          split
          · rfl
          · exact int_findLive_eq _ rest
        · rw [find_array_field hf, findLive_array_field hf]

/-! ## When a copy out of memory halts -/

/-- Every reference the object holds points into `[lo, hi)`. -/
def RefsIn (lo hi : Nat) : MObj → Prop
  | .struct fs => ∀ x ∈ fs, ∀ m, x.2 = .ref m → lo ≤ m ∧ m < hi
  | .array es _ => ∀ x ∈ es, ∀ m, x = .ref m → lo ≤ m ∧ m < hi

theorem RefsIn.mono {lo lo' hi hi' : Nat} {obj : MObj} (h : RefsIn lo hi obj) (hl : lo' ≤ lo)
    (hh : hi ≤ hi') : RefsIn lo' hi' obj := by
  cases obj with
  | struct fs =>
    intro x hx m hm
    have := h x hx m hm
    exact ⟨Nat.le_trans hl this.1, Nat.lt_of_lt_of_le this.2 hh⟩
  | array es fx =>
    intro x hx m hm
    have := h x hx m hm
    exact ⟨Nat.le_trans hl this.1, Nat.lt_of_lt_of_le this.2 hh⟩

/-- The objects `[lo, hi)` of the heap `h` are there, and each references
only older objects of the interval: what a copy into memory leaves, what a
write of an older reference keeps, and what makes a copy out of memory
return. -/
def DescFrom (h : List (Nat × MObj)) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → ∃ obj, lookupBy j h = some obj ∧ RefsIn lo j obj

theorem DescFrom.empty (h : List (Nat × MObj)) (lo : Nat) : DescFrom h lo lo :=
  fun _ hj hj' => absurd hj' (Nat.not_lt.2 hj)

theorem DescFrom.append {h : List (Nat × MObj)} {lo mid hi : Nat} (h₁ : DescFrom h lo mid)
    (h₂ : DescFrom h mid hi) (hl : lo ≤ mid) : DescFrom h lo hi := by
  intro j hj hj'
  by_cases hm : j < mid
  · exact h₁ j hj hm
  · obtain ⟨obj, ho, hr⟩ := h₂ j (Nat.not_lt.1 hm) hj'
    exact ⟨obj, ho, hr.mono hl (Nat.le_refl _)⟩

theorem DescFrom.ext {τ τ' : State} {lo hi : Nat} (hd : DescFrom τ.heap lo hi)
    (hh : hi ≤ τ.nextId) (hx : τ.HeapExt τ') : DescFrom τ'.heap lo hi := by
  intro j hj hj'
  rw [hx.2 j (Nat.lt_of_lt_of_le hj' hh)]
  exact hd j hj hj'

/-- The object a write changes, and how: one slot set to the value written. -/
theorem writeAddr_obj {σ τ : State} {mv : MVal} {a : Addr} (h : writeAddr σ mv a = .ok τ) :
    ∃ obj obj', lookupBy a.id σ.heap = some obj ∧ τ.heap = setBy a.id obj' σ.heap ∧
      ∀ lo hi, RefsIn lo hi obj → (∀ m, mv = .ref m → lo ≤ m ∧ m < hi) → RefsIn lo hi obj' := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind, State.getObj] at h
    cases hg : lookupBy id σ.heap with
    | none => simp only [hg, reduceCtorEq] at h
    | some obj =>
      cases obj with
      | array es fx => simp only [hg, reduceCtorEq] at h
      | struct fs =>
        simp only [hg, Except.ok.injEq] at h
        subst h
        refine ⟨_, _, hg, rfl, fun lo hi hr hmv x hx m hm => ?_⟩
        rcases mem_setBy hx with rfl | hx
        · exact hmv m hm
        · exact hr x hx m hm
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind, State.getObj] at h
    cases hg : lookupBy id σ.heap with
    | none => simp only [hg, reduceCtorEq] at h
    | some obj =>
      cases obj with
      | struct fs => simp only [hg, reduceCtorEq] at h
      | array es fx =>
        simp only [hg] at h
        split at h
        · simp only [Except.ok.injEq] at h
          subst h
          refine ⟨_, _, hg, rfl, fun lo hi hr hmv x hx m hm => ?_⟩
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hr x hx m hm
          · exact hmv m hm
        · cases h

/-- A write keeps the objects older-referencing, where what it writes at an
object of the interval is a primitive or an older object of it. -/
theorem DescFrom.writeAddr {σ τ : State} {mv : MVal} {a : Addr} {lo hi : Nat}
    (hd : DescFrom σ.heap lo hi) (hw : writeAddr σ mv a = .ok τ)
    (hmv : lo ≤ a.id → a.id < hi → ∀ m, mv = .ref m → lo ≤ m ∧ m < a.id) :
    DescFrom τ.heap lo hi := by
  obtain ⟨obj, obj', hg, hτ, hr⟩ := writeAddr_obj hw
  intro j hj hj'
  rw [hτ]
  by_cases hja : j = a.id
  · subst hja
    obtain ⟨obj₁, hg₁, hr₁⟩ := hd _ hj hj'
    rw [hg] at hg₁
    cases hg₁
    exact ⟨obj', lookupBy_setBy_self _ _ _, hr _ _ hr₁ (hmv hj hj')⟩
  · rw [lookupBy_setBy_ne hja]
    exact hd j hj hj'

/-- **A copy out of memory returns** where every object below the root is
there and references only older ones (Lean only: `copyMem` halts on a cycle,
where KeY's view is total). -/
theorem copyMToSt_ok_desc {σ : State} {lo hi : Nat} (hd : DescFrom σ.heap lo hi) :
    ∀ id, lo ≤ id → id < hi → ∀ rem : List Nat, (∀ j, lo ≤ j → j ≤ id → j ∈ rem) →
      ∃ v, copyMToSt σ rem (.ref id) = .ok v := by
  intro id
  refine Nat.strongRecOn id ?_
  intro id ih hlo hhi rem hrem
  obtain ⟨obj, hg, hr⟩ := hd id hlo hhi
  have hmem : id ∈ rem := hrem id hlo (Nat.le_refl _)
  have hslot : ∀ mv : MVal, (∀ m, mv = .ref m → lo ≤ m ∧ m < id) →
      ∃ w, copyMToSt σ (rem.erase id) mv = .ok w := by
    intro mv hmv
    cases mv with
    | prim pv => exact ⟨_, Close.copyMToSt_prim σ _ pv⟩
    | ref m =>
      obtain ⟨h1, h2⟩ := hmv m rfl
      exact ih m h2 h1 (Nat.lt_trans h2 hhi) _ fun j hj hj' =>
        (List.mem_erase_of_ne (Nat.ne_of_lt (Nat.lt_of_le_of_lt hj' h2))).2
          (hrem j hj (Nat.le_trans hj' (Nat.le_of_lt h2)))
  cases obj with
  | struct fs =>
    have hfs : ∀ fs' : List (Name × MVal), (∀ x ∈ fs', ∀ m, x.2 = .ref m → lo ≤ m ∧ m < id) →
        ∃ sfs, copyMFields σ (rem.erase id) fs' = .ok sfs := by
      intro fs' hf
      induction fs' with
      | nil => exact ⟨[], by rw [copyMFields]⟩
      | cons x rest ihr =>
        obtain ⟨n, mv⟩ := x
        obtain ⟨w, hw⟩ := hslot mv (hf (n, mv) List.mem_cons_self)
        obtain ⟨srest, hs⟩ := ihr (fun y hy => hf y (List.mem_cons_of_mem _ hy))
        exact ⟨(n, w) :: srest, by rw [copyMFields, hw, hs]; rfl⟩
    obtain ⟨sfs, hs⟩ := hfs fs hr
    exact ⟨_, copyMToSt_ref_struct hmem hg hs⟩
  | array es fx =>
    have hes : ∀ es' : List MVal, (∀ x ∈ es', ∀ m, x = .ref m → lo ≤ m ∧ m < id) →
        ∃ ses, copyMElems σ (rem.erase id) es' = .ok ses := by
      intro es' he
      induction es' with
      | nil => exact ⟨[], by rw [copyMElems]⟩
      | cons x rest ihr =>
        obtain ⟨w, hw⟩ := hslot x (he x List.mem_cons_self)
        obtain ⟨srest, hs⟩ := ihr (fun y hy => he y (List.mem_cons_of_mem _ hy))
        exact ⟨w :: srest, by rw [copyMElems, hw, hs]; rfl⟩
    obtain ⟨ses, hs⟩ := hes es hr
    exact ⟨_, copyMToSt_ref_array hmem hg hs⟩

/-- `copyMToSt_ok_desc` at `copyMem`, which starts from every identity of the heap. -/
theorem copyMem_ok_desc {σ : State} {lo hi id : Nat} (hd : DescFrom σ.heap lo hi) (hlo : lo ≤ id)
    (hhi : id < hi) : ∃ v, copyMem σ (.ref id) = .ok v :=
  copyMToSt_ok_desc hd id hlo hhi _ fun j hj hj' => by
    obtain ⟨obj, hg, -⟩ := hd j hj (Nat.lt_of_le_of_lt hj' hhi)
    exact lookupBy_mem_keys hg

mutual

/-- A copy into memory leaves its objects older-referencing, and its root in
its interval. -/
theorem copyStToM_desc (τ' : State) (σ : State) (v : SVal) :
    ∀ τ mv, copyStToM σ v = .ok (τ, mv) → τ.HeapExt τ' →
      DescFrom τ'.heap σ.nextId τ.nextId ∧ ∀ m, mv = .ref m → σ.nextId ≤ m ∧ m < τ.nextId := by
  intro τ mv h hx
  cases v with
  | prim p =>
    obtain ⟨rfl, rfl⟩ := copyStToM_prim_inv h
    exact ⟨DescFrom.empty _ _, fun m hm => nomatch hm⟩
  | map e d => exact (copyStToM_map_inv h).elim
  | struct fs =>
    obtain ⟨τ₁, mfs, hf, hτ, rfl⟩ := copyStToM_struct_inv h
    obtain ⟨hobj, hx₁, hn⟩ := alloc_ext hτ hx
    obtain ⟨hd, hr⟩ := copyStFields_desc τ' σ fs τ₁ mfs hf hx₁
    have hle : σ.nextId ≤ τ₁.nextId := copyStFields_nextId σ fs τ₁ mfs hf
    rw [hn]
    refine ⟨fun j hj hj' => ?_, fun m hm => ?_⟩
    · by_cases hjl : j < τ₁.nextId
      · exact hd j hj hjl
      · have hj : j = τ₁.nextId := by omega
        subst hj
        exact ⟨_, hobj, hr⟩
    · cases hm
      exact ⟨hle, Nat.lt_succ_self _⟩
  | array es sh fx =>
    obtain ⟨τ₁, mes, he, hτ, rfl⟩ := copyStToM_array_inv h
    obtain ⟨hobj, hx₁, hn⟩ := alloc_ext hτ hx
    obtain ⟨hd, hr⟩ := copyStElems_desc τ' σ es τ₁ mes he hx₁
    have hle : σ.nextId ≤ τ₁.nextId := copyStElems_nextId σ es τ₁ mes he
    rw [hn]
    refine ⟨fun j hj hj' => ?_, fun m hm => ?_⟩
    · by_cases hjl : j < τ₁.nextId
      · exact hd j hj hjl
      · have hj : j = τ₁.nextId := by omega
        subst hj
        exact ⟨_, hobj, hr fx⟩
    · cases hm
      exact ⟨hle, Nat.lt_succ_self _⟩

theorem copyStFields_desc (τ' : State) (σ : State) (fs : List (Name × SVal)) :
    ∀ τ mfs, copyStFields σ fs = .ok (τ, mfs) → τ.HeapExt τ' →
      DescFrom τ'.heap σ.nextId τ.nextId ∧ RefsIn σ.nextId τ.nextId (.struct mfs) := by
  intro τ mfs h hx
  cases fs with
  | nil =>
    obtain ⟨rfl, rfl⟩ := copyStFields_nil_inv h
    exact ⟨DescFrom.empty _ _, fun x hx => nomatch hx⟩
  | cons fv rest =>
    obtain ⟨n, v⟩ := fv
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStFields_cons_inv h
    have hx₁ : σ₁.HeapExt τ' := (copyStFields_heapExt σ₁ rest τ mrest h2).trans hx
    have hle₁ : σ.nextId ≤ σ₁.nextId := copyStToM_nextId σ v σ₁ mv h1
    have hle₂ : σ₁.nextId ≤ τ.nextId := copyStFields_nextId σ₁ rest τ mrest h2
    obtain ⟨hd₁, hr₁⟩ := copyStToM_desc τ' σ v σ₁ mv h1 hx₁
    obtain ⟨hd₂, hr₂⟩ := copyStFields_desc τ' σ₁ rest τ mrest h2 hx
    refine ⟨hd₁.append hd₂ hle₁, fun x hx m hm => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · have := hr₁ m hm
      exact ⟨this.1, Nat.lt_of_lt_of_le this.2 hle₂⟩
    · have := hr₂ x hx m hm
      exact ⟨Nat.le_trans hle₁ this.1, this.2⟩

theorem copyStElems_desc (τ' : State) (σ : State) (es : List SVal) :
    ∀ τ mes, copyStElems σ es = .ok (τ, mes) → τ.HeapExt τ' →
      DescFrom τ'.heap σ.nextId τ.nextId ∧ ∀ fx, RefsIn σ.nextId τ.nextId (.array mes fx) := by
  intro τ mes h hx
  cases es with
  | nil =>
    obtain ⟨rfl, rfl⟩ := copyStElems_nil_inv h
    exact ⟨DescFrom.empty _ _, fun _ x hx => nomatch hx⟩
  | cons v rest =>
    obtain ⟨σ₁, mv, mrest, h1, h2, rfl⟩ := copyStElems_cons_inv h
    have hx₁ : σ₁.HeapExt τ' := (copyStElems_heapExt σ₁ rest τ mrest h2).trans hx
    have hle₁ : σ.nextId ≤ σ₁.nextId := copyStToM_nextId σ v σ₁ mv h1
    have hle₂ : σ₁.nextId ≤ τ.nextId := copyStElems_nextId σ₁ rest τ mrest h2
    obtain ⟨hd₁, hr₁⟩ := copyStToM_desc τ' σ v σ₁ mv h1 hx₁
    obtain ⟨hd₂, hr₂⟩ := copyStElems_desc τ' σ₁ rest τ mrest h2 hx
    refine ⟨hd₁.append hd₂ hle₁, fun fx x hx m hm => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · have := hr₁ m hm
      exact ⟨this.1, Nat.lt_of_lt_of_le this.2 hle₂⟩
    · have := hr₂ fx x hx m hm
      exact ⟨Nat.le_trans hle₁ this.1, this.2⟩

end

/-! ## When a copy into memory halts -/

theorem fieldsHaveMapping_lookup : ∀ {L : List (Name × Ty)} {n : Name} {T : Ty},
    lookupBy n L = some T → fieldsHaveMapping L = false → tyHasMapping T = false
  | [], n, T, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (n', T') :: rest, n, T, h, hf => by
    rw [fieldsHaveMapping, Bool.or_eq_false_iff] at hf
    simp only [lookupBy] at h
    split at h
    · cases h
      exact hf.1
    · exact fieldsHaveMapping_lookup h hf.2

open SVal.canonB (canonFieldsB canonElemsB) in
mutual

/-- **A copy into memory returns** on a canonical value of a type that holds
no mapping (Lean only: `copyStToM` halts on a mapping, which solc does not
compile; the closer's `wt` premise gives the canonical value). -/
theorem copyStToM_ok_noMap (σ : State) (v : SVal) :
    ∀ T : Ty, v.canonB T = true → tyHasMapping T = false → ∃ τ mv, copyStToM σ v = .ok (τ, mv) := by
  intro T hc hT
  cases v with
  | prim pv => cases pv <;> exact ⟨_, _, rfl⟩
  | map e d =>
    cases T with
    | prim p => simp only [SVal.canonB, Bool.false_eq_true] at hc
    | ref R =>
      cases R with
      | mapping K V => rw [tyHasMapping] at hT; cases hT
      | struct s => simp only [SVal.canonB, Bool.false_eq_true] at hc
      | array E => simp only [SVal.canonB, Bool.false_eq_true] at hc
      | fixed E n => simp only [SVal.canonB, Bool.false_eq_true] at hc
  | struct fs =>
    cases T with
    | prim p => simp only [SVal.canonB, Bool.false_eq_true] at hc
    | ref R =>
      cases R with
      | struct s =>
        simp only [SVal.canonB, Bool.and_eq_true] at hc
        rw [tyHasMapping] at hT
        obtain ⟨τ₁, mfs, hf⟩ := copyStFields_ok_noMap σ fs s hc.2 hT
        exact ⟨_, _, by rw [copyStToM, hf]; rfl⟩
      | mapping K V => simp only [SVal.canonB, Bool.false_eq_true] at hc
      | array E => simp only [SVal.canonB, Bool.false_eq_true] at hc
      | fixed E n => simp only [SVal.canonB, Bool.false_eq_true] at hc
  | array es sh fx =>
    cases T with
    | prim p => simp only [SVal.canonB, Bool.false_eq_true] at hc
    | ref R =>
      cases R with
      | array E =>
        simp only [SVal.canonB, Bool.and_eq_true] at hc
        rw [tyHasMapping] at hT
        obtain ⟨τ₁, mes, he⟩ := copyStElems_ok_noMap σ es E hc.1.2 hT
        exact ⟨_, _, by rw [copyStToM, he]; rfl⟩
      | fixed E n =>
        simp only [SVal.canonB, Bool.and_eq_true] at hc
        rw [tyHasMapping] at hT
        obtain ⟨τ₁, mes, he⟩ := copyStElems_ok_noMap σ es E hc.1.2 hT
        exact ⟨_, _, by rw [copyStToM, he]; rfl⟩
      | mapping K V => simp only [SVal.canonB, Bool.false_eq_true] at hc
      | struct s => simp only [SVal.canonB, Bool.false_eq_true] at hc

theorem copyStFields_ok_noMap (σ : State) (fs : List (Name × SVal)) :
    ∀ s : Name, canonFieldsB s fs = true → fieldsHaveMapping (structDef s) = false →
      ∃ τ mfs, copyStFields σ fs = .ok (τ, mfs) := by
  intro s hc hs
  cases fs with
  | nil => exact ⟨_, _, rfl⟩
  | cons fv rest =>
    obtain ⟨n, v⟩ := fv
    simp only [canonFieldsB, Bool.and_eq_true] at hc
    split at hc
    · rename_i T hT
      obtain ⟨σ₁, mv, h1⟩ := copyStToM_ok_noMap σ v T hc.1 (fieldsHaveMapping_lookup hT hs)
      obtain ⟨τ, mrest, h2⟩ := copyStFields_ok_noMap σ₁ rest s hc.2 hs
      exact ⟨_, _, by rw [copyStFields, h1, Res.ok_bind']; dsimp only; rw [h2]; rfl⟩
    · exact absurd hc.1 Bool.false_ne_true

theorem copyStElems_ok_noMap (σ : State) (es : List SVal) :
    ∀ E : Ty, canonElemsB E es = true → tyHasMapping E = false →
      ∃ τ mes, copyStElems σ es = .ok (τ, mes) := by
  intro E hc hE
  cases es with
  | nil => exact ⟨_, _, rfl⟩
  | cons v rest =>
    simp only [canonElemsB, Bool.and_eq_true] at hc
    obtain ⟨σ₁, mv, h1⟩ := copyStToM_ok_noMap σ v E hc.1 hE
    obtain ⟨τ, mrest, h2⟩ := copyStElems_ok_noMap σ₁ rest E hc.2 hE
    exact ⟨_, _, by rw [copyStElems, h1, Res.ok_bind']; dsimp only; rw [h2]; rfl⟩

end

/-! ## Names fixed at their birth -/

/-- One allocation of a leaf: the root it minted, the heap right after it,
and the counters it used. -/
structure Birth where
  root : Nat
  heap : List (Nat × MObj)
  lo : Nat
  hi : Nat

/-- The allocations of a leaf, oldest first: the `k`-th is KeY's `k`-th
`freshIdp`. -/
abbrev Births := List Birth

/-- The birth a copy into memory gives: its root is taken from the copy's
result, since the root is allocated last. -/
def Birth.ofCopy (σ τ : State) (n : Nat) : Birth := ⟨n, τ.heap, σ.nextId, τ.nextId⟩

/-- The object the name `idC(k, p)` denotes: `p` resolved from the `k`-th
root in the heap of its birth. -/
def Births.eval (B : Births) (k : Nat) (p : List Seg) : Option Nat :=
  match B[k]? with
  | some b => resolveFrom b.heap b.root p
  | none => none

/-- A birth as a copy leaves it: a tree in its interval, every reference
older. -/
def Birth.Ok (b : Birth) : Prop := Owned b.heap b.lo b.hi (.ref b.root) ∧ DescFrom b.heap b.lo b.hi

/-- The births of a run from the counter `base` to the state `τ`: each as a
copy leaves it, in order, in disjoint intervals below `τ`'s counter. -/
def Births.Ok (B : Births) (base : Nat) (τ : State) : Prop :=
  base ≤ τ.nextId ∧ ∀ (k : Nat) b, B[k]? = some b → b.Ok ∧ base ≤ b.lo ∧ b.hi ≤ τ.nextId ∧
    ∀ (k' : Nat) b', k < k' → B[k']? = some b' → b.hi ≤ b'.lo

theorem Birth.ok_ofCopy {σ τ : State} {v : SVal} {n : Nat} (h : copyStToM σ v = .ok (τ, .ref n)) :
    (Birth.ofCopy σ τ n).Ok :=
  ⟨copyStToM_owned τ σ v τ _ h (State.HeapExt.refl τ),
    (copyStToM_desc τ σ v τ _ h (State.HeapExt.refl τ)).1⟩

theorem Births.Ok.nil {base : Nat} {τ : State} (h : base ≤ τ.nextId) : Births.Ok [] base τ :=
  ⟨h, fun k b hb => by simp only [List.getElem?_nil, reduceCtorEq] at hb⟩

/-- A run that only moves the counter on keeps its births. -/
theorem Births.Ok.mono {B : Births} {base : Nat} {τ τ' : State} (h : B.Ok base τ)
    (hn : τ.nextId ≤ τ'.nextId) : B.Ok base τ' := by
  refine ⟨Nat.le_trans h.1 hn, fun k b hb => ?_⟩
  obtain ⟨hok, hlo, hhi, hord⟩ := h.2 k b hb
  exact ⟨hok, hlo, Nat.le_trans hhi hn, hord⟩

theorem getElem?_snoc {B : Births} {b b' : Birth} {k : Nat} (h : (B ++ [b])[k]? = some b') :
    (k < B.length ∧ B[k]? = some b') ∨ (k = B.length ∧ b' = b) := by
  by_cases hk : k < B.length
  · rw [List.getElem?_append_left hk] at h
    exact .inl ⟨hk, h⟩
  · rw [List.getElem?_append_right (Nat.not_lt.1 hk)] at h
    have h0 : k - B.length = 0 := by
      cases hkl : k - B.length with
      | zero => rfl
      | succ j => rw [hkl] at h; simp only [List.getElem?_cons_succ, List.getElem?_nil,
          reduceCtorEq] at h
    rw [h0, List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr ⟨by omega, h.symm⟩

/-- An allocation adds its birth to the run's. -/
theorem Births.Ok.snoc {B : Births} {base : Nat} {σ τ : State} {v : SVal} {n : Nat}
    (h : B.Ok base σ) (hc : copyStToM σ v = .ok (τ, .ref n)) :
    (B ++ [Birth.ofCopy σ τ n]).Ok base τ := by
  have hle : σ.nextId ≤ τ.nextId := copyStToM_nextId σ v τ _ hc
  refine ⟨Nat.le_trans h.1 hle, fun k b hb => ?_⟩
  rcases getElem?_snoc hb with ⟨hk, hb⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hok, hlo, hhi, hord⟩ := h.2 k b hb
    refine ⟨hok, hlo, Nat.le_trans hhi hle, fun k' b' hkk' hb' => ?_⟩
    rcases getElem?_snoc hb' with ⟨_, hb'⟩ | ⟨rfl, rfl⟩
    · exact hord k' b' hkk' hb'
    · exact hhi
  · refine ⟨Birth.ok_ofCopy hc, h.1, Nat.le_refl _, fun k' b' hkk' hb' => ?_⟩
    rcases getElem?_snoc hb' with ⟨hk', _⟩ | ⟨hk', _⟩ <;> omega

/-- **A name keeps its object** when later allocations are born
(`eval_mono`): KeY's `\unique idC`. -/
theorem Births.eval_mono {B : Births} {b : Birth} {k : Nat} (hk : k < B.length) (p : List Seg) :
    (B ++ [b]).eval k p = B.eval k p := by
  simp only [Births.eval, List.getElem?_append_left hk]

theorem Births.eval_last (B : Births) (b : Birth) (p : List Seg) :
    (B ++ [b]).eval B.length p = resolveFrom b.heap b.root p := by
  simp only [Births.eval, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

theorem Births.eval_some {B : Births} {k : Nat} {p : List Seg} {m : Nat} (h : B.eval k p = some m) :
    ∃ b, B[k]? = some b ∧ resolveFrom b.heap b.root p = some m := by
  unfold Births.eval at h
  split at h
  · rename_i b hb
    exact ⟨b, hb, h⟩
  · cases h

/-- A name denotes an object of its root's interval. -/
theorem Births.eval_interval {B : Births} {base : Nat} {τ : State} (hB : B.Ok base τ) {k : Nat}
    {p : List Seg} {m : Nat} (h : B.eval k p = some m) :
    ∃ b, B[k]? = some b ∧ b.lo ≤ m ∧ m < b.hi ∧ base ≤ m ∧ m < τ.nextId := by
  obtain ⟨b, hb, hr⟩ := Births.eval_some h
  obtain ⟨⟨ho, -⟩, hlo, hhi, -⟩ := hB.2 k b hb
  have := (Owned.ref_iff.1 ho).1 p m hr
  exact ⟨b, hb, this.1, this.2, by omega, by omega⟩

/-- **Two names of one object are one name**: two roots are apart
(`newFromAdd`, `newAddDifferent`), and two paths from one root are apart
(`copyStToM_resolve_inj`). -/
theorem Births.eval_inj {B : Births} {base : Nat} {τ : State} (hB : B.Ok base τ) {k k' : Nat}
    {p q : List Seg} {m : Nat} (hp : B.eval k p = some m) (hq : B.eval k' q = some m) :
    k = k' ∧ p = q := by
  obtain ⟨b, hb, hrp⟩ := Births.eval_some hp
  obtain ⟨b', hb', hrq⟩ := Births.eval_some hq
  obtain ⟨⟨ho, -⟩, -, -, hord⟩ := hB.2 k b hb
  obtain ⟨⟨ho', -⟩, -, -, hord'⟩ := hB.2 k' b' hb'
  have i₁ := (Owned.ref_iff.1 ho).1 p m hrp
  have i₂ := (Owned.ref_iff.1 ho').1 q m hrq
  rcases Nat.lt_trichotomy k k' with hkk | rfl | hkk
  · have := hord k' b' hkk hb'
    omega
  · rw [hb, Option.some.injEq] at hb'
    subst hb'
    exact ⟨rfl, (Owned.ref_iff.1 ho).2 p q m hrp hrq⟩
  · have := hord' k b hkk hb
    omega

theorem step_congr {h h' : List (Nat × MObj)} {m : Nat} (a : Seg)
    (heq : lookupBy m h = lookupBy m h') : step h m a = step h' m a := by
  cases a <;> simp only [step, heq]

/-- **A reference slot of a name is the name one segment longer**, read in
the birth heap (KeY's `initIdentity`, `idCCDef`, `readFromCopyToStorageIdentity`). -/
theorem birth_slot {B : Births} {b : Birth} {k m : Nat} {p : List Seg} (a : Seg)
    (hb : B[k]? = some b) (hm : B.eval k p = some m) :
    B.eval k (p ++ [a]) = step b.heap m a := by
  simp only [Births.eval, hb] at hm ⊢
  rw [resolveFrom_append, hm, Option.bind_some, resolveFrom]
  cases step b.heap m a <;> rfl

/-- `birth_slot` read in a state that holds the object as its birth left it. -/
theorem birth_slot_readAddr {B : Births} {b : Birth} {k m m' : Nat} {p : List Seg} {τ : State}
    (a : Seg) (hb : B[k]? = some b) (hm : B.eval k p = some m)
    (hobj : lookupBy m τ.heap = lookupBy m b.heap) :
    B.eval k (p ++ [a]) = some m' ↔ readAddr τ (.ofSeg m a) = .ok (.ref m') := by
  rw [birth_slot a hb hm, ← step_congr a hobj]
  exact step_iff_readAddr τ m m' a

end MemNames

end Solidity
