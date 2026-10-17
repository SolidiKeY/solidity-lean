import Solidity.Theory.Typed.Obs
import Solidity.Semantics.StorageWt

/-!
# Typed storage values, hereditarily

The typed storage (`Semantics/Storage.lean`) says by its types what the
untyped one had to check: a struct has its members, a word is in range, a
fixed-size array has its length and nothing past it.  What a reachable
storage satisfies beyond that is a condition on each node of a value (a
mapping's keys distinct, the slots past an array's end cleared, …), asked
of every node: `SVal.All L`, for the node conditions `L : Hered`.  The run
invariants of `Typing/Reachability.lean` (`SVal.Canon`),
`Typing/Constructibility.lean` (`SVal.Tight`, `SVal.Fits`) and
`Typing/Fits.lean` (`SVal.Bnd`) are each one `Hered`.

`SVal.All` is a fold (`SVal.fold`, its equations by `rfl` and named,
`Solidity/Eqns.lean`), so a proof unfolds it one constructor at a time.
What every such predicate shares is proved here once: it holds of what a
read finds (`SVal.findM_all`), of a member or element, of a default when
the node conditions hold of the defaults' nodes (`SVal.dflt_all`).

Also here: the defaults' equations (`SVal.dflt_struct` …, `SVal.dflt` is
by fuel), the list lemmas the proofs above share, and the live slots along
a typed path (`SVal.Live`).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB tyRank fieldsRank lookupBy_setBy_self
  lookupBy_setBy_ne setBy_setBy_self lookupBy_eq_some_mem)

/-! ## Association lists -/

section Lists

variable {κ α : Type} [DecidableEq κ]

theorem lookupBy_isSome_of_mem' {k : κ} {v : α} : {l : List (κ × α)} → (k, v) ∈ l →
    (lookupBy k l).isSome = true
  | [], h => nomatch h
  | (k', v') :: rest, h => by
    simp only [lookupBy]
    split
    · rfl
    · rename_i hk
      rcases List.mem_cons.mp h with h | h
      · cases h; exact absurd rfl hk
      · exact lookupBy_isSome_of_mem' h

/-- An entry of a list with distinct keys is what its key looks up. -/
theorem lookupBy_of_nodup {k : κ} {v : α} : {l : List (κ × α)} → nodupKeysB l = true →
    (k, v) ∈ l → lookupBy k l = some v
  | [], _, h => nomatch h
  | (k', v') :: rest, hnd, h => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
    simp only [lookupBy]
    rcases List.mem_cons.mp h with he | hm
    · cases he; simp only [↓reduceIte]
    · split
      · rename_i hk
        subst hk
        have := lookupBy_isSome_of_mem' (k := k) hm
        rw [hnd.1] at this
        exact nomatch this
      · exact lookupBy_of_nodup hnd.2 hm

/-- Every entry of `setBy k v l` is `(k, v)` or one of `l`'s. -/
theorem mem_setBy {k : κ} {v : α} {e : κ × α} : {l : List (κ × α)} → e ∈ setBy k v l →
    e = (k, v) ∨ e ∈ l
  | [], h => by simp only [setBy, List.mem_cons, List.not_mem_nil, or_false] at h; exact Or.inl h
  | (k', v') :: rest, h => by
    simp only [setBy] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · rcases mem_setBy h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem lookupBy_none_setBy {k k' : κ} {v : α} (hne : k ≠ k') {l : List (κ × α)}
    (h : lookupBy k l = none) : lookupBy k (setBy k' v l) = none := by
  rw [lookupBy_setBy_ne hne]; exact h

/-- `setBy` keeps the keys distinct. -/
theorem nodupKeysB_setBy' {k : κ} {v : α} : {l : List (κ × α)} → nodupKeysB l = true →
    nodupKeysB (setBy k v l) = true
  | [], _ => by simp only [setBy, nodupKeysB, lookupBy, Option.isNone_none, Bool.and_self]
  | (k', v') :: rest, hnd => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
    simp only [setBy]
    split
    · rename_i hk
      subst hk
      simp only [nodupKeysB, hnd.1, Option.isNone_none, hnd.2, Bool.and_self]
    · rename_i hk
      simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none]
      exact ⟨lookupBy_none_setBy (Ne.symm hk) hnd.1, nodupKeysB_setBy' hnd.2⟩

theorem setBy_of_lookupBy {k : κ} {v : α} : {l : List (κ × α)} → lookupBy k l = some v →
    setBy k v l = l
  | [], h => by simp only [lookupBy, reduceCtorEq] at h
  | (k', w) :: rest, h => by
    simp only [lookupBy] at h
    by_cases hk : k = k'
    · simp only [hk, ↓reduceIte, Option.some.injEq] at h
      subst hk h
      simp only [setBy, ↓reduceIte]
    · simp only [hk, ↓reduceIte] at h
      simp only [setBy, hk, ↓reduceIte, setBy_of_lookupBy h]

theorem lookupBy_append_none {k : κ} : {l₁ : List (κ × α)} → (l₂ : List (κ × α)) →
    lookupBy k l₁ = none → lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _, _ => rfl
  | (k', v') :: l₁, l₂, h => by
    simp only [lookupBy] at h ⊢
    split at h
    · exact nomatch h
    · rename_i hk
      simp only [List.cons_append, lookupBy, hk, ↓reduceIte]
      exact lookupBy_append_none l₂ h

theorem setBy_append_none {k : κ} {v : α} : {l₁ : List (κ × α)} → (l₂ : List (κ × α)) →
    lookupBy k l₁ = none → setBy k v (l₁ ++ l₂) = l₁ ++ setBy k v l₂
  | [], _, _ => rfl
  | (k', v') :: l₁, l₂, h => by
    simp only [lookupBy] at h
    split at h
    · exact nomatch h
    · rename_i hk
      simp only [List.cons_append, setBy, hk, ↓reduceIte]
      rw [setBy_append_none l₂ h]

theorem nodupKeysB_mid {k : κ} {v : α} : {l₁ : List (κ × α)} → {l₂ : List (κ × α)} →
    nodupKeysB (l₁ ++ (k, v) :: l₂) = true → lookupBy k l₁ = none
  | [], _, _ => rfl
  | (k', v') :: l₁, l₂, h => by
    simp only [List.cons_append, nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    simp only [lookupBy]
    split
    · rename_i hk
      subst hk
      have := lookupBy_isSome_of_mem' (k := k) (v := v)
        (List.mem_append_right l₁ List.mem_cons_self : (k, v) ∈ l₁ ++ (k, v) :: l₂)
      rw [h.1] at this
      exact nomatch this
    · exact nodupKeysB_mid h.2

end Lists

/-! ## Defaults by their equations

`SVal.dflt` is by fuel, a bound on the rank; the fuel does not matter
(`SVal.dfltBelow_irrel`), so a default unfolds one type constructor at a
time. -/

theorem SFields.dfltBelow_irrel {k k' : Nat} {ih : (T : Ty) → tyRank T < k → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → SVal T} (hih : ∀ T h h', ih T h = ih' T h') :
    (fs : List (Name × Ty)) → (h : fieldsRank fs < k) → (h' : fieldsRank fs < k') →
    SFields.dfltBelow k ih fs h = SFields.dfltBelow k' ih' fs h'
  | [], _, _ => rfl
  | (_, T) :: fs, h, h' => by
    simp only [SFields.dfltBelow]
    rw [hih T, SFields.dfltBelow_irrel hih fs]

mutual
theorem SVal.dfltAt_irrel {k k' : Nat} {ih : (T : Ty) → tyRank T < k → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → SVal T} (hih : ∀ T h h', ih T h = ih' T h') :
    (T : Ty) → (h : tyRank T < k + 1) → (h' : tyRank T < k' + 1) →
    SVal.dfltAt k ih T h = SVal.dfltAt k' ih' T h'
  | .prim _, _, _ => rfl
  | .ref R, h, h' => SVal.dfltRefAt_irrel hih R h h'

theorem SVal.dfltRefAt_irrel {k k' : Nat} {ih : (T : Ty) → tyRank T < k → SVal T}
    {ih' : (T : Ty) → tyRank T < k' → SVal T} (hih : ∀ T h h', ih T h = ih' T h') :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) → (h' : tyRank (.ref R) < k' + 1) →
    SVal.dfltRefAt k ih R h = SVal.dfltRefAt k' ih' R h'
  | .struct s, h, h' => by
    simp only [SVal.dfltRefAt]
    rw [SFields.dfltBelow_irrel hih]
  | .array _, _, _ => rfl
  | .fixed E n, h, h' => by
    simp only [SVal.dfltRefAt]
    rw [SVal.dfltAt_irrel hih E]
  | .mapping _ V, h, h' => by
    simp only [SVal.dfltRefAt]
    rw [SVal.dfltAt_irrel hih V]
end

theorem SVal.dfltBelow_irrel : (k k' : Nat) → (T : Ty) → (h : tyRank T < k) →
    (h' : tyRank T < k') → SVal.dfltBelow k T h = SVal.dfltBelow k' T h'
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h' => absurd h' (Nat.not_lt_zero _)
  | k + 1, k' + 1, T, h, h' => by
    simp only [SVal.dfltBelow]
    exact SVal.dfltAt_irrel (fun T h h' => SVal.dfltBelow_irrel k k' T h h') T h h'

theorem SVal.dfltBelow_dflt (k : Nat) (T : Ty) (h : tyRank T < k) :
    SVal.dfltBelow k T h = SVal.dflt T :=
  SVal.dfltBelow_irrel _ _ T h _

theorem SFields.dfltBelow_eq (k : Nat) :
    (fs : List (Name × Ty)) → (h : fieldsRank fs < k) →
    SFields.dfltBelow k (SVal.dfltBelow k) fs h = SFields.dflt fs
  | [], _ => rfl
  | (_, T) :: fs, h => by
    simp only [SFields.dfltBelow, SFields.dflt]
    rw [SVal.dfltBelow_dflt, SFields.dfltBelow_eq k fs]

/-- A default unfolded once. -/
theorem SVal.dflt_eq_at (T : Ty) :
    SVal.dflt T = SVal.dfltAt (rankBound T) (SVal.dfltBelow (rankBound T)) T
      (Nat.lt_succ_of_le (tyRank_le_rankBound T)) := rfl

theorem SVal.dflt_prim (p : PrimTy) : SVal.dflt (.prim p) = .prim (PrimTy.dflt p) := rfl

theorem SVal.dflt_struct (s : Name) :
    SVal.dflt (.ref (.struct s)) = .struct (SFields.dflt (structDef s)) := by
  rw [SVal.dflt_eq_at]
  simp only [SVal.dfltAt, SVal.dfltRefAt]
  rw [SFields.dfltBelow_eq]

theorem SVal.dflt_array (E : Ty) :
    SVal.dflt (.ref (.array E)) = .array .nil .nil SVal.zero_lt_bound := rfl

theorem SVal.dflt_fixed (E : Ty) (n : Nat) :
    SVal.dflt (.ref (.fixed E n)) = .fixed (SVec.replicate (SVal.dflt E) n) := by
  rw [SVal.dflt_eq_at]
  simp only [SVal.dfltAt, SVal.dfltRefAt]
  exact congrArg (fun x => SVal.fixed (SVec.replicate x n))
    (SVal.dfltAt_irrel (fun T h h' => SVal.dfltBelow_irrel _ _ T h h') E _ _)

theorem SVal.dflt_map (K : PrimTy) (V : Ty) :
    SVal.dflt (.ref (.mapping K V)) = .map .nil (SVal.dflt V) := by
  rw [SVal.dflt_eq_at]
  simp only [SVal.dfltAt, SVal.dfltRefAt]
  exact congrArg (SVal.map .nil)
    (SVal.dfltAt_irrel (fun T h h' => SVal.dfltBelow_irrel _ _ T h h') V _ _)

/-- A default's subterm at a fuel that defaults agree on is the default. -/
theorem SVal.dfltAt_eq {k : Nat} {ih : (T : Ty) → tyRank T < k → SVal T}
    (heq : ∀ T h, ih T h = SVal.dflt T) (T : Ty) (h : tyRank T < k + 1) :
    SVal.dfltAt k ih T h = SVal.dflt T := by
  rw [SVal.dfltAt_irrel (ih' := SVal.dfltBelow k)
    (fun T h h' => by rw [heq, SVal.dfltBelow_dflt]) T h h]
  exact SVal.dfltBelow_dflt (k + 1) T h

/-! ## Hereditary predicates -/

/-- What a predicate asks of each node of a value, by kind: of a dynamic
array its live elements and the slots past its end, of a fixed-size array
its type, of a mapping its entries and its default.  A word and a struct
ask nothing of their own. -/
structure Hered where
  arr : {E : Ty} → {n : Nat} → SVec E n → SList E → Prop
  fix : Ty → Nat → Prop
  map : (K : PrimTy) → {V : Ty} → SMap K V → SVal V → Prop

/-- Every node satisfying `P`'s condition, as a fold. -/
def allFold (P : Hered) : Fold where
  V _ := Prop
  F _ := Prop
  L _ := Prop
  W _ _ := Prop
  M _ _ := Prop
  prim := fun _ => True
  struct := fun _ ih => ih
  array := fun e sh _ ie ish => P.arr e sh ∧ ie ∧ ish
  fixed := fun {E} {n} _ ie => P.fix E n ∧ ie
  map := fun {K} {_} m d im id => P.map K m d ∧ im ∧ id
  fnil := True
  fcons := fun _ _ iv ir => iv ∧ ir
  lnil := True
  lcons := fun _ _ iv ir => iv ∧ ir
  wnil := True
  wcons := fun _ _ iv ir => iv ∧ ir
  mnil := True
  mcons := fun _ _ _ iv ir => iv ∧ ir

/-- Every node of `v` satisfies `P`'s condition. -/
def SVal.All (P : Hered) {T : Ty} (v : SVal T) : Prop := v.fold (allFold P)
def SFields.All (P : Hered) {fs : List (Name × Ty)} (x : SFields fs) : Prop := x.fold (allFold P)
def SList.All (P : Hered) {E : Ty} (l : SList E) : Prop := l.fold (allFold P)
def SVec.All (P : Hered) {E : Ty} {n : Nat} (l : SVec E n) : Prop := l.fold (allFold P)
def SMap.All (P : Hered) {K : PrimTy} {V : Ty} (m : SMap K V) : Prop := m.fold (allFold P)

section All

variable (P : Hered)

theorem SVal.All_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).All P = True := rfl
theorem SVal.All_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).All P = fs.All P := rfl
theorem SVal.All_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).All P = (P.arr e sh ∧ e.All P ∧ sh.All P) := rfl
theorem SVal.All_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).All P = (P.fix E n ∧ e.All P) := rfl
theorem SVal.All_map {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) :
    (SVal.map (K := K) m d).All P = (P.map K m d ∧ m.All P ∧ d.All P) := rfl
theorem SFields.All_nil : (SFields.nil).All P = True := rfl
theorem SFields.All_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T)
    (rest : SFields fs) : (SFields.cons (f := f) v rest).All P = (v.All P ∧ rest.All P) := rfl
theorem SList.All_nil {E : Ty} : (SList.nil (E := E)).All P = True := rfl
theorem SList.All_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).All P = (v.All P ∧ rest.All P) := rfl
theorem SVec.All_nil {E : Ty} : (SVec.nil (E := E)).All P = True := rfl
theorem SVec.All_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).All P = (v.All P ∧ rest.All P) := rfl
theorem SMap.All_nil {V : Ty} : (SMap.nil (K := K) (V := V)).All P = True := rfl
theorem SMap.All_cons {K : PrimTy} {V : Ty} (k : K.Denote) (v : SVal V) (rest : SMap K V) :
    (SMap.cons k v rest).All P = (v.All P ∧ rest.All P) := rfl

end All

attribute [irreducible] SVal.All SFields.All SList.All SVec.All SMap.All
attribute [eqns SVal.All_prim SVal.All_struct SVal.All_array SVal.All_fixed SVal.All_map] SVal.All
attribute [eqns SFields.All_nil SFields.All_cons] SFields.All
attribute [eqns SList.All_nil SList.All_cons] SList.All
attribute [eqns SVec.All_nil SVec.All_cons] SVec.All
attribute [eqns SMap.All_nil SMap.All_cons] SMap.All

section AllLemmas

variable {P : Hered}

theorem SVec.all_iff {E : Ty} : {n : Nat} → {e : SVec E n} → e.All P ↔ ∀ x ∈ e.toList, x.All P
  | _, .nil => by simp only [SVec.All, SVec.toList, List.not_mem_nil, false_implies, implies_true]
  | _, .cons v rest => by
    simp only [SVec.All, SVec.toList, List.mem_cons, forall_eq_or_imp]
    rw [SVec.all_iff]

theorem SList.all_iff {E : Ty} : {l : SList E} → l.All P ↔ ∀ x ∈ l.toList, x.All P
  | .nil => by simp only [SList.All, SList.toList, List.not_mem_nil, false_implies, implies_true]
  | .cons v rest => by
    simp only [SList.All, SList.toList, List.mem_cons, forall_eq_or_imp]
    rw [SList.all_iff]

theorem SMap.all_iff {K : PrimTy} {V : Ty} : {m : SMap K V} → m.All P ↔ ∀ e ∈ m.toList, e.2.All P
  | .nil => by simp only [SMap.All, SMap.toList, List.not_mem_nil, false_implies, implies_true]
  | .cons k v rest => by
    simp only [SMap.All, SMap.toList, List.mem_cons, forall_eq_or_imp]
    rw [SMap.all_iff]

theorem SVec.all_ofList {E : Ty} {l : List (SVal E)} :
    (SVec.ofList l).All P ↔ ∀ x ∈ l, x.All P := by
  rw [SVec.all_iff, SVec.toList_ofList]

theorem SList.all_ofList {E : Ty} {l : List (SVal E)} :
    (SList.ofList l).All P ↔ ∀ x ∈ l, x.All P := by
  rw [SList.all_iff, SList.toList_ofList]

theorem SMap.all_ofList {K : PrimTy} {V : Ty} {l : List (K.Denote × SVal V)} :
    (SMap.ofList l).All P ↔ ∀ e ∈ l, e.2.All P := by
  rw [SMap.all_iff, SMap.toList_ofList]

theorem SVec.all_replicate {E : Ty} {x : SVal E} (hx : x.All P) (n : Nat) :
    (SVec.replicate x n).All P := by
  rw [SVec.all_iff, SVec.toList_replicate]
  intro y hy
  rw [List.eq_of_mem_replicate hy]
  exact hx

theorem SFields.all_get {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → {x : SFields fs} →
    (h : lookupBy f fs = some T) → x.All P → (x.get h).All P
  | [], _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, hx => by
    simp only [SFields.All] at hx
    rw [SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
      exact hx.1
    · simp only [e, dite_false]
      exact SFields.all_get _ hx.2

theorem SFields.all_set {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → {x : SFields fs} →
    (h : lookupBy f fs = some T) → {y : SVal T} → x.All P → y.All P → (x.set h y).All P
  | [], _, .nil, h, _, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, y, hx, hy => by
    simp only [SFields.All] at hx
    rw [SFields.set_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true, SFields.All]
      exact ⟨hy, hx.2⟩
    · simp only [e, dite_false, SFields.All]
      exact ⟨hx.1, SFields.all_set _ hx.2 hy⟩

/-- **What a read finds satisfies what the value does.** -/
theorem SVal.findM_all : {T U : Ty} → {x : SVal T} → (p : Path T U) → {w : SVal U} →
    x.All P → x.findM p = some w → w.All P
  | _, _, x, .nil, w, hx, h => by
    have : x = w := by cases x <;> (simp only [SVal.findM, Option.some.injEq] at h; exact h)
    exact this ▸ hx
  | _, _, .struct fs, .field hf p, w, hx, h => by
    simp only [SVal.findM] at h
    simp only [SVal.All] at hx
    exact SVal.findM_all p (SFields.all_get hf hx) h
  | _, _, .array e sh hn, .at i p, w, hx, h => by
    simp only [SVal.All] at hx
    simp only [SVal.findM] at h
    split at h
    · rename_i y hy
      have hm := List.mem_of_getElem? hy
      rcases List.mem_append.mp hm with hm | hm
      · exact SVal.findM_all p (SVec.all_iff.mp hx.2.1 y hm) h
      · exact SVal.findM_all p (SList.all_iff.mp hx.2.2 y hm) h
    · exact nomatch h
  | _, _, .fixed e, .atF i p, w, hx, h => by
    simp only [SVal.All] at hx
    simp only [SVal.findM] at h
    split at h
    · rename_i y hy
      exact SVal.findM_all p (SVec.all_iff.mp hx.2 y (List.mem_of_getElem? hy)) h
    · exact nomatch h
  | _, _, .map m d, .key k p, w, hx, h => by
    simp only [SVal.All] at hx
    simp only [SVal.findM] at h
    split at h
    · rename_i y hy
      exact SVal.findM_all p (SMap.all_iff.mp hx.2.1 (k, y) (lookupBy_eq_some_mem hy)) h
    · exact SVal.findM_all p hx.2.2 h

theorem SVal.find_all {T U : Ty} {x : SVal T} (p : Path T U) {w : SVal U} (hx : x.All P)
    (h : x.find p = some w) : w.All P :=
  SVal.findM_all p hx (by rw [← SVal.find_eq_findM]; exact h)

/-! ### Defaults -/

theorem SFields.dfltBelow_all {k : Nat} (hih : ∀ T h, (SVal.dfltBelow k T h).All P) :
    (fs : List (Name × Ty)) → (h : fieldsRank fs < k) →
    (SFields.dfltBelow k (SVal.dfltBelow k) fs h).All P
  | [], _ => by simp only [SFields.dfltBelow, SFields.All]
  | (_, T) :: fs, h => by
    simp only [SFields.dfltBelow, SFields.All]
    exact ⟨hih T _, SFields.dfltBelow_all hih fs _⟩

mutual
theorem SVal.dfltAt_all (harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
    (hfix : ∀ E n, P.fix E n) (hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V)) {k : Nat}
    (hih : ∀ T h, (SVal.dfltBelow k T h).All P) :
    (T : Ty) → (h : tyRank T < k + 1) → (SVal.dfltAt k (SVal.dfltBelow k) T h).All P
  | .prim _, _ => by simp only [SVal.dfltAt, SVal.All]
  | .ref R, h => SVal.dfltRefAt_all harr hfix hmap hih R h

theorem SVal.dfltRefAt_all (harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
    (hfix : ∀ E n, P.fix E n) (hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V)) {k : Nat}
    (hih : ∀ T h, (SVal.dfltBelow k T h).All P) :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) →
    (SVal.dfltRefAt k (SVal.dfltBelow k) R h).All P
  | .struct s, h => by
    simp only [SVal.dfltRefAt, SVal.All]
    exact SFields.dfltBelow_all hih _ _
  | .array E, _ => by
    simp only [SVal.dfltRefAt, SVal.All]
    exact ⟨harr E, by simp only [SVec.All], by simp only [SList.All]⟩
  | .fixed E n, h => by
    simp only [SVal.dfltRefAt, SVal.All]
    exact ⟨hfix E n, SVec.all_replicate (SVal.dfltAt_all harr hfix hmap hih E _) n⟩
  | .mapping K V, h => by
    simp only [SVal.dfltRefAt, SVal.All]
    refine ⟨?_, by simp only [SMap.All], SVal.dfltAt_all harr hfix hmap hih V _⟩
    rw [SVal.dfltAt_eq (fun T h => SVal.dfltBelow_dflt k T h)]
    exact hmap K V
end

section Dflt

variable (harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
  (hfix : ∀ E n, P.fix E n)
  (hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V))

include harr hfix hmap

theorem SVal.dfltBelow_all : (k : Nat) → (T : Ty) → (h : tyRank T < k) →
    (SVal.dfltBelow k T h).All P
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h => SVal.dfltAt_all harr hfix hmap (SVal.dfltBelow_all k) T h

/-- **A default satisfies a predicate whose conditions the defaults' nodes
meet**: an empty array, any fixed size, an empty mapping of the default. -/
theorem SVal.dflt_all (T : Ty) : (SVal.dflt T).All P :=
  SVal.dfltBelow_all harr hfix hmap _ T _

theorem SFields.dflt_all : (fs : List (Name × Ty)) → (SFields.dflt fs).All P
  | [] => by simp only [SFields.dflt, SFields.All]
  | (_, T) :: fs => by
    simp only [SFields.dflt, SFields.All]
    exact ⟨SVal.dflt_all harr hfix hmap T, SFields.dflt_all fs⟩

end Dflt

end AllLemmas

/-! ## Live slots along a path -/

/-- A path from a word is empty. -/
theorem Path.eq_prim {p : PrimTy} {U : Ty} (q : Path (.prim p) U) : U = .prim p := by
  cases q; rfl

/-- Along `p` from `x`, every array of words is entered at a live slot: a
word is written past an array's end by no program (`Storage.checkIndex`). -/
def SVal.Live : {T U : Ty} → SVal T → Path T U → Prop
  | _, _, _, .nil => True
  | _, _, .struct fs, .field h p => (fs.get h).Live p
  | _, _, @SVal.array E n e sh _, .at i p => ∀ y,
      (e.toList ++ sh.toList)[i.1.toNat]? = some y → (E.isPrimitive = true → i.1.toNat < n) ∧ y.Live p
  | _, _, .fixed e, .atF i p => ∀ y, e.toList[i.1.toNat]? = some y → y.Live p
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some y => y.Live p
    | none => d.Live p

theorem Ty.isPrimitive_of_path {E U : Ty} (p : Path E U) (hE : E.isPrimitive = true) :
    U.isPrimitive = true := by
  cases E with
  | prim q => rw [Path.eq_prim p]; rfl
  | ref _ => exact absurd hE (by simp only [Ty.isPrimitive, Bool.false_eq_true, not_false_eq_true])

/-- A path to a reference enters no array of words. -/
theorem SVal.live_of_ref : {T U : Ty} → (x : SVal T) → (p : Path T U) → U.isPrimitive = false →
    x.Live p
  | _, _, x, .nil, _ => by cases x <;> simp only [SVal.Live]
  | _, _, .struct fs, .field _ p, hU => by
    simp only [SVal.Live]; exact SVal.live_of_ref _ p hU
  | _, _, .array e sh _, .at i p, hU => by
    simp only [SVal.Live]
    intro y _
    refine ⟨fun hE => ?_, SVal.live_of_ref y p hU⟩
    rw [Ty.isPrimitive_of_path p hE] at hU
    exact nomatch hU
  | _, _, .fixed e, .atF i p, hU => by
    simp only [SVal.Live]; exact fun y _ => SVal.live_of_ref y p hU
  | _, _, .map m d, .key k p, hU => by
    simp only [SVal.Live]
    split
    · exact SVal.live_of_ref _ p hU
    · exact SVal.live_of_ref d p hU

/-- Live along a path to a reference, then along what it finds. -/
theorem SVal.live_append : {T R U : Ty} → (x : SVal T) → (p : Path T R) → (q : Path R U) →
    R.isPrimitive = false → (∀ y, x.findM p = some y → y.Live q) → x.Live (p.append q)
  | _, _, _, x, .nil, q, _, h => by rw [Path.append_nil]; exact h x (SVal.findM_nil' x)
  | _, _, _, .struct fs, .field hf p, q, hR, h => by
    rw [Path.append_field]
    simp only [SVal.Live]
    exact SVal.live_append _ p q hR fun y hy => h y (by simp only [SVal.findM]; exact hy)
  | _, _, _, .array e sh _, .at i p, q, hR, h => by
    rw [Path.append_at]
    simp only [SVal.Live]
    intro y hy
    refine ⟨fun hE => ?_, SVal.live_append y p q hR fun z hz => h z ?_⟩
    · rw [Ty.isPrimitive_of_path p hE] at hR; exact nomatch hR
    · simp only [SVal.findM, hy]; exact hz
  | _, _, _, .fixed e, .atF i p, q, hR, h => by
    rw [Path.append_atF]
    simp only [SVal.Live]
    intro y hy
    exact SVal.live_append y p q hR fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)
  | _, _, _, .map m d, .key k p, q, hR, h => by
    rw [Path.append_key]
    simp only [SVal.Live]
    split
    · rename_i y hy
      exact SVal.live_append y p q hR fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)
    · rename_i hy
      exact SVal.live_append d p q hR fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)

/-! ## Saves -/

section Save

variable {P : Hered}
  (harr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (i : Nat) (x : SVal E),
    i < e.toList.length + sh.toList.length → (E.isPrimitive = true → i < n) → P.arr e sh →
    x.All P →
    P.arr (SVec.ofList (((e.toList ++ sh.toList).set i x).take n))
      (SList.ofList (((e.toList ++ sh.toList).set i x).drop n)))
  (hmap : ∀ {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) (x : SVal V), x.All P →
    P.map K m d → P.map K (SMap.ofList (setBy k x m.toList)) d)

include harr hmap

/-- **A save keeps a hereditary predicate** whose node conditions survive a
slot or an entry replaced, entering arrays of words at live slots. -/
theorem SVal.saveM_all : {T U : Ty} → {x : SVal T} → (p : Path T U) → {new : SVal U} →
    {x' : SVal T} → x.All P → new.All P → x.Live p → x.saveM p new = some x' →
    x'.All P
  | _, _, x, .nil, new, x', _, hn, _, h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; exact hn)
  | _, _, .struct fs, .field hf p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.All] at hx ⊢
    simp only [SVal.Live] at hl
    exact SFields.all_set hf hx (SVal.saveM_all p (SFields.all_get hf hx) hn hl hy)
  | _, _, .array e sh _, .at i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.Live] at hl
      obtain ⟨hlive, hl⟩ := hl y hy
      have hall : ∀ w ∈ e.toList ++ sh.toList, w.All P := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact SVec.all_iff.mp hx.2.1 w hw
        · exact SList.all_iff.mp hx.2.2 w hw
      have hzA := SVal.saveM_all p (hall y (List.mem_of_getElem? hy)) hn hl hz
      have hlen : i.1.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hy).1
      have hset : ∀ w ∈ (e.toList ++ sh.toList).set i.1.toNat z, w.All P := by
        intro w hw
        rcases List.mem_or_eq_of_mem_set hw with hw | hw
        · exact hall w hw
        · exact hw ▸ hzA
      refine ⟨harr e sh i.1.toNat z (by rwa [List.length_append] at hlen) hlive hx.1 hzA,
        SVec.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_take hw),
        SList.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_drop hw)⟩
    · exact nomatch h
  | _, _, .fixed e, .atF i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.Live] at hl
      have hzA := SVal.saveM_all p
        (SVec.all_iff.mp hx.2 y (List.mem_of_getElem? hy)) hn (hl y hy) hz
      refine ⟨hx.1, SVec.all_iff.mpr fun w hw => ?_⟩
      rw [SVec.toList_set] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | hw
      · exact SVec.all_iff.mp hx.2 w hw
      · exact hw ▸ hzA
    · exact nomatch h
  | _, _, .map m d, .key k p, new, x', hx, hn, hl, h => by
    simp only [SVal.All] at hx
    simp only [SVal.Live] at hl
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_all p
        (SMap.all_iff.mp hx.2.1 (k, y) (lookupBy_eq_some_mem hy)) hn (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨hmap m d k z hzA hx.1, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_all p hx.2.2 hn (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨hmap m d k z hzA hx.1, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he

end Save

/-! ## Deletes, copies -/

section Ops

variable {P : Hered}

/-- An array condition that survives the slots past the end dropped. -/
def Hered.StripOK (P : Hered) : Prop :=
  ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), P.arr e sh → e.All P →
    P.arr e.strip SList.nil

/-- An array condition that survives the elements cleared into the slots
past the end. -/
def Hered.DelOK (P : Hered) : Prop :=
  ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), P.arr e sh → e.All P →
    P.arr SVec.nil (SList.ofList (e.defaultOf.toList ++ sh.toList))

/-- An array condition that survives an array copied over another. -/
def Hered.OvOK (P : Hered) : Prop :=
  ∀ {E : Ty} {m n : Nat} (oel : SVec E m) (osh : SList E) (nel : SVec E n) (nsh : SList E),
    P.arr oel osh → P.arr nel nsh → oel.All P → osh.All P → nel.All P →
    P.arr (SVec.overlayOn (oel.toList ++ osh.toList) nel)
      (SList.ofList ((oel.toList.drop n).map SVal.defaultOf ++ osh.toList.drop (n - m)))

mutual
/-- A value as nothing wrote it keeps a predicate whose array condition
survives the slots past the end dropped. -/
theorem SVal.strip_all (hs : P.StripOK) : {T : Ty} → {v : SVal T} → v.All P → v.strip.All P
  | _, .prim _, _ => by simp only [SVal.strip, SVal.All]
  | _, .struct _, h => by
    simp only [SVal.strip, SVal.All] at h ⊢; exact SFields.strip_all hs h
  | _, .array e sh _, h => by
    simp only [SVal.strip, SVal.All] at h ⊢
    exact ⟨hs e sh h.1 h.2.1, SVec.strip_all hs h.2.1, by simp only [SList.All]⟩
  | _, .fixed _, h => by
    simp only [SVal.strip, SVal.All] at h ⊢; exact ⟨h.1, SVec.strip_all hs h.2⟩
  | _, .map _ _, h => by simp only [SVal.strip]; exact h

theorem SFields.strip_all (hs : P.StripOK) : {fs : List (Name × Ty)} → {x : SFields fs} →
    x.All P → x.strip.All P
  | _, .nil, _ => by simp only [SFields.strip, SFields.All]
  | _, .cons _ _, h => by
    simp only [SFields.strip, SFields.All] at h ⊢
    exact ⟨SVal.strip_all hs h.1, SFields.strip_all hs h.2⟩

theorem SVec.strip_all (hs : P.StripOK) : {E : Ty} → {n : Nat} → {e : SVec E n} → e.All P →
    e.strip.All P
  | _, _, .nil, _ => by simp only [SVec.strip, SVec.All]
  | _, _, .cons _ _, h => by
    simp only [SVec.strip, SVec.All] at h ⊢; exact ⟨SVal.strip_all hs h.1, SVec.strip_all hs h.2⟩
end

mutual
/-- `delete`'s value keeps a predicate whose array condition survives the
elements cleared into the slots past the end. -/
theorem SVal.defaultOf_all (hd : P.DelOK) : {T : Ty} → {v : SVal T} → v.All P →
    v.defaultOf.All P
  | _, .prim _, _ => by simp only [SVal.defaultOf, SVal.All]
  | _, .struct _, h => by
    simp only [SVal.defaultOf, SVal.All] at h ⊢; exact SFields.defaultOf_all hd h
  | _, .array e sh _, h => by
    simp only [SVal.defaultOf, SVal.All] at h ⊢
    refine ⟨hd e sh h.1 h.2.1, by simp only [SVec.All], SList.all_ofList.mpr fun w hw => ?_⟩
    rcases List.mem_append.mp hw with hw | hw
    · exact SVec.all_iff.mp (SVec.defaultOf_all hd h.2.1) w hw
    · exact SList.all_iff.mp h.2.2 w hw
  | _, .fixed _, h => by
    simp only [SVal.defaultOf, SVal.All] at h ⊢; exact ⟨h.1, SVec.defaultOf_all hd h.2⟩
  | _, .map _ _, h => by simp only [SVal.defaultOf]; exact h

theorem SFields.defaultOf_all (hd : P.DelOK) : {fs : List (Name × Ty)} → {x : SFields fs} →
    x.All P → x.defaultOf.All P
  | _, .nil, _ => by simp only [SFields.defaultOf, SFields.All]
  | _, .cons _ _, h => by
    simp only [SFields.defaultOf, SFields.All] at h ⊢
    exact ⟨SVal.defaultOf_all hd h.1, SFields.defaultOf_all hd h.2⟩

theorem SVec.defaultOf_all (hd : P.DelOK) : {E : Ty} → {n : Nat} → {e : SVec E n} → e.All P →
    e.defaultOf.All P
  | _, _, .nil, _ => by simp only [SVec.defaultOf, SVec.All]
  | _, _, .cons _ _, h => by
    simp only [SVec.defaultOf, SVec.All] at h ⊢
    exact ⟨SVal.defaultOf_all hd h.1, SVec.defaultOf_all hd h.2⟩
end

mutual
/-- **A copy over a value keeps a predicate** whose array condition
survives an array copied over another. -/
theorem SVal.overlay_all (hs : P.StripOK) (hd : P.DelOK) (hov : P.OvOK) :
    {T : Ty} → (o v : SVal T) → o.All P → v.All P → (o.overlay v).All P
  | _, _, .prim _, _, _ => by simp only [SVal.overlay, SVal.All]
  | _, .struct ofs, .struct nfs, ho, hv => by
    simp only [SVal.overlay, SVal.All] at ho hv ⊢
    exact SFields.overlay_all hs hd hov ofs nfs ho hv
  | _, .array oel osh _, .array nel nsh _, ho, hv => by
    simp only [SVal.overlay, SVal.All] at ho hv ⊢
    have hold : ∀ w ∈ oel.toList ++ osh.toList, w.All P := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact SVec.all_iff.mp ho.2.1 w hw
      · exact SList.all_iff.mp ho.2.2 w hw
    refine ⟨hov oel osh nel nsh ho.1 hv.1 ho.2.1 ho.2.2 hv.2.1,
      SVec.overlayOn_all hs hd hov _ hold nel hv.2.1, SList.all_ofList.mpr fun w hw => ?_⟩
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      exact SVal.defaultOf_all hd (SVec.all_iff.mp ho.2.1 u (List.mem_of_mem_drop hu))
    · exact SList.all_iff.mp ho.2.2 w (List.mem_of_mem_drop hw)
  | _, .fixed oel, .fixed nel, ho, hv => by
    simp only [SVal.overlay, SVal.All] at ho hv ⊢
    exact ⟨hv.1, SVec.overlayOn_all hs hd hov _ (SVec.all_iff.mp ho.2) nel hv.2⟩
  | _, .map _ _, .map _ _, ho, _ => by simp only [SVal.overlay]; exact ho

theorem SFields.overlay_all (hs : P.StripOK) (hd : P.DelOK) (hov : P.OvOK) :
    {fs : List (Name × Ty)} → (os ns : SFields fs) → os.All P → ns.All P →
    (os.overlay ns).All P
  | _, .nil, .nil, _, _ => by simp only [SFields.overlay, SFields.All]
  | _, .cons o os, .cons v rest, ho, hv => by
    simp only [SFields.overlay, SFields.All] at ho hv ⊢
    exact ⟨SVal.overlay_all hs hd hov o v ho.1 hv.1,
      SFields.overlay_all hs hd hov os rest ho.2 hv.2⟩

theorem SVec.overlayOn_all (hs : P.StripOK) (hd : P.DelOK) (hov : P.OvOK) :
    {E : Ty} → {n : Nat} → (L : List (SVal E)) → (∀ w ∈ L, w.All P) →
    (e : SVec E n) → e.All P → (SVec.overlayOn L e).All P
  | _, _, _, _, .nil, _ => by simp only [SVec.overlayOn, SVec.All]
  | _, _, [], _, .cons v rest, he => by
    simp only [SVec.overlayOn, SVec.All] at he ⊢
    exact ⟨SVal.strip_all hs he.1, SVec.strip_all hs he.2⟩
  | _, _, o :: L, hL, .cons v rest, he => by
    simp only [SVec.overlayOn, SVec.All] at he ⊢
    exact ⟨SVal.overlay_all hs hd hov o v (hL o List.mem_cons_self) he.1,
      SVec.overlayOn_all hs hd hov L (fun w hw => hL w (List.mem_cons_of_mem _ hw)) rest he.2⟩
end

end Ops

/-! ## Plain values: what memory copies back -/

/-- A value with no slots past an array's end and no mapping: what a copy
out of memory makes (`MVal.copyMToSt`). -/
def plainH : Hered where
  arr _ sh := sh = .nil
  fix _ _ := True
  map _ := fun _ _ => False

/-- No slot past an array's end, no mapping. -/
abbrev SVal.Plain {T : Ty} (v : SVal T) : Prop := v.All plainH

mutual
/-- Copying a mapping-free storage value, such as a row of arrays, drops
its source histories and yields a plain value. -/
theorem SVal.strip_plain : {T : Ty} → (v : SVal T) → T.mapFree = true → v.strip.Plain
  | _, .prim _, _ => by simp only [SVal.strip, SVal.All]
  | _, .struct fs, h => by
    simp only [SVal.strip, SVal.All]
    exact SFields.strip_plain fs (mapFree_structDef _ (by
      simpa only [Ty.mapFree, decide_eq_true_eq] using h))
  | _, .array e _ _, h => by
    simp only [SVal.strip, SVal.All, plainH, SList.All]
    exact ⟨trivial, SVec.strip_plain e h, trivial⟩
  | _, .fixed e, h => by
    simp only [SVal.strip, SVal.All, plainH]
    exact ⟨trivial, SVec.strip_plain e h⟩
  | _, .map _ _, h => by cases h

/-- The fields of a mapping-free struct remain plain when copied. -/
theorem SFields.strip_plain : {fs : List (Name × Ty)} → (vs : SFields fs) →
    (∀ nt ∈ fs, nt.2.mapFree = true) → vs.strip.All plainH
  | _, .nil, _ => by simp only [SFields.strip, SFields.All]
  | _, .cons v vs, h => by
    simp only [SFields.strip, SFields.All]
    exact ⟨SVal.strip_plain v (h _ List.mem_cons_self),
      SFields.strip_plain vs (fun nt hn => h nt (List.mem_cons_of_mem _ hn))⟩

/-- Copying the live elements of an array keeps only plain children. -/
theorem SVec.strip_plain : {E : Ty} → {n : Nat} → (vs : SVec E n) →
    E.mapFree = true → vs.strip.All plainH
  | _, _, .nil, _ => by simp only [SVec.strip, SVec.All]
  | _, _, .cons v vs, h => by
    simp only [SVec.strip, SVec.All]
    exact ⟨SVal.strip_plain v h, SVec.strip_plain vs h⟩
end

/-- Padding `[a,b]` with a default preserves every hereditary predicate
held by `a`, `b` and the default. -/
theorem SVec.padRight_all {E : Ty} {P : Hered} {d : SVal E} (hd : d.All P) :
    {n : Nat} → (vs : SVec E n) → (m : Nat) → vs.All P → (vs.padRight d m).All P
  | _, _, 0, _ => by rw [SVec.padRight, SVec.All_nil]; trivial
  | 0, .nil, m + 1, _ => by
    simp only [SVec.padRight, SVec.All]
    exact ⟨hd, SVec.padRight_all hd .nil m (by rw [SVec.All_nil]; trivial)⟩
  | _ + 1, .cons v vs, m + 1, h => by
    simp only [SVec.All] at h
    simp only [SVec.padRight, SVec.All]
    exact ⟨h.1, SVec.padRight_all hd vs m h.2⟩

/-- A map-free fixed-array snapshot converted to its destination shape is
plain, so the existing memory-copy preservation principle applies to it. -/
theorem FixedCopy.apply_plain {E : Ty} {n : Nat} {R : RefTy}
    (c : FixedCopy E n R) (v : SVal (.ref (.fixed E n))) (hm : E.mapFree = true) :
    (c.apply v).Plain := by
  cases v with
  | fixed vs =>
    cases c with
    | dynamic bound =>
      simp only [FixedCopy.apply, SVal.All, plainH, SList.All]
      exact ⟨trivial, SVec.strip_plain vs hm, trivial⟩
    | fixed m fits =>
      simp only [FixedCopy.apply, SVal.All, plainH]
      exact ⟨trivial, SVec.padRight_all (SVal.strip_plain (SVal.dflt E) hm) _ _ (SVec.strip_plain vs hm)⟩

theorem SVec.ofLen_all {P : Hered} {α : Type} {E : Ty} (f : α → SVal E) :
    (n : Nat) → (l : List α) → (h : l.length = n) → (∀ a ∈ l, (f a).All P) →
    (SVec.ofLen f n l h).All P
  | 0, [], _, _ => by simp only [SVec.ofLen, SVec.All]
  | n + 1, a :: l, h, hl => by
    simp only [SVec.ofLen, SVec.All]
    exact ⟨hl a List.mem_cons_self, SVec.ofLen_all f n l _ fun b hb => hl b (List.mem_cons_of_mem _ hb)⟩
  | 0, _ :: _, h, _ => absurd h (by simp only [List.length_cons, Nat.add_one_ne_zero,
      not_false_eq_true])
  | _ + 1, [], h, _ => absurd h (by simp only [List.length_nil, Nat.zero_ne_add_one,
      not_false_eq_true])

section Copy

variable {H : HTy} (hp : Heap H)

theorem MFields.copyBelow_plain {k : Nat} {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    (hih : ∀ T h v, (ih T h v).Plain) : (fs : List (Name × Ty)) → (h : fieldsRank fs < k) →
    (x : MFields H fs) → (MFields.copyBelow k ih fs h x).All plainH
  | [], _, _ => by simp only [MFields.copyBelow, SFields.All]
  | (_, T) :: fs, h, x => by
    simp only [MFields.copyBelow, SFields.All]
    exact ⟨hih T _ _, MFields.copyBelow_plain hih fs _ x.2⟩

mutual
theorem MVal.copyAt_plain {k : Nat} {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    (hih : ∀ T h v, (ih T h v).Plain) :
    (T : Ty) → (h : tyRank T < k + 1) → (v : MVal H T) → (MVal.copyAt hp k ih T h v).Plain
  | .prim _, _, _ => by simp only [MVal.copyAt, SVal.All]
  | .ref R, h, r => MVal.copyRefAt_plain hih R h r

theorem MVal.copyRefAt_plain {k : Nat} {ih : (T : Ty) → tyRank T < k → MVal H T → SVal T}
    (hih : ∀ T h v, (ih T h v).Plain) :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) → (r : HRef H R) →
    (MVal.copyRefAt hp k ih R h r).Plain
  | .struct s, h, r => by
    simp only [MVal.copyRefAt, SVal.All]
    exact MFields.copyBelow_plain hih _ _ _
  | .array E, h, r => by
    simp only [MVal.copyRefAt, SVal.All]
    refine ⟨rfl, SVec.all_ofList.mpr fun w hw => ?_, by simp only [SList.All]⟩
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
    exact MVal.copyAt_plain hih E _ u
  | .fixed E n, h, r => by
    simp only [MVal.copyRefAt, SVal.All]
    exact ⟨trivial, SVec.ofLen_all _ n _ _ fun u _ => MVal.copyAt_plain hih E _ u⟩
  | .mapping _ _, _, r => (hp.get r : Empty).elim
end

theorem MVal.copyBelow_plain : (k : Nat) → (T : Ty) → (h : tyRank T < k) → (v : MVal H T) →
    (MVal.copyBelow hp k T h v).Plain
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h, v => MVal.copyAt_plain hp (MVal.copyBelow_plain k) T h v

/-- **A copy out of memory is plain**: no slot past an array's end, no
mapping (memory holds none). -/
theorem MVal.copyMToSt_plain {T : Ty} (v : MVal H T) : (MVal.copyMToSt hp v).Plain :=
  MVal.copyBelow_plain hp _ T _ v

end Copy

/-! ## Types whose defaults are well-formed all the way down -/

/-- `T`'s default is well-formed all the way down: a struct `defaultOkS`
admits, and arrays and mappings of such. -/
def Ty.okDeep : Ty → Bool
  | .prim _ => true
  | .ref (.struct s) => s ∈ defaultOkStructs
  | .ref (.array E) => E.okDeep
  | .ref (.fixed E _) => E.okDeep
  | .ref (.mapping _ V) => V.okDeep

theorem struct_okDeep {s : Name} (h : s ∈ defaultOkStructs) :
    ∀ nt ∈ structDef s, nt.2.okDeep = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [structDef, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Ty.okDeep,
        String.reduceEq, imp_self, forall_eq_or_imp, defaultOkStructs, or_self, decide_true,
        and_self, or_true]

theorem okDeep_defaultOkS : ∀ {T : Ty}, T.okDeep = true → T.defaultOkS = true
  | .prim _, _ => rfl
  | .ref (.struct _), h => by simpa only [Ty.defaultOkS, decide_eq_true_eq, Ty.okDeep] using h
  | .ref (.array _), _ => rfl
  | .ref (.fixed E _), h => by
    simp only [Ty.okDeep] at h; simpa only [Ty.defaultOkS] using okDeep_defaultOkS (T := E) h
  | .ref (.mapping _ V), h => by
    simp only [Ty.okDeep] at h; simpa only [Ty.defaultOkS] using okDeep_defaultOkS (T := V) h

/-- What a path reaches from an `okDeep` type is `okDeep`. -/
theorem Path.okDeep : {T U : Ty} → Path T U → T.okDeep = true → U.okDeep = true
  | _, _, .nil, h => h
  | _, _, .field hf p, h =>
    Path.okDeep p (struct_okDeep (by simpa only [Ty.okDeep, decide_eq_true_eq] using h) _
      (lookupBy_eq_some_mem hf))
  | _, _, .at _ p, h => Path.okDeep p (by simpa only [Ty.okDeep] using h)
  | _, _, .atF _ p, h => Path.okDeep p (by simpa only [Ty.okDeep] using h)
  | _, _, .key _ p, h => Path.okDeep p (by simpa only [Ty.okDeep] using h)

/-- What it takes for `Q`'s node conditions to imply `P`'s, at the types
`G` holds of, `G` closed under members, elements and values. -/
structure Hered.Mono (P Q : Hered) (G : Ty → Prop) : Prop where
  gs : ∀ s, G (.ref (.struct s)) → ∀ nt ∈ structDef s, G nt.2
  ga : ∀ E, G (.ref (.array E)) → G E
  gf : ∀ E n, G (.ref (.fixed E n)) → G E
  gm : ∀ K V, G (.ref (.mapping K V)) → G V
  arr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), n < 2 ^ 256 → G (.ref (.array E)) →
    Q.arr e sh → P.arr e sh
  fix : ∀ E n, G (.ref (.fixed E n)) → Q.fix E n → P.fix E n
  map : ∀ {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V), G (.ref (.mapping K V)) → Q.map K m d →
    P.map K m d

section Mono

variable {P Q : Hered} {G : Ty → Prop}

mutual
/-- A predicate whose node conditions imply another's, at the types `G`
holds of. -/
theorem SVal.all_mono (hm : P.Mono Q G) : {T : Ty} → (v : SVal T) → G T → v.All Q → v.All P
  | _, .prim _, _, _ => by simp only [SVal.All]
  | _, .struct fs, hT, h => by
    simp only [SVal.All] at h ⊢
    exact SFields.all_mono hm fs (hm.gs _ hT) h
  | _, .array e sh hn, hT, h => by
    simp only [SVal.All] at h ⊢
    exact ⟨hm.arr e sh hn hT h.1, SVec.all_mono hm e (hm.ga _ hT) h.2.1,
      SList.all_mono hm sh (hm.ga _ hT) h.2.2⟩
  | _, .fixed e, hT, h => by
    simp only [SVal.All] at h ⊢
    exact ⟨hm.fix _ _ hT h.1, SVec.all_mono hm e (hm.gf _ _ hT) h.2⟩
  | _, .map m d, hT, h => by
    simp only [SVal.All] at h ⊢
    exact ⟨hm.map m d hT h.1, SMap.all_mono hm m (hm.gm _ _ hT) h.2.1,
      SVal.all_mono hm d (hm.gm _ _ hT) h.2.2⟩

theorem SFields.all_mono (hm : P.Mono Q G) : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ nt ∈ fs, G nt.2) → x.All Q → x.All P
  | _, .nil, _, _ => by simp only [SFields.All]
  | _, .cons v rest, hfs, h => by
    simp only [SFields.All] at h ⊢
    exact ⟨SVal.all_mono hm v (hfs _ List.mem_cons_self) h.1,
      SFields.all_mono hm rest (fun nt hm' => hfs nt (List.mem_cons_of_mem _ hm')) h.2⟩

theorem SList.all_mono (hm : P.Mono Q G) : {E : Ty} → (l : SList E) → G E → l.All Q → l.All P
  | _, .nil, _, _ => by simp only [SList.All]
  | _, .cons v rest, hE, h => by
    simp only [SList.All] at h ⊢
    exact ⟨SVal.all_mono hm v hE h.1, SList.all_mono hm rest hE h.2⟩

theorem SVec.all_mono (hm : P.Mono Q G) : {E : Ty} → {n : Nat} → (l : SVec E n) → G E →
    l.All Q → l.All P
  | _, _, .nil, _, _ => by simp only [SVec.All]
  | _, _, .cons v rest, hE, h => by
    simp only [SVec.All] at h ⊢
    exact ⟨SVal.all_mono hm v hE h.1, SVec.all_mono hm rest hE h.2⟩

theorem SMap.all_mono (hm : P.Mono Q G) : {K : PrimTy} → {V : Ty} → (m : SMap K V) → G V → m.All Q → m.All P
  | _, _, .nil, _, _ => by simp only [SMap.All]
  | _, _, .cons _ v rest, hV, h => by
    simp only [SMap.All] at h ⊢
    exact ⟨SVal.all_mono hm v hV h.1, SMap.all_mono hm rest hV h.2⟩
end

end Mono

/-- A predicate whose node conditions imply another's, everywhere. -/
theorem SVal.all_mono' {P Q : Hered}
    (harr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), n < 2 ^ 256 → Q.arr e sh →
      P.arr e sh)
    (hfix : ∀ E n, Q.fix E n → P.fix E n)
    (hmap : ∀ {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V), Q.map K m d → P.map K m d)
    {T : Ty} (v : SVal T) (h : v.All Q) : v.All P :=
  SVal.all_mono (G := fun _ => True) ⟨fun _ _ _ _ => trivial, fun _ _ => trivial,
    fun _ _ _ => trivial, fun _ _ _ => trivial, fun e sh hn _ => harr e sh hn,
    fun E n _ => hfix E n, fun m d _ => hmap m d⟩ v trivial h

/-- The same at `okDeep` types. -/
theorem SVal.all_mono_deep {P Q : Hered}
    (harr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), n < 2 ^ 256 → E.okDeep = true →
      Q.arr e sh → P.arr e sh)
    (hfix : ∀ E n, E.okDeep = true → Q.fix E n → P.fix E n)
    (hmap : ∀ {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V), V.okDeep = true → Q.map K m d →
      P.map K m d)
    {T : Ty} (v : SVal T) (hT : T.okDeep = true) (h : v.All Q) : v.All P :=
  SVal.all_mono (G := fun T => T.okDeep = true)
    ⟨fun _ h => struct_okDeep (by simpa only [Ty.okDeep, decide_eq_true_eq] using h),
      fun _ h => by simpa only [Ty.okDeep] using h, fun _ _ h => by simpa only [Ty.okDeep] using h,
      fun _ _ h => by simpa only [Ty.okDeep] using h,
      fun e sh hn h => harr e sh hn (by simpa only [Ty.okDeep] using h),
      fun E n h => hfix E n (by simpa only [Ty.okDeep] using h),
      fun m d h => hmap m d (by simpa only [Ty.okDeep] using h)⟩ v hT h

/-! ## Storage -/

namespace Storage

variable {C : Contract} {P : Hered}

/-- Every root satisfies `P`. -/
abbrev All (P : Hered) (st : Storage C) : Prop := SFields.All P st

theorem find_all {st : Storage C} {U : Ty} {r : SRef C U} {w : SVal U} (hs : st.All P)
    (h : st.find r = some w) : w.All P :=
  SVal.find_all r.path (SFields.all_get r.hroot hs) h

theorem root_all {st : Storage C} {U : Ty} (r : SRef C U) (hs : st.All P) :
    (st.get r.hroot).All P :=
  SFields.all_get r.hroot hs

/-- The value a save at `r` writes into its root. -/
theorem save_eq_some {st st' : Storage C} {U : Ty} {r : SRef C U} {new : SVal U}
    (h : st.save r new = some st') :
    ∃ v', (st.get r.hroot).saveM r.path new = some v' ∧ st' = st.set r.hroot v' := by
  simp only [Storage.save, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨v', hv, rfl⟩ := h
  exact ⟨v', by rw [← SVal.save_eq_saveM]; exact hv, rfl⟩

end Storage

/-! ## Saves read back

A save is idempotent (`SVal.saveM_idem`) and the last of two saves at one
path wins (`SVal.saveM_saveM`); with `SVal.findM_saveM` and the decomposition
of a save below a path (`SVal.saveM_append`, `Theory/Typed/Obs.lean`) they
are the algebra `Typing/Constructibility.lean`'s builder is tracked in. -/

/-- Two dynamic arrays with the same live elements and slots are the same. -/
theorem SVal.array_ext {E : Ty} {n m : Nat} (e : SVec E n) (e' : SVec E m) (sh sh' : SList E)
    (h : n < 2 ^ 256) (h' : m < 2 ^ 256) (he : e.toList = e'.toList) (hs : sh.toList = sh'.toList) :
    SVal.array e sh h = SVal.array e' sh' h' := by
  have hnm : n = m := by rw [← SVec.length_toList e, he, SVec.length_toList]
  subst hnm
  rw [SVec.eq_of_toList_eq e e' he, ← SList.ofList_toList sh, hs, SList.ofList_toList]

theorem SFields.set_get_self {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → x.set h (x.get h) = x
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h => by
    rw [SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true, SFields.set_cons]
    · simp only [e, dite_false, SFields.set_cons, SFields.set_get_self rest]

theorem SFields.set_set {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (a b : SVal T) → (x.set h a).set h b = x.set h b
  | [], _, .nil, h, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, a, b => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [SFields.set_cons, e, dite_true]
    · simp only [SFields.set_cons, e, dite_false, SFields.set_set rest]

/-- **A save is idempotent**: saving again what a save left changes nothing
(the key a save through a mapping's default added is there now). -/
theorem SVal.saveM_idem : {T U : Ty} → (x : SVal T) → (p : Path T U) → (v : SVal U) →
    {x' : SVal T} → x.saveM p v = some x' → x'.saveM p v = some x'
  | _, _, x, .nil, v, x', h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; cases v <;> rfl)
  | _, _, .struct fs, .field hf p, v, x', h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.saveM, SFields.get_set_same, SVal.saveM_idem _ p v hy, Option.bind_eq_bind,
      Option.bind_some, SFields.set_set]
  | _, _, @SVal.array _ n e sh hn, .at i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hl : i.1.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hy).1
      have hslots : (SVec.ofList (((e.toList ++ sh.toList).set i.1.toNat z).take n)).toList ++
          (SList.ofList (((e.toList ++ sh.toList).set i.1.toNat z).drop n)).toList =
          (e.toList ++ sh.toList).set i.1.toNat z := by
        rw [SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
      simp only [SVal.saveM, hslots, List.getElem?_set_self hl,
        SVal.saveM_idem y p v hz, Option.bind_eq_bind, Option.bind_some, List.set_set]
      congr 1
      apply SVal.array_ext <;> simp only [SVec.toList_ofList, SList.toList_ofList,
        List.length_take, List.length_set, List.length_append, SVec.length_toList,
        Nat.min_def, Nat.le_add_right, ↓reduceIte, List.take_append_drop, List.set_set]
    · simp only [reduceCtorEq] at h
  | _, _, .fixed e, .atF i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hl : i.1.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hy).1
      simp only [SVal.saveM, SVec.toList_set, List.getElem?_set_self hl,
        SVal.saveM_idem y p v hz, Option.bind_eq_bind, Option.bind_some]
      congr 2
      apply SVec.eq_of_toList_eq
      simp only [SVec.toList_set, List.set_set]
    · simp only [reduceCtorEq] at h
  | _, _, .map m d, .key k p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.saveM, SMap.toList_ofList, lookupBy_setBy_self, SVal.saveM_idem y p v hz,
        Option.bind_eq_bind, Option.bind_some, setBy_setBy_self]
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.saveM, SMap.toList_ofList, lookupBy_setBy_self, SVal.saveM_idem d p v hz,
        Option.bind_eq_bind, Option.bind_some, setBy_setBy_self]

theorem SVal.saveM_nil {T : Ty} (y z : SVal T) : y.saveM .nil z = some z := by cases y <;> rfl

/-- **The last of two saves at one path wins.** -/
theorem SVal.saveM_saveM : {T U : Ty} → (x : SVal T) → (p : Path T U) → (a b : SVal U) →
    {x₁ x₂ : SVal T} → x.saveM p a = some x₁ → x₁.saveM p b = some x₂ → x.saveM p b = some x₂
  | _, _, x, .nil, a, b, x₁, x₂, h₁, h₂ => by
    rw [SVal.saveM_nil] at h₁ ⊢
    cases h₁
    rw [SVal.saveM_nil] at h₂
    exact h₂
  | _, _, .struct fs, .field hf p, a, b, x₁, x₂, h₁, h₂ => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
    obtain ⟨y, hy, rfl⟩ := h₁
    simp only [SVal.saveM, SFields.get_set_same, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h₂
    obtain ⟨z, hz, rfl⟩ := h₂
    simp only [SVal.saveM, SVal.saveM_saveM _ p a b hy hz, Option.bind_eq_bind, Option.bind_some,
      SFields.set_set]
  | _, _, @SVal.array _ n e sh hn, .at i p, a, b, x₁, x₂, h₁, h₂ => by
    simp only [SVal.saveM] at h₁
    split at h₁
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
      obtain ⟨z, hz, rfl⟩ := h₁
      have hl : i.1.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hy).1
      simp only [SVal.saveM, SVec.toList_ofList, SList.toList_ofList,
        List.take_append_drop, List.getElem?_set_self hl, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨w, hw, rfl⟩ := h₂
      simp only [SVal.saveM, hy, SVal.saveM_saveM y p a b hz hw,
        Option.bind_eq_bind, Option.bind_some]
      congr 1
      apply SVal.array_ext <;> simp only [SVec.toList_ofList, SList.toList_ofList,
        List.length_take, List.length_set, List.length_append, SVec.length_toList,
        Nat.min_def, Nat.le_add_right, ↓reduceIte, List.take_append_drop, List.set_set]
    · simp only [reduceCtorEq] at h₁
  | _, _, .fixed e, .atF i p, a, b, x₁, x₂, h₁, h₂ => by
    simp only [SVal.saveM] at h₁
    split at h₁
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
      obtain ⟨z, hz, rfl⟩ := h₁
      have hl : i.1.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hy).1
      simp only [SVal.saveM, SVec.toList_set, List.getElem?_set_self hl,
        Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨w, hw, rfl⟩ := h₂
      simp only [SVal.saveM, hy, SVal.saveM_saveM y p a b hz hw,
        Option.bind_eq_bind, Option.bind_some]
      congr 2
      apply SVec.eq_of_toList_eq
      simp only [SVec.toList_set, List.set_set]
    · simp only [reduceCtorEq] at h₁
  | _, _, .map m d, .key k p, a, b, x₁, x₂, h₁, h₂ => by
    simp only [SVal.saveM] at h₁
    split at h₁
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
      obtain ⟨z, hz, rfl⟩ := h₁
      simp only [SVal.saveM, SMap.toList_ofList, lookupBy_setBy_self, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨w, hw, rfl⟩ := h₂
      simp only [SVal.saveM, hy, SVal.saveM_saveM y p a b hz hw, Option.bind_eq_bind,
        Option.bind_some, setBy_setBy_self]
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
      obtain ⟨z, hz, rfl⟩ := h₁
      simp only [SVal.saveM, SMap.toList_ofList, lookupBy_setBy_self, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨w, hw, rfl⟩ := h₂
      simp only [SVal.saveM, hy, SVal.saveM_saveM d p a b hz hw, Option.bind_eq_bind,
        Option.bind_some, setBy_setBy_self]

/-! ## Defaults, read and cleared -/

theorem SFields.dflt_get {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (h : lookupBy f fs = some T) → (SFields.dflt fs).get h = SVal.dflt T
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, h => by
    rw [SFields.dflt, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.dflt_get _

/-- Members with distinct names are equal when every member is. -/
theorem SFields.ext_get : {fs : List (Name × Ty)} → nodupKeysB fs = true → (x y : SFields fs) →
    (∀ f T (h : lookupBy f fs = some T), x.get h = y.get h) → x = y
  | [], _, .nil, .nil, _ => rfl
  | (f, T) :: fs, hnd, .cons v rest, .cons w rest', h => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd
    have h0 : lookupBy f ((f, T) :: fs) = some T := by simp only [lookupBy, ↓reduceIte]
    have hv : v = w := by
      have := h f T h0
      simp only [SFields.get_cons, dite_true] at this
      exact this
    subst hv
    have hr : rest = rest' := SFields.ext_get hnd.2 rest rest' fun g U hg => by
      have hne : g ≠ f := fun he => by rw [he, hnd.1] at hg; exact nomatch hg
      have h1 : lookupBy g ((f, T) :: fs) = some U := by
        simp only [lookupBy, hne, ↓reduceIte]; exact hg
      have := h g U h1
      simp only [SFields.get_cons, hne, dite_false] at this
      exact this
    rw [hr]

theorem SVec.defaultOf_replicate {E : Ty} {x : SVal E} (hx : x.defaultOf = x) (n : Nat) :
    (SVec.replicate x n).defaultOf = SVec.replicate x n := by
  apply SVec.eq_of_toList_eq
  rw [SVec.toList_defaultOf, SVec.toList_replicate, List.map_replicate, hx]

theorem SFields.dfltBelow_defaultOf {k : Nat} (hih : ∀ T h, (SVal.dfltBelow k T h).defaultOf =
    SVal.dfltBelow k T h) : (fs : List (Name × Ty)) → (h : fieldsRank fs < k) →
    (SFields.dfltBelow k (SVal.dfltBelow k) fs h).defaultOf =
      SFields.dfltBelow k (SVal.dfltBelow k) fs h
  | [], _ => by simp only [SFields.dfltBelow, SFields.defaultOf]
  | (_, T) :: fs, h => by
    simp only [SFields.dfltBelow, SFields.defaultOf, hih, SFields.dfltBelow_defaultOf hih fs]

mutual
theorem SVal.dfltAt_defaultOf {k : Nat} (hih : ∀ T h, (SVal.dfltBelow k T h).defaultOf =
    SVal.dfltBelow k T h) : (T : Ty) → (h : tyRank T < k + 1) →
    (SVal.dfltAt k (SVal.dfltBelow k) T h).defaultOf = SVal.dfltAt k (SVal.dfltBelow k) T h
  | .prim _, _ => by simp only [SVal.dfltAt, SVal.defaultOf]
  | .ref R, h => SVal.dfltRefAt_defaultOf hih R h

theorem SVal.dfltRefAt_defaultOf {k : Nat} (hih : ∀ T h, (SVal.dfltBelow k T h).defaultOf =
    SVal.dfltBelow k T h) : (R : RefTy) → (h : tyRank (.ref R) < k + 1) →
    (SVal.dfltRefAt k (SVal.dfltBelow k) R h).defaultOf = SVal.dfltRefAt k (SVal.dfltBelow k) R h
  | .struct s, h => by
    simp only [SVal.dfltRefAt, SVal.defaultOf, SFields.dfltBelow_defaultOf hih]
  | .array E, _ => by
    simp only [SVal.dfltRefAt, SVal.defaultOf, SVec.toList_defaultOf, SVec.toList_nil,
      SList.toList_nil, List.map_nil, List.append_nil]
    rfl
  | .fixed E n, h => by
    simp only [SVal.dfltRefAt, SVal.defaultOf]
    rw [SVec.defaultOf_replicate (SVal.dfltAt_defaultOf hih E _)]
  | .mapping K V, h => by simp only [SVal.dfltRefAt, SVal.defaultOf]
end

theorem SVal.dfltBelow_defaultOf : (k : Nat) → (T : Ty) → (h : tyRank T < k) →
    (SVal.dfltBelow k T h).defaultOf = SVal.dfltBelow k T h
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h => SVal.dfltAt_defaultOf (SVal.dfltBelow_defaultOf k) T h

/-- `delete` on a default changes nothing. -/
theorem SVal.defaultOf_dflt (T : Ty) : (SVal.dflt T).defaultOf = SVal.dflt T :=
  SVal.dfltBelow_defaultOf _ T _

end Solidity
