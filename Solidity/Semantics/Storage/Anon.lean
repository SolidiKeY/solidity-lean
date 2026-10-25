import Solidity.Semantics.Storage.Ops

/-!
# Anonymised roots

KeY's `anon(heap, locset, anonHeap)` on the typed storage: `Storage.anon L
old new` is `old` with every root `L` names taken from `new`.  `L` is a
modifies set at the granularity of the roots: what a loop body may write
(`Prog.storeAt`, `Calculus/Blocks.lean`), what its invariant rule
anonymises (`Op2.anon`, `Fml.anonHavoc`), and what the frame theorem
leaves out (`Stmt.run_keeps`, `Semantics/RunFrame.lean`): a run that writes
only the roots of `L` ends in `anon L σ τ = τ`, every other root as it was.

A root is named as the syntax names it, the first member of its name
(`lookupBy`, as `SFields.get` and `set` read it), so the laws hold for any
member list, a repeated name included; none of them asks for distinct
names.  The definitions are folds of `set` and `get`, which the kernel
reduces (Gate G0, condition 2): no `match` on `SFields`.
-/

namespace Solidity

open Semantics (lookupBy)

namespace SFields

variable {fs : List (Name × Ty)}

/-! ## Laws of `set` -/

theorem set_set {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (a b : SVal T) → (x.set h a).set h b = x.set h b
  | [], _, .nil, h, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, a, b => by
    rw [set_cons, set_cons]
    by_cases e : f = f'
    · have hT := lookupBy_cons_pos e h
      subst hT
      simp only [e, ↓reduceDIte, set_cons]
    · simp only [e, ↓reduceDIte, set_cons, set_set rest _ a b]

theorem set_set_comm {f g : Name} : {fs : List (Name × Ty)} → {T U : Ty} → (x : SFields fs) →
    (hf : lookupBy f fs = some T) → (hg : lookupBy g fs = some U) → f ≠ g → (a : SVal T) →
    (b : SVal U) → (x.set hf a).set hg b = (x.set hg b).set hf a
  | [], _, _, .nil, h, _, _, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, U, .cons v rest, hf, hg, hfg, a, b => by
    by_cases e : f = f'
    · have hT := lookupBy_cons_pos e hf
      subst hT
      have eg : ¬ g = f' := fun h' => hfg (e.trans h'.symm)
      simp only [set_cons, e, eg, ↓reduceDIte]
    · by_cases eg : g = f'
      · have hU := lookupBy_cons_pos eg hg
        subst hU
        simp only [set_cons, e, eg, ↓reduceDIte]
      · simp only [set_cons, e, eg, ↓reduceDIte, set_set_comm rest _ _ hfg a b]

theorem set_get_self {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → x.set h (x.get h) = x
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h => by
    by_cases e : f = f'
    · have hT := lookupBy_cons_pos e h
      subst hT
      simp only [set_cons, get_cons, e, ↓reduceDIte]
    · simp only [set_cons, get_cons, e, ↓reduceDIte, set_get_self rest]

/-! ## One root copied -/

/-- `x` with its member `r` taken from `y`, when the members have one. -/
def copyFrom (r : Name) (y x : SFields fs) : SFields fs :=
  match h : lookupBy r fs with
  | some _ => x.set h (y.get h)
  | none => x

theorem copyFrom_of_lookup {r : Name} {T : Ty} (h : lookupBy r fs = some T) (y x : SFields fs) :
    copyFrom r y x = x.set h (y.get h) := by
  unfold copyFrom
  split
  · rename_i T' h'
    have hT : T' = T := Option.some.inj (h'.symm.trans h)
    subst hT
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem copyFrom_of_none {r : Name} (h : lookupBy r fs = none) (y x : SFields fs) :
    copyFrom r y x = x := by
  unfold copyFrom
  split
  · rename_i T' h'
    rw [h] at h'
    cases h'
  · rfl

theorem copyFrom_self (r : Name) (x : SFields fs) : copyFrom r x x = x := by
  cases h : lookupBy r fs with
  | none => exact copyFrom_of_none h x x
  | some T => rw [copyFrom_of_lookup h, set_get_self]

theorem copyFrom_copyFrom_same (r : Name) (b c z : SFields fs) :
    copyFrom r c (copyFrom r b z) = copyFrom r c z := by
  cases h : lookupBy r fs with
  | none => rw [copyFrom_of_none h, copyFrom_of_none h, copyFrom_of_none h]
  | some T => rw [copyFrom_of_lookup h, copyFrom_of_lookup h, copyFrom_of_lookup h, set_set]

theorem copyFrom_comm {r r' : Name} (hr : r ≠ r') (b c z : SFields fs) :
    copyFrom r' c (copyFrom r b z) = copyFrom r b (copyFrom r' c z) := by
  cases h : lookupBy r fs with
  | none => rw [copyFrom_of_none h, copyFrom_of_none h]
  | some T =>
    cases h' : lookupBy r' fs with
    | none => rw [copyFrom_of_none h', copyFrom_of_none h']
    | some U =>
      rw [copyFrom_of_lookup h, copyFrom_of_lookup h', copyFrom_of_lookup h,
        copyFrom_of_lookup h', set_set_comm _ h h' hr]

/-- Two roots copied from one source commute, the same root or not. -/
theorem copyFrom_comm_src (r r' : Name) (b z : SFields fs) :
    copyFrom r' b (copyFrom r b z) = copyFrom r b (copyFrom r' b z) := by
  by_cases hr : r = r'
  · subst hr; rfl
  · exact copyFrom_comm hr b b z

theorem get_copyFrom {r f : Name} {T : Ty} (y x : SFields fs) (h : lookupBy f fs = some T) :
    (copyFrom r y x).get h = if f = r then y.get h else x.get h := by
  cases hr : lookupBy r fs with
  | none =>
    rw [copyFrom_of_none hr]
    by_cases e : f = r
    · subst e; rw [h] at hr; cases hr
    · simp only [e, ↓reduceIte]
  | some U =>
    rw [copyFrom_of_lookup hr]
    by_cases e : f = r
    · subst e
      have hU : U = T := Option.some.inj (hr.symm.trans h)
      subst hU
      simp only [↓reduceIte, get_set_same]
    · simp only [e, ↓reduceIte]
      exact get_set_ne x hr h (Ne.symm e) _

/-! ## The roots of a modifies set copied -/

/-- `x` with every member `L` names taken from `y` (KeY's `anon(x, L, y)`). -/
def anon (L : List Name) (x y : SFields fs) : SFields fs :=
  L.foldr (fun r acc => copyFrom r y acc) x

theorem anon_nil (x y : SFields fs) : anon [] x y = x := rfl

theorem anon_cons (r : Name) (L : List Name) (x y : SFields fs) :
    anon (r :: L) x y = copyFrom r y (anon L x y) := rfl

theorem anon_append (L M : List Name) (x y : SFields fs) :
    anon (L ++ M) x y = anon L (anon M x y) y := by
  simp only [anon, List.foldr_append]

/-- **A root read through `anon`**: `y`'s where `L` names it, `x`'s elsewhere
(KeY's `selectOfAnon`). -/
theorem get_anon {f : Name} {T : Ty} (L : List Name) (x y : SFields fs)
    (h : lookupBy f fs = some T) : (anon L x y).get h = if f ∈ L then y.get h else x.get h := by
  induction L with
  | nil => simp only [anon_nil, List.not_mem_nil, ↓reduceIte]
  | cons r L ih =>
    rw [anon_cons, get_copyFrom, ih]
    by_cases e : f = r
    · simp only [e, ↓reduceIte, List.mem_cons_self]
    · simp only [e, ↓reduceIte, List.mem_cons, false_or]

theorem anon_self (L : List Name) (x : SFields fs) : anon L x x = x := by
  induction L with
  | nil => rfl
  | cons r L ih => rw [anon_cons, ih, copyFrom_self]

theorem copyFrom_anon_src (r : Name) (M : List Name) (b z : SFields fs) :
    copyFrom r b (anon M z b) = anon M (copyFrom r b z) b := by
  induction M with
  | nil => rfl
  | cons r' M ih => rw [anon_cons, anon_cons, ← ih, copyFrom_comm_src]

/-- Two modifies sets copied from one source commute. -/
theorem anon_comm_src (L M : List Name) (a b : SFields fs) :
    anon L (anon M a b) b = anon M (anon L a b) b := by
  induction L with
  | nil => rfl
  | cons r L ih => rw [anon_cons, anon_cons, ih, copyFrom_anon_src]

theorem anon_copyFrom_notMem {r : Name} {L : List Name} (hr : r ∉ L) (b c z : SFields fs) :
    anon L (copyFrom r b z) c = copyFrom r b (anon L z c) := by
  induction L with
  | nil => rfl
  | cons r' L ih =>
    have hne : r ≠ r' := fun e => hr (e ▸ List.mem_cons_self)
    have hL : r ∉ L := fun h => hr (List.mem_cons_of_mem _ h)
    rw [anon_cons, anon_cons, ih hL, copyFrom_comm hne]

theorem anon_copyFrom_mem {r : Name} {L : List Name} (hr : r ∈ L) (b c z : SFields fs) :
    anon L (copyFrom r b z) c = anon L z c := by
  induction L with
  | nil => cases hr
  | cons r' L ih =>
    rw [anon_cons, anon_cons]
    by_cases hL : r ∈ L
    · rw [ih hL]
    · have e : r = r' := by
        rcases List.mem_cons.1 hr with e | e
        · exact e
        · exact absurd e hL
      subst e
      rw [anon_copyFrom_notMem hL, copyFrom_copyFrom_same]

/-- An anonymised state anonymised again over the same set: the last
source wins. -/
theorem anon_anon (L : List Name) (a b c : SFields fs) :
    anon L (anon L a b) c = anon L a c := by
  induction L generalizing a with
  | nil => rfl
  | cons r L ih =>
    rw [anon_cons, anon_cons, anon_cons]
    by_cases hL : r ∈ L
    · rw [anon_copyFrom_mem hL, ih]
    · rw [anon_copyFrom_notMem hL, copyFrom_copyFrom_same, ih]

/-- A member set, read through a modifies set: the write where `L` names its
root, nothing elsewhere. -/
theorem anon_set {f : Name} {T : Ty} (L : List Name) (x : SFields fs)
    (h : lookupBy f fs = some T) (v : SVal T) :
    anon L x (x.set h v) = if f ∈ L then x.set h v else x := by
  induction L with
  | nil => simp only [anon_nil, List.not_mem_nil, ↓reduceIte]
  | cons r L ih =>
    rw [anon_cons, ih]
    by_cases e : f = r
    · subst e
      simp only [List.mem_cons_self, ↓reduceIte]
      by_cases hL : f ∈ L
      · simp only [hL, ↓reduceIte, copyFrom_self]
      · simp only [hL, ↓reduceIte, copyFrom_of_lookup h, get_set_same]
    · simp only [List.mem_cons, e, false_or]
      by_cases hL : f ∈ L
      · simp only [hL, ↓reduceIte, copyFrom_self]
      · simp only [hL, ↓reduceIte]
        cases hr : lookupBy r fs with
        | none => exact copyFrom_of_none hr _ _
        | some U =>
          rw [copyFrom_of_lookup hr, get_set_ne x h hr e v, set_get_self]

theorem copyFrom_congr {r : Name} {y y' : SFields fs} (x : SFields fs)
    (h : ∀ T (hr : lookupBy r fs = some T), y.get hr = y'.get hr) :
    copyFrom r y x = copyFrom r y' x := by
  cases hl : lookupBy r fs with
  | none => rw [copyFrom_of_none hl, copyFrom_of_none hl]
  | some T => rw [copyFrom_of_lookup hl, copyFrom_of_lookup hl, h T hl]

/-- `anon L x y` reads `y` only at the members `L` names. -/
theorem anon_congr {L : List Name} {y y' : SFields fs} (x : SFields fs)
    (h : ∀ r ∈ L, ∀ T (hr : lookupBy r fs = some T), y.get hr = y'.get hr) :
    anon L x y = anon L x y' := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    rw [anon_cons, anon_cons, ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr'),
      copyFrom_congr _ (h r List.mem_cons_self)]

/-- An anonymised storage is framed by its set: anonymised again from the
same source, it is itself. -/
theorem anon_idem (L : List Name) (a b : SFields fs) : anon L a (anon L a b) = anon L a b :=
  anon_congr a fun r hr T h => by rw [get_anon, if_pos hr]

end SFields

/-! ## Storages framed by a modifies set -/

namespace Storage

variable {C : Contract}

/-- `anon(old, L, new)`: the roots `L` names from `new`, the others from `old`. -/
def anon (L : List Name) (old new : Storage C) : Storage C := SFields.anon L old new

/-- **`τ` differs from `σ` only at the roots `L` names**: the frame of a run
that writes only there (`Stmt.run_keeps`). -/
def Framed (L : List Name) (σ τ : Storage C) : Prop := anon L σ τ = τ

namespace Framed

variable {L M : List Name} {a b c : Storage C}

theorem refl (L : List Name) (a : Storage C) : Framed L a a := SFields.anon_self L a

theorem trans (h₁ : Framed L a b) (h₂ : Framed L b c) : Framed L a c := by
  unfold Framed anon at *
  rw [← SFields.anon_anon L a b c, h₁, h₂]

/-- A larger set frames what a smaller one does: on the right. -/
theorem left (h : Framed L a b) : Framed (M ++ L) a b := by
  unfold Framed anon at *
  rw [SFields.anon_append, h, SFields.anon_self]

/-- A larger set frames what a smaller one does: on the left. -/
theorem right (h : Framed L a b) : Framed (L ++ M) a b := by
  unfold Framed anon at *
  rw [SFields.anon_append, SFields.anon_comm_src, h, SFields.anon_self]

theorem mono (hLM : ∀ r ∈ L, r ∈ M) (h : Framed L a b) : Framed M a b := by
  have h' : Framed (M ++ L) a b := h.left
  unfold Framed anon at *
  rw [SFields.anon_append] at h'
  -- every root of `L` is copied again by `M`
  have e : ∀ (L' : List Name), (∀ r ∈ L', r ∈ M) → ∀ z,
      SFields.anon M (SFields.anon L' z b) b = SFields.anon M z b := by
    intro L' hL'
    induction L' with
    | nil => intro z; rfl
    | cons r L' ih =>
      intro z
      rw [SFields.anon_cons, SFields.anon_copyFrom_mem (hL' r List.mem_cons_self),
        ih (fun r h => hL' r (List.mem_cons_of_mem _ h))]
  rw [e L hLM a] at h'
  exact h'

/-- A root written: framed by any set naming it. -/
theorem set {f : Name} {T : Ty} (hf : f ∈ L) (x : Storage C) (h : lookupBy f C.vars = some T)
    (v : SVal T) : Framed L x (SFields.set x h v) := by
  unfold Framed anon
  rw [SFields.anon_set, if_pos hf]

/-- A root written by `save`: framed by any set naming the reference's root. -/
theorem save {U : Ty} {st st' : Storage C} {r : SRef C U} {new : SVal U} (hr : r.root ∈ L)
    (h : st.save r new = some st') : Framed L st st' := by
  unfold Storage.save at h
  obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact Framed.set hr st r.hroot v

theorem write {U : Ty} {st st' : Storage C} {r : SRef C U} {new : SVal U} (hr : r.root ∈ L)
    (h : st.write r new = some st') : Framed L st st' := by
  unfold Storage.write at h
  split at h
  · exact Framed.save hr h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    exact Framed.save hr h

theorem delete {U : Ty} {st st' : Storage C} {r : SRef C U} (hr : r.root ∈ L)
    (h : st.delete r = some st') : Framed L st st' := by
  unfold Storage.delete at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  exact Framed.save hr h

/-- An anonymised storage is framed by its set. -/
theorem ofAnon (L : List Name) (a b : Storage C) : Framed L a (Storage.anon L a b) :=
  SFields.anon_idem L a b

/-- What a framed storage leaves: the anonymised storage itself. -/
theorem eq_anon (h : Framed L a b) : anon L a b = b := h

end Framed

/-- **A root read through `anon`**: `new`'s where `L` names it, `old`'s
elsewhere (KeY's `selectOfAnon`). -/
theorem get_anon {r : Name} {T : Ty} (L : List Name) (old new : Storage C)
    (h : lookupBy r C.vars = some T) :
    SFields.get (anon L old new) h = if r ∈ L then SFields.get new h else SFields.get old h :=
  SFields.get_anon L old new h

theorem find_anon {U : Ty} (L : List Name) (old new : Storage C) (r : SRef C U) :
    (anon L old new).find r = if r.root ∈ L then new.find r else old.find r := by
  unfold Storage.find
  rw [get_anon]
  split <;> rfl

/-- **A root outside the set reads as it did** (`sol_close` discharges both
premises: the frame from the leaf's context, `CloseS.holds_bind_anonSt`,
the root by computing). -/
theorem Framed.find_eq {L : List Name} {a b : Storage C} {U : Ty} (h : Framed L a b)
    {r : SRef C U} (hr : r.root ∉ L) : b.find r = a.find r := by
  calc b.find r = (anon L a b).find r := by rw [h.eq_anon]
    _ = a.find r := by rw [find_anon, if_neg hr]

end Storage

end Solidity
