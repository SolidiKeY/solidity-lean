import Solidity.Semantics.Heap

/-!
# The Theory, typed: a value is its observations

KeY's storage theory (`structRules.key`) read on typed locations.  A value
of a sort is what its reads show (`Obs`): the word at every primitive
location below it, the live length of every dynamic array, and whether a
location is there at all.  So the Theory's equality is `=`: two values with
the same observations are one value, and the laws need no equivalence to be
stated up to.

**One structure for every location family.**  `Obs L` is generic in the
locations `L : Ty → Type`, a location being typed by what it holds: `TVal T`
(`Obs (Path T)`, a stored value, read below it), `TSto C` (`Obs (SLoc C)`, a
storage, read at a state variable's path or at a dangling one).  A location
family appends a path and strips a prefix (`ObsLoc`), and every operation
(`find`, `save`, `delAt`, `copyTo`, `push`, `pop`, …) and every law is
stated once, over any of them.

**Total.**  A write is total (`save` at a path not there makes it there), so
solkey's `findOnSave`/`findOnSaveFrame` hold with no premise that the write
lands.  A location not there reads the default word, length `0`, and
`has = false`.

**From the type.**  What a delete, a copy and a push do below the location
they act on is computed from the location's type and the value's
observations (`TVal.del`, `TVal.overlay`, `TVal.strip`, `TVal.pushA`), as
the interpreter does it on a typed value (`SVal.defaultOf`, `SVal.overlay`,
`SVal.strip`, `Storage.push`): no lazy leaf, no node kind.

**The bridge.**  A typed value is read here by `SVal.obs`, a storage by
`Storage.obs`; each operation of the interpreter is, read so, the
operation of this module (`SVal.obs_save`, `SVal.obs_overlay`, …).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy)

/-! ## Typed paths -/

namespace Path

theorem append_assoc : {T U V W : Ty} → (p : Path T U) → (q : Path U V) → (r : Path V W) →
    (p.append q).append r = p.append (q.append r)
  | _, _, _, _, .nil, q, r => by rw [Path.append_nil, Path.append_nil]
  | _, _, _, _, .field h p, q, r => by
    rw [Path.append_field, Path.append_field, Path.append_field, Path.append_assoc p q r]
  | _, _, _, _, .at i p, q, r => by
    rw [Path.append_at, Path.append_at, Path.append_at, Path.append_assoc p q r]
  | _, _, _, _, .atF i p, q, r => by
    rw [Path.append_atF, Path.append_atF, Path.append_atF, Path.append_assoc p q r]
  | _, _, _, _, .key k p, q, r => by
    rw [Path.append_key, Path.append_key, Path.append_key, Path.append_assoc p q r]

theorem append_nil_right : {T U : Ty} → (p : Path T U) → p.append .nil = p
  | _, _, .nil => append_nil _
  | _, _, .field h p => by rw [append_field, append_nil_right p]
  | _, _, .at i p => by rw [append_at, append_nil_right p]
  | _, _, .atF i p => by rw [append_atF, append_nil_right p]
  | _, _, .key k p => by rw [append_key, append_nil_right p]

theorem ty_eq_of_lookup {s f : Name} {T T' : Ty} (h : lookupBy f (structDef s) = some T)
    (h' : lookupBy f (structDef s) = some T') : T' = T :=
  Option.some.inj (h'.symm.trans h)

/-- The rest of `q` past `p`, where `q` goes through `p`. -/
def strip? : {T U W : Ty} → Path T U → Path T W → Option (Path U W)
  | _, _, _, .nil, q => some q
  | _, _, _, @Path.field _ f _ _ h p, @Path.field _ f' _ _ h' q =>
    if e : f = f' then strip? p (ty_eq_of_lookup h (e ▸ h') ▸ q) else none
  | _, _, _, .at i p, .at j q => if i = j then strip? p q else none
  | _, _, _, .atF i p, .atF j q => if i = j then strip? p q else none
  | _, _, _, .key i p, .key j q => if i = j then strip? p q else none
  | _, _, _, _, _ => none

theorem strip?_append : {T U W : Ty} → (p : Path T U) → (r : Path U W) →
    strip? p (p.append r) = some r
  | _, _, _, .nil, r => by rw [append_nil]; rfl
  | _, _, _, .field h p, r => by
    rw [append_field]; simp only [strip?, dite_true]; exact strip?_append p r
  | _, _, _, .at i p, r => by
    rw [append_at]; simp only [strip?, if_true]; exact strip?_append p r
  | _, _, _, .atF i p, r => by
    rw [append_atF]; simp only [strip?, if_true]; exact strip?_append p r
  | _, _, _, .key i p, r => by
    rw [append_key]; simp only [strip?, if_true]; exact strip?_append p r

theorem eq_of_strip? : {T U W : Ty} → (p : Path T U) → (q : Path T W) → {r : Path U W} →
    strip? p q = some r → q = p.append r
  | _, _, _, .nil, q, r, h => by
    simp only [strip?, Option.some.injEq] at h; subst h; exact (append_nil _).symm
  | _, _, _, @Path.field _ f _ _ hf p, @Path.field _ f' _ _ hf' q, r, h => by
    simp only [strip?] at h
    split at h
    · rename_i e
      subst e
      obtain rfl := ty_eq_of_lookup hf hf'
      rw [append_field, eq_of_strip? p q h]
    · cases h
  | _, _, _, .at i p, .at j q, r, h => by
    simp only [strip?] at h
    split at h
    · rename_i e; subst e; rw [append_at, eq_of_strip? p q h]
    · cases h
  | _, _, _, .atF i p, .atF j q, r, h => by
    simp only [strip?] at h
    split at h
    · rename_i e; subst e; rw [append_atF, eq_of_strip? p q h]
    · cases h
  | _, _, _, .key i p, .key j q, r, h => by
    simp only [strip?] at h
    split at h
    · rename_i e; subst e; rw [append_key, eq_of_strip? p q h]
    · cases h
  | _, _, _, .field _ _, .nil, _, h | _, _, _, .at _ _, .nil, _, h
  | _, _, _, .atF _ _, .nil, _, h | _, _, _, .key _ _, .nil, _, h => by cases h

/-- Two paths from one type with one erasure are one path. -/
theorem heq_of_erase {T U W : Ty} (p : Path T U) (q : Path T W) (h : p.erase = q.erase) :
    U = W ∧ HEq p q := by
  induction p generalizing W with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, HEq.rfl⟩
    | _ => simp only [Path.erase, reduceCtorEq] at h
  | @field s f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | @field _ f' T₂ _ hf' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.field.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | «at» j q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | atF j q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | key k' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩

/-- A path whose erasure extends another's, from one type, is the other
followed by a path. -/
theorem split_of_erase {T U W : Ty} (p : Path T U) (q : Path T W) {s : List Semantics.Seg}
    (h : q.erase = p.erase ++ s) : ∃ r : Path U W, q = p.append r ∧ r.erase = s := by
  induction p generalizing W with
  | nil => exact ⟨q, (Path.append_nil q).symm, h⟩
  | @field s₀ f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | @field _ f' T₂ _ hf' q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.field.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_field hf p r).symm, hr⟩
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | «at» j q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_at _ p r).symm, hr⟩
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | atF j q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_atF _ p r).symm, hr⟩
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | key k' q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_key _ p r).symm, hr⟩

/-- A path that goes nowhere. -/
def IsNil {T U : Ty} (p : Path T U) : Prop := p.erase = []

/-- Where `q` does not go through `p`, the two part, or `q` stops above `p`. -/
theorem strip?_none : {T U W : Ty} → (p : Path T U) → (q : Path T W) → strip? p q = none →
    Diverges p q ∨ ∃ r : Path W U, r.erase ≠ [] ∧ p = q.append r
  | _, _, _, .nil, q, h => by simp only [strip?, reduceCtorEq] at h
  | _, _, _, .field hf p, .nil, _ => .inr ⟨.field hf p, by simp only [erase, ne_eq,
      reduceCtorEq, not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .at i p, .nil, _ => .inr ⟨.at i p, by simp only [erase, ne_eq, reduceCtorEq,
      not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .atF i p, .nil, _ => .inr ⟨.atF i p, by simp only [erase, ne_eq, reduceCtorEq,
      not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .key i p, .nil, _ => .inr ⟨.key i p, by simp only [erase, ne_eq, reduceCtorEq,
      not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, @Path.field _ f _ _ hf p, @Path.field _ f' _ _ hf' q, h => by
    by_cases e : f = f'
    · subst e
      obtain rfl := ty_eq_of_lookup hf hf'
      simp only [strip?, dite_true] at h
      rcases strip?_none p q h with hd | ⟨r, hr, rfl⟩
      · exact .inl (.fieldIn hf hd)
      · exact .inr ⟨r, hr, by rw [append_field]⟩
    · exact .inl (.field hf hf' p q e)
  | _, _, _, .at i p, .at j q, h => by
    by_cases e : i = j
    · subst e
      simp only [strip?, if_true] at h
      rcases strip?_none p q h with hd | ⟨r, hr, rfl⟩
      · exact .inl (.atIn i hd)
      · exact .inr ⟨r, hr, by rw [append_at]⟩
    · exact .inl (.at p q e)
  | _, _, _, .atF i p, .atF j q, h => by
    by_cases e : i = j
    · subst e
      simp only [strip?, if_true] at h
      rcases strip?_none p q h with hd | ⟨r, hr, rfl⟩
      · exact .inl (.atFIn i hd)
      · exact .inr ⟨r, hr, by rw [append_atF]⟩
    · exact .inl (.atF p q e)
  | _, _, _, .key i p, .key j q, h => by
    by_cases e : i = j
    · subst e
      simp only [strip?, if_true] at h
      rcases strip?_none p q h with hd | ⟨r, hr, rfl⟩
      · exact .inl (.keyIn i hd)
      · exact .inr ⟨r, hr, by rw [append_key]⟩
    · exact .inl (.key p q e)

/-- Two paths that part: neither goes through the other, at any rest. -/
theorem strip?_diverges {T U W : Ty} {p : Path T U} {q : Path T W} (hd : Diverges p q) :
    ∀ {V : Ty} (r : Path W V), strip? p (q.append r) = none := by
  induction hd with
  | field h h' p q hne =>
    intro V r
    rw [append_field]; simp only [strip?, hne, dite_false]
  | fieldIn h _ ih =>
    intro V r
    rw [append_field]; simp only [strip?, dite_true]; exact ih r
  | «at» p q hne =>
    intro V r
    rw [append_at]; simp only [strip?, hne, if_false]
  | atIn i _ ih =>
    intro V r
    rw [append_at]; simp only [strip?, if_true]; exact ih r
  | atF p q hne =>
    intro V r
    rw [append_atF]; simp only [strip?, hne, if_false]
  | atFIn i _ ih =>
    intro V r
    rw [append_atF]; simp only [strip?, if_true]; exact ih r
  | key p q hne =>
    intro V r
    rw [append_key]; simp only [strip?, hne, if_false]
  | keyIn k _ ih =>
    intro V r
    rw [append_key]; simp only [strip?, if_true]; exact ih r

theorem strip?_append_append : {T U V W : Ty} → (p : Path T U) → (q : Path U V) → (r : Path U W) →
    strip? (p.append q) (p.append r) = strip? q r
  | _, _, _, _, .nil, q, r => by rw [append_nil, append_nil]
  | _, _, _, _, .field h p, q, r => by
    rw [append_field, append_field]; simp only [strip?, dite_true]; exact strip?_append_append p q r
  | _, _, _, _, .at i p, q, r => by
    rw [append_at, append_at]; simp only [strip?, if_true]; exact strip?_append_append p q r
  | _, _, _, _, .atF i p, q, r => by
    rw [append_atF, append_atF]; simp only [strip?, if_true]; exact strip?_append_append p q r
  | _, _, _, _, .key i p, q, r => by
    rw [append_key, append_key]; simp only [strip?, if_true]; exact strip?_append_append p q r

end Path

/-! ## Observations -/

/-- **A value is its observations** at the locations `L`: the word at each
primitive location, the live length of each dynamic array, and whether a
location is there. -/
structure Obs (L : Ty → Type) where
  word : {P : PrimTy} → L (.prim P) → P.Denote
  len : {E : Ty} → L (.ref (.array E)) → Nat
  has : {U : Ty} → L U → Bool

/-- A stored value of type `T`, read below it. -/
abbrev TVal (T : Ty) := Obs (Path T)

theorem Obs.ext {L : Ty → Type} {o o' : Obs L}
    (hw : ∀ {P : PrimTy} (q : L (.prim P)), o.word q = o'.word q)
    (hl : ∀ {E : Ty} (q : L (.ref (.array E))), o.len q = o'.len q)
    (hh : ∀ {U : Ty} (q : L U), o.has q = o'.has q) : o = o' := by
  cases o; cases o'
  simp only [Obs.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> (funext; funext; first | exact hw _ | exact hl _ | exact hh _)

/-- **A family of locations**: a location followed by a path, and the path
a location goes on by below another. -/
class ObsLoc (L : Ty → Type) where
  app : {U W : Ty} → L U → Path U W → L W
  strip? : {U W : Ty} → L U → L W → Option (Path U W)
  strip?_app : ∀ {U W : Ty} (p : L U) (r : Path U W), strip? p (app p r) = some r
  eq_of_strip? : ∀ {U W : Ty} (p : L U) (q : L W) {r : Path U W}, strip? p q = some r → q = app p r
  app_app : ∀ {U V W : Ty} (p : L U) (q : Path U V) (r : Path V W),
    app (app p q) r = app p (q.append r)
  app_nil : ∀ {U : Ty} (p : L U), app p .nil = p
  strip?_app_app : ∀ {U V W : Ty} (p : L U) (q : Path U V) (r : Path U W),
    strip? (app p q) (app p r) = Path.strip? q r

instance (T : Ty) : ObsLoc (Path T) where
  app p r := p.append r
  strip? p q := Path.strip? p q
  strip?_app p r := Path.strip?_append p r
  eq_of_strip? p q := Path.eq_of_strip? p q
  app_app p q r := Path.append_assoc p q r
  app_nil p := Path.append_nil_right p
  strip?_app_app p q r := Path.strip?_append_append p q r

theorem ObsLoc.app_path {T U W : Ty} (p : Path T U) (r : Path U W) :
    (ObsLoc.app p r : Path T W) = p.append r := rfl
theorem ObsLoc.strip?_path {T U W : Ty} (p : Path T U) (q : Path T W) :
    (ObsLoc.strip? p q : Option (Path U W)) = Path.strip? p q := rfl

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- **`find`**: the value at `p`, read below it. -/
def find (o : Obs L) {U : Ty} (p : L U) : TVal U :=
  ⟨fun r => o.word (ObsLoc.app p r), fun r => o.len (ObsLoc.app p r),
    fun r => o.has (ObsLoc.app p r)⟩

/-- **`save`**: `v` at `p`, everything below `p` read in `v`. -/
def save (o : Obs L) {U : Ty} (p : L U) (v : TVal U) : Obs L :=
  ⟨fun q => match ObsLoc.strip? p q with
     | some r => v.word r
     | none => o.word q,
   fun q => match ObsLoc.strip? p q with
     | some r => v.len r
     | none => o.len q,
   fun q => match ObsLoc.strip? p q with
     | some r => v.has r
     | none => o.has q⟩

theorem find_word (o : Obs L) {U : Ty} (p : L U) {P : PrimTy} (r : Path U (.prim P)) :
    (o.find p).word r = o.word (ObsLoc.app p r) := rfl
theorem find_len (o : Obs L) {U : Ty} (p : L U) {E : Ty} (r : Path U (.ref (.array E))) :
    (o.find p).len r = o.len (ObsLoc.app p r) := rfl
theorem find_has (o : Obs L) {U : Ty} (p : L U) {V : Ty} (r : Path U V) :
    (o.find p).has r = o.has (ObsLoc.app p r) := rfl

/-- **`findOnSave`**: a save reads back where it was made. -/
theorem find_save_same (o : Obs L) {U : Ty} (p : L U) (v : TVal U) :
    (o.save p v).find p = v := by
  cases v
  simp only [find, save, ObsLoc.strip?_app]

/-- **`findOnSaveFrame`**: a read nowhere below the save does not see it. -/
theorem find_save_frame (o : Obs L) {U W : Ty} (p : L U) (q : L W) (v : TVal U)
    (h : ∀ {V : Ty} (r : Path W V), ObsLoc.strip? p (ObsLoc.app q r) = none) :
    (o.save p v).find q = o.find q := by
  simp only [find, save, h]

/-- A read below a read. -/
theorem find_find (o : Obs L) {U V : Ty} (p : L U) (q : Path U V) :
    (o.find p).find q = o.find (ObsLoc.app p q) := by
  simp only [find, ObsLoc.app_path, ObsLoc.app_app]

theorem find_nil (o : Obs L) {U : Ty} (p : L U) : (o.find p).find .nil = o.find p := by
  rw [find_find, ObsLoc.app_nil]

/-- A save of what is there changes nothing. -/
theorem save_find (o : Obs L) {U : Ty} (p : L U) : o.save p (o.find p) = o := by
  apply Obs.ext <;> intro _ q <;> simp only [save, find] <;> split <;>
    first | rfl | (rename_i r h; rw [ObsLoc.eq_of_strip? p q h])

/-- A save over a save at one location: the second wins. -/
theorem save_save (o : Obs L) {U : Ty} (p : L U) (v w : TVal U) :
    (o.save p v).save p w = o.save p w := by
  apply Obs.ext <;> intro _ q <;> simp only [save] <;> split <;> rfl

/-- A save below `q`, read at `q`: the value there with the save made in it. -/
theorem find_save_below (o : Obs L) {U V : Ty} (q : L U) (r : Path U V) (v : TVal V) :
    (o.save (ObsLoc.app q r) v).find q = (o.find q).save r v := by
  apply Obs.ext <;> intro _ w <;>
    simp only [find, save, ObsLoc.strip?_app_app, ObsLoc.strip?_path]

end Obs

/-! ## Storage locations -/

namespace SRef

variable {C : Contract}

theorem ty_eq {U W : Ty} (r : SRef C U) (q : SRef C W) (h : r.root = q.root) : q.ty = r.ty :=
  Option.some.inj (q.hroot.symm.trans (h ▸ r.hroot))

/-- The rest of `q` past `r`, where `q` goes through `r`. -/
def strip? {U W : Ty} (r : SRef C U) (q : SRef C W) : Option (Path U W) :=
  if h : r.root = q.root then Path.strip? r.path (ty_eq r q h ▸ q.path) else none

theorem strip?_append {U W : Ty} (r : SRef C U) (p : Path U W) : r.strip? (r.append p) = some p := by
  rcases r with ⟨n, h, rp⟩
  unfold strip? append
  rw [dif_pos rfl]
  exact Path.strip?_append rp p

theorem eq_of_strip? {U W : Ty} (r : SRef C U) (q : SRef C W) {p : Path U W}
    (h : r.strip? q = some p) : q = r.append p := by
  rcases r with ⟨n, hn, rp⟩
  rcases q with ⟨n', hn', qp⟩
  simp only [strip?] at h
  split at h
  · rename_i e
    subst e
    obtain rfl : _ = _ := Option.some.inj (hn.symm.trans hn')
    simp only [append, Path.eq_of_strip? rp qp h]
  · cases h

theorem append_append {U V W : Ty} (r : SRef C U) (p : Path U V) (q : Path V W) :
    (r.append p).append q = r.append (p.append q) := by
  simp only [append, Path.append_assoc]

theorem append_nil {U : Ty} (r : SRef C U) : r.append .nil = r := by
  simp only [append, Path.append_nil_right]

theorem strip?_append_append {U V W : Ty} (r : SRef C U) (p : Path U V) (q : Path U W) :
    (r.append p).strip? (r.append q) = Path.strip? p q := by
  rcases r with ⟨n, h, rp⟩
  unfold strip? append
  rw [dif_pos rfl]
  exact Path.strip?_append_append rp p q

theorem strip?_root_ne {U W : Ty} (r : SRef C U) (q : SRef C W) (h : r.root ≠ q.root) :
    r.strip? q = none := by
  unfold strip?; rw [dif_neg h]

end SRef

/-- **A storage location**: a state variable's path, or a dangling path (an
unset alias's, read and written like any other location; the program never
reaches one, `Storage.obs` reads it as not there). -/
inductive SLoc (C : Contract) (T : Ty) where
  | ref (r : SRef C T)
  | dangling (U : Ty) (p : Path U T)

namespace SLoc

variable {C : Contract}

/-- A location followed by a path. -/
def app {U W : Ty} : SLoc C U → Path U W → SLoc C W
  | .ref r, q => .ref (r.append q)
  | .dangling V p, q => .dangling V (p.append q)

/-- The rest of `q` past `p`. -/
def strip? {U W : Ty} : SLoc C U → SLoc C W → Option (Path U W)
  | .ref r, .ref q => r.strip? q
  | .dangling V p, .dangling V' q => if h : V' = V then Path.strip? p (h ▸ q) else none
  | _, _ => none

theorem strip?_app {U W : Ty} (p : SLoc C U) (r : Path U W) : strip? p (app p r) = some r := by
  cases p with
  | ref r' => exact SRef.strip?_append r' r
  | dangling V p => simp only [app, strip?, dite_true]; exact Path.strip?_append p r

theorem eq_of_strip? {U W : Ty} (p : SLoc C U) (q : SLoc C W) {r : Path U W}
    (h : strip? p q = some r) : q = app p r := by
  cases p with
  | ref r₀ =>
    cases q with
    | ref q => exact congrArg SLoc.ref (SRef.eq_of_strip? r₀ q h)
    | dangling => cases h
  | dangling V p =>
    cases q with
    | ref => cases h
    | dangling V' q =>
      simp only [strip?] at h
      split at h
      · rename_i e; subst e; exact congrArg (SLoc.dangling _) (Path.eq_of_strip? p q h)
      · cases h

theorem app_app {U V W : Ty} (p : SLoc C U) (q : Path U V) (r : Path V W) :
    app (app p q) r = app p (q.append r) := by
  cases p <;> simp only [app, SRef.append_append, Path.append_assoc]

theorem app_nil {U : Ty} (p : SLoc C U) : app p .nil = p := by
  cases p <;> simp only [app, SRef.append_nil, Path.append_nil_right]

theorem strip?_app_app {U V W : Ty} (p : SLoc C U) (q : Path U V) (r : Path U W) :
    strip? (app p q) (app p r) = Path.strip? q r := by
  cases p with
  | ref r₀ => exact SRef.strip?_append_append r₀ q r
  | dangling V p => simp only [app, strip?, dite_true]; exact Path.strip?_append_append p q r

instance : ObsLoc (SLoc C) where
  app := app
  strip? := strip?
  strip?_app := strip?_app
  eq_of_strip? := eq_of_strip?
  app_app := app_app
  app_nil := app_nil
  strip?_app_app := strip?_app_app

theorem app_ref {U W : Ty} (r : SRef C U) (q : Path U W) :
    (ObsLoc.app (SLoc.ref r) q : SLoc C W) = .ref (r.append q) := rfl
theorem strip?_ref {U W : Ty} (r : SRef C U) (q : SRef C W) :
    (ObsLoc.strip? (SLoc.ref r) (SLoc.ref q) : Option (Path U W)) = r.strip? q := rfl

end SLoc

/-- A storage, read at its locations. -/
abbrev TSto (C : Contract) := Obs (SLoc C)

/-! ## Typed values, read below a path -/

/-- A read below a path is the read of what is found at the path. -/
theorem SVal.findM_append {T U W : Ty} : (x : SVal T) → (p : Path T U) → (r : Path U W) →
    x.findM (p.append r) = (x.findM p).bind (·.findM r)
  | x, .nil, r => by rw [Path.append_nil]; cases x <;> rfl
  | .struct fs, .field hf p, r => by
    rw [Path.append_field]
    simp only [SVal.findM]
    exact SVal.findM_append _ p r
  | .array e sh hn, .at i p, r => by
    rw [Path.append_at]
    simp only [SVal.findM]
    split
    · split
      · rename_i x0 _
        exact SVal.findM_append x0 p r
      · rfl
    · rfl
  | .fixed e, .atF i p, r => by
    rw [Path.append_atF]
    simp only [SVal.findM]
    split
    · split
      · rename_i x0 _
        exact SVal.findM_append x0 p r
      · rfl
    · rfl
  | .map m d, .key k p, r => by
    rw [Path.append_key]
    simp only [SVal.findM]
    split
    · rename_i x0 _
      exact SVal.findM_append x0 p r
    · exact SVal.findM_append d p r

/-- A save below a path is the save, at the path, of what is found there with
the save below it; its compiled form. -/
theorem SVal.saveM_append_eq {T U W : Ty} : (x : SVal T) → (p : Path T U) → (r : Path U W) →
    (v : SVal W) → x.saveM (p.append r) v =
      (x.findM p).bind fun y => (y.saveM r v).bind fun y' => x.saveM p y'
  | x, .nil, r, v => by
    rw [Path.append_nil]
    cases x <;> (simp only [SVal.findM, Option.bind_some]; cases SVal.saveM _ r v <;> rfl)
  | .struct fs, .field hf p, r, v => by
    rw [Path.append_field]
    simp only [SVal.saveM, SVal.findM, Option.bind_eq_bind]
    rw [SVal.saveM_append_eq _ p r v]
    cases (fs.get hf).findM p with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      cases y.saveM r v with
      | none => rfl
      | some y' => rfl
  | .array e sh hn, .at i p, r, v => by
    rw [Path.append_at]
    simp only [SVal.saveM, SVal.findM]
    split
    · rename_i hi
      split
      · rename_i x0 hx
        simp only [Option.bind_eq_bind]
        rw [SVal.saveM_append_eq x0 p r v]
        cases x0.findM p with
        | none => rfl
        | some y =>
          simp only [Option.bind_some]
          cases y.saveM r v with
          | none => rfl
          | some y' => simp only [Option.bind_some, SVal.saveM, hi, if_true, hx]
      · rfl
    · rfl
  | .fixed e, .atF i p, r, v => by
    rw [Path.append_atF]
    simp only [SVal.saveM, SVal.findM]
    split
    · rename_i hi
      split
      · rename_i x0 hx
        simp only [Option.bind_eq_bind]
        rw [SVal.saveM_append_eq x0 p r v]
        cases x0.findM p with
        | none => rfl
        | some y =>
          simp only [Option.bind_some]
          cases y.saveM r v with
          | none => rfl
          | some y' => simp only [Option.bind_some, SVal.saveM, hi, if_true, hx]
      · rfl
    · rfl
  | .map m d, .key k p, r, v => by
    rw [Path.append_key]
    simp only [SVal.saveM, SVal.findM]
    split
    · rename_i x0 hx
      simp only [Option.bind_eq_bind]
      rw [SVal.saveM_append_eq x0 p r v]
      cases x0.findM p with
      | none => rfl
      | some y =>
        simp only [Option.bind_some]
        cases y.saveM r v with
        | none => rfl
        | some y' => simp only [Option.bind_some, SVal.saveM, hx]
    · rename_i hx
      simp only [Option.bind_eq_bind]
      rw [SVal.saveM_append_eq d p r v]
      cases d.findM p with
      | none => rfl
      | some y =>
        simp only [Option.bind_some]
        cases y.saveM r v with
        | none => rfl
        | some y' => simp only [Option.bind_some, SVal.saveM, hx]

/-- Where a path finds a value, a save at it lands. -/
theorem SVal.saveM_of_findM {T U : Ty} : (x : SVal T) → (p : Path T U) → {y : SVal U} →
    x.findM p = some y → ∀ v : SVal U, ∃ x', x.saveM p v = some x'
  | x, .nil, _, _, v => ⟨v, by cases x <;> rfl⟩
  | .struct fs, .field hf p, y, h, v => by
    simp only [SVal.findM] at h
    obtain ⟨z, hz⟩ := SVal.saveM_of_findM _ p h v
    exact ⟨_, by simp only [SVal.saveM, hz, Option.bind_eq_bind, Option.bind_some]; rfl⟩
  | .array e sh hn, .at i p, y, h, v => by
    simp only [SVal.findM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x0 hx
        obtain ⟨z, hz⟩ := SVal.saveM_of_findM x0 p h v
        exact ⟨_, by simp only [SVal.saveM, hi, if_true, hx, hz, Option.bind_eq_bind,
          Option.bind_some]; rfl⟩
      · cases h
    · cases h
  | .fixed e, .atF i p, y, h, v => by
    simp only [SVal.findM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x0 hx
        obtain ⟨z, hz⟩ := SVal.saveM_of_findM x0 p h v
        exact ⟨_, by simp only [SVal.saveM, hi, if_true, hx, hz, Option.bind_eq_bind,
          Option.bind_some]; rfl⟩
      · cases h
    · cases h
  | .map m d, .key k p, y, h, v => by
    simp only [SVal.findM] at h
    split at h
    · rename_i x0 hx
      obtain ⟨z, hz⟩ := SVal.saveM_of_findM x0 p h v
      exact ⟨_, by simp only [SVal.saveM, hx, hz, Option.bind_eq_bind, Option.bind_some]; rfl⟩
    · rename_i hx
      obtain ⟨z, hz⟩ := SVal.saveM_of_findM d p h v
      exact ⟨_, by simp only [SVal.saveM, hx, hz, Option.bind_eq_bind, Option.bind_some]; rfl⟩

/-- A save below a path is a save at the path of the value found there,
saved below. -/
theorem SVal.saveM_append {T U W : Ty} (x : SVal T) (p : Path T U) (r : Path U W) (v : SVal W)
    {x' : SVal T} (h : x.saveM (p.append r) v = some x') :
    ∃ y y', x.findM p = some y ∧ y.saveM r v = some y' ∧ x.saveM p y' = some x' := by
  induction p with
  | nil => exact ⟨x, x', by cases x <;> rfl, by rw [Path.append_nil] at h; exact h, by cases x <;> rfl⟩
  | @field s f T₁ U₁ hf p ih =>
    cases x with
    | struct fs =>
      simp only [Path.append_field, SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      obtain ⟨y, y', hy, hy', hz'⟩ := ih (fs.get hf) r hz
      refine ⟨y, y', ?_, hy', ?_⟩
      · simp only [SVal.findM]; exact hy
      · simp only [SVal.saveM, hz', Option.bind_eq_bind, Option.bind_some]
  | @«at» E U₁ i p ih =>
    cases x with
    | array e sh hn =>
      simp only [Path.append_at, SVal.saveM] at h
      split at h
      · rename_i hi
        split at h
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
          refine ⟨y, y', ?_, hy', ?_⟩
          · simp only [SVal.findM, hi, if_true, hx]; exact hy
          · simp only [SVal.saveM, hi, if_true, hx, hz', Option.bind_eq_bind, Option.bind_some]
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
  | @atF E U₁ n i p ih =>
    cases x with
    | fixed e =>
      simp only [Path.append_atF, SVal.saveM] at h
      split at h
      · rename_i hi
        split at h
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
          refine ⟨y, y', ?_, hy', ?_⟩
          · simp only [SVal.findM, hi, if_true, hx]; exact hy
          · simp only [SVal.saveM, hi, if_true, hx, hz', Option.bind_eq_bind, Option.bind_some]
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
  | @key K V U₁ k p ih =>
    cases x with
    | map m d =>
      simp only [Path.append_key, SVal.saveM] at h
      split at h
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]
      · rename_i hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih d r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]

/-- A save at an element below an array keeps the array's live length. -/
theorem SVal.saveM_at_n {E W : Ty} {y y' : SVal (.ref (.array E))} {i : Int} {r : Path E W}
    {v : SVal W} (h : y.saveM (.at i r) v = some y') :
    (SVal.view y' : ArrView E).n = (SVal.view y : ArrView E).n := by
  cases y with
  | array e sh hn =>
    rename_i n
    simp only [SVal.saveM] at h
    split at h
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, -, rfl⟩ := h
        show (List.take n _).length = n
        rw [List.length_take, List.length_set, List.length_append, SVec.length_toList]
        omega
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-! ## A typed value as its observations -/

/-- The word a read finds: the default where nothing is there. -/
def SVal.wordOf {P : PrimTy} : Option (SVal (.prim P)) → P.Denote
  | some w => SVal.view w
  | none => PrimTy.dflt P

/-- The live length a read finds: `0` where nothing is there. -/
def SVal.lenOf {E : Ty} : Option (SVal (.ref (.array E))) → Nat
  | some w => (SVal.view w : ArrView E).n
  | none => 0

/-- A value that may not be there, read below. -/
def SVal.obsOpt {T : Ty} (x : Option (SVal T)) : TVal T :=
  ⟨fun r => SVal.wordOf (x.bind (·.findM r)), fun r => SVal.lenOf (x.bind (·.findM r)),
    fun r => (x.bind (·.findM r)).isSome⟩

/-- **A typed value as its observations.** -/
def SVal.obs {T : Ty} (v : SVal T) : TVal T := SVal.obsOpt (some v)

theorem SVal.obs_word {T : Ty} (v : SVal T) {P : PrimTy} (r : Path T (.prim P)) :
    v.obs.word r = SVal.wordOf (v.findM r) := rfl
theorem SVal.obs_len {T : Ty} (v : SVal T) {E : Ty} (r : Path T (.ref (.array E))) :
    v.obs.len r = SVal.lenOf (v.findM r) := rfl
theorem SVal.obs_has {T : Ty} (v : SVal T) {U : Ty} (r : Path T U) :
    v.obs.has r = (v.findM r).isSome := rfl

/-- What a value holds at `p`, read below. -/
theorem SVal.obs_find {T U : Ty} (v : SVal T) (p : Path T U) : v.obs.find p = SVal.obsOpt (v.findM p) := by
  apply Obs.ext <;> intro _ r <;>
    simp only [Obs.find, SVal.obs, SVal.obsOpt, Option.bind_some, ObsLoc.app_path, SVal.findM_append]

theorem SVal.obsOpt_some {T : Ty} (v : SVal T) : SVal.obsOpt (some v) = v.obs := rfl

/-- **`findOnSave`, the bridge**: a typed save, read, is the Theory's. -/
theorem SVal.obs_saveM {T U : Ty} {x x' : SVal T} {p : Path T U} {v : SVal U}
    (h : x.saveM p v = some x') : x'.obs = x.obs.save p v.obs := by
  have key : ∀ {W : Ty} (q : Path T W), Path.strip? p q = none →
      (x'.findM q).isSome = (x.findM q).isSome ∧
      (∀ {E : Ty} (hW : W = .ref (.array E)), SVal.lenOf (hW ▸ x'.findM q) = SVal.lenOf (hW ▸ x.findM q)) ∧
      (∀ {P : PrimTy} (hW : W = .prim P), hW ▸ x'.findM q = hW ▸ x.findM q) := by
    intro W q hq
    rcases Path.strip?_none p q hq with hd | ⟨r, hr, rfl⟩
    · have e := SVal.findM_saveM_diverges hd x v h
      exact ⟨by rw [e], fun _ => by rw [e], fun _ => by rw [e]⟩
    · obtain ⟨y, y', hy, hy', hx'⟩ := SVal.saveM_append x q r v h
      have hf : x'.findM q = some y' := SVal.findM_saveM x q y' hx'
      refine ⟨by rw [hf, hy]; rfl, fun hW => ?_, fun hW => ?_⟩
      · subst hW
        cases r with
        | nil => exact absurd rfl hr
        | «at» i r => rw [hf, hy]; exact SVal.saveM_at_n hy'
      · subst hW
        cases r with
        | nil => exact absurd rfl hr
  apply Obs.ext
  · intro P q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_word, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      simp only [SVal.obs_word, (key q hr).2.2 rfl]
  · intro E q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_len, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      exact (key q hr).2.1 rfl
  · intro W q
    simp only [Obs.save, ObsLoc.strip?_path]
    split
    · rename_i r hr
      rw [Path.eq_of_strip? p q hr]
      simp only [SVal.obs_has, SVal.findM_append, SVal.findM_saveM x p v h, Option.bind_some]
    · rename_i hr
      exact (key q hr).1

theorem SVal.obsOpt_find {T U : Ty} (x : Option (SVal T)) (p : Path T U) :
    (SVal.obsOpt x).find p = SVal.obsOpt (x.bind (·.findM p)) := by
  cases x with
  | none => rfl
  | some v => exact SVal.obs_find v p

/-! ## A storage as its observations -/

/-- **A typed storage as its observations**: at a state variable's path what
the value there shows, a dangling location not there. -/
def Storage.obs {C : Contract} (st : Storage C) : TSto C :=
  ⟨fun l => match l with
     | .ref r => (st.get r.hroot).obs.word r.path
     | .dangling _ _ => PrimTy.dflt _,
   fun l => match l with
     | .ref r => (st.get r.hroot).obs.len r.path
     | .dangling _ _ => 0,
   fun l => match l with
     | .ref r => (st.get r.hroot).obs.has r.path
     | .dangling _ _ => false⟩

namespace Storage

variable {C : Contract}

theorem obs_word_ref (st : Storage C) {P : PrimTy} (r : SRef C (.prim P)) :
    st.obs.word (.ref r) = (st.get r.hroot).obs.word r.path := rfl
theorem obs_len_ref (st : Storage C) {E : Ty} (r : SRef C (.ref (.array E))) :
    st.obs.len (.ref r) = (st.get r.hroot).obs.len r.path := rfl
theorem obs_has_ref (st : Storage C) {U : Ty} (r : SRef C U) :
    st.obs.has (.ref r) = (st.get r.hroot).obs.has r.path := rfl

/-- What a storage holds at `r`, read below. -/
theorem obs_find {U : Ty} (st : Storage C) (r : SRef C U) :
    st.obs.find (.ref r) = SVal.obsOpt (st.find r) := by
  rw [Storage.find, SVal.find_eq_findM, ← SVal.obs_find]
  rfl

/-- The storage read at a root: the value there. -/
theorem obs_find_root (st : Storage C) (n : Name) {T : Ty} (hn : C.rootType n = some T) :
    st.obs.find (.ref (SRef.ofRoot n hn)) = (st.get hn).obs := by
  rw [obs_find, Storage.find, SVal.find_eq_findM]
  cases st.get hn <;> rfl

/-- Two storages that agree at every root agree. -/
theorem obs_ext {o : TSto C} (st : Storage C)
    (h : ∀ (n : Name) {T : Ty} (hn : C.rootType n = some T),
      (st.get hn).obs = o.find (.ref (SRef.ofRoot n hn)))
    (hw : ∀ {P : PrimTy} (U : Ty) (p : Path U (.prim P)), o.word (.dangling U p) = PrimTy.dflt P)
    (hl : ∀ {E : Ty} (U : Ty) (p : Path U (.ref (.array E))), o.len (.dangling U p) = 0)
    (hh : ∀ {V : Ty} (U : Ty) (p : Path U V), o.has (.dangling U p) = false) : st.obs = o := by
  have e : ∀ {W : Ty} (q : SRef C W),
      (SLoc.ref q : SLoc C W) = ObsLoc.app (SLoc.ref (SRef.ofRoot q.root q.hroot)) q.path := by
    intro W q
    rcases q with ⟨n, hn, qp⟩
    show _ = SLoc.ref ⟨n, hn, Path.nil.append qp⟩
    rw [Path.append_nil]
  apply Obs.ext
  · intro P q
    cases q with
    | ref q => rw [obs_word_ref, h, e q]; rfl
    | dangling U p => exact (hw U p).symm
  · intro E q
    cases q with
    | ref q => rw [obs_len_ref, h, e q]; rfl
    | dangling U p => exact (hl U p).symm
  · intro V q
    cases q with
    | ref q => rw [obs_has_ref, h, e q]; rfl
    | dangling U p => exact (hh U p).symm

/-- **The bridge of a save**: a typed save, read, is the Theory's. -/
theorem obs_save {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') : st'.obs = st.obs.save (.ref r) v.obs := by
  unfold Storage.save at h
  rcases r with ⟨n, hn, rp⟩
  cases hs : (st.get hn).save rp v with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some x' =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    subst h
    rw [SVal.save_eq_saveM] at hs
    have hv := SVal.obs_saveM hs
    have er : (SLoc.ref ⟨n, hn, rp⟩ : SLoc C U) = ObsLoc.app (SLoc.ref (SRef.ofRoot n hn)) rp := by
      show _ = SLoc.ref ⟨n, hn, Path.nil.append rp⟩
      rw [Path.append_nil]
    refine obs_ext _ (fun n' T' hn' => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    by_cases e : n' = n
    · subst e
      obtain rfl : T' = _ := Option.some.inj (hn'.symm.trans hn)
      rw [SFields.get_set_same, hv, er, Obs.find_save_below, obs_find_root]
    · rw [SFields.get_set_ne _ hn hn' (Ne.symm e), Obs.find_save_frame, obs_find_root]
      intro V q
      exact SRef.strip?_root_ne _ _ (Ne.symm e)

end Storage

/-! ## One component of the observations

A delete, a strip and a copy are read one component at a time (`Comp`): a
word, a length, or whether a location is there; each is defined once over
the component and is the three of them (`TVal.ofComp`). -/

/-- A component of the observations at the locations of type `V`. -/
structure Comp (V : Ty) (α : Type) where
  /-- The component at `r` of a value. -/
  read : {U : Ty} → TVal U → Path U V → α
  /-- The component of a typed value found, or of nothing. -/
  ofOpt : Option (SVal V) → α
  /-- The component at a location deleted. -/
  reset : TVal V → α
  read_obsOpt : ∀ {U : Ty} (x : Option (SVal U)) (r : Path U V),
    read (SVal.obsOpt x) r = ofOpt (x.bind (·.findM r))
  read_find : ∀ {U W : Ty} (o : TVal U) (p : Path U W) (r : Path W V),
    read (o.find p) r = read o (p.append r)
  overlay_top : ∀ x y : SVal V, ofOpt (some (x.overlay y)) = ofOpt (some y)
  strip_top : ∀ x : SVal V, ofOpt (some x.strip) = ofOpt (some x)
  reset_some : ∀ x : SVal V, reset x.obs = ofOpt (some x.defaultOf)
  reset_none : reset (SVal.obsOpt none) = ofOpt none

namespace Comp

/-- The word at a primitive location. -/
def word (P : PrimTy) : Comp (.prim P) P.Denote where
  read o r := o.word r
  ofOpt := SVal.wordOf
  reset _ := PrimTy.dflt P
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top x y := by cases y; rw [SVal.overlay_prim]
  strip_top x := by cases x; rw [SVal.strip_prim]
  reset_some x := by cases x; rw [SVal.defaultOf_prim]; rfl
  reset_none := rfl

/-- The live length of a dynamic array. -/
def len (E : Ty) : Comp (.ref (.array E)) Nat where
  read o r := o.len r
  ofOpt := SVal.lenOf
  reset _ := 0
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top x y := by cases x; cases y; rw [SVal.overlay_array]; rfl
  strip_top x := by cases x; rw [SVal.strip_array]; rfl
  reset_some x := by cases x; rw [SVal.defaultOf_array]; rfl
  reset_none := rfl

/-- Whether a location is there. -/
def has (V : Ty) : Comp V Bool where
  read o r := o.has r
  ofOpt x := x.isSome
  reset o := o.has .nil
  read_obsOpt _ _ := rfl
  read_find _ _ _ := rfl
  overlay_top _ _ := rfl
  strip_top _ := rfl
  reset_some x := by cases x <;> rfl
  reset_none := rfl

/-- What is not there. -/
abbrev absent {V : Ty} {α : Type} (c : Comp V α) : α := c.ofOpt none

end Comp

namespace TVal

/-- A value from its three components, each read by `f`. -/
def ofComp {U : Ty} (f : {V : Ty} → {α : Type} → Comp V α → Path U V → α) : TVal U :=
  ⟨fun r => f (Comp.word _) r, fun r => f (Comp.len _) r, fun r => f (Comp.has _) r⟩

theorem eq_ofComp {U : Ty} {o : TVal U} {f : {V : Ty} → {α : Type} → Comp V α → Path U V → α}
    (h : ∀ {V : Ty} {α : Type} (c : Comp V α) (r : Path U V), c.read o r = f c r) :
    o = ofComp f :=
  Obs.ext (fun r => h (Comp.word _) r) (fun r => h (Comp.len _) r) (fun r => h (Comp.has _) r)

variable {V : Ty} {α : Type}

/-- A delete, one component (`SVal.defaultOf`): reset below the location,
but a mapping's entries and an array's slots past its live end are kept. -/
def delR (c : Comp V α) : {U : Ty} → TVal U → Path U V → α
  | _, o, .nil => c.reset o
  | _, o, .field h r => delR c (o.find (.field h .nil)) r
  | _, o, .atF i r => delR c (o.find (.atF i .nil)) r
  | _, o, .key k r => c.read o (.key k r)
  | _, o, .at i r =>
    if 0 ≤ i ∧ i.toNat < o.len .nil then delR c (o.find (.at i .nil)) r else c.read o (.at i r)

/-- A value as nothing has written it, one component (`SVal.strip`): no
slots past an array's live end. -/
def stripR (c : Comp V α) : {U : Ty} → TVal U → Path U V → α
  | _, o, .nil => c.read o .nil
  | _, o, .field h r => stripR c (o.find (.field h .nil)) r
  | _, o, .atF i r => stripR c (o.find (.atF i .nil)) r
  | _, o, .key k r => c.read o (.key k r)
  | _, o, .at i r =>
    if 0 ≤ i ∧ i.toNat < o.len .nil then stripR c (o.find (.at i .nil)) r else c.absent

/-- A copy of `n` laid over `o`, one component (`SVal.overlay`): member by
member, element by element over the old slots (onto fresh ones as nothing
wrote them), the old elements past the new length deleted, the old slots
past both kept, a mapping kept. -/
def ovR (c : Comp V α) : {U : Ty} → TVal U → TVal U → Path U V → α
  | _, _, n, .nil => c.read n .nil
  | _, o, n, .field h r => ovR c (o.find (.field h .nil)) (n.find (.field h .nil)) r
  | _, o, n, .atF i r => ovR c (o.find (.atF i .nil)) (n.find (.atF i .nil)) r
  | _, o, n, .key k r =>
    if n.has .nil then (if o.has .nil then c.read o (.key k r) else c.read n (.key k r))
    else c.absent
  | _, o, n, .at i r =>
    if n.has .nil then
      if 0 ≤ i ∧ i.toNat < n.len .nil then ovR c (o.find (.at i .nil)) (n.find (.at i .nil)) r
      else if 0 ≤ i ∧ i.toNat < o.len .nil then delR c (o.find (.at i .nil)) r
      else c.read o (.at i r)
    else c.absent

end TVal

/-- **`delValue`** of a stored value: reset, as `delete` resets it. -/
def TVal.del {U : Ty} (o : TVal U) : TVal U := TVal.ofComp fun c r => TVal.delR c o r
/-- A value as written to fresh slots (`SVal.strip`). -/
def TVal.strip {U : Ty} (o : TVal U) : TVal U := TVal.ofComp fun c r => TVal.stripR c o r
/-- **A copy**: `n` laid over `o` (`SVal.overlay`). -/
def TVal.overlay {U : Ty} (o n : TVal U) : TVal U := TVal.ofComp fun c r => TVal.ovR c o n r

/-! ### A read, step by step -/

theorem SVal.findM_nil' {T : Ty} (x : SVal T) : x.findM .nil = some x := by cases x <;> rfl

theorem SVal.findM_field' {s f : Name} {T U : Ty} (fs : SFields (structDef s))
    (h : lookupBy f (structDef s) = some T) (r : Path T U) :
    (SVal.struct fs).findM (.field h r) = (fs.get h).findM r := rfl

theorem SVal.findM_at' {E U : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (i : Int) (r : Path E U) : (SVal.array e sh hn).findM (.at i r) =
      if 0 ≤ i then (e.toList ++ sh.toList)[i.toNat]?.bind (·.findM r) else none := by
  simp only [SVal.findM]
  split
  · cases (e.toList ++ sh.toList)[i.toNat]? <;> rfl
  · rfl

theorem SVal.findM_atF' {E U : Ty} {n : Nat} (e : SVec E n) (i : Int) (r : Path E U) :
    (SVal.fixed e).findM (.atF i r) =
      if 0 ≤ i then e.toList[i.toNat]?.bind (·.findM r) else none := by
  simp only [SVal.findM]
  split
  · cases e.toList[i.toNat]? <;> rfl
  · rfl

theorem Option.bind_some_id {β : Type} (x : Option β) : x.bind (fun y => some y) = x := by
  cases x <;> rfl

theorem SVal.findM_field_nil {s f : Name} {T : Ty} (fs : SFields (structDef s))
    (h : lookupBy f (structDef s) = some T) :
    (SVal.struct fs).findM (.field h .nil) = some (fs.get h) := by
  rw [SVal.findM_field', SVal.findM_nil']

theorem SVal.findM_at_nil {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (i : Int) : (SVal.array e sh hn).findM (.at i .nil) =
      if 0 ≤ i then (e.toList ++ sh.toList)[i.toNat]? else none := by
  rw [SVal.findM_at']
  split
  · cases (e.toList ++ sh.toList)[i.toNat]? with
    | none => rfl
    | some w => exact SVal.findM_nil' w
  · rfl

theorem SVal.findM_atF_nil {E : Ty} {n : Nat} (e : SVec E n) (i : Int) :
    (SVal.fixed e).findM (.atF i .nil) = if 0 ≤ i then e.toList[i.toNat]? else none := by
  rw [SVal.findM_atF']
  split
  · cases e.toList[i.toNat]? with
    | none => rfl
    | some w => exact SVal.findM_nil' w
  · rfl

theorem SVal.findM_key' {K V U : Ty} (m : SMap V) (d : SVal V) (k : Int) (r : Path V U) :
    (SVal.map (K := K) m d).findM (.key k r) = ((lookupBy k m.toList).getD d).findM r := by
  simp only [SVal.findM]
  cases lookupBy k m.toList <;> rfl

/-! ### Members and elements of a delete, a strip, a copy -/

theorem SFields.get_defaultOf {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (xs : SFields fs) → (h : lookupBy f fs = some T) →
    xs.defaultOf.get h = (xs.get h).defaultOf
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons x xs, h => by
    rw [SFields.defaultOf_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_defaultOf xs _

theorem SFields.get_strip {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (xs : SFields fs) → (h : lookupBy f fs = some T) →
    xs.strip.get h = (xs.get h).strip
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons x xs, h => by
    rw [SFields.strip_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_strip xs _

theorem SFields.get_overlay {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (os ns : SFields fs) → (h : lookupBy f fs = some T) →
    (os.overlay ns).get h = (os.get h).overlay (ns.get h)
  | [], _, .nil, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons o os, .cons n ns, h => by
    rw [SFields.overlay_cons, SFields.get_cons, SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact SFields.get_overlay os ns _

theorem SVec.toList_defaultOf {E : Ty} : {n : Nat} → (e : SVec E n) →
    e.defaultOf.toList = e.toList.map SVal.defaultOf
  | _, .nil => by rw [SVec.defaultOf_nil, SVec.toList_nil]; rfl
  | _, .cons v rest => by
    rw [SVec.defaultOf_cons, SVec.toList_cons, SVec.toList_cons, SVec.toList_defaultOf rest]; rfl

theorem SVec.toList_strip {E : Ty} : {n : Nat} → (e : SVec E n) →
    e.strip.toList = e.toList.map SVal.strip
  | _, .nil => by rw [SVec.strip_nil, SVec.toList_nil]; rfl
  | _, .cons v rest => by
    rw [SVec.strip_cons, SVec.toList_cons, SVec.toList_cons, SVec.toList_strip rest]; rfl

/-- A copy over what may not be there: as nothing wrote it, onto nothing. -/
def SVal.overlayOpt {U : Ty} : Option (SVal U) → Option (SVal U) → Option (SVal U)
  | _, none => none
  | none, some n => some n.strip
  | some o, some n => some (o.overlay n)

theorem SVal.overlayOpt_none {U : Ty} (x : Option (SVal U)) : SVal.overlayOpt x none = none := by
  cases x <;> rfl
theorem SVal.overlayOpt_none_some {U : Ty} (n : SVal U) :
    SVal.overlayOpt none (some n) = some n.strip := rfl
theorem SVal.overlayOpt_some_some {U : Ty} (o n : SVal U) :
    SVal.overlayOpt (some o) (some n) = some (o.overlay n) := rfl

theorem SVal.obsOpt_has_nil {U : Ty} (x : Option (SVal U)) : (SVal.obsOpt x).has .nil = x.isSome := by
  cases x with
  | none => rfl
  | some v => show (v.findM .nil).isSome = true; rw [SVal.findM_nil']; rfl
theorem SVal.obsOpt_len_nil {E : Ty} (x : Option (SVal (.ref (.array E)))) :
    (SVal.obsOpt x).len .nil = SVal.lenOf x := by
  cases x with
  | none => rfl
  | some v => show SVal.lenOf (v.findM .nil) = _; rw [SVal.findM_nil']

/-- The new elements laid over the old slots, slot by slot. -/
theorem SVec.getElem?_overlayOn {E : Ty} : {n : Nat} → (L : List (SVal E)) → (e : SVec E n) →
    (j : Nat) → (SVec.overlayOn L e).toList[j]? = SVal.overlayOpt L[j]? e.toList[j]?
  | _, L, .nil, j => by
    rw [SVec.overlayOn_nil, SVec.toList_nil, List.getElem?_nil]; cases L[j]? <;> rfl
  | _, [], .cons v rest, j => by
    rw [SVec.overlayOn_nil_cons, SVec.toList_cons, SVec.toList_cons, ← SVec.overlayOn_nil_left,
      List.getElem?_nil]
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      rw [SVec.getElem?_overlayOn [] rest j, List.getElem?_nil]
  | _, o :: L, .cons v rest, j => by
    rw [SVec.overlayOn_cons_cons, SVec.toList_cons, SVec.toList_cons]
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      exact SVec.getElem?_overlayOn L rest j

/-! ### The bridge of a delete, a strip, a copy -/

theorem TVal.delR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x : Option (SVal U)) →
    (r : Path U V) → TVal.delR c (SVal.obsOpt x) r = c.ofOpt ((x.map SVal.defaultOf).bind (·.findM r))
  | _, none, .nil => c.reset_none
  | _, some v, .nil => by
    show c.reset v.obs = _
    rw [c.reset_some, Option.map_some, Option.bind_some, SVal.findM_nil']
  | _, x, .field h r => by
    show TVal.delR c ((SVal.obsOpt x).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | struct fs =>
        simp only [Option.bind_some, Option.map_some, SVal.defaultOf_struct, SVal.findM_field',
          SFields.get_defaultOf, SVal.findM_nil']
  | _, x, .atF i r => by
    show TVal.delR c ((SVal.obsOpt x).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | fixed e =>
        simp only [Option.bind_some, Option.map_some, SVal.defaultOf_fixed, SVal.findM_atF',
          SVec.toList_defaultOf, List.getElem?_map, SVal.findM_nil']
        split
        · cases e.toList[i.toNat]? <;> rfl
        · rfl
  | _, x, .key k r => by
    show c.read (SVal.obsOpt x) (.key k r) = _
    rw [c.read_obsOpt]
    cases x with
    | none => rfl
    | some v => cases v; rw [Option.map_some, SVal.defaultOf_map]
  | _, none, @Path.at E _ i r => by
    have e : (SVal.obsOpt (none : Option (SVal (.ref (.array E))))).len .nil = 0 := rfl
    simp only [TVal.delR, e, Nat.not_lt_zero, and_false, if_false, c.read_obsOpt]
    rfl
  | _, some v, .at i r => by
    cases v with
    | array e sh hn =>
      rename_i n
      show (if 0 ≤ i ∧ i.toNat < n then
        TVal.delR c ((SVal.obsOpt (some (SVal.array e sh hn))).find (.at i .nil)) r
        else c.read (SVal.obsOpt (some (SVal.array e sh hn))) (.at i r)) = _
      simp only [Option.map_some, Option.bind_some, SVal.defaultOf_array]
      split
      · rename_i hi
        have hl : i.toNat < e.toList.length := by
          rw [SVec.length_toList]; exact hi.2
        rw [SVal.obsOpt_find, TVal.delR_obsOpt c _ r]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', hi.1, if_true, SList.toList_ofList,
          SVec.toList_nil, List.nil_append, SVec.toList_defaultOf, List.getElem?_append_left
            (show i.toNat < (e.toList.map SVal.defaultOf).length by rw [List.length_map]; exact hl),
          List.getElem?_map, List.getElem?_append_left hl, SVal.findM_nil']
        cases e.toList[i.toNat]? <;> rfl
      · rename_i hi
        rw [c.read_obsOpt]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', SList.toList_ofList, SVec.toList_nil,
          List.nil_append, SVec.toList_defaultOf]
        split
        · rename_i h0
          have hge : e.toList.length ≤ i.toNat := by
            rw [SVec.length_toList]; omega
          rw [List.getElem?_append_right (show (e.toList.map SVal.defaultOf).length ≤ i.toNat by
            rw [List.length_map]; exact hge), List.getElem?_append_right hge, List.length_map]
        · rfl

theorem TVal.stripR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x : Option (SVal U)) →
    (r : Path U V) → TVal.stripR c (SVal.obsOpt x) r = c.ofOpt ((x.map SVal.strip).bind (·.findM r))
  | _, none, .nil => by rw [TVal.stripR, c.read_obsOpt]; rfl
  | _, some v, .nil => by
    rw [TVal.stripR, c.read_obsOpt, Option.map_some, Option.bind_some, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.strip_top]
  | _, x, .field h r => by
    show TVal.stripR c ((SVal.obsOpt x).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | struct fs =>
        simp only [Option.bind_some, Option.map_some, SVal.strip_struct, SVal.findM_field',
          SFields.get_strip, SVal.findM_nil']
  | _, x, .atF i r => by
    show TVal.stripR c ((SVal.obsOpt x).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
    congr 1
    cases x with
    | none => rfl
    | some v =>
      cases v with
      | fixed e =>
        simp only [Option.bind_some, Option.map_some, SVal.strip_fixed, SVal.findM_atF',
          SVec.toList_strip, List.getElem?_map, SVal.findM_nil']
        split
        · cases e.toList[i.toNat]? <;> rfl
        · rfl
  | _, x, .key k r => by
    show c.read (SVal.obsOpt x) (.key k r) = _
    rw [c.read_obsOpt]
    cases x with
    | none => rfl
    | some v => cases v; rw [Option.map_some, SVal.strip_map]
  | _, none, @Path.at E _ i r => by
    have e : (SVal.obsOpt (none : Option (SVal (.ref (.array E))))).len .nil = 0 := rfl
    simp only [TVal.stripR, e, Nat.not_lt_zero, and_false, if_false]
    rfl
  | _, some v, .at i r => by
    cases v with
    | array e sh hn =>
      rename_i n
      show (if 0 ≤ i ∧ i.toNat < n then
        TVal.stripR c ((SVal.obsOpt (some (SVal.array e sh hn))).find (.at i .nil)) r
        else c.absent) = _
      simp only [Option.map_some, Option.bind_some, SVal.strip_array]
      split
      · rename_i hi
        have hl : i.toNat < e.toList.length := by
          rw [SVec.length_toList]; exact hi.2
        rw [SVal.obsOpt_find, TVal.stripR_obsOpt c _ r]
        congr 1
        simp only [Option.bind_some, SVal.findM_at', hi.1, if_true, SList.toList_nil,
          List.append_nil, SVec.toList_strip, List.getElem?_map, List.getElem?_append_left hl,
          SVal.findM_nil']
        cases e.toList[i.toNat]? <;> rfl
      · rename_i hi
        simp only [SVal.findM_at', SList.toList_nil, List.append_nil, SVec.toList_strip]
        split
        · rename_i h0
          have hge : (e.toList.map SVal.strip).length ≤ i.toNat := by
            rw [List.length_map, SVec.length_toList]; omega
          rw [List.getElem?_eq_none hge]
          rfl
        · rfl

/-- The slots of an array copy past its new length: the old elements
deleted, then the old slots past them. -/
theorem shadow_getElem?_lt {β : Type} (f : β → β) (oel osh : List β) {n i : Nat} (hi : n ≤ i)
    (him : i < oel.length) :
    ((oel.drop n).map f ++ osh.drop (n - oel.length))[i - n]? = (oel[i]?).map f := by
  have hl : i - n < ((oel.drop n).map f).length := by
    rw [List.length_map, List.length_drop]; omega
  rw [List.getElem?_append_left hl, List.getElem?_map, List.getElem?_drop,
    show n + (i - n) = i by omega]

theorem shadow_getElem?_ge {β : Type} (f : β → β) (oel osh : List β) {n i : Nat} (hi : n ≤ i)
    (him : oel.length ≤ i) :
    ((oel.drop n).map f ++ osh.drop (n - oel.length))[i - n]? = (oel ++ osh)[i]? := by
  have hl : ((oel.drop n).map f).length ≤ i - n := by
    rw [List.length_map, List.length_drop]; omega
  rw [List.getElem?_append_right hl, List.getElem?_drop, List.getElem?_append_right him,
    List.length_map, List.length_drop]
  congr 1
  omega

theorem TVal.ovR_obsOpt {V : Ty} {α : Type} (c : Comp V α) : {U : Ty} → (x y : Option (SVal U)) →
    (r : Path U V) → TVal.ovR c (SVal.obsOpt x) (SVal.obsOpt y) r =
      c.ofOpt ((SVal.overlayOpt x y).bind (·.findM r))
  | _, x, none, .nil => by rw [TVal.ovR, c.read_obsOpt]; cases x <;> rfl
  | _, none, some n, .nil => by
    rw [TVal.ovR, c.read_obsOpt, Option.bind_some, SVal.overlayOpt, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.strip_top]
  | _, some o, some n, .nil => by
    rw [TVal.ovR, c.read_obsOpt, Option.bind_some, SVal.overlayOpt, Option.bind_some,
      SVal.findM_nil', SVal.findM_nil', c.overlay_top]
  | _, x, y, .field h r => by
    show TVal.ovR c ((SVal.obsOpt x).find (.field h .nil)) ((SVal.obsOpt y).find (.field h .nil)) r = _
    rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
    congr 1
    cases y with
    | none => simp only [Option.bind_none, SVal.overlayOpt_none, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
    | some n =>
      cases n with
      | struct nfs =>
        cases x with
        | none =>
          simp only [Option.bind_none, Option.bind_some, SVal.findM_field_nil, SVal.findM_nil',
            SVal.overlayOpt_none_some, SVal.findM_field', SVal.strip_struct, SFields.get_strip, Option.bind_some_id, Option.map_some]
        | some o =>
          cases o with
          | struct ofs =>
            simp only [Option.bind_some, SVal.findM_field_nil, SVal.findM_nil',
              SVal.overlayOpt_some_some, SVal.findM_field', SVal.overlay_struct, SFields.get_overlay, Option.bind_some_id, Option.map_some]
  | _, x, y, .atF i r => by
    show TVal.ovR c ((SVal.obsOpt x).find (.atF i .nil)) ((SVal.obsOpt y).find (.atF i .nil)) r = _
    rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
    congr 1
    cases y with
    | none => simp only [Option.bind_none, SVal.overlayOpt_none, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
    | some n =>
      cases n with
      | fixed nel =>
        cases x with
        | none =>
          simp only [Option.bind_none, Option.bind_some, SVal.findM_atF_nil,
            SVal.overlayOpt_none_some, SVal.findM_atF', SVal.strip_fixed, SVec.toList_strip,
            List.getElem?_map, SVal.findM_nil', Option.bind_some_id, Option.map_some]
          by_cases h0 : 0 ≤ i
          · simp only [h0, if_true]
            cases nel.toList[i.toNat]? with
            | none => rfl
            | some w => rw [SVal.overlayOpt_none_some]; rfl
          · simp only [h0, if_false, SVal.overlayOpt_none, Option.bind_none]
        | some o =>
          cases o with
          | fixed oel =>
            simp only [Option.bind_some, SVal.findM_atF_nil, SVal.findM_atF', SVal.findM_nil',
              Option.bind_some_id, SVal.overlayOpt_some_some, SVal.overlay_fixed,
              SVec.getElem?_overlayOn, Option.map_some]
            by_cases h0 : 0 ≤ i
            · simp only [h0, if_true, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
            · simp only [h0, if_false, SVal.overlayOpt_none, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]; rfl
  | _, x, y, .key k r => by
    show (if (SVal.obsOpt y).has .nil then (if (SVal.obsOpt x).has .nil then
      c.read (SVal.obsOpt x) (.key k r) else c.read (SVal.obsOpt y) (.key k r)) else c.absent) = _
    simp only [SVal.obsOpt_has_nil, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
    cases y with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, if_false, Option.bind_none,
        SVal.overlayOpt_none, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
    | some n =>
      cases n with
      | map ne nd =>
        cases x with
        | none =>
          simp only [Option.isSome_some, Option.isSome_none, if_true, Bool.false_eq_true,
            if_false, c.read_obsOpt, SVal.overlayOpt_none_some, SVal.strip_map, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
        | some o =>
          cases o with
          | map oe od =>
            simp only [Option.isSome_some, if_true, c.read_obsOpt, SVal.overlayOpt_some_some,
              SVal.overlay_map, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
  | _, x, y, .at i r => by
    cases y with
    | none =>
      simp only [TVal.ovR, SVal.obsOpt_has_nil, Option.isSome_none, Bool.false_eq_true, if_false,
        Option.bind_none, SVal.overlayOpt_none, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
    | some n =>
      cases n with
      | array nel nsh hn =>
        rename_i nn
        have eh : (SVal.obsOpt (some (SVal.array nel nsh hn))).has .nil = true := rfl
        have el : (SVal.obsOpt (some (SVal.array nel nsh hn))).len .nil = nn := rfl
        simp only [TVal.ovR, eh, el, if_true, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
        split
        · rename_i hi
          have hl : i.toNat < nel.toList.length := by rw [SVec.length_toList]; exact hi.2
          rw [SVal.obsOpt_find, SVal.obsOpt_find, TVal.ovR_obsOpt c _ _ r]
          congr 1
          cases x with
          | none =>
            simp only [Option.bind_none, Option.bind_some, SVal.findM_at_nil, SVal.findM_at', hi.1,
              if_true, SVal.overlayOpt_none_some, SVal.strip_array, SList.toList_nil,
              List.append_nil, SVec.toList_strip, List.getElem?_map, List.getElem?_append_left hl, SVal.findM_nil', Option.bind_some_id, Option.map_some]
            cases nel.toList[i.toNat]? with
            | none => rfl
            | some w => rw [SVal.overlayOpt_none_some]; rfl
          | some o =>
            cases o with
            | array oel osh hm =>
              simp only [Option.bind_some, SVal.findM_at_nil, SVal.findM_at', hi.1, if_true,
                SVal.overlayOpt_some_some, SVal.overlay_array, SList.toList_ofList, SVal.findM_nil', Option.bind_some_id, Option.map_some]
              have hl' : i.toNat < (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length := by
                rw [SVec.length_toList]; exact hi.2
              rw [List.getElem?_append_left hl', SVec.getElem?_overlayOn,
                List.getElem?_append_left hl]
        · rename_i hi
          cases x with
          | none =>
            simp only [SVal.obsOpt_len_nil, SVal.lenOf, Nat.not_lt_zero, and_false, if_false, c.read_obsOpt, SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
            simp only [Option.bind_none, SVal.overlayOpt_none_some, Option.bind_some, SVal.strip_array,
              SVal.findM_at', SList.toList_nil, List.append_nil, SVec.toList_strip, SVal.findM_nil', Option.bind_some_id, Option.map_some]
            split
            · rename_i h0
              have hge : (nel.toList.map SVal.strip).length ≤ i.toNat := by
                rw [List.length_map, SVec.length_toList]; omega
              rw [List.getElem?_eq_none hge]; rfl
            · rfl
          | some o =>
            cases o with
            | array oel osh hm =>
              rename_i mm
              have el' : (SVal.obsOpt (some (SVal.array oel osh hm))).len .nil = mm := rfl
              simp only [el', SVal.findM_nil', Option.bind_some_id, Option.bind_some, Option.map_some]
              split
              · rename_i hi'
                rw [SVal.obsOpt_find, TVal.delR_obsOpt]
                congr 1
                have hge : nn ≤ i.toNat := by omega
                have hlt : i.toNat < oel.toList.length := by rw [SVec.length_toList]; exact hi'.2
                simp only [Option.bind_some, SVal.findM_at', hi'.1, if_true, SVal.findM_nil',
                  SVal.overlayOpt, SVal.overlay_array, SList.toList_ofList, Option.bind_some_id, Option.map_some]
                have hl' : (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length ≤ i.toNat := by
                  rw [SVec.length_toList]; exact hge
                rw [List.getElem?_append_right hl', SVec.length_toList, show nn - mm =
                  nn - oel.toList.length by rw [SVec.length_toList], shadow_getElem?_lt _ _ _ hge hlt,
                  List.getElem?_append_left hlt]
              · rename_i hi'
                rw [c.read_obsOpt]
                congr 1
                simp only [Option.bind_some, SVal.findM_at', SVal.overlayOpt, SVal.overlay_array,
                  SList.toList_ofList, SVal.findM_nil', Option.bind_some_id, Option.map_some]
                split
                · rename_i h0
                  have hge : nn ≤ i.toNat := by omega
                  have hge' : oel.toList.length ≤ i.toNat := by rw [SVec.length_toList]; omega
                  have hl' : (SVec.overlayOn (oel.toList ++ osh.toList) nel).toList.length ≤
                      i.toNat := by
                    rw [SVec.length_toList]; exact hge
                  rw [List.getElem?_append_right hl', SVec.length_toList, show nn - mm =
                    nn - oel.toList.length by rw [SVec.length_toList],
                    shadow_getElem?_ge _ _ _ hge hge']
                · rfl

theorem SVal.obs_defaultOf {U : Ty} (x : SVal U) : x.defaultOf.obs = x.obs.del :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, TVal.delR_obsOpt]; rfl

theorem SVal.obs_strip {U : Ty} (x : SVal U) : x.strip.obs = x.obs.strip :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, TVal.stripR_obsOpt]; rfl

theorem SVal.obs_overlay {U : Ty} (x y : SVal U) : (x.overlay y).obs = x.obs.overlay y.obs :=
  TVal.eq_ofComp fun c r => by
    rw [SVal.obs, c.read_obsOpt, SVal.obs, SVal.obs, TVal.ovR_obsOpt]; rfl

/-! ## Under a `select` -/

/-- A struct's members as the state variables of a contract: what
`select(s, r)` reads as a storage (`Storage (Contract.ofStruct s)`), and
where a path under it is rooted (`SRef (Contract.ofStruct s) T`), so the
storage's operations read it unchanged. -/
def Contract.ofStruct (s : Name) : Contract := { vars := structDef s }

/-- A path under `select(s, r)` as a path from the root `r`: its member
first. -/
def SRef.under {C : Contract} {s r : Name} {U : Ty} (q : SRef (Contract.ofStruct s) U)
    (h : C.rootType r = some (.ref (.struct s))) : SRef C U :=
  ⟨r, h, .field q.hroot q.path⟩

/-- The struct at the root `r` of `st`, as a storage of its members. -/
def Storage.selectT {C : Contract} {s r : Name} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) : Storage (Contract.ofStruct s) :=
  (SVal.view (st.get h) : SFields (structDef s))

/-- A location under `select(s, r)` as a location of the whole storage. -/
def SLoc.under {C : Contract} {s r : Name} {U : Ty} (h : C.rootType r = some (.ref (.struct s))) :
    SLoc (Contract.ofStruct s) U → SLoc C U
  | .ref q => .ref (q.under h)
  | .dangling V p => .dangling V p

/-- **`select(s, r)`**: the struct at the root `r`, read as a storage of its
members. -/
def Obs.select {C : Contract} {s r : Name} (o : TSto C) (h : C.rootType r = some (.ref (.struct s))) :
    TSto (Contract.ofStruct s) :=
  ⟨fun l => o.word (l.under h), fun l => o.len (l.under h), fun l => o.has (l.under h)⟩

theorem Storage.obs_selectT {C : Contract} {s r : Name} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) : (st.selectT h).obs = st.obs.select h := by
  have e : ∀ {U : Ty} (q : SRef (Contract.ofStruct s) U),
      (st.selectT h).get q.hroot = (SVal.view (st.get h) : SFields (structDef s)).get q.hroot := fun _ => rfl
  apply Obs.ext
  · intro P q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.word q.path = (st.get h).obs.word (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl
  · intro E q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.len q.path = (st.get h).obs.len (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl
  · intro V q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.has q.path = (st.get h).obs.has (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl

/-! ## The operations on a storage

Each is a `save` at the location it acts on (`Obs.save`), of what the
location holds with the operation made on it: so its frame is `save`'s. -/

namespace Path

/-- The path that goes nowhere. -/
def isNilB {T U : Ty} : Path T U → Bool
  | .nil => true
  | _ => false

end Path

namespace TVal

/-- The array with its live length set. -/
def setLen {E : Ty} (a : TVal (.ref (.array E))) (k : Nat) : TVal (.ref (.array E)) :=
  ⟨a.word, fun r => if r.isNilB then k else a.len r, a.has⟩

/-- A word as a stored value. -/
def ofWord {P : PrimTy} (x : P.Denote) : TVal (.prim P) := (SVal.prim x).obs

/-- **`push`** onto an array: `x` appended past the live elements. -/
def pushA {E : Ty} (a : TVal (.ref (.array E))) (x : TVal E) : TVal (.ref (.array E)) :=
  TVal.setLen (a.save (.at (a.len .nil) .nil) x) (a.len .nil + 1)

/-- One more live element: the slot past the end as it is (a word reset, a
missing slot at its default). -/
def extendA {E : Ty} (a : TVal (.ref (.array E))) : TVal (.ref (.array E)) :=
  if E.isPrimitive || !a.has (.at (a.len .nil) .nil) then a.pushA (SVal.dflt E).obs
  else a.setLen (a.len .nil + 1)

/-- **`pop`**: the last live element moved past the end, reset unless
`keep`; an empty array as it is. -/
def popA {E : Ty} (keep : Bool) (a : TVal (.ref (.array E))) : TVal (.ref (.array E)) :=
  if a.len .nil = 0 then a
  else if keep then a.setLen (a.len .nil - 1)
  else TVal.setLen (a.save (.at ((a.len .nil - 1 : Nat) : Int) .nil)
    (TVal.del (a.find (.at ((a.len .nil - 1 : Nat) : Int) .nil)))) (a.len .nil - 1)

end TVal

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- **`delAt`**: the value at `p` deleted. -/
def delAt (o : Obs L) {U : Ty} (p : L U) : Obs L := o.save p (TVal.del (o.find p))
/-- **`save`** of a copy: `v` laid over what is at `p` (a word replaces). -/
def copyTo (o : Obs L) {U : Ty} (p : L U) (v : TVal U) : Obs L :=
  o.save p (TVal.overlay (o.find p) v)
/-- **`push`**: `x` appended to the array at `p`. -/
def push (o : Obs L) {E : Ty} (p : L (.ref (.array E))) (x : TVal E) : Obs L :=
  o.save p (TVal.pushA (o.find p) x)
/-- One more live element at the array at `p` (`pushSlot`, `extend`). -/
def extend (o : Obs L) {E : Ty} (p : L (.ref (.array E))) : Obs L :=
  o.save p (TVal.extendA (o.find p))
/-- **`pop`** at `p`, the element reset unless `keep` (`shrink`). -/
def pop (o : Obs L) (keep : Bool) {E : Ty} (p : L (.ref (.array E))) : Obs L :=
  o.save p (TVal.popA keep (o.find p))

end Obs

/-! ### The bridge of the storage operations -/

theorem TVal.overlay_prim {P : PrimTy} (o n : TVal (.prim P)) : o.overlay n = n := by
  apply Obs.ext
  · intro P' r; cases r; rfl
  · intro E r; cases r
  · intro V r; cases r; rfl

theorem SVal.find_eq_findM' {T U : Ty} (v : SVal T) (p : Path T U) : v.find p = v.findM p :=
  SVal.find_eq_findM v p

theorem List.getElem?_snoc_tail {β : Type} (l : List β) (x : β) (sh : List β) {k : Nat}
    (hk : k ≠ l.length) : (l ++ [x] ++ sh.tail)[k]? = (l ++ sh)[k]? := by
  rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
  · rw [List.append_assoc, List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · obtain ⟨m, rfl⟩ : ∃ m, k = l.length + 1 + m := ⟨k - l.length - 1, by omega⟩
    rw [List.append_assoc, List.singleton_append, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), show l.length + 1 + m - l.length = m + 1 by omega,
      List.getElem?_cons_succ]
    cases sh with
    | nil => rfl
    | cons c rest => rw [List.tail_cons, List.getElem?_cons_succ]

/-- An array with `x` appended, as the Theory's `pushA`. -/
theorem SVal.obs_pushArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (x : SVal E) (sh' : List (SVal E)) (hsh : sh' = sh.toList.tail)
    (h' : (e.toList ++ [x]).length < 2 ^ 256) :
    (SVal.array (SVec.ofList (e.toList ++ [x])) (SList.ofList sh') h').obs =
      TVal.pushA (SVal.array e sh hn).obs x.obs := by
  have hl : e.toList.length = n := SVec.length_toList e
  have hf : ∀ {W : Ty} (j : Int) (r : Path E W),
      (SVal.array (SVec.ofList (e.toList ++ [x])) (SList.ofList sh') h').findM (.at j r) =
        if (n : Int) = j then x.findM r else (SVal.array e sh hn).findM (.at j r) := by
    intro W j r
    rw [SVal.findM_at', SVal.findM_at', SVec.toList_ofList, SList.toList_ofList, hsh]
    by_cases hj : (n : Int) = j
    · subst hj
      simp only [if_true, Int.natCast_nonneg, Int.toNat_natCast]
      rw [List.append_assoc, List.getElem?_append_right (by rw [hl]; exact Nat.le_refl _),
        hl, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero, Option.bind_some]
    · simp only [hj, if_false]
      split
      · rw [List.getElem?_snoc_tail _ _ _ (by rw [hl]; omega)]
      · rfl
  have el : (SVal.array e sh hn).obs.len .nil = n := rfl
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r =>
      show SVal.wordOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Obs.save, el, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro E' q
    cases q with
    | nil =>
      show (e.toList ++ [x]).length = _
      simp only [TVal.pushA, TVal.setLen, Path.isNilB, if_true, el, List.length_append, hl,
        List.length_singleton]
    | «at» j r =>
      show SVal.lenOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Path.isNilB, Bool.false_eq_true, if_false, Obs.save, el,
        ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r =>
      show Option.isSome _ = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Obs.save, el, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl

/-- An array with the same slots and a new live length. -/
theorem SVal.obs_array_setLen {E : Ty} {n n' : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (e' : SVec E n') (sh' : SList E) (hn' : n' < 2 ^ 256)
    (hs : e'.toList ++ sh'.toList = e.toList ++ sh.toList) :
    (SVal.array e' sh' hn').obs = TVal.setLen (SVal.array e sh hn).obs n' := by
  have hf : ∀ {W : Ty} (j : Int) (r : Path E W),
      (SVal.array e' sh' hn').findM (.at j r) = (SVal.array e sh hn).findM (.at j r) := by
    intro W j r; rw [SVal.findM_at', SVal.findM_at', hs]
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r => show SVal.wordOf (_ : Option _) = SVal.wordOf (_ : Option _); rw [Option.bind_some,
        Option.bind_some, hf]
  · intro E' q
    cases q with
    | nil => rfl
    | «at» j r => show SVal.lenOf (_ : Option _) = SVal.lenOf (_ : Option _); rw [Option.bind_some,
        Option.bind_some, hf]
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r => show Option.isSome _ = Option.isSome _; rw [Option.bind_some, Option.bind_some, hf]

/-- An array with one slot replaced and a new live length. -/
theorem SVal.obs_array_set {E : Ty} {n n' : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (e' : SVec E n') (sh' : SList E) (hn' : n' < 2 ^ 256) (k : Nat) (y : SVal E)
    (hk : k < (e.toList ++ sh.toList).length)
    (hs : e'.toList ++ sh'.toList = (e.toList ++ sh.toList).set k y) :
    (SVal.array e' sh' hn').obs =
      TVal.setLen ((SVal.array e sh hn).obs.save (.at (k : Int) .nil) y.obs) n' := by
  have hf : ∀ {W : Ty} (j : Int) (r : Path E W),
      (SVal.array e' sh' hn').findM (.at j r) =
        if (k : Int) = j then y.findM r else (SVal.array e sh hn).findM (.at j r) := by
    intro W j r
    rw [SVal.findM_at', SVal.findM_at', hs]
    by_cases hj : (k : Int) = j
    · subst hj
      simp only [if_true, Int.natCast_nonneg, Int.toNat_natCast, List.getElem?_set_self hk,
        Option.bind_some]
    · simp only [hj, if_false]
      split
      · rw [List.getElem?_set_ne (by omega)]
      · rfl
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r =>
      show SVal.wordOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Obs.save, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro E' q
    cases q with
    | nil => rfl
    | «at» j r =>
      show SVal.lenOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Path.isNilB, Bool.false_eq_true, if_false, Obs.save,
        ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r =>
      show Option.isSome _ = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Obs.save, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl

namespace Storage

variable {C : Contract}

theorem obs_find_some {U : Ty} {st : Storage C} {r : SRef C U} {w : SVal U} (h : st.find r = some w) :
    st.obs.find (.ref r) = w.obs := by
  rw [obs_find, h]; rfl

/-- **The bridge of a write**: a word saved, a value laid over what is there. -/
theorem obs_write {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.write r v = some st') : st'.obs = st.obs.copyTo (.ref r) v.obs := by
  unfold Storage.write at h
  split at h
  · rename_i hp
    rw [obs_save h, Obs.copyTo]
    cases U with
    | prim P => rw [TVal.overlay_prim]
    | ref R => simp only [SVal.isPrim, Ty.isPrimitive, Bool.false_eq_true] at hp
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨cur, hc, h⟩ := h
    rw [obs_save h, Obs.copyTo, obs_find_some hc, SVal.obs_overlay]

/-- **The bridge of a delete.** -/
theorem obs_delete {U : Ty} {st st' : Storage C} {r : SRef C U} (h : st.delete r = some st') :
    st'.obs = st.obs.delAt (.ref r) := by
  unfold Storage.delete at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨cur, hc, h⟩ := h
  rw [obs_save h, Obs.delAt, obs_find_some hc, SVal.obs_defaultOf]


/-- A push that returns: the array found, its slot, the element made of it,
and the save of the array with it appended. -/
theorem push_some {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (h : st.push r val = some st') :
    ∃ (n : Nat) (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (x : SVal E)
      (h' : (e.toList ++ [x]).length < 2 ^ 256),
      st.find r = some (.array e sh hn) ∧ val (pushSlot E sh.toList).1 = some x ∧
      st.save r (.array (SVec.ofList (e.toList ++ [x])) (.ofList (pushSlot E sh.toList).2) h') =
        some st' := by
  unfold Storage.push at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      cases hx : val (pushSlot _ sh.toList).1 with
      | none => simp only [hx, Option.bind_none, reduceCtorEq] at h
      | some x =>
        simp only [hx, Option.bind_some] at h
        split at h
        · exact ⟨_, e, sh, hn, x, _, rfl, hx, h⟩
        · cases h

theorem pushSlot_snd {E : Ty} (l : List (SVal E)) : (pushSlot E l).2 = l.tail := by
  cases l <;> rfl

/-- **The bridge of a push** of a value made of nothing of the slot. -/
theorem obs_push {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))} {x : SVal E}
    (h : st.push r (fun _ => some x) = some st') : st'.obs = st.obs.push (.ref r) x.obs := by
  obtain ⟨n, e, sh, hn, x', h', hf, hx, hs⟩ := push_some h
  cases hx
  rw [obs_save hs, Obs.push, obs_find_some hf,
    SVal.obs_pushArr e sh hn x _ (pushSlot_snd _) h']

/-- The slot past the end, appended as it is. -/
theorem obs_extendArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (h' : (e.toList ++ [(pushSlot E sh.toList).1]).length < 2 ^ 256) :
    (SVal.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
      (.ofList (pushSlot E sh.toList).2) h').obs = TVal.extendA (SVal.array e sh hn).obs := by
  rw [SVal.obs_pushArr e sh hn _ _ (pushSlot_snd _) h', TVal.extendA]
  have hl : e.toList.length = n := SVec.length_toList e
  have el : (SVal.array e sh hn).obs.len .nil = n := rfl
  cases hs : sh.toList with
  | nil =>
    have hh : (SVal.array e sh hn).obs.has (.at (n : Int) .nil) = false := by
      show Option.isSome ((some _).bind _) = false
      rw [Option.bind_some, SVal.findM_at', hs, List.append_nil]
      simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_eq_none (by omega)]; rfl
    simp only [el, hh, Bool.not_false, Bool.or_true, if_true]
    rfl
  | cons c rest =>
    have hh : (SVal.array e sh hn).obs.has (.at (n : Int) .nil) = true := by
      show Option.isSome ((some _).bind _) = true
      rw [Option.bind_some, SVal.findM_at', hs]
      simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_append_right (by omega), hl, Nat.sub_self, List.getElem?_cons_zero,
        Option.bind_some, SVal.findM_nil']; rfl
    simp only [el, hh, Bool.not_true, Bool.or_false]
    cases hp : E.isPrimitive with
    | true => simp only [pushSlot, hp, if_true]
    | false =>
      simp only [pushSlot, hp, Bool.false_eq_true, if_false]
      have hc : (SVal.array e sh hn).obs.find (.at (n : Int) .nil) = c.obs := by
        rw [SVal.obs_find, SVal.findM_at_nil, hs]
        simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast]
        rw [List.getElem?_append_right (by omega), hl, Nat.sub_self, List.getElem?_cons_zero]
        rfl
      rw [TVal.pushA, el, ← hc, Obs.save_find]

/-- **The bridge of `pushSlot`**: one more live element, the slot as it is. -/
theorem obs_push_slot {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    (h : st.push r some = some st') : st'.obs = st.obs.extend (.ref r) := by
  obtain ⟨n, e, sh, hn, x', h', hf, hx, hs⟩ := push_some h
  cases hx
  rw [obs_save hs, Obs.extend, obs_find_some hf, obs_extendArr e sh hn h']

/-- **The bridge of `extend`** (`pushPlace`). -/
theorem obs_pushPlace {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))} {k : Nat}
    (h : st.pushPlace r = some (st', k)) : st'.obs = st.obs.extend (.ref r) := by
  unfold Storage.pushPlace at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      split at h
      · rename_i h'
        cases hs : st.save r (SVal.array (SVec.ofList (e.toList ++ [(pushSlot _ sh.toList).1]))
            (SList.ofList (pushSlot _ sh.toList).2) (SVec.snoc_lt_bound e _ h')) with
        | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
        | some st₁ =>
          simp only [hs, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rw [obs_save hs, Obs.extend, obs_find_some hf, obs_extendArr]
      · cases h

/-- **The bridge of a pop**: the last element past the end, reset unless
`keep`. -/
theorem obs_pop {E : Ty} {st st' : Storage C} {keep : Bool} {r : SRef C (.ref (.array E))}
    (h : st.pop keep r = some st') : st'.obs = st.obs.pop keep (.ref r) := by
  unfold Storage.pop at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      rename_i n
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      split at h
      · cases h
      · rename_i last tl hrev
        rw [obs_save h, Obs.pop, obs_find_some hf]
        have hl : e.toList.length = n := SVec.length_toList e
        have hne : e.toList ≠ [] := fun he => by simp only [he, List.reverse_nil, reduceCtorEq] at hrev
        have he : e.toList = tl.reverse ++ [last] := by
          rw [← List.reverse_reverse e.toList, hrev, List.reverse_cons]
        have hlast : e.toList.dropLast ++ [last] = e.toList := by
          rw [he, List.dropLast_concat]
        have hpos : n ≠ 0 := by intro h0; rw [← hl] at h0; exact hne (List.eq_nil_of_length_eq_zero h0)
        have el : (SVal.array e sh hn).obs.len .nil = n := rfl
        have hdl : (e.toList.dropLast).length = n - 1 := by rw [List.length_dropLast, hl]
        simp only [TVal.popA, el, hpos, if_false]
        cases keep with
        | true =>
          simp only [if_true]
          congr 1
          have hx := SVal.obs_array_setLen e sh hn (SVec.ofList e.toList.dropLast)
            (SList.ofList (last :: sh.toList)) (by rw [hdl]; omega)
            (by rw [SVec.toList_ofList, SList.toList_ofList, ← List.singleton_append,
              ← List.append_assoc, hlast])
          exact hx.trans (congrArg _ hdl)
        | false =>
          simp only [Bool.false_eq_true, if_false]
          have hk : n - 1 < (e.toList ++ sh.toList).length := by
            rw [List.length_append, hl]; omega
          have hc : (SVal.array e sh hn).obs.find (.at ((n - 1 : Nat) : Int) .nil) = last.obs := by
            rw [SVal.obs_find, SVal.findM_at_nil]
            simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast]
            rw [List.getElem?_append_left (by rw [hl]; omega), ← hlast,
              List.getElem?_append_right (by omega), hdl, Nat.sub_self, List.getElem?_cons_zero]
            rfl
          rw [hc, ← SVal.obs_defaultOf]
          congr 1
          have hx := SVal.obs_array_set e sh hn (SVec.ofList e.toList.dropLast)
            (SList.ofList (last.defaultOf :: sh.toList)) (by rw [hdl]; omega) (n - 1) last.defaultOf hk
            (by rw [SVec.toList_ofList, SList.toList_ofList, show e.toList ++ sh.toList =
              e.toList.dropLast ++ (last :: sh.toList) by
                rw [← List.singleton_append, ← List.append_assoc, hlast],
              List.set_append_right _ _ (by omega), hdl, Nat.sub_self, List.set_cons_zero])
          exact hx.trans (congrArg _ hdl)

end Storage

end Solidity
