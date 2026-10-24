import Solidity.Semantics.Heap

/-!
# Observations: typed paths and values read below them

Typed paths, observations, storage locations, typed values read below a
path.

A piece of `Theory/Typed/Obs.lean`, whose docstring describes the whole.
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

/-- A path whose erasure extends another's, from one type, is the other
followed by a path. -/
theorem split_of_labels {T U W : Ty} (p : Path T U) (q : Path T W) {s : List Semantics.Selector}
    (h : q.labels = p.labels ++ s) : ∃ r : Path U W, q = p.append r ∧ r.labels = s := by
  induction p generalizing W with
  | nil =>
    simp only [Path.labels, List.nil_append] at h
    exact ⟨q, (Path.append_nil q).symm, h⟩
  | @field s₀ f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.labels, List.cons_append, reduceCtorEq] at h
    | @field _ f' T₂ _ hf' q =>
      simp only [Path.labels, List.cons_append, List.cons.injEq, Semantics.Selector.field.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_field hf p r).symm, hr⟩
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.labels, List.cons_append, reduceCtorEq] at h
    | «at» j q =>
      simp only [Path.labels, List.cons_append, List.cons.injEq, Semantics.Selector.idx.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_at _ p r).symm, hr⟩
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.labels, List.cons_append, reduceCtorEq] at h
    | atF j q =>
      simp only [Path.labels, List.cons_append, List.cons.injEq, Semantics.Selector.idx.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_atF _ p r).symm, hr⟩
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.labels, List.cons_append, reduceCtorEq] at h
    | key k' q =>
      simp only [Path.labels, List.cons_append, List.cons.injEq, Semantics.Selector.key.injEq] at h
      obtain ⟨hk, h⟩ := h
      obtain rfl : k' = k := eq_of_heq (Sigma.mk.inj hk).2
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_key _ p r).symm, hr⟩

/-- Where `q` does not go through `p`, the two part, or `q` stops above `p`. -/
theorem strip?_none : {T U W : Ty} → (p : Path T U) → (q : Path T W) → strip? p q = none →
    Diverges p q ∨ ∃ r : Path W U, r.labels ≠ [] ∧ p = q.append r
  | _, _, _, .nil, q, h => by simp only [strip?, reduceCtorEq] at h
  | _, _, _, .field hf p, .nil, _ => .inr ⟨.field hf p, by simp only [labels, ne_eq,
      reduceCtorEq, not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .at i p, .nil, _ => .inr ⟨.at i p, by simp only [labels, ne_eq, reduceCtorEq,
      not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .atF i p, .nil, _ => .inr ⟨.atF i p, by simp only [labels, ne_eq, reduceCtorEq,
      not_false_eq_true], (append_nil _).symm⟩
  | _, _, _, .key i p, .nil, _ => .inr ⟨.key i p, by simp only [labels, ne_eq, reduceCtorEq,
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

theorem save_word_below (o : Obs L) {U : Ty} (p : L U) {P : PrimTy} (r : Path U (.prim P))
    (v : TVal U) : (o.save p v).word (ObsLoc.app p r) = v.word r := by
  simp only [save, ObsLoc.strip?_app]

theorem save_word_same (o : Obs L) {P : PrimTy} (p : L (.prim P)) (v : TVal (.prim P)) :
    (o.save p v).word p = v.word .nil := by
  have e := save_word_below o p .nil v
  rwa [ObsLoc.app_nil] at e

theorem save_word_frame (o : Obs L) {U : Ty} {p : L U} {P : PrimTy} {q : L (.prim P)}
    (v : TVal U) (h : ObsLoc.strip? p q = none) : (o.save p v).word q = o.word q := by
  simp only [save, h]

theorem save_len_frame (o : Obs L) {U : Ty} {p : L U} {E : Ty} {q : L (.ref (.array E))}
    (v : TVal U) (h : ObsLoc.strip? p q = none) : (o.save p v).len q = o.len q := by
  simp only [save, h]

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
    · rename_i x0 _
      exact SVal.findM_append x0 p r
    · rfl
  | .fixed e, .atF i p, r => by
    rw [Path.append_atF]
    simp only [SVal.findM]
    split
    · rename_i x0 _
      exact SVal.findM_append x0 p r
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
    · rename_i x0 hx
      simp only [Option.bind_eq_bind]
      rw [SVal.saveM_append_eq x0 p r v]
      cases x0.findM p with
      | none => rfl
      | some y =>
        simp only [Option.bind_some]
        cases y.saveM r v with
        | none => rfl
        | some y' => simp only [Option.bind_some]
    · rfl
  | .fixed e, .atF i p, r, v => by
    rw [Path.append_atF]
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
        | some y' => simp only [Option.bind_some]
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
        | some y' => simp only [Option.bind_some]
    · rename_i hx
      simp only [Option.bind_eq_bind]
      rw [SVal.saveM_append_eq d p r v]
      cases d.findM p with
      | none => rfl
      | some y =>
        simp only [Option.bind_some]
        cases y.saveM r v with
        | none => rfl
        | some y' => simp only [Option.bind_some]

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
    · rename_i x0 hx
      obtain ⟨z, hz⟩ := SVal.saveM_of_findM x0 p h v
      exact ⟨_, by simp only [SVal.saveM, hx, hz, Option.bind_eq_bind,
        Option.bind_some]; rfl⟩
    · cases h
  | .fixed e, .atF i p, y, h, v => by
    simp only [SVal.findM] at h
    split at h
    · rename_i x0 hx
      obtain ⟨z, hz⟩ := SVal.saveM_of_findM x0 p h v
      exact ⟨_, by simp only [SVal.saveM, hx, hz, Option.bind_eq_bind,
        Option.bind_some]; rfl⟩
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
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]
      · simp only [reduceCtorEq] at h
  | @atF E U₁ n i p ih =>
    cases x with
    | fixed e =>
      simp only [Path.append_atF, SVal.saveM] at h
      split at h
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]
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
theorem SVal.saveM_at_n {E W : Ty} {y y' : SVal (.ref (.array E))} {i : PrimTy.uint.Denote} {r : Path E W}
    {v : SVal W} (h : y.saveM (.at i r) v = some y') :
    (SVal.view y' : ArrView E).n = (SVal.view y : ArrView E).n := by
  cases y with
  | array e sh hn =>
    rename_i n
    simp only [SVal.saveM] at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, -, rfl⟩ := h
      show (List.take n _).length = n
      rw [List.length_take, List.length_set, List.length_append, SVec.length_toList]
      omega
    · simp only [reduceCtorEq] at h

end Solidity
