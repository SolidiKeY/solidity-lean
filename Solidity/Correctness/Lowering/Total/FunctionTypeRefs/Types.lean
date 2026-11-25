import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Function-type reference tables: the Source type of a retained type

`rawSty` computes the Source type a retained `RawTy` stands for in a location,
from an explicit struct resolution `res` (written struct name to declaration
identity): the marked elementary type of a leaf name, the same nesting and
lengths, a storage mapping's key and value. It consults no Source typing
function. `rawSty_typed` connects it to `ReferenceDecode.rawType`: under
`Resolved` obligations for the names `res` answers, the spelled type name
elaborates to exactly that type and `RawRep` relates the two, both obtained from
`rawType_typed` (`rep_sty` identifies its witness with `rawSty`'s). `res` is a
parameter: discharging it against a unit's struct declarations is not done here.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeRefs

open Source (Syn STy DataLoc)
open ReferenceDecode (rawType rawElem rawNames rawKey rawKey_ok RawRep Resolved rawType_typed
  bind_ok)

/-- An explicit struct resolution: a written struct name's declaration identity. -/
abbrev Resolution := String → Option Source.DeclName

/-- A leaf name: its marked elementary type, else the struct `res` resolves it to. -/
def leafSty (res : Resolution) (loc : DataLoc) (s : String) : Option STy :=
  match rawElem s with
  | some e => some (e.ty loc)
  | none => (res s).map (.struct loc)

/-- A mapping key: a marked elementary type name, at its value type. -/
def keySty : RawTy → Option STy
  | .named k => (rawElem k).map (·.ty .memory)
  | _ => none

/-- The Source type of a type as read, in the location `loc`. -/
def rawSty (res : Resolution) : DataLoc → RawTy → Option STy
  | loc, .named s => leafSty res loc s
  | loc, .array T => (rawSty res loc T).map (.array loc · none)
  | loc, .fixed T n => if n = 0 then none else (rawSty res loc T).map (.array loc · (some n))
  | loc, .mapping K V =>
    if loc = .storage then
      (keySty K).bind fun κ => (rawSty res .storage V).map (.mapping κ)
    else none

variable {C : Contract} {E : Source.Env} {scope : Option String} {res : Resolution}

theorem leafSty_elem {loc : DataLoc} {s : String} {e : Source.Elem} (he : rawElem s = some e) :
    leafSty res loc s = some (e.ty loc) := by
  unfold leafSty
  rw [he]

theorem leafSty_struct {loc : DataLoc} {s : String} (he : rawElem s = none) :
    leafSty res loc s = (res s).map (.struct loc) := by
  unfold leafSty
  rw [he]

/-- A name resolves to at most one declaration identity. -/
theorem Resolved.unique {w : Name} {d d' : Source.DeclName} (h : Resolved E scope w d)
    (h' : Resolved E scope w d') : d = d' := by
  obtain ⟨decl, look, -, rfl⟩ := h
  obtain ⟨decl', look', -, rfl⟩ := h'
  cases look.symm.trans look'
  rfl

/-- `rawSty` answers only where `res` answers every struct name mentioned. -/
theorem rawSty_names : (T : RawTy) → (loc : DataLoc) → {τ : STy} → rawSty res loc T = some τ →
    ∀ s ∈ rawNames T, rawElem s = none → ∃ d, res s = some d
  | .named s, loc, τ, h, s', ms, he => by
    simp only [rawNames, List.mem_singleton] at ms
    subst ms
    simp only [rawSty, leafSty_struct he, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, -⟩ := h
    exact ⟨d, hd⟩
  | .array T, loc, τ, h, s, ms, he => by
    simp only [rawSty, Option.map_eq_some_iff] at h
    obtain ⟨τ', h, -⟩ := h
    exact rawSty_names T loc h s ms he
  | .fixed T n, loc, τ, h, s, ms, he => by
    simp only [rawSty] at h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨τ', h, -⟩ := h
      exact rawSty_names T loc h s ms he
  | .mapping K V, loc, τ, h, s, ms, he => by
    simp only [rawSty] at h
    split at h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨κ, -, τ', h, -⟩ := h
      exact rawSty_names V .storage h s ms he
    · cases h

/-- The represented type is `rawSty`'s, whenever `res` answers within `Resolved`. -/
theorem rep_sty (sound : ∀ s d, res s = some d → Resolved E scope s d) {loc : DataLoc}
    {T : RawTy} {τ' : STy} (rep : RawRep C E scope loc T τ') :
    ∀ {τ : STy}, rawSty res loc T = some τ → τ' = τ := by
  induction rep with
  | elem he =>
    intro τ h
    simp only [rawSty, leafSty_elem he, Option.some.injEq] at h
    exact h
  | struct he _ _ hd =>
    intro τ h
    simp only [rawSty, leafSty_struct he, Option.map_eq_some_iff] at h
    obtain ⟨d', hd', rfl⟩ := h
    rw [Resolved.unique hd (sound _ _ hd')]
  | array _ ih =>
    intro τ h
    simp only [rawSty, Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h
    rw [ih h]
  | fixed pos _ ih =>
    intro τ h
    simp only [rawSty, Nat.ne_of_gt pos, if_false, Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h
    rw [ih h]
  | mapping he _ ih =>
    intro τ h
    simp only [rawSty, keySty, if_true, he, Option.map_some, Option.bind_some,
      Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h
    rw [ih h]

/-- Where `res` answers every name `Resolved` does, the represented type is computed. -/
theorem rawSty_of_rep (complete : ∀ s d, Resolved E scope s d → res s = some d) {loc : DataLoc}
    {T : RawTy} {τ : STy} (rep : RawRep C E scope loc T τ) : rawSty res loc T = some τ := by
  induction rep with
  | elem he => simp only [rawSty, leafSty_elem he]
  | struct he _ _ hd => simp only [rawSty, leafSty_struct he, complete _ _ hd, Option.map_some]
  | array _ ih => simp only [rawSty, ih, Option.map_some]
  | fixed pos _ ih => simp only [rawSty, Nat.ne_of_gt pos, if_false, ih, Option.map_some]
  | mapping he _ ih =>
    simp only [rawSty, keySty, if_true, he, Option.bind_some, ih, Option.map_some]

/-- **A retained type's Source type.** A successful spelling at `loc` elaborates
to exactly the type `rawSty` computes, and represents the retained type. -/
theorem rawSty_typed (sound : ∀ s d, res s = some d → Resolved E scope s d) {loc : DataLoc}
    {T : RawTy} {t : Syn .typeName} {τ : STy} (ok : rawType C loc T = .ok t)
    (sty : rawSty res loc T = some τ) :
    t.tys E scope loc = some [τ] ∧ RawRep C E scope loc T τ := by
  obtain ⟨τ', typed, rep⟩ := rawType_typed (E := E) (scope := scope) T loc t ok fun s ms he =>
    let ⟨d, hd⟩ := rawSty_names T loc sty s ms he
    ⟨d, sound s d hd⟩
  cases rep_sty sound rep sty
  exact ⟨typed, rep⟩

/-- A spelling does not depend on the location: one that succeeds anywhere
succeeds in storage, the most permissive location, with the same type name. -/
theorem rawType_storage : (T : RawTy) → (loc : DataLoc) → {t : Syn .typeName} →
    rawType C loc T = .ok t → rawType C .storage T = .ok t
  | .named s, loc, t, h => by simpa only [rawType] using h
  | .array T, loc, t, h => by
    simp only [rawType, bind_ok] at h ⊢
    obtain ⟨t', ht, h⟩ := h
    exact ⟨t', rawType_storage T loc ht, h⟩
  | .fixed T n, loc, t, h => by
    simp only [rawType] at h ⊢
    split at h
    · cases h
    · rename_i pos
      rw [if_neg pos]
      simp only [bind_ok] at h ⊢
      obtain ⟨t', ht, h⟩ := h
      exact ⟨t', rawType_storage T loc ht, h⟩
  | .mapping K V, loc, t, h => by
    simp only [rawType] at h
    split at h
    · rename_i hloc
      subst hloc
      simpa only [rawType, if_true] using h
    · cases h

/-- Spellings of one type at two locations are the same type name. -/
theorem rawType_loc {T : RawTy} {loc loc' : DataLoc} {t t' : Syn .typeName}
    (h : rawType C loc T = .ok t) (h' : rawType C loc' T = .ok t') : t = t' :=
  Except.ok.inj ((rawType_storage T loc h).symm.trans (rawType_storage T loc' h'))

end Solidity.Correctness.Lowering.Total.FunctionTypeRefs
