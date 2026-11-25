import Solidity.Correctness.Lowering.Total.FunctionTypeDecode
import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Loop lowering: typed reference tables for retained function signatures

`FunctionTypeDecode` leaves open its table `Refs` and the typing facts. Both are
constructed here from retained data: a `Table` of `Entry`s (a component's type
as read, `RawTy`, and its recorded location) of one contract `C` and scope.
`spell` is `spellFnTy`'s spelling of a type that is no function type (by
construction, not proved: a partial macro); `Entry.key` appends the location
word, as `Entry.part` is spelled. `refs` spells an answered component by
`ReferenceDecode.rawType`; `refTys` gives its Source type by `rawSty`,
structurally from an explicit struct resolution `res`, consulting no Source
typing. `refsTyped` proves `RefsTyped` from `Resolved` obligations on what `res`
answers, through `rawType_typed` and `RawRep` (`rawSty_typed`); `value_rep`,
`located_rep`: a typed lookup is a retained entry, coherently spelled, at its
recorded location, whose spelling elaborates to the type representing it.

Spellings do not determine entries (`.named "uint[]"`, `.array (.named "uint")`;
a name `Tmemory`, `T` at `memory`) and no lookup picks: a key is answered when
every entry so spelled is the same entry, a base when all its located entries
have one type and no other entry is spelled as it with a location word
(`base_iff`, `base_conflict`). A component with no location is typed in `memory`
(`RefsTyped.value`). `Refs.located` takes no location: a coherent base has one
type name (`rawType_storage`) once a recorded location spells it; only `refTys`
is per location and carries meaning.

Outstanding, not excluded: an entry `rawType` refuses at its location (enum,
`bytes`/`string`, function-type or member names, a key, a mapping outside
storage, a zero length) is listed by `outstanding` with its `RawError` and has
no type there. Unlisted and untyped: conflicting spellings, struct names `res`
does not answer, an entry with no location spelled as an elementary name or
with a location word (the reader never asks for it). `address payable` stays
`address`, as retained. Open, for the original decoder: the unit's table, `res`
and its `Resolved` facts, annotations, frames, function-index binding,
integration, simulation.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeRefs

open Source (Syn STy DataLoc)
open FunctionTypeDecode (Part Parts Ann Refs RefTys RefsTyped locName)
open ReferenceDecode (rawType rawElem rawNames RawRep RawError Resolved rawType_typed bind_ok)

deriving instance DecidableEq for RawTy

/-- A component type's spelling inside a function type (`spellFnTy`). -/
def spell : RawTy → String
  | .named s => s
  | .mapping k v => "mapping(" ++ spell k ++ "=>" ++ spell v ++ ")"
  | .array t => spell t ++ "[]"
  | .fixed t n => spell t ++ "[" ++ toString n ++ "]"

/-- A retained component: its type as read and its recorded location. -/
structure Entry where
  ty : RawTy
  loc : Option DataLoc
  deriving DecidableEq, Repr
/-- The component spelling: the type, then the location word, no separator. -/
def Entry.key (e : Entry) : String :=
  match e.loc with
  | none => spell e.ty
  | some l => spell e.ty ++ locName l
/-- The tree component an entry answers for. -/
def Entry.part (e : Entry) : Part Ann :=
  match e.loc with
  | none => .named (spell e.ty)
  | some l => .located (spell e.ty) l

/-- An entry's key is its component's spelling; the location is kept. -/
theorem Entry.part_spell (e : Entry) : e.part.spell = e.key ∧ e.part.loc = e.loc := by
  cases e with | mk T l => cases l <;> exact ⟨rfl, rfl⟩

/-- The common value of a list: none for the empty list or on any disagreement. -/
def agree {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | a :: l => if l.all (· = a) then some a else none

theorem agree_iff {α : Type} [DecidableEq α] {l : List α} {a : α} :
    agree l = some a ↔ a ∈ l ∧ ∀ x ∈ l, x = a := by
  cases l with
  | nil => simp [agree]
  | cons b l =>
    simp only [agree, List.all_eq_true, decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h; split at h <;> cases h; exact ⟨.inl rfl, rfl, by assumption⟩
    · rintro ⟨-, rfl, all⟩; rw [if_pos all]

/-- The retained components of one contract and scope; repetitions allowed. -/
abbrev Table := List Entry

/-- No entry but `T` at `l` is spelled as the base `b` with the word of `l`. -/
abbrev BoundaryFree (tbl : Table) (b : String) (T : RawTy) : Prop :=
  ∀ e ∈ tbl, ∀ l ∈ [DataLoc.memory, .storage, .calldata], e.key = b ++ locName l → e = ⟨T, some l⟩

/-- The one type of the located entries with base spelling `b`, boundary unambiguous. -/
def Table.base (tbl : Table) (b : String) : Option RawTy :=
  (agree ((tbl.filter fun e => e.loc.isSome ∧ spell e.ty = b).map (·.ty))).bind fun T =>
    if BoundaryFree tbl b T then some T else none
/-- The type retained with no location as `c`, when every entry spelled `c` is that entry. -/
def Table.value (tbl : Table) (c : String) : Option RawTy :=
  match agree (tbl.filter (·.key = c)) with
  | some ⟨T, none⟩ => some T
  | _ => none
/-- The type retained for the base `b` at the recorded location `l`. -/
def Table.located (tbl : Table) (b : String) (l : DataLoc) : Option RawTy :=
  (tbl.base b).bind fun T => if (⟨T, some l⟩ : Entry) ∈ tbl then some T else none

variable {tbl : Table}

/-- A base is answered by the type of every located entry so spelled, at any location. -/
theorem base_iff {b : String} {T : RawTy} :
    tbl.base b = some T ↔ (∃ l, ⟨T, some l⟩ ∈ tbl) ∧ spell T = b ∧
      (∀ e ∈ tbl, e.loc.isSome → spell e.ty = b → e.ty = T) ∧ BoundaryFree tbl b T := by
  simp only [Table.base, Option.bind_eq_some_iff, agree_iff, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨T₀, ⟨⟨⟨T', l⟩, ⟨m, isLoc, sp⟩, rfl⟩, all⟩, h⟩
    split at h <;> cases h
    cases l with
    | none => cases isLoc
    | some l =>
      exact ⟨⟨l, m⟩, sp, fun e me le se => all _ ⟨e, ⟨me, le, se⟩, rfl⟩, by assumption⟩
  · rintro ⟨⟨l, m⟩, sp, all, free⟩
    exact ⟨T, ⟨⟨_, ⟨m, rfl, sp⟩, rfl⟩, fun T' ⟨e, h, eq⟩ => eq ▸ all e h.1 h.2.1 h.2.2⟩,
      by rw [if_pos free]⟩

/-- Located entries of one base spelling and different types, at any locations: no answer. -/
theorem base_conflict {T T' : RawTy} {l l' : DataLoc} (m : ⟨T, some l⟩ ∈ tbl)
    (m' : ⟨T', some l'⟩ ∈ tbl) (sp : spell T' = spell T) (ne : T ≠ T') :
    tbl.base (spell T) = none := by
  cases h : tbl.base (spell T) with
  | none => rfl
  | some x =>
    have all := (base_iff.1 h).2.2.1
    exact (ne ((all _ m rfl rfl).trans (all _ m' rfl sp).symm)).elim

/-- A value lookup is a retained entry with no location, the only one so spelled. -/
theorem value_iff {c : String} {T : RawTy} : tbl.value c = some T ↔
    ⟨T, none⟩ ∈ tbl ∧ spell T = c ∧ ∀ e ∈ tbl, e.key = c → e = ⟨T, none⟩ := by
  have key : agree (tbl.filter (·.key = c)) = some ⟨T, none⟩ ↔
      ⟨T, none⟩ ∈ tbl ∧ spell T = c ∧ ∀ e ∈ tbl, e.key = c → e = ⟨T, none⟩ := by
    simp only [agree_iff, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨⟨m, k⟩, all⟩ => ⟨m, k, fun e me ke => all e ⟨me, ke⟩⟩,
      fun ⟨m, k, all⟩ => ⟨⟨m, k⟩, fun e ⟨me, ke⟩ => all e me ke⟩⟩
  rw [← key]; unfold Table.value
  split
  · rename_i T' eq; simp [eq]
  · rename_i ne; exact ⟨fun h => (nomatch h), fun h => (ne T h).elim⟩

theorem located_iff {b : String} {l : DataLoc} {T : RawTy} :
    tbl.located b l = some T ↔ tbl.base b = some T ∧ ⟨T, some l⟩ ∈ tbl := by
  simp only [Table.located, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨T', hb, h⟩; split at h <;> cases h; exact ⟨hb, by assumption⟩
  · exact fun ⟨hb, he⟩ => ⟨T, hb, by rw [if_pos he]⟩
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
    if loc = .storage then (keySty K).bind fun κ => (rawSty res .storage V).map (.mapping κ)
    else none

variable {C : Contract} {E : Source.Env} {scope : Option String} {res : Resolution}
theorem leafSty_elem {loc : DataLoc} {s : String} {e : Source.Elem} (he : rawElem s = some e) :
    leafSty res loc s = some (e.ty loc) := by unfold leafSty; rw [he]
theorem leafSty_struct {loc : DataLoc} {s : String} (he : rawElem s = none) :
    leafSty res loc s = (res s).map (.struct loc) := by unfold leafSty; rw [he]

/-- `rawSty` answers only where `res` answers every struct name mentioned. -/
theorem rawSty_names : (T : RawTy) → (loc : DataLoc) → {τ : STy} →
    rawSty res loc T = some τ → ∀ s ∈ rawNames T, rawElem s = none → ∃ d, res s = some d
  | .named s, loc, τ, h, s', ms, he => by
    cases List.mem_singleton.1 ms
    simp only [rawSty, leafSty_struct he, Option.map_eq_some_iff] at h
    exact ⟨_, h.choose_spec.1⟩
  | .array T, loc, τ, h, s, ms, he => by
    simp only [rawSty, Option.map_eq_some_iff] at h
    exact rawSty_names T loc h.choose_spec.1 s ms he
  | .fixed T n, loc, τ, h, s, ms, he => by
    simp only [rawSty] at h
    split at h; · cases h
    simp only [Option.map_eq_some_iff] at h
    exact rawSty_names T loc h.choose_spec.1 s ms he
  | .mapping K V, loc, τ, h, s, ms, he => by
    simp only [rawSty] at h
    split at h <;> simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, reduceCtorEq] at h
    obtain ⟨κ, -, τ', h, -⟩ := h
    exact rawSty_names V .storage h s ms he

/-- The represented type is `rawSty`'s, whenever `res` answers within `Resolved`. -/
theorem rep_sty (sound : ∀ s d, res s = some d → Resolved E scope s d) {loc : DataLoc}
    {T : RawTy} {τ' : STy} (rep : RawRep C E scope loc T τ') :
    ∀ {τ : STy}, rawSty res loc T = some τ → τ' = τ := by
  induction rep with
  | elem he => exact fun h => by simpa only [rawSty, leafSty_elem he, Option.some.injEq] using h
  | struct he _ _ hd =>
    intro τ h
    simp only [rawSty, leafSty_struct he, Option.map_eq_some_iff] at h
    obtain ⟨d', hd', rfl⟩ := h
    obtain ⟨decl, look, -, rfl⟩ := hd
    obtain ⟨decl', look', -, rfl⟩ := sound _ _ hd'
    cases look.symm.trans look'; rfl
  | array _ ih =>
    intro τ h
    simp only [rawSty, Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h; rw [ih h]
  | fixed pos _ ih =>
    intro τ h
    simp only [rawSty, Nat.ne_of_gt pos, if_false, Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h; rw [ih h]
  | mapping he _ ih =>
    intro τ h
    simp only [rawSty, keySty, if_true, he, Option.map_some, Option.bind_some,
      Option.map_eq_some_iff] at h
    obtain ⟨τ₀, h, rfl⟩ := h; rw [ih h]

/-- **A retained type's Source type**: its spelling elaborates to it, and it represents it. -/
theorem rawSty_typed (sound : ∀ s d, res s = some d → Resolved E scope s d) {loc : DataLoc}
    {T : RawTy} {t : Syn .typeName} {τ : STy} (ok : rawType C loc T = .ok t)
    (sty : rawSty res loc T = some τ) :
    t.tys E scope loc = some [τ] ∧ RawRep C E scope loc T τ := by
  obtain ⟨τ', typed, rep⟩ := rawType_typed (E := E) (scope := scope) T loc t ok fun s ms he =>
    let ⟨d, hd⟩ := rawSty_names T loc sty s ms he
    ⟨d, sound s d hd⟩
  cases rep_sty sound rep sty
  exact ⟨typed, rep⟩

/-- A spelling that succeeds anywhere succeeds in storage, with the same type name. -/
theorem rawType_storage : (T : RawTy) → (loc : DataLoc) → {t : Syn .typeName} →
    rawType C loc T = .ok t → rawType C .storage T = .ok t
  | .named s, loc, t, h => by simpa only [rawType] using h
  | .array T, loc, t, h => by
    simp only [rawType, bind_ok] at h ⊢
    exact h.imp fun t' h => ⟨rawType_storage T loc h.1, h.2⟩
  | .fixed T n, loc, t, h => by
    simp only [rawType] at h ⊢
    split at h; · cases h
    rename_i pos; rw [if_neg pos]
    simp only [bind_ok] at h ⊢
    exact h.imp fun t' h => ⟨rawType_storage T loc h.1, h.2⟩
  | .mapping K V, loc, t, h => by
    simp only [rawType] at h
    split at h <;> try cases h
    rename_i hloc; subst hloc
    simpa only [rawType, if_true] using h

/-- **The reference table of retained components.** A component with no
location is spelled in `memory`; a located base by its one type, once a recorded
location spells it (in storage, the same type name: `rawType_storage`). -/
def refs (C : Contract) (tbl : Table) : Refs where
  value c := (tbl.value c).bind fun T => (rawType C .memory T).toOption
  located b := (tbl.base b).bind fun T =>
    if [DataLoc.memory, .storage, .calldata].any fun l =>
      (⟨T, some l⟩ : Entry) ∈ tbl ∧ (rawType C l T).toOption.isSome
    then (rawType C .storage T).toOption else none

/-- **The Source types of the retained components**, per recorded location. -/
def refTys (C : Contract) (res : Resolution) (tbl : Table) : RefTys where
  value c := (tbl.value c).bind fun T =>
    (rawType C .memory T).toOption.bind fun _ => rawSty res .memory T
  located b l := (tbl.located b l).bind fun T =>
    (rawType C l T).toOption.bind fun _ => rawSty res l T

/-- The entries `rawType` refuses at their location, each with its reason. -/
def outstanding (C : Contract) (tbl : Table) : List (Entry × RawError) :=
  tbl.filterMap fun e =>
    match rawType C (e.loc.getD .memory) e.ty with
    | .error err => some (e, err)
    | .ok _ => none
theorem toOption_iff {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

/-- **A typed component with no location**: a retained entry, the only one so
spelled, whose spelling elaborates in `memory` to the type representing it. -/
theorem value_rep (sound : ∀ s d, res s = some d → Resolved E scope s d) {c : String} {τ : STy}
    (h : (refTys C res tbl).value c = some τ) :
    ∃ T t, (⟨T, none⟩ ∈ tbl ∧ spell T = c ∧ ∀ e ∈ tbl, e.key = c → e = ⟨T, none⟩) ∧
      (refs C tbl).value c = some t ∧ rawType C .memory T = .ok t ∧
      t.tys E scope .memory = some [τ] ∧ RawRep C E scope .memory T τ := by
  simp only [refTys, refs, Option.bind_eq_some_iff, toOption_iff] at h ⊢
  obtain ⟨T, hT, t, ok, sty⟩ := h
  obtain ⟨typed, rep⟩ := rawSty_typed sound ok sty
  exact ⟨T, t, value_iff.1 hT, ⟨T, hT, ok⟩, ok, typed, rep⟩

/-- **A typed located component**: a retained entry at that very location, of
the one type of its base, whose spelling (the table's) elaborates there to the
type representing it. -/
theorem located_rep (sound : ∀ s d, res s = some d → Resolved E scope s d) {b : String}
    {l : DataLoc} {τ : STy} (h : (refTys C res tbl).located b l = some τ) :
    ∃ T t, (⟨T, some l⟩ ∈ tbl ∧ spell T = b ∧ BoundaryFree tbl b T ∧
        ∀ e ∈ tbl, e.loc.isSome → spell e.ty = b → e.ty = T) ∧
      (refs C tbl).located b = some t ∧ rawType C l T = .ok t ∧
      t.tys E scope l = some [τ] ∧ RawRep C E scope l T τ := by
  simp only [refTys, Option.bind_eq_some_iff, toOption_iff] at h
  obtain ⟨T, hT, t, ok, sty⟩ := h
  obtain ⟨typed, rep⟩ := rawSty_typed sound ok sty
  obtain ⟨hb, m⟩ := located_iff.1 hT
  refine ⟨T, t, ⟨m, (base_iff.1 hb).2.1, (base_iff.1 hb).2.2.2, (base_iff.1 hb).2.2.1⟩, ?_, ok,
    typed, rep⟩
  simp only [refs, hb, Option.bind_some]
  rw [if_pos (List.any_eq_true.2 ⟨l, by cases l <;> simp, by simp [m, ok, Except.toOption]⟩),
    rawType_storage T l ok]
  rfl

/-- **The typing facts of the constructed tables**, from the resolution obligations
alone: each struct name `res` answers resolves in `E` to the declaration `res` gives. -/
theorem refsTyped (sound : ∀ s d, res s = some d → Resolved E scope s d) :
    RefsTyped E scope (refs C tbl) (refTys C res tbl) where
  value hT hτ := by
    obtain ⟨_, t, -, ht, -, typed, -⟩ := value_rep sound hτ
    cases hT.symm.trans ht; exact typed
  located hT hτ := by
    obtain ⟨_, t, -, ht, -, typed, -⟩ := located_rep sound hτ
    cases hT.symm.trans ht; exact typed

/-- Each entry is spelled by `rawType` at its location or listed with its reason. -/
theorem read_or_outstanding {e : Entry} (m : e ∈ tbl) :
    (∃ t, rawType C (e.loc.getD .memory) e.ty = .ok t) ∨
      ∃ err, (e, err) ∈ outstanding C tbl := by
  cases h : rawType C (e.loc.getD .memory) e.ty with
  | ok t => exact .inl ⟨t, rfl⟩
  | error err => exact .inr ⟨err, List.mem_filterMap.2 ⟨e, m, by rw [h]⟩⟩

/-- A located entry `rawType` refuses has no type at its own location. -/
theorem outstanding_untyped {T : RawTy} {l : DataLoc} {err : RawError} {b : String}
    (h : rawType C l T = .error err) (hT : tbl.located b l = some T) :
    (refTys C res tbl).located b l = none := by
  simp only [refTys, hT, h, Option.bind_some, Except.toOption, Option.bind_none]

/-- **`fnType_ty` at the constructed tables**, annotations supplied by the caller
(`Part.typeName_tys` and `Parts.params_tys` apply to `refsTyped` likewise). -/
theorem fnType_ty (sound : ∀ s d, res s = some d → Resolved E scope s d) (ext : Bool) (a : Ann)
    (ps rs : Parts Ann) {T : Syn .typeName} {πs ρs : List STy} (loc : DataLoc)
    (hT : (Part.fn ext a ps rs).typeName (refs C tbl) = some T)
    (hπ : ps.stys (refTys C res tbl) = some πs) (hρ : rs.stys (refTys C res tbl) = some ρs) :
    (∃ P R, ps.params (refs C tbl) = some P ∧ rs.params (refs C tbl) = some R ∧
      T = .fnType P (a.vis ext) a.mutability R ∧
      P.tys E scope .memory = some πs ∧ R.tys E scope .memory = some ρs) ∧
    T.ty E scope loc = some (.fn ext πs ρs a.mutability) :=
  FunctionTypeDecode.fnType_ty (refsTyped sound) ext a ps rs loc hT hπ hρ

end Solidity.Correctness.Lowering.Total.FunctionTypeRefs
