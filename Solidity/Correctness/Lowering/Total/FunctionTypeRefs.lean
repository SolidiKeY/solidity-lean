import Solidity.Correctness.Lowering.Total.FunctionTypeRefs.Table
import Solidity.Correctness.Lowering.Total.FunctionTypeRefs.Types

/-!
# Loop lowering: typed reference tables for retained function signatures

`FunctionTypeDecode` reads a retained signature as a tree and leaves open the
table `Refs` of the components it does not read and their typing facts. Here
both are constructed from retained data: a `Table` of `Entry`s (a component's
type as read and its recorded location, `FunctionTypeRefs/Table.lean`) and the
contract `C`. `refs C tbl` spells each answered component by
`ReferenceDecode.rawType`; `refTys C res tbl` gives its Source type by `rawSty`
(`FunctionTypeRefs/Types.lean`) from an explicit struct resolution `res`.
`refsTyped` proves `FunctionTypeDecode.RefsTyped` from `ReferenceDecode.Resolved`
obligations on what `res` answers, through `rawType_typed`; `value_rep` and
`located_rep` state what a successful lookup is: a retained entry, uniquely
spelled, at the recorded location, whose spelling elaborates to the type and
`RawRep`-represents it. `part_tys`, `params_tys` and `fnType_ty` are the
existing interfaces at these tables, annotations supplied by the caller.

A component without a location is typed in `memory`, as `RefsTyped.value` and
`Syn.tys` on a parameter without one fix it. A located base has one type name
at every location (`rawType_loc`) and one Source type per recorded location:
`uint[]` at `memory` and at `storage` are different types and both are kept.

Outstanding, not excluded: an entry `rawType` refuses (an enum, `bytes`/`string`,
function-type or member-spelling name, an unsupported key, a mapping outside
storage, a zero length) is listed with its `RawError` by `outstanding`
(`read_or_outstanding`: every entry is spelled or listed) and answered by no
lookup; so are conflicting spellings. `address payable` stays `address`, as
retained. A struct name `res` does not answer has no type here.

Open, for the original decoder: that a unit's `Table` holds the components of
its signatures (`spell` against `spellFnTy` is by construction, not proved:
`spellFnTy` is a partial macro), `res` and its `Resolved` facts from the struct
declarations, the annotations, frame correspondence, function-index binding,
unit integration, inference completeness, simulation.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeRefs

open Source (Syn STy DataLoc)
open FunctionTypeDecode (Part Parts Ann Refs RefTys RefsTyped locName)
open ReferenceDecode (rawType RawRep RawError Resolved)

theorem toOption_iff {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

/-- The spelled type name of the base `b` at the recorded location `l`. -/
def Table.readAt (C : Contract) (tbl : Table) (b : String) (l : DataLoc) :
    Option (Syn .typeName) :=
  (tbl.located b l).bind fun T => (rawType C l T).toOption

/-- **The reference table of retained components.** A component with no
location is spelled in `memory`; a located base by its spelling at a recorded
location (all of them agree, `readAt_agree`). -/
def refs (C : Contract) (tbl : Table) : Refs where
  value c := (tbl.value c).bind fun T => (rawType C .memory T).toOption
  located b :=
    match tbl.readAt C b .memory, tbl.readAt C b .storage with
    | some t, _ => some t
    | none, some t => some t
    | none, none => tbl.readAt C b .calldata

/-- **The Source types of the retained components**, a located one at each
recorded location where it is spelled. -/
def refTys (C : Contract) (res : Resolution) (tbl : Table) : RefTys where
  value c := (tbl.value c).bind fun T =>
    (rawType C .memory T).toOption.bind fun _ => rawSty res .memory T
  located b l := (tbl.located b l).bind fun T =>
    (rawType C l T).toOption.bind fun _ => rawSty res l T

/-- The entries `rawType` refuses, each with its reason: outstanding obligations. -/
def outstanding (C : Contract) (tbl : Table) : List (Entry × RawError) :=
  tbl.filterMap fun e =>
    match rawType C (e.loc.getD .memory) e.ty with
    | .error err => some (e, err)
    | .ok _ => none

variable {C : Contract} {tbl : Table} {res : Resolution} {E : Source.Env} {scope : Option String}

/-! ## Lookups are retained entries -/

theorem refs_value_iff {c : String} {t : Syn .typeName} :
    (refs C tbl).value c = some t ↔ ∃ T, tbl.value c = some T ∧ rawType C .memory T = .ok t := by
  simp only [refs, Option.bind_eq_some_iff, toOption_iff]

theorem readAt_iff {b : String} {l : DataLoc} {t : Syn .typeName} :
    tbl.readAt C b l = some t ↔ ∃ T, tbl.located b l = some T ∧ rawType C l T = .ok t := by
  simp only [Table.readAt, Option.bind_eq_some_iff, toOption_iff]

/-- The spellings of one base at its recorded locations are one type name. -/
theorem readAt_agree {b : String} {l l' : DataLoc} {t t' : Syn .typeName}
    (h : tbl.readAt C b l = some t) (h' : tbl.readAt C b l' = some t') : t = t' := by
  obtain ⟨T, hT, ok⟩ := readAt_iff.1 h
  obtain ⟨T', hT', ok'⟩ := readAt_iff.1 h'
  cases located_agree hT hT'
  exact rawType_loc ok ok'

/-- A located base is answered exactly by its spelling at a recorded location. -/
theorem refs_located_iff {b : String} {t : Syn .typeName} :
    (refs C tbl).located b = some t ↔ ∃ l, tbl.readAt C b l = some t := by
  simp only [refs]
  constructor
  · intro h
    split at h
    · cases h; exact ⟨.memory, by assumption⟩
    · cases h; exact ⟨.storage, by assumption⟩
    · exact ⟨.calldata, h⟩
  · rintro ⟨l, h⟩
    split
    · rename_i t' _ hm; rw [readAt_agree hm h]
    · rename_i t' _ hs; rw [readAt_agree hs h]
    · rename_i hm hs
      cases l
      · rw [hm] at h; cases h
      · rw [hs] at h; cases h
      · exact h

theorem refTys_value_iff {c : String} {τ : STy} :
    (refTys C res tbl).value c = some τ ↔ ∃ T t, tbl.value c = some T ∧
      rawType C .memory T = .ok t ∧ rawSty res .memory T = some τ := by
  simp only [refTys, Option.bind_eq_some_iff, toOption_iff]
  exact ⟨fun ⟨T, hT, t, ok, sty⟩ => ⟨T, t, hT, ok, sty⟩,
    fun ⟨T, t, hT, ok, sty⟩ => ⟨T, hT, t, ok, sty⟩⟩

theorem refTys_located_iff {b : String} {l : DataLoc} {τ : STy} :
    (refTys C res tbl).located b l = some τ ↔ ∃ T t, tbl.located b l = some T ∧
      rawType C l T = .ok t ∧ rawSty res l T = some τ := by
  simp only [refTys, Option.bind_eq_some_iff, toOption_iff]
  exact ⟨fun ⟨T, hT, t, ok, sty⟩ => ⟨T, t, hT, ok, sty⟩,
    fun ⟨T, t, hT, ok, sty⟩ => ⟨T, hT, t, ok, sty⟩⟩

/-! ## Represented types and `RefsTyped` -/

/-- **A typed component with no location.** It is a retained entry without a
location, the only entry so spelled; the table spells it, the spelling
elaborates in `memory` to the type, and the type represents the entry. -/
theorem value_rep (sound : ∀ s d, res s = some d → Resolved E scope s d) {c : String} {τ : STy}
    (h : (refTys C res tbl).value c = some τ) :
    ∃ T t, (⟨T, none⟩ ∈ tbl ∧ spell T = c ∧ ∀ e ∈ tbl, e.key = c → e = ⟨T, none⟩) ∧
      (refs C tbl).value c = some t ∧ rawType C .memory T = .ok t ∧
      t.tys E scope .memory = some [τ] ∧ RawRep C E scope .memory T τ := by
  obtain ⟨T, t, hT, ok, sty⟩ := refTys_value_iff.1 h
  obtain ⟨typed, rep⟩ := rawSty_typed sound ok sty
  exact ⟨T, t, entry_iff.1 (value_iff.1 hT), refs_value_iff.2 ⟨T, hT, ok⟩, ok, typed, rep⟩

/-- **A typed located component.** It is a retained entry at that very
location, the only entry so spelled, of the one type every located entry of its
base has; the table spells it, the spelling elaborates at the recorded location
to the type, and the type represents the entry there. -/
theorem located_rep (sound : ∀ s d, res s = some d → Resolved E scope s d) {b : String}
    {l : DataLoc} {τ : STy} (h : (refTys C res tbl).located b l = some τ) :
    ∃ T t, (⟨T, some l⟩ ∈ tbl ∧ spell T = b ∧
        (∀ e ∈ tbl, e.key = b ++ locName l → e = ⟨T, some l⟩) ∧
        ∀ e ∈ tbl, e.loc.isSome → spell e.ty = b → e.ty = T) ∧
      (refs C tbl).located b = some t ∧ rawType C l T = .ok t ∧
      t.tys E scope l = some [τ] ∧ RawRep C E scope l T τ := by
  obtain ⟨T, t, hT, ok, sty⟩ := refTys_located_iff.1 h
  obtain ⟨typed, rep⟩ := rawSty_typed sound ok sty
  obtain ⟨hb, he⟩ := located_iff.1 hT
  obtain ⟨m, -, only⟩ := entry_iff.1 he
  exact ⟨T, t, ⟨m, (base_iff.1 hb).2.1, only, (base_iff.1 hb).2.2⟩,
    refs_located_iff.2 ⟨l, readAt_iff.2 ⟨T, hT, ok⟩⟩, ok, typed, rep⟩

/-- **The typing facts of the constructed tables**, from the resolution
obligations alone: every struct name `res` answers resolves, in the supplied
environment, to the declaration `res` gives. -/
theorem refsTyped (sound : ∀ s d, res s = some d → Resolved E scope s d) :
    RefsTyped E scope (refs C tbl) (refTys C res tbl) where
  value hT hτ := by
    obtain ⟨_, t, -, ht, -, typed, -⟩ := value_rep sound hτ
    cases hT.symm.trans ht
    exact typed
  located hT hτ := by
    obtain ⟨_, t, -, ht, -, typed, -⟩ := located_rep sound hτ
    cases hT.symm.trans ht
    exact typed

/-! ## Outstanding entries -/

theorem mem_outstanding {e : Entry} {err : RawError} :
    (e, err) ∈ outstanding C tbl ↔ e ∈ tbl ∧ rawType C (e.loc.getD .memory) e.ty = .error err := by
  simp only [outstanding, List.mem_filterMap]
  constructor
  · rintro ⟨e', m, h⟩
    split at h
    · cases h; exact ⟨m, by assumption⟩
    · cases h
  · rintro ⟨m, h⟩
    exact ⟨e, m, by rw [h]⟩

/-- No entry is dropped: each is spelled at its location or listed with its reason. -/
theorem read_or_outstanding {e : Entry} (m : e ∈ tbl) :
    (∃ t, rawType C (e.loc.getD .memory) e.ty = .ok t) ∨ ∃ err, (e, err) ∈ outstanding C tbl := by
  cases h : rawType C (e.loc.getD .memory) e.ty with
  | ok t => exact .inl ⟨t, rfl⟩
  | error err => exact .inr ⟨err, mem_outstanding.2 ⟨m, h⟩⟩

/-- A uniquely spelled entry without a location is answered exactly when it is
not outstanding. -/
theorem value_or_outstanding {c : String} {T : RawTy} (h : tbl.value c = some T) :
    (∃ t, (refs C tbl).value c = some t) ∨ ∃ err, (⟨T, none⟩, err) ∈ outstanding C tbl :=
  (read_or_outstanding (C := C) (value_mem h).1).imp
    (fun ⟨t, ok⟩ => ⟨t, refs_value_iff.2 ⟨T, h, ok⟩⟩) id

/-- A coherently retained located entry is answered or outstanding. -/
theorem located_or_outstanding {b : String} {l : DataLoc} {T : RawTy}
    (h : tbl.located b l = some T) :
    (∃ t, (refs C tbl).located b = some t) ∨ ∃ err, (⟨T, some l⟩, err) ∈ outstanding C tbl :=
  (read_or_outstanding (C := C) (located_mem h).1).imp
    (fun ⟨t, ok⟩ => ⟨t, refs_located_iff.2 ⟨l, readAt_iff.2 ⟨T, h, ok⟩⟩⟩) id

/-! ## The existing interfaces at the constructed tables -/

section Consume

variable (sound : ∀ s d, res s = some d → Resolved E scope s d)
include sound

/-- `Part.typeName_tys` at the constructed tables. -/
theorem part_tys (t : Part Ann) {T : Syn .typeName} {τ : STy}
    (hT : t.typeName (refs C tbl) = some T) (hτ : t.sty (refTys C res tbl) = some τ) :
    T.tys E scope (t.loc.getD .memory) = some [τ] :=
  Part.typeName_tys (refsTyped sound) t hT hτ

/-- `Parts.params_tys` at the constructed tables. -/
theorem params_tys (ts : Parts Ann) {P : Syn (.list .param)} {τs : List STy}
    (hP : ts.params (refs C tbl) = some P) (hτ : ts.stys (refTys C res tbl) = some τs) :
    P.tys E scope .memory = some τs :=
  Parts.params_tys (refsTyped sound) ts hP hτ

/-- **`fnType_ty` at the constructed tables**: a retained signature whose
reference components the table answers, with the caller's annotations, denotes
exactly `STy.fn ext params returns mutability`. -/
theorem fnType_ty (ext : Bool) (a : Ann) (ps rs : Parts Ann) {T : Syn .typeName}
    {πs ρs : List STy} (loc : DataLoc)
    (hT : (Part.fn ext a ps rs).typeName (refs C tbl) = some T)
    (hπ : ps.stys (refTys C res tbl) = some πs) (hρ : rs.stys (refTys C res tbl) = some ρs) :
    (∃ P R, ps.params (refs C tbl) = some P ∧ rs.params (refs C tbl) = some R ∧
      T = .fnType P (a.vis ext) a.mutability R ∧
      P.tys E scope .memory = some πs ∧ R.tys E scope .memory = some ρs) ∧
    T.ty E scope loc = some (.fn ext πs ρs a.mutability) :=
  FunctionTypeDecode.fnType_ty (refsTyped sound) ext a ps rs loc hT hπ hρ

end Consume

end Solidity.Correctness.Lowering.Total.FunctionTypeRefs
