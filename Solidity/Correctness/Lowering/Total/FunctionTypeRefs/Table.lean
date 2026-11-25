import Solidity.Correctness.Lowering.Total.FunctionTypeDecode
import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Function-type reference tables: retained entries and coherent lookup

A retained component of a function-type signature is an `Entry`: its type as
read (`RawTy`, what `expandTy` keeps) and its recorded location, if one was
written. `spell` is the component spelling `spellFnTy` writes for a type that is
no function type (a name as written, `mapping(K=>V)`, `T[]`, `T[n]`), and
`Entry.key` appends the location word with no separator, so a located entry's
key is the spelling of the `Part.located` the reader produces (`Entry.part_spell`).

Spellings do not determine entries: `.named "uint[]"` and `.array (.named
"uint")` are spelled alike, and so are a name `Tmemory` and `T` at `memory`.
Lookups therefore never pick: `Table.entry` answers a key only when every entry
with that key is the same entry, `Table.base` a base only when every located
entry with that base has the same type at every recorded location, and
`Table.located` needs both. A repeated identical entry is harmless; any
conflict leaves the spelling unanswered (`entry_iff`, `base_iff`).
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeRefs

open Source (DataLoc)
open FunctionTypeDecode (Part Ann locName)

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

/-- The tree component an entry answers for: `named` without a location,
`located` with its recorded one. -/
def Entry.part (e : Entry) : Part Ann :=
  match e.loc with
  | none => .named (spell e.ty)
  | some l => .located (spell e.ty) l

/-- An entry's key is exactly its component's spelling. -/
theorem Entry.part_spell (e : Entry) : e.part.spell = e.key := by
  cases e with | mk T l => cases l <;> rfl

/-- An entry's component carries its recorded location, unchanged. -/
theorem Entry.part_loc (e : Entry) : e.part.loc = e.loc := by
  cases e with | mk T l => cases l <;> rfl

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
    · intro h
      split at h
      · cases h
        exact ⟨.inl rfl, rfl, by assumption⟩
      · cases h
    · rintro ⟨-, rfl, all⟩
      rw [if_pos all]

/-- The retained components of a unit, in any order, repetitions allowed. -/
abbrev Table := List Entry

/-- The entry spelled `k`, when every entry spelled `k` is that entry. -/
def Table.entry (tbl : Table) (k : String) : Option Entry :=
  agree (tbl.filter (·.key = k))

/-- The type of the located entries with base spelling `b`, when they all have it. -/
def Table.base (tbl : Table) (b : String) : Option RawTy :=
  agree ((tbl.filter fun e => e.loc.isSome ∧ spell e.ty = b).map (·.ty))

/-- The type retained for a component with no location. -/
def Table.value (tbl : Table) (c : String) : Option RawTy :=
  match tbl.entry c with
  | some ⟨T, none⟩ => some T
  | _ => none

/-- The type retained for the base `b` at the recorded location `l`. -/
def Table.located (tbl : Table) (b : String) (l : DataLoc) : Option RawTy :=
  (tbl.base b).bind fun T =>
    if tbl.entry (b ++ locName l) = some ⟨T, some l⟩ then some T else none

variable {tbl : Table}

/-- A key is answered by a retained entry with that key, the only one. -/
theorem entry_iff {k : String} {e : Entry} :
    tbl.entry k = some e ↔ e ∈ tbl ∧ e.key = k ∧ ∀ e' ∈ tbl, e'.key = k → e' = e := by
  simp only [Table.entry, agree_iff, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨⟨m, k⟩, all⟩ => ⟨m, k, fun e' m' k' => all e' ⟨m', k'⟩⟩,
    fun ⟨m, k, all⟩ => ⟨⟨m, k⟩, fun e' ⟨m', k'⟩ => all e' m' k'⟩⟩

/-- A base is answered by the type of a retained located entry so spelled, the
type of every located entry so spelled, whatever its location. -/
theorem base_iff {b : String} {T : RawTy} :
    tbl.base b = some T ↔ (∃ l, ⟨T, some l⟩ ∈ tbl) ∧ spell T = b ∧
      ∀ e ∈ tbl, e.loc.isSome → spell e.ty = b → e.ty = T := by
  simp only [Table.base, agree_iff, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨T', l⟩, ⟨m, isLoc, sp⟩, rfl⟩, all⟩
    cases l with
    | none => cases isLoc
    | some l => exact ⟨⟨l, m⟩, sp, fun e me le se => all _ ⟨e, ⟨me, le, se⟩, rfl⟩⟩
  · rintro ⟨⟨l, m⟩, sp, all⟩
    exact ⟨⟨_, ⟨m, rfl, sp⟩, rfl⟩, fun T' ⟨e, ⟨me, le, se⟩, eq⟩ => eq ▸ all e me le se⟩

/-- Two different entries with one spelling: the spelling is not answered. -/
theorem entry_conflict {e e' : Entry} (m : e ∈ tbl) (m' : e' ∈ tbl) (k : e'.key = e.key)
    (ne : e ≠ e') : tbl.entry e.key = none := by
  cases h : tbl.entry e.key with
  | none => rfl
  | some x =>
    obtain ⟨-, -, all⟩ := entry_iff.1 h
    exact (ne ((all e m rfl).trans (all e' m' k).symm)).elim

/-- Two located entries with one base spelling and different types, at any
locations: the base is not answered. -/
theorem base_conflict {T T' : RawTy} {l l' : DataLoc} (m : ⟨T, some l⟩ ∈ tbl)
    (m' : ⟨T', some l'⟩ ∈ tbl) (sp : spell T' = spell T) (ne : T ≠ T') :
    tbl.base (spell T) = none := by
  cases h : tbl.base (spell T) with
  | none => rfl
  | some x =>
    obtain ⟨-, -, all⟩ := base_iff.1 h
    exact (ne ((all _ m rfl rfl).trans (all _ m' rfl sp).symm)).elim

theorem value_iff {c : String} {T : RawTy} :
    tbl.value c = some T ↔ tbl.entry c = some ⟨T, none⟩ := by
  unfold Table.value
  split
  · rename_i eq
    simp [eq]
  · rename_i ne
    constructor
    · intro h; cases h
    · intro h; exact (ne T h).elim

theorem located_iff {b : String} {l : DataLoc} {T : RawTy} :
    tbl.located b l = some T ↔
      tbl.base b = some T ∧ tbl.entry (b ++ locName l) = some ⟨T, some l⟩ := by
  simp only [Table.located, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨T', hb, h⟩
    split at h
    · cases h; exact ⟨hb, by assumption⟩
    · cases h
  · rintro ⟨hb, he⟩
    exact ⟨T, hb, by rw [if_pos he]⟩

/-- A value lookup is a retained entry with no location, spelled as asked. -/
theorem value_mem {c : String} {T : RawTy} (h : tbl.value c = some T) :
    ⟨T, none⟩ ∈ tbl ∧ spell T = c :=
  let ⟨m, k, _⟩ := entry_iff.1 (value_iff.1 h)
  ⟨m, k⟩

/-- A located lookup is a retained entry at that very location, its base spelled
as asked. -/
theorem located_mem {b : String} {l : DataLoc} {T : RawTy} (h : tbl.located b l = some T) :
    ⟨T, some l⟩ ∈ tbl ∧ spell T = b :=
  ⟨(entry_iff.1 (located_iff.1 h).2).1, (base_iff.1 (located_iff.1 h).1).2.1⟩

/-- One base, one type: lookups at different locations never disagree. -/
theorem located_agree {b : String} {l l' : DataLoc} {T T' : RawTy}
    (h : tbl.located b l = some T) (h' : tbl.located b l' = some T') : T = T' :=
  Option.some.inj ((located_iff.1 h).1.symm.trans (located_iff.1 h').1)

end Solidity.Correctness.Lowering.Total.FunctionTypeRefs
