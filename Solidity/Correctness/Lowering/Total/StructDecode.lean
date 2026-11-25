import Solidity.Correctness.Lowering.Total.StructDecode.Lookup

/-!
# Decoding a contract's struct table into Source struct declarations

`decode` reads `Contract.structs` in order. An entry `(written, table)` becomes
one contract-level `Source.Syn.struct written …`: its members are the ordered
fields of `Semantics.structDef table`, each under its own name, its type spelled
by `ReferenceDecode.spellType` at the rows `Semantics.structWidths table` keeps
for it (a narrow member keeps its width; an array, a mapping and a nested struct
keep their structure). The declaration is named by the written name; the table
name, which may spell members, is never written, and a nested struct is written
by the one identifier that reads as its table type (`ReferenceDecode.written?`).

Nothing is dropped or guessed: an entry that has no declaration is an `Error`
naming its position (`decode_ok_iff`, `decode_error`, `part_cause`). A repeated
written name is declared as often as the table has it.

Proved for a successful decoding:
- `decode_collect`: the collected declarations are the entries, in order (`Gen`);
- `Gen.structFields`, `structFields_typed`: `Source.Decl.structFields` and
  `Source.Env.structFields` are the retained ordered fields, each related by
  `ReferenceDecode.Rep`, under the resolution obligations of the structs used;
- `lookup_own`, `resolved`, `resolved_iff`: in an environment holding the
  generated declarations in the contract scope, a declared name satisfies
  `ReferenceDecode.Resolved` from that scope exactly when the table declares it
  once and no surrounding declaration of the scope carries it;
- `structFields_closed`: the member obligations discharged from `Declared`
  and `Free`, facts of the table and of the surrounding declarations.

Open, with the complete-unit decoder: a struct used but absent from
`Contract.structs` (a table struct, `Declared` fails: its declaration and scope
are not retained), declarations at file level, a written name that also reads as
an elementary, enum or contract name, resolution from another scope (a base, a
derived contract), the member types `ReferenceDecode` leaves open, retained
`RawTy` members, unit composition, metadata agreement and semantic binding. A
component; it defines no admission predicate.
-/
namespace Solidity.Correctness.Lowering.Total.StructDecode

open Solidity.Semantics (lookupBy structDef structWidths isEnc)
open Source (Syn STy DataLoc)
open ReferenceDecode (spellType readTy structsTy written? Resolved Rep bind_ok)

/-- Why a table entry has no Source declaration; `index` is its position. -/
inductive Error where
  /-- The key is no written identifier: it spells members, or it is empty. -/
  | notWritten (index : Nat) (written table : Name)
  /-- The table type has no member: unknown, refused or empty; Source needs one. -/
  | noMembers (index : Nat) (written table : Name)
  /-- A member whose type has no reference spelling. -/
  | member (index : Nat) (written table member : Name) (why : ReferenceDecode.Error)
  /-- A width row of the table type that no member's spelling reads. -/
  | unreadRow (index : Nat) (written table key : Name) (value : Nat)
  deriving DecidableEq, Repr

/-- One member: its type spelled at its own rows, under its name. A member type
has no location; `storage` is where every member type has a spelling. -/
def member (C : Contract) (widths : List (Name × Nat)) (x : Name × Ty) :
    Except (Name × ReferenceDecode.Error) (Syn .structMember) :=
  match spellType C widths x.1 .storage x.2 with
  | .ok t => .ok (.structMember t x.1)
  | .error e => .error (x.1, e)

/-- Every member in order; the first without a spelling is the error. -/
def members (C : Contract) (widths : List (Name × Nat)) :
    List (Name × Ty) → Except (Name × ReferenceDecode.Error) (Syn (.list .structMember))
  | [] => .ok .nil
  | x :: xs => do
    let m ← member C widths x
    let ms ← members C widths xs
    .ok (.cons m ms)

/-- The first width row that the spelling of no member reads. -/
def stray (widths : List (Name × Nat)) (fs : List (Name × Ty)) : Option (Name × Nat) :=
  widths.find? fun r => !(fs.flatMap fun x => readTy x.1 x.2).contains r.1

/-- The declaration of the entry at position `i`. -/
def part (C : Contract) (i : Nat) (entry : Name × Name) : Except Error (Syn (.part false)) :=
  if isEnc entry.1 || entry.1 == "" then .error (.notWritten i entry.1 entry.2)
  else match members C (structWidths entry.2) (structDef entry.2) with
    | .error e => .error (.member i entry.1 entry.2 e.1 e.2)
    | .ok .nil => .error (.noMembers i entry.1 entry.2)
    | .ok (.cons m ms) =>
      match stray (structWidths entry.2) (structDef entry.2) with
      | some r => .error (.unreadRow i entry.1 entry.2 r.1 r.2)
      | none => .ok (.struct entry.1 m ms)

/-- The entries from position `i` on; the first without a declaration fails. -/
def parts (C : Contract) (i : Nat) : List (Name × Name) →
    Except Error (Syn (.list (.part false)))
  | [] => .ok .nil
  | e :: es => do
    let p ← part C i e
    let ps ← parts C (i + 1) es
    .ok (.cons p ps)

/-- The contract's structs as ordered Source contract parts. -/
def decode (C : Contract) : Except Error (Syn (.list (.part false))) := parts C 0 C.structs

/-- The members a member list writes, in order: name and type name. -/
def memberList : {c : Source.Cat} → Syn c → List (String × Syn .typeName)
  | _, .cons x xs => memberList x ++ memberList xs
  | _, .structMember t n => [(n, t)]
  | _, _ => []

variable {C : Contract} {widths : List (Name × Nat)} {c : String}

/-- A written member of a field: the field's name, its type's spelling. -/
def Spelled (C : Contract) (widths : List (Name × Nat)) (x : Name × Ty)
    (m : String × Syn .typeName) : Prop :=
  m.1 = x.1 ∧ spellType C widths x.1 .storage x.2 = .ok m.2

/-- The representation obligation of one entry: what `part` needs. -/
def Representable (C : Contract) (entry : Name × Name) : Prop :=
  isEnc entry.1 = false ∧ entry.1 ≠ "" ∧ structDef entry.2 ≠ [] ∧
    stray (structWidths entry.2) (structDef entry.2) = none ∧
    ∀ x ∈ structDef entry.2, ∃ t, spellType C (structWidths entry.2) x.1 .storage x.2 = .ok t

/-- The declaration generated for a table entry in the contract `c`: a struct
of that scope under the written name, its members the table type's fields. -/
def Gen (C : Contract) (c : String) (entry : Name × Name) (d : Source.Decl) : Prop :=
  ∃ m ms, d = ⟨.struct, entry.1, some c, false, .struct entry.1 m ms⟩ ∧
    members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms) ∧
    Representable C entry

/-- The cause an error names, on its entry. -/
def Cause (C : Contract) (entry : Name × Name) : Error → Prop
  | .notWritten _ w t => (w, t) = entry ∧ (isEnc w = true ∨ w = "")
  | .noMembers _ w t => (w, t) = entry ∧ structDef t = []
  | .member _ w t f why => (w, t) = entry ∧
      ∃ x ∈ structDef t, x.1 = f ∧ spellType C (structWidths t) f .storage x.2 = .error why
  | .unreadRow _ w t k v => (w, t) = entry ∧ stray (structWidths t) (structDef t) = some (k, v)

/-- The position an error names. -/
def Error.index : Error → Nat
  | .notWritten i .. | .noMembers i .. | .member i .. | .unreadRow i .. => i

/-! ## Assembly -/

theorem member_ok {x : Name × Ty} {m : Syn .structMember} (h : member C widths x = .ok m) :
    ∃ t, spellType C widths x.1 .storage x.2 = .ok t ∧ m = .structMember t x.1 := by
  unfold member at h
  split at h <;> cases h
  exact ⟨_, by assumption, rfl⟩

/-- One member per field, in order, under its name, its type as spelled. -/
theorem members_spelled : ∀ {fs : List (Name × Ty)} {ms : Syn (.list .structMember)},
    members C widths fs = .ok ms → Pairs (Spelled C widths) fs (memberList ms)
  | [], ms, h => by cases h; exact .nil
  | x :: xs, ms, h => by
      simp only [members, bind_ok] at h
      obtain ⟨m, hm, ms', hms, h⟩ := h
      cases Except.ok.inj h
      obtain ⟨t, ht, rfl⟩ := member_ok hm
      exact .cons ⟨rfl, ht⟩ (members_spelled hms)

theorem members_ok_iff : ∀ fs : List (Name × Ty),
    (∃ ms, members C widths fs = .ok ms) ↔
      ∀ x ∈ fs, ∃ t, spellType C widths x.1 .storage x.2 = .ok t
  | [] => by simp [members]
  | x :: xs => by
      have ih := members_ok_iff xs
      simp only [members, bind_ok, List.mem_cons, forall_eq_or_imp, ← ih]
      constructor
      · rintro ⟨_, m, hm, ms, hms, _⟩
        obtain ⟨t, ht, _⟩ := member_ok hm
        exact ⟨⟨t, ht⟩, ms, hms⟩
      · rintro ⟨⟨t, ht⟩, ms, hms⟩
        exact ⟨_, .structMember t x.1, by simp only [member, ht], ms, hms, rfl⟩

/-- A failed member list names a field and the error of its spelling. -/
theorem members_error : ∀ {fs : List (Name × Ty)} {f : Name} {why : ReferenceDecode.Error},
    members C widths fs = .error (f, why) →
      ∃ x ∈ fs, x.1 = f ∧ spellType C widths f .storage x.2 = .error why
  | [], _, _, h => by cases h
  | x :: xs, f, why, h => by
      simp only [members] at h
      cases hm : member C widths x with
      | error e =>
        rw [hm] at h; cases h
        unfold member at hm
        split at hm <;> cases hm
        exact ⟨x, List.mem_cons_self, rfl, by assumption⟩
      | ok m =>
        rw [hm] at h
        cases hms : members C widths xs with
        | error e =>
          rw [hms] at h; cases h
          obtain ⟨y, my, hy⟩ := members_error hms
          exact ⟨y, List.mem_cons_of_mem _ my, hy⟩
        | ok ms => rw [hms] at h; cases h

theorem members_nil {fs : List (Name × Ty)} (h : members C widths fs = .ok .nil) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons x xs =>
    simp only [members, bind_ok] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h

/-- A generated part is the struct of its entry, which is representable. -/
theorem part_ok {i : Nat} {entry : Name × Name} {p : Syn (.part false)}
    (h : part C i entry = .ok p) :
    ∃ m ms, p = .struct entry.1 m ms ∧
      members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms) ∧
      Representable C entry := by
  unfold part at h
  split at h; · cases h
  rename_i plain
  split at h
  · cases h
  · cases h
  · rename_i m ms hm
    split at h <;> cases h
    rename_i hs
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at plain
    refine ⟨m, ms, rfl, hm, plain.1, plain.2, ?_, hs, (members_ok_iff _).1 ⟨_, hm⟩⟩
    intro empty
    rw [empty] at hm; cases hm

/-- A part exists exactly for a representable entry. -/
theorem part_ok_iff (i : Nat) (entry : Name × Name) :
    (∃ p, part C i entry = .ok p) ↔ Representable C entry := by
  refine ⟨fun ⟨p, h⟩ => ?_, fun ⟨enc, name, ne, hs, all⟩ => ?_⟩
  · obtain ⟨_, _, _, _, rep⟩ := part_ok h
    exact rep
  obtain ⟨ms, hm⟩ := (members_ok_iff _).2 all
  cases ms with
  | nil => exact absurd (members_nil hm) ne
  | cons m ms' => exact ⟨.struct entry.1 m ms', by simp [part, enc, name, hm, hs]⟩

/-- An error names its own position and its cause on the entry there. -/
theorem part_cause {i : Nat} {entry : Name × Name} {err : Error}
    (h : part C i entry = .error err) : err.index = i ∧ Cause C entry err := by
  unfold part at h
  split at h
  · rename_i bad; cases h
    exact ⟨rfl, rfl, by simpa using bad⟩
  split at h
  · rename_i e he; cases h
    exact ⟨rfl, rfl, members_error (f := e.1) (why := e.2) he⟩
  · rename_i he; cases h
    exact ⟨rfl, rfl, members_nil he⟩
  · split at h <;> cases h
    rename_i r hr
    exact ⟨rfl, rfl, hr⟩

/-- **Declarations, shape and order**: one generated declaration per entry. -/
theorem parts_collect (c : String) :
    ∀ (i : Nat) (es : List (Name × Name)) (ps : Syn (.list (.part false))),
      parts C i es = .ok ps → Pairs (Gen C c) es (ps.collect (some c))
  | _, [], ps, h => by cases h; exact .nil
  | i, e :: es, ps, h => by
      simp only [parts, bind_ok] at h
      obtain ⟨p, hp, ps', hps, h⟩ := h
      cases Except.ok.inj h
      obtain ⟨m, ms, rfl, hm, rep⟩ := part_ok hp
      exact .cons ⟨m, ms, rfl, hm, rep⟩ (parts_collect c (i + 1) es ps' hps)

theorem parts_ok_iff : ∀ (i : Nat) (es : List (Name × Name)),
    (∃ ps, parts C i es = .ok ps) ↔ ∀ e ∈ es, Representable C e
  | _, [] => by simp [parts]
  | i, e :: es => by
      simp only [parts, bind_ok, List.mem_cons, forall_eq_or_imp, ← parts_ok_iff (i + 1) es,
        ← part_ok_iff i e]
      exact ⟨fun ⟨_, p, hp, ps, hps, _⟩ => ⟨⟨p, hp⟩, ps, hps⟩,
        fun ⟨⟨p, hp⟩, ps, hps⟩ => ⟨_, p, hp, ps, hps, rfl⟩⟩

theorem parts_error : ∀ (i : Nat) (es : List (Name × Name)) (err : Error),
    parts C i es = .error err →
      i ≤ err.index ∧ ∃ entry, es[err.index - i]? = some entry ∧ Cause C entry err
  | _, [], _, h => by cases h
  | i, e :: es, err, h => by
      simp only [parts] at h
      cases hp : part C i e with
      | error e' =>
        rw [hp] at h; cases h
        obtain ⟨hi, cause⟩ := part_cause hp
        exact ⟨by omega, e, by simp [hi], cause⟩
      | ok p =>
        rw [hp] at h
        cases hps : parts C (i + 1) es with
        | error e' =>
          rw [hps] at h; cases h
          obtain ⟨le, entry, at', cause⟩ := parts_error (i + 1) es err hps
          refine ⟨by omega, entry, ?_, cause⟩
          rw [show err.index - i = (err.index - (i + 1)) + 1 by omega]
          simpa using at'
        | ok ps => rw [hps] at h; cases h

/-- The collected declarations are the table's entries, in order, each the
struct of its entry in the scope `c`: none missing, none added. -/
theorem decode_collect {ps : Syn (.list (.part false))} (h : decode C = .ok ps) (c : String) :
    Pairs (Gen C c) C.structs (ps.collect (some c)) :=
  parts_collect c 0 C.structs ps h

/-- Decoding succeeds exactly when every entry is representable. -/
theorem decode_ok_iff (C : Contract) :
    (∃ ps, decode C = .ok ps) ↔ ∀ e ∈ C.structs, Representable C e :=
  parts_ok_iff 0 C.structs

/-- A failure names an entry of the table by position, and its cause there. -/
theorem decode_error {err : Error} (h : decode C = .error err) :
    ∃ entry, C.structs[err.index]? = some entry ∧ Cause C entry err := by
  simpa using (parts_error 0 C.structs err h).2

end Solidity.Correctness.Lowering.Total.StructDecode
