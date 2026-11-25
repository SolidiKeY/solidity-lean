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

/-! ## Member types -/

variable {E : Source.Env} {scope : Option String} {pre post : List Source.Decl}

/-- A decoded member list elaborates, at a location every member type has a
spelling in, to one type per field, in order, each representing its field at the
field's rows, under the resolution obligations of the structs the fields use. -/
theorem members_typed (loc : DataLoc) :
    ∀ {fs : List (Name × Ty)} {ms : Syn (.list .structMember)},
      members C widths fs = .ok ms →
      (∀ x ∈ fs, loc = .storage ∨ maplessTy x.2 = true) →
      (∀ x ∈ fs, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
      ms.memberNames = fs.map (·.1) ∧ ∃ τs, ms.tys E scope loc = some τs ∧
        Pairs (fun x τ => Rep C widths E scope x.1 loc x.2 τ) fs τs
  | [], ms, h, _, _ => by cases h; exact ⟨rfl, [], rfl, .nil⟩
  | x :: xs, ms, h, here, res => by
      simp only [members, bind_ok] at h
      obtain ⟨m, hm, ms', hms, h⟩ := h
      cases Except.ok.inj h
      obtain ⟨t, ht, rfl⟩ := member_ok hm
      have ht' : spellType C widths x.1 loc x.2 = .ok t := by
        rcases here x List.mem_cons_self with rfl | mapless
        · exact ht
        · rw [spellType_loc _ _ _ mapless]; exact ht
      obtain ⟨τ, typed, rep⟩ := ReferenceDecode.spellType_typed x.2 x.1 loc t ht'
        (res x List.mem_cons_self)
      obtain ⟨names, τs, typeds, reps⟩ := members_typed loc hms
        (fun y my => here y (List.mem_cons_of_mem _ my))
        (fun y my => res y (List.mem_cons_of_mem _ my))
      exact ⟨by simp [Source.Syn.memberNames, names], τ :: τs,
        by simp [Source.Syn.tys, typed, typeds], .cons rep reps⟩

/-- What a struct's elaborated fields are against its table type: the retained
names in order, each with a type representing the field's at the field's rows. -/
def Fields (C : Contract) (E : Source.Env) (c : String) (loc : DataLoc) (table : Name)
    (out : Option (List (String × STy))) : Prop :=
  ∃ τs, out = some (((structDef table).map (·.1)).zip τs) ∧
    Pairs (fun x τ => Rep C (structWidths table) E (some c) x.1 loc x.2 τ) (structDef table) τs

/-- **`Source.Decl.structFields` of a generated declaration**: the retained
ordered fields, in `storage` and in every location for a mapping-free member list. -/
theorem Gen.structFields {entry : Name × Name} {d : Source.Decl} (g : Gen C c entry d)
    (loc : DataLoc) (here : ∀ x ∈ structDef entry.2, loc = .storage ∨ maplessTy x.2 = true)
    (res : ∀ x ∈ structDef entry.2, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
      ∃ d', Resolved E (some c) w d') :
    Fields C E c loc entry.2 (d.structFields E loc) := by
  obtain ⟨m, ms, rfl, hm, -⟩ := g
  obtain ⟨names, τs, typed, reps⟩ := members_typed loc hm here res
  exact ⟨τs, by simp [Source.Decl.structFields, typed, names], reps⟩

/-! ## Resolution -/

theorem Resolved.unique {w : Name} {d d' : Source.DeclName} (h : Resolved E scope w d)
    (h' : Resolved E scope w d') : d = d' := by
  obtain ⟨decl, look, -, rfl⟩ := h
  obtain ⟨decl', look', -, rfl⟩ := h'
  rw [look] at look'; cases look'; rfl

theorem Gen.named {entry : Name × Name} {d : Source.Decl} (g : Gen C c entry d) (w : Name) :
    named c w d = (entry.1 == w) := by
  obtain ⟨m, ms, rfl, -, -, name, -⟩ := g
  by_cases hw : entry.1 = w
  · subst hw; simp [StructDecode.named, name]
  · simp [StructDecode.named, hw]

/-- The generated declarations of a name are the entries of that key, in order. -/
theorem gen_filter (w : Name) {es : List (Name × Name)} {ds : List Source.Decl}
    (h : Pairs (Gen C c) es ds) :
    Pairs (Gen C c) (es.filter (·.1 == w)) (ds.filter (named c w)) := by
  induction h with
  | nil => exact .nil
  | cons g _ ih =>
    rw [List.filter_cons, List.filter_cons, g.named w]
    split
    · exact .cons g ih
    · exact ih

/-- The first struct declaration of a name is the one of the key's first row. -/
theorem gen_find {w e : Name} {es : List (Name × Name)} {ds : List Source.Decl}
    (h : Pairs (Gen C c) es ds) : lookupBy w es = some e →
    ∃ d, ds.find? (fun d => d.kind == .struct && d.scope == some c && d.name == w) = some d ∧
      Gen C c (w, e) d := by
  induction h with
  | nil => intro hl; cases hl
  | @cons a d _ _ g _ ih =>
    intro hl
    obtain ⟨w0, e0⟩ := a
    obtain ⟨m, ms, rfl, hm, rep⟩ := id g
    by_cases hw : w = w0
    · subst hw
      simp only [lookupBy, if_true, Option.some.injEq] at hl
      subst hl
      exact ⟨_, by simp, g⟩
    · simp only [lookupBy, hw, if_false] at hl
      obtain ⟨d, find, gd⟩ := ih hl
      have hw' : (w0 == w) = false := by simpa using fun h : w0 = w => hw h.symm
      exact ⟨d, by simpa [List.find?_cons, hw'] using find, gd⟩

theorem declared_eq (hE : E.decls = pre ++ ps ++ post) (w : Name) :
    E.declared (some c) w =
      pre.filter (named c w) ++ ps.filter (named c w) ++ post.filter (named c w) := by
  simp only [Source.Env.declared, hE, List.filter_append]; rfl

/-- **Lookup of a declared name** from the contract scope: the surrounding
declarations of the scope under that name, around the generated ones, which are
the entries of that key. Bases and the file level are shadowed. -/
theorem lookup_own {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) {w : Name}
    (hw : C.structs.filter (·.1 == w) ≠ []) :
    Pairs (Gen C c) (C.structs.filter (·.1 == w)) ((ps.collect (some c)).filter (named c w)) ∧
      E.lookup (some c) w = pre.filter (named c w) ++
        (ps.collect (some c)).filter (named c w) ++ post.filter (named c w) := by
  have g := gen_filter w (decode_collect h c)
  refine ⟨g, ?_⟩
  rw [lookup_declared, declared_eq hE]
  rw [declared_eq hE]
  intro empty
  simp only [List.append_eq_nil_iff] at empty
  have len := g.length
  rw [empty.1.2] at len
  exact hw (List.eq_nil_of_length_eq_zero len)

/-- **Discharge of `Resolved`**: a name the table declares exactly once, and no
surrounding declaration of the scope carries, denotes from the contract scope
exactly the generated declaration of its entry. -/
theorem resolved {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) {w : Name}
    (one : (C.structs.filter (·.1 == w)).length = 1)
    (free : ∀ d ∈ pre ++ post, ¬(d.scope = some c ∧ d.name = w)) :
    ∃ e d, lookupBy w C.structs = some e ∧ Gen C c (w, e) d ∧ E.lookup (some c) w = [d] ∧
      Resolved E (some c) w ⟨some c, w⟩ := by
  have none : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ pre ++ post) → l.filter (named c w) = [] :=
    fun l sub => List.filter_eq_nil_iff.2 fun d md nd => free d (sub d md) (by
      simp only [named, Bool.and_eq_true, beq_iff_eq] at nd; exact nd.1)
  obtain ⟨entry, hf⟩ := List.length_eq_one_iff.1 one
  obtain ⟨g, look⟩ := lookup_own h hE (w := w) (by rw [hf]; exact List.cons_ne_nil _ _)
  rw [none pre fun d md => List.mem_append_left _ md,
    none post fun d md => List.mem_append_right _ md, List.nil_append, List.append_nil] at look
  rw [hf] at g
  generalize (ps.collect (some c)).filter (named c w) = gs at g look
  cases g with
  | cons gd rest =>
    cases rest
    have key : entry.1 = w := by
      have mem : entry ∈ C.structs.filter (·.1 == w) := by rw [hf]; exact List.mem_singleton_self _
      simpa using (List.mem_filter.1 mem).2
    obtain ⟨w0, e⟩ := entry
    cases key
    refine ⟨e, _, by rw [lookupBy_filter, hf]; rfl, gd, look, ?_⟩
    obtain ⟨m, ms, rfl, -⟩ := id gd
    exact ⟨_, look, rfl, rfl⟩

/-- **Resolution, exactly**: a name with a table entry satisfies `Resolved` from
the contract scope if and only if the table declares it once and no surrounding
declaration of the scope carries it. A repeated written name and an interfering
declaration are both unresolved. -/
theorem resolved_iff {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) {w : Name}
    (hw : C.structs.filter (·.1 == w) ≠ []) :
    (∃ d, Resolved E (some c) w d) ↔ (C.structs.filter (·.1 == w)).length = 1 ∧
      ∀ d ∈ pre ++ post, ¬(d.scope = some c ∧ d.name = w) := by
  refine ⟨fun ⟨_, decl, look, _, _⟩ => ?_, fun ⟨one, free⟩ => ?_⟩
  · obtain ⟨g, eq⟩ := lookup_own h hE hw
    have len := congrArg List.length (eq.symm.trans look)
    simp only [List.length_append, ← g.length, List.length_cons, List.length_nil] at len
    have pos := List.length_pos_iff.2 hw
    have name : w ≠ "" := by
      obtain ⟨entry, mem⟩ := List.exists_mem_of_ne_nil _ hw
      obtain ⟨inTable, key⟩ := List.mem_filter.1 mem
      obtain ⟨_, named, _⟩ := (decode_ok_iff C).1 ⟨ps, h⟩ entry inTable
      exact (show entry.1 = w by simpa using key) ▸ named
    refine ⟨by omega, fun d md ⟨sc, nm⟩ => ?_⟩
    have nd : named c w d = true := by simp [named, sc, nm, name]
    rcases List.mem_append.1 md with m | m
    · have := List.length_pos_of_mem (List.mem_filter.2 ⟨m, nd⟩); omega
    · have := List.length_pos_of_mem (List.mem_filter.2 ⟨m, nd⟩); omega
  · obtain ⟨_, _, _, _, _, res⟩ := resolved h hE one free
    exact ⟨_, res⟩

/-! ## Fields of the declared structs -/

/-- **`Source.Env.structFields` of a declared name**: the retained ordered
fields of the table type its first entry names, when no earlier declaration of
the scope is a struct of that name, under the resolution obligations of the
structs the fields use. -/
theorem structFields_typed {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) {w e : Name}
    (hw : lookupBy w C.structs = some e)
    (first : ∀ d ∈ pre, ¬(d.kind = .struct ∧ d.scope = some c ∧ d.name = w))
    (loc : DataLoc) (here : ∀ x ∈ structDef e, loc = .storage ∨ maplessTy x.2 = true)
    (res : ∀ x ∈ structDef e, ∀ s ∈ structsTy x.2, ∀ w', written? C s = some w' →
      ∃ d, Resolved E (some c) w' d) :
    Fields C E c loc e (E.structFields ⟨some c, w⟩ loc) := by
  obtain ⟨d, find, g⟩ := gen_find (decode_collect h c) hw
  have none : pre.find? (fun d => d.kind == .struct && d.scope == some c && d.name == w) = none :=
    List.find?_eq_none.2 fun d md => by simpa using fun k s => (first d md ⟨k, s, ·⟩)
  have decl : E.declOf .struct ⟨some c, w⟩ = some d := by
    simp only [Source.Env.declOf, hE, List.find?_append, none, find, Option.none_or, Option.some_or]
  simpa only [Source.Env.structFields, decl, Option.bind_some] using g.structFields loc here res

/-- Table fact: every struct the members of `table` use is written by a name the
table declares exactly once. It fails for a struct with no entry. -/
def Declared (C : Contract) (table : Name) : Prop :=
  ∀ x ∈ structDef table, ∀ s ∈ structsTy x.2, ∀ w ∈ written? C s,
    (C.structs.filter (·.1 == w)).length = 1

/-- Noninterference: no surrounding declaration of the contract scope carries a
name the table declares. -/
def Free (C : Contract) (c : String) (ds : List Source.Decl) : Prop :=
  ∀ d ∈ ds, d.scope = some c → lookupBy d.name C.structs = none

/-- `resolved` from the two stated facts. -/
theorem resolved_of_free {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) (free : Free C c (pre ++ post))
    {w : Name} (one : (C.structs.filter (·.1 == w)).length = 1) :
    ∃ e d, lookupBy w C.structs = some e ∧ Gen C c (w, e) d ∧ E.lookup (some c) w = [d] ∧
      Resolved E (some c) w ⟨some c, w⟩ :=
  resolved h hE one fun d md ⟨sc, nm⟩ => by
    obtain ⟨entry, hf⟩ := List.length_eq_one_iff.1 one
    have := free d md sc
    rw [nm, lookupBy_filter, hf] at this
    cases this

/-- **Fields with the member obligations discharged**: for a declared name whose
table type is `Declared`, among `Free` surrounding declarations, the Source
fields are the retained ordered fields; every struct a member uses resolves to
the generated declaration of its written name (`resolved_of_free`). -/
theorem structFields_closed {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
    (hE : E.decls = pre ++ ps.collect (some c) ++ post) (free : Free C c (pre ++ post))
    {w e : Name} (hw : lookupBy w C.structs = some e) (dec : Declared C e)
    (loc : DataLoc) (here : ∀ x ∈ structDef e, loc = .storage ∨ maplessTy x.2 = true) :
    Fields C E c loc e (E.structFields ⟨some c, w⟩ loc) :=
  structFields_typed h hE hw
    (fun d md ⟨_, sc, nm⟩ => by
      have := free d (List.mem_append_left _ md) sc
      rw [nm, hw] at this; cases this)
    loc here fun x mx s ms w' hw' => by
      obtain ⟨_, _, _, _, _, res⟩ := resolved_of_free h hE free (dec x mx s ms w' hw')
      exact ⟨_, res⟩

end Solidity.Correctness.Lowering.Total.StructDecode
