import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Decoding a contract's struct table into Source struct declarations

`decode` reads `Contract.structs` in order. An entry `(written, table)` becomes
one contract-level `Source.Syn.struct written …`: its members are the ordered
fields of `Semantics.structDef table`, each under its name, its type spelled by
`ReferenceDecode.spellType` at the rows `Semantics.structWidths table` keeps for
it. A table name that spells members is never written; a nested struct is written
by the one identifier that reads as its table type. No entry or member is dropped
or guessed: an entry without a declaration is an `Error` naming its position
(`decode_ok_iff`), and a repeated written name is declared as often as it occurs.

Proved for a successful decoding: `decode_collect` (the declarations are the
entries, in order); `Gen.structFields`, `structFields_typed` (the Source fields
are the retained ordered fields, each related by `ReferenceDecode.Rep`);
`lookup_own`, `resolved`, `resolved_only` (a declared name is `Resolved` from the
contract scope exactly when the table declares it once and no surrounding
declaration of the scope carries it); `structFields_closed` (the member
obligations discharged from the facts `Declared` and `Free`).

Open, with the complete-unit decoder: a struct used but absent from
`Contract.structs` (`Declared` fails: its declaration and scope are not retained),
file-level declarations, a written name that is no identifier or also reads as an
elementary, enum or contract name, resolution from another scope, the member types
`ReferenceDecode` leaves open, that `readTy` lists exactly the rows a spelling
reads, that a resolved nested struct has its table type's members, retained `RawTy`
members, which entry and cause an `Error` names, that a unit's declarations have
the shape `pre ++ generated ++ post`, and semantic binding. No admission predicate.
-/
namespace Solidity.Correctness.Lowering.Total.StructDecode

open Solidity.Semantics (lookupBy structDef structWidths isEnc)
open Source (Syn STy DataLoc)
open ReferenceDecode (spellType spellRef readTy structsTy written? Resolved Rep bind_ok)

/-- Why a table entry has no Source declaration; `index` is its position. -/
inductive Error where
  | notWritten (index : Nat) (written table : Name) -- the key spells members, or is empty
  | noMembers (index : Nat) (written table : Name) -- the table keeps no member of the type
  | member (index : Nat) (written table member : Name) (why : ReferenceDecode.Error)
  | unreadRow (index : Nat) (written table key : Name) (value : Nat) -- no member reads it
  deriving DecidableEq, Repr

/-- Every member in order, its type spelled at its own rows, under its name; the first
without a spelling is the error. `storage` is where every member type has a spelling. -/
def members (C : Contract) (widths : List (Name × Nat)) :
    List (Name × Ty) → Except (Name × ReferenceDecode.Error) (Syn (.list .structMember))
  | [] => .ok .nil
  | x :: xs =>
    match spellType C widths x.1 .storage x.2 with
    | .error e => .error (x.1, e)
    | .ok t => do .ok (.cons (.structMember t x.1) (← members C widths xs))

/-- The first width row whose key `readTy` lists for no member. -/
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
def parts (C : Contract) (i : Nat) : List (Name × Name) → Except Error (Syn (.list (.part false)))
  | [] => .ok .nil
  | e :: es => do .ok (.cons (← part C i e) (← parts C (i + 1) es))

/-- The contract's structs as ordered Source contract parts. -/
def decode (C : Contract) : Except Error (Syn (.list (.part false))) := parts C 0 C.structs

/-- The obligation of one entry: a written name, some members, all spelled, every row read. -/
def Representable (C : Contract) (entry : Name × Name) : Prop :=
  (∃ m ms, members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms)) ∧
    stray (structWidths entry.2) (structDef entry.2) = none ∧ isEnc entry.1 = false ∧ entry.1 ≠ ""

/-- The declaration generated for a table entry in the contract `c`. -/
def Gen (C : Contract) (c : String) (entry : Name × Name) (d : Source.Decl) : Prop :=
  ∃ m ms, d = ⟨.struct, entry.1, some c, false, .struct entry.1 m ms⟩ ∧
    members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms) ∧ entry.1 ≠ ""

/-- Ordered correspondence of two lists: neither has an extra element. -/
inductive Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs R [] []
  | cons {a b as bs} : R a b → Pairs R as bs → Pairs R (a :: as) (b :: bs)
theorem Pairs.length {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Pairs R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

variable {C : Contract} {widths : List (Name × Nat)} {c : String} {E : Source.Env}
  {scope : Option String} {pre post : List Source.Decl}

theorem part_ok_iff {i : Nat} {entry : Name × Name} {p : Syn (.part false)} :
    part C i entry = .ok p ↔ (∃ m ms, p = .struct entry.1 m ms ∧
      members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms)) ∧
      stray (structWidths entry.2) (structDef entry.2) = none ∧ isEnc entry.1 = false ∧
      entry.1 ≠ "" := by
  constructor
  · intro h
    unfold part at h
    split at h; · cases h
    rename_i plain
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at plain
    split at h; · cases h
    · cases h
    split at h <;> cases h
    exact ⟨⟨_, _, rfl, by assumption⟩, by assumption, plain⟩
  · rintro ⟨⟨m, ms, rfl, hm⟩, hs, enc, name⟩
    simp [part, enc, name, hm, hs]

theorem parts_ok_iff : ∀ (i : Nat) (es : List (Name × Name)),
    (∃ ps, parts C i es = .ok ps) ↔ ∀ e ∈ es, Representable C e
  | _, [] => by simp [parts]
  | i, e :: es => by
      simp only [parts, bind_ok, List.mem_cons, forall_eq_or_imp, ← parts_ok_iff (i + 1) es]
      exact ⟨fun ⟨_, p, hp, ps, hps, _⟩ =>
          ⟨let ⟨⟨m, ms, _, hm⟩, r⟩ := part_ok_iff.1 hp; ⟨⟨m, ms, hm⟩, r⟩, ps, hps⟩,
        fun ⟨⟨⟨m, ms, hm⟩, r⟩, ps, hps⟩ => ⟨_, _, part_ok_iff.2 ⟨⟨m, ms, rfl, hm⟩, r⟩, ps, hps, rfl⟩⟩

/-- Decoding succeeds exactly when every entry is representable. -/
theorem decode_ok_iff (C : Contract) :
    (∃ ps, decode C = .ok ps) ↔ ∀ e ∈ C.structs, Representable C e := parts_ok_iff 0 C.structs

theorem parts_collect (c : String) :
    ∀ (i : Nat) (es : List (Name × Name)) (ps : Syn (.list (.part false))),
      parts C i es = .ok ps → Pairs (Gen C c) es (ps.collect (some c))
  | _, [], ps, h => by cases h; exact .nil
  | i, e :: es, ps, h => by
      simp only [parts, bind_ok] at h
      obtain ⟨p, hp, ps', hps, h⟩ := h
      cases Except.ok.inj h
      obtain ⟨⟨m, ms, rfl, hm⟩, -, -, name⟩ := part_ok_iff.1 hp
      exact .cons ⟨m, ms, rfl, hm, name⟩ (parts_collect c (i + 1) es ps' hps)

/-- **Shape and order**: the declarations are the entries' structs, in order, no other. -/
theorem decode_collect {ps : Syn (.list (.part false))} (h : decode C = .ok ps) (c : String) :
    Pairs (Gen C c) C.structs (ps.collect (some c)) := parts_collect c 0 C.structs ps h

/-! ## Member types -/
mutual
/-- No mapping outside the structs the type mentions. -/
def maplessTy : Ty → Bool
  | .prim _ => true
  | .ref R => maplessRef R
def maplessRef : RefTy → Bool
  | .struct _ => true
  | .array T | .fixed T _ => maplessTy T
  | .mapping _ _ => false
end
mutual
/-- Only a mapping's spelling asks for the location. -/
theorem spellType_loc : (T : Ty) → (key : Name) → (loc : DataLoc) → maplessTy T = true →
    spellType C widths key loc T = spellType C widths key .storage T
  | .prim _, _, _, _ => by simp only [spellType]
  | .ref R, key, loc, h => by
      simpa only [spellType] using spellRef_loc R key loc (by simpa only [maplessTy] using h)
theorem spellRef_loc : (R : RefTy) → (key : Name) → (loc : DataLoc) → maplessRef R = true →
    spellRef C widths key loc R = spellRef C widths key .storage R
  | .struct _, _, _, _ => by simp only [spellRef]
  | .array T, key, loc, h | .fixed T _, key, loc, h => by
      simp only [spellRef, spellType_loc T _ loc (by simpa only [maplessRef] using h)]
  | .mapping _ _, _, _, h => by simp [maplessRef] at h
end

/-- A decoded member list elaborates to one type per field, in order, each representing
its field at the field's rows, under the resolution obligations of the structs used. -/
theorem members_typed (loc : DataLoc) :
    ∀ {fs : List (Name × Ty)} {ms : Syn (.list .structMember)},
      members C widths fs = .ok ms → (∀ x ∈ fs, loc = .storage ∨ maplessTy x.2 = true) →
      (∀ x ∈ fs, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
      ms.memberNames = fs.map (·.1) ∧ ∃ τs, ms.tys E scope loc = some τs ∧
        Pairs (fun x τ => Rep C widths E scope x.1 loc x.2 τ) fs τs
  | [], ms, h, _, _ => by cases h; exact ⟨rfl, [], rfl, .nil⟩
  | x :: xs, ms, h, here, res => by
      unfold members at h
      split at h; · cases h
      rename_i t ht
      simp only [bind_ok] at h
      obtain ⟨ms', hms, h⟩ := h
      cases Except.ok.inj h
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

/-- Elaborated fields against a table type: its names in order, each type represented. -/
def Fields (C : Contract) (E : Source.Env) (c : String) (loc : DataLoc) (table : Name)
    (out : Option (List (String × STy))) : Prop :=
  ∃ τs, out = some (((structDef table).map (·.1)).zip τs) ∧
    Pairs (fun x τ => Rep C (structWidths table) E (some c) x.1 loc x.2 τ) (structDef table) τs

/-- **`Source.Decl.structFields` of a generated declaration**: the retained fields, in
`storage`, and anywhere when no member type has a mapping outside the structs it names. -/
theorem Gen.structFields {entry : Name × Name} {d : Source.Decl} (g : Gen C c entry d)
    (loc : DataLoc) (here : ∀ x ∈ structDef entry.2, loc = .storage ∨ maplessTy x.2 = true)
    (res : ∀ x ∈ structDef entry.2, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
      ∃ d', Resolved E (some c) w d') : Fields C E c loc entry.2 (d.structFields E loc) := by
  obtain ⟨m, ms, rfl, hm, -⟩ := g
  obtain ⟨names, τs, typed, reps⟩ := members_typed loc hm here res
  exact ⟨τs, by simp [Source.Decl.structFields, typed, names], reps⟩

/-! ## Resolution -/

/-- A declaration of the scope `c` named `w`, as `Source.Env.declared` asks. -/
def named (c : String) (w : Name) (d : Source.Decl) : Bool :=
  d.scope == some c && d.name == w && w != ""

/-- From a contract, a name it declares denotes its own declarations of it only. -/
theorem lookup_declared {x : String} (h : E.declared (some c) x ≠ []) :
    E.lookup (some c) x = E.declared (some c) x := by
  have vis : E.visible (some c) (some c) x = E.declared (some c) x := by
    simp [Source.Env.visible]
  obtain ⟨rest, chain⟩ : ∃ rest, (E.linearize c).getD [c] = c :: rest := by
    unfold Source.Env.linearize Source.Env.linearizeF
    dsimp only
    generalize List.mapM (E.linearizeF E.decls.length) (E.bases c).reverse = r
    cases r with
    | none => exact ⟨[], rfl⟩
    | some ls =>
      dsimp only
      generalize Source.Env.merge _ _ = m
      cases m <;> exact ⟨_, rfl⟩
  have ne : (E.declared (some c) x).isEmpty = false := by
    cases hd : E.declared (some c) x with
    | nil => exact absurd hd h
    | cons _ _ => rfl
  simp [Source.Env.lookup, chain, vis, ne]

/-- The first row of a key is the head of the rows of that key. -/
theorem lookupBy_filter {α : Type} (w : Name) : ∀ l : List (Name × α),
    lookupBy w l = ((l.filter (·.1 == w)).head?).map (·.2)
  | [] => rfl
  | (k, v) :: l => by
      by_cases hk : k = w
      · subst hk; simp [lookupBy]
      · have hk' : ¬ w = k := fun h => hk h.symm
        simp [lookupBy, hk, hk', lookupBy_filter w l]

theorem Gen.named {entry : Name × Name} {d : Source.Decl} (g : Gen C c entry d) (w : Name) :
    named c w d = (entry.1 == w) := by
  obtain ⟨m, ms, rfl, -, name⟩ := g
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

section Unit
variable {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
  (hE : E.decls = pre ++ ps.collect (some c) ++ post) {w : Name}
include h hE
/-- **Lookup of a declared name** from the contract scope: the scope's surrounding
declarations of that name around the generated ones, the entries of that key. -/
theorem lookup_own (hw : C.structs.filter (·.1 == w) ≠ []) :
    Pairs (Gen C c) (C.structs.filter (·.1 == w)) ((ps.collect (some c)).filter (named c w)) ∧
      E.lookup (some c) w = pre.filter (named c w) ++
        (ps.collect (some c)).filter (named c w) ++ post.filter (named c w) := by
  have g := gen_filter w (decode_collect h c)
  have eq : E.declared (some c) w = pre.filter (named c w) ++
      (ps.collect (some c)).filter (named c w) ++ post.filter (named c w) := by
    simp only [Source.Env.declared, hE, List.filter_append]; rfl
  refine ⟨g, ?_⟩
  rw [lookup_declared, eq]; rw [eq]; intro empty
  simp only [List.append_eq_nil_iff] at empty
  have len := g.length
  rw [empty.1.2] at len
  exact hw (List.eq_nil_of_length_eq_zero len)

/-- **Discharge of `Resolved`**: a name the table declares once and no surrounding
declaration of the scope carries denotes exactly its entry's generated declaration. -/
theorem resolved (one : (C.structs.filter (·.1 == w)).length = 1)
    (free : ∀ d ∈ pre ++ post, ¬(d.scope = some c ∧ d.name = w)) :
    ∃ e d, lookupBy w C.structs = some e ∧ Gen C c (w, e) d ∧ E.lookup (some c) w = [d] ∧
      Resolved E (some c) w ⟨some c, w⟩ := by
  have none : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ pre ++ post) → l.filter (named c w) = [] :=
    fun l sub => List.filter_eq_nil_iff.2 fun d md nd => free d (sub d md) (by
      simp only [named, Bool.and_eq_true, beq_iff_eq] at nd; exact nd.1)
  obtain ⟨⟨w0, e⟩, hf⟩ := List.length_eq_one_iff.1 one
  obtain ⟨g, look⟩ := lookup_own h hE (w := w) (by rw [hf]; exact List.cons_ne_nil _ _)
  rw [none pre fun d md => List.mem_append_left _ md,
    none post fun d md => List.mem_append_right _ md, List.nil_append, List.append_nil] at look
  rw [hf] at g
  generalize (ps.collect (some c)).filter (named c w) = gs at g look
  cases g with
  | cons gd rest =>
    cases rest
    have key : w0 = w := by
      have mem : (w0, e) ∈ C.structs.filter (·.1 == w) := by rw [hf]; exact List.mem_singleton_self _
      simpa using (List.mem_filter.1 mem).2
    cases key
    refine ⟨e, _, by rw [lookupBy_filter, hf]; rfl, gd, look, ?_⟩
    obtain ⟨m, ms, rfl, -⟩ := id gd
    exact ⟨_, look, rfl, rfl⟩

/-- **Only then**: a `Resolved` name with an entry is declared once and not carried by
a surrounding declaration; a repeated or interfered name is unresolved. -/
theorem resolved_only (hw : C.structs.filter (·.1 == w) ≠ [])
    (r : ∃ d, Resolved E (some c) w d) : (C.structs.filter (·.1 == w)).length = 1 ∧
      ∀ d ∈ pre ++ post, ¬(d.scope = some c ∧ d.name = w) := by
  obtain ⟨_, decl, look, _, _⟩ := r
  obtain ⟨g, eq⟩ := lookup_own h hE hw
  have len := congrArg List.length (eq.symm.trans look)
  simp only [List.length_append, ← g.length, List.length_cons, List.length_nil] at len
  have pos := List.length_pos_iff.2 hw
  have name : w ≠ "" := by
    obtain ⟨entry, mem⟩ := List.exists_mem_of_ne_nil _ hw
    obtain ⟨inTable, key⟩ := List.mem_filter.1 mem
    obtain ⟨_, _, _, named⟩ := (decode_ok_iff C).1 ⟨ps, h⟩ entry inTable
    exact (show entry.1 = w by simpa using key) ▸ named
  refine ⟨by omega, fun d md ⟨sc, nm⟩ => ?_⟩
  have nd : named c w d = true := by simp [named, sc, nm, name]
  rcases List.mem_append.1 md with m | m <;>
    have := List.length_pos_of_mem (List.mem_filter.2 ⟨m, nd⟩) <;> omega

/-- **`Source.Env.structFields` of a declared name**: the retained fields of its first
entry's table type, when no earlier struct of the scope has the name, under the
resolution obligations of the structs the fields use. -/
theorem structFields_typed {e : Name} (hw : lookupBy w C.structs = some e)
    (first : ∀ d ∈ pre, ¬(d.kind = .struct ∧ d.scope = some c ∧ d.name = w))
    (loc : DataLoc) (here : ∀ x ∈ structDef e, loc = .storage ∨ maplessTy x.2 = true)
    (res : ∀ x ∈ structDef e, ∀ s ∈ structsTy x.2, ∀ w', written? C s = some w' →
      ∃ d, Resolved E (some c) w' d) : Fields C E c loc e (E.structFields ⟨some c, w⟩ loc) := by
  obtain ⟨d, find, g⟩ := gen_find (decode_collect h c) hw
  have none : pre.find? (fun d => d.kind == .struct && d.scope == some c && d.name == w) = none :=
    List.find?_eq_none.2 fun d md => by simpa using fun k s => (first d md ⟨k, s, ·⟩)
  have decl : E.declOf .struct ⟨some c, w⟩ = some d := by
    simp only [Source.Env.declOf, hE, List.find?_append, none, find, Option.none_or, Option.some_or]
  simpa only [Source.Env.structFields, decl, Option.bind_some] using g.structFields loc here res

/-- Table fact: each struct the members of `table` use is written by a name declared once. -/
def Declared (C : Contract) (table : Name) : Prop :=
  ∀ x ∈ structDef table, ∀ s ∈ structsTy x.2, ∀ w ∈ written? C s,
    (C.structs.filter (·.1 == w)).length = 1
omit h hE in
instance (C : Contract) (table : Name) : Decidable (Declared C table) := by
  unfold Declared; infer_instance

/-- Noninterference: no surrounding declaration of the scope carries a declared name. -/
def Free (C : Contract) (c : String) (ds : List Source.Decl) : Prop :=
  ∀ d ∈ ds, d.scope = some c → lookupBy d.name C.structs = none

/-- **Fields, obligations discharged** by `resolved`: for a declared name whose table
type is `Declared`, among `Free` surrounding declarations. -/
theorem structFields_closed (free : Free C c (pre ++ post)) {e : Name}
    (hw : lookupBy w C.structs = some e) (dec : Declared C e) (loc : DataLoc)
    (here : ∀ x ∈ structDef e, loc = .storage ∨ maplessTy x.2 = true) :
    Fields C E c loc e (E.structFields ⟨some c, w⟩ loc) :=
  structFields_typed h hE hw
    (fun d md ⟨_, sc, nm⟩ => by
      have := free d (List.mem_append_left _ md) sc
      rw [nm, hw] at this; cases this)
    loc here fun x mx s ms w' hw' => by
      have one := dec x mx s ms w' hw'
      obtain ⟨entry, hf⟩ := List.length_eq_one_iff.1 one
      obtain ⟨_, _, _, _, _, res⟩ := resolved h hE one fun d md ⟨sc, nm⟩ => by
        have := free d md sc
        rw [nm, lookupBy_filter, hf] at this; cases this
      exact ⟨_, res⟩
end Unit

end Solidity.Correctness.Lowering.Total.StructDecode
