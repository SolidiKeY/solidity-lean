import Solidity.Syntax.Raw
import Solidity.Source.Machine

/-!
# Decoding a contract's enum table into ordered Source declarations

`decode` reads `Contract.enums` (each enum with its members in order) as
contract-level Source enum parts (`Source.Syn.enum name first rest`), one per
entry, in declaration order, keeping every name, member and member position.

Source syntax requires at least one member, while a raw `Contract` admits an
entry with none. Such an entry is neither dropped nor padded: decoding fails
with `Error.emptyEnum`, naming its position and name (`decode_error_iff`,
`decode_error_entry`). `Representable` is that remaining representation
obligation; it is not discharged here and it does not narrow the raw domain.

Proved for a successful decoding:
- `decode_collect`: the collected declarations are exactly the raw entries,
  in order, each an enum part of the given contract scope (`decode_collect_shape`);
- `sourceMembers_eq` / `sourceMember?_eq`: Source lookup of an enum's members
  (`Env.declOf .enum`) and of a member's index agrees with the raw
  `lookupBy` / `findIdx?` lookup (the reading of `enumLit?`), absent names
  included, in any environment that adds only non-enum declarations;
- `enumSize_eq`: the Source layout's `enumSize` is the raw member count.

Not established here: the reading of enum uses (`E.m`, conversions, enum-typed
variables erased to `uint`), type reconstruction, and semantic binding; those
stay with the complete-unit decoder.
-/
namespace Solidity.Correctness.Lowering.Total.EnumDecode

open Solidity.Semantics (lookupBy)

/-- Why an enum table has no Source representation. -/
inductive Error where
  /-- The entry at `index`, named `name`, has no member; Source enums have one. -/
  | emptyEnum (index : Nat) (name : Name)
  deriving DecidableEq, Repr

/-- Decode the entries from position `i` on; the first memberless entry fails. -/
def decodeList (i : Nat) : List (Name × List Name) →
    Except Error (Source.Syn (.list (.part false)))
  | [] => .ok .nil
  | (n, []) :: _ => .error (.emptyEnum i n)
  | (n, m :: ms) :: es => do
    let rest ← decodeList (i + 1) es
    pure (.cons (.enum n m ms) rest)

/-- The contract's enums as ordered Source contract parts. -/
def decode (C : Contract) : Except Error (Source.Syn (.list (.part false))) :=
  decodeList 0 C.enums

/-- The representation obligation: every enum entry has a member. -/
def Representable (C : Contract) : Prop := ∀ e ∈ C.enums, e.2 ≠ []

instance (C : Contract) : Decidable (Representable C) :=
  inferInstanceAs (Decidable (∀ e ∈ C.enums, e.2 ≠ []))

/-! ## Readings of a declaration and of the raw table -/

/-- The name and ordered members an enum declaration carries. -/
def entryOf : Source.Decl → Option (Name × List Name)
  | ⟨.enum, _, _, _, .enum n f r⟩ => some (n, f :: r)
  | _ => none

/-- The members of the declaration found, if it is an enum declaration. -/
def membersOf : Option Source.Decl → Option (List String)
  | some ⟨.enum, _, _, _, .enum _ f r⟩ => some (f :: r)
  | _ => none

/-- Source lookup of an enum's ordered members, by declaration name. -/
def sourceMembers (E : Source.Env) (dn : Source.DeclName) : Option (List String) :=
  membersOf (E.declOf .enum dn)

/-- Source lookup of a member's index. -/
def sourceMember? (E : Source.Env) (dn : Source.DeclName) (m : String) : Option Nat :=
  (sourceMembers E dn).bind (·.idxOf? m)

/-- Raw lookup of a member's index, as `enumLit?` reads `E.m`. -/
def rawMember? (C : Contract) (n m : Name) : Option Nat :=
  (lookupBy n C.enums).bind fun ms => ms.findIdx? (· == m)

/-! ## Failure exactly on the representation obligation -/

private theorem decodeList_ok_iff (i : Nat) :
    ∀ es : List (Name × List Name),
      (∃ ps, decodeList i es = .ok ps) ↔ ∀ e ∈ es, e.2 ≠ []
  | [] => by simp [decodeList]
  | (n, []) :: _ => by simp [decodeList]
  | (n, m :: ms) :: es => by
    have ih := decodeList_ok_iff (i + 1) es
    cases h : decodeList (i + 1) es with
    | error err =>
      simp only [h, reduceCtorEq, exists_false, false_iff] at ih
      simp only [decodeList, h, bind, Except.bind, reduceCtorEq, exists_false, false_iff]
      intro hall
      exact ih fun e he => hall e (List.mem_cons_of_mem _ he)
    | ok ps =>
      simp only [h, Except.ok.injEq, exists_eq', true_iff] at ih
      simp only [decodeList, h, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        exists_eq', true_iff, List.mem_cons, forall_eq_or_imp]
      exact ⟨by simp, ih⟩

/-- Decoding succeeds exactly on representable tables. -/
theorem decode_ok_iff (C : Contract) : (∃ ps, decode C = .ok ps) ↔ Representable C :=
  decodeList_ok_iff 0 C.enums

/-- Decoding fails exactly when some entry has no member. -/
theorem decode_error_iff (C : Contract) :
    (∃ err, decode C = .error err) ↔ ¬ Representable C := by
  rw [← decode_ok_iff]
  cases decode C <;> simp

private theorem decodeList_error_entry :
    ∀ (i : Nat) (es : List (Name × List Name)) (j : Nat) (n : Name),
      decodeList i es = .error (.emptyEnum j n) → i ≤ j ∧ es[j - i]? = some (n, [])
  | i, [], _, _, h => by simp [decodeList] at h
  | i, (n', []) :: _, j, n, h => by
    simp only [decodeList, Except.error.injEq, Error.emptyEnum.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | i, (n', m :: ms) :: es, j, n, h => by
    cases hr : decodeList (i + 1) es with
    | error err =>
      simp only [decodeList, hr, bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨hle, hget⟩ := decodeList_error_entry (i + 1) es j n hr
      refine ⟨by omega, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using hget
    | ok ps => simp [decodeList, hr, bind, Except.bind, pure, Except.pure] at h

/-- A failure names a memberless entry: its position and its name. -/
theorem decode_error_entry {C : Contract} {j : Nat} {n : Name}
    (h : decode C = .error (.emptyEnum j n)) : C.enums[j]? = some (n, []) := by
  simpa using (decodeList_error_entry 0 C.enums j n h).2

/-! ## Exact declarations -/

private theorem decodeList_collect (s : String) :
    ∀ (i : Nat) (es : List (Name × List Name)) (ps : Source.Syn (.list (.part false))),
      decodeList i es = .ok ps →
        (ps.collect (some s)).map entryOf = es.map some ∧
        ∀ d ∈ ps.collect (some s), ∃ n f r,
          d = ⟨.enum, n, some s, false, .enum n f r⟩
  | _, [], ps, h => by
    simp only [decodeList, Except.ok.injEq] at h
    subst h
    simp [Source.Syn.collect]
  | _, (n, []) :: _, _, h => by simp [decodeList] at h
  | i, (n, m :: ms) :: es, ps, h => by
    cases hr : decodeList (i + 1) es with
    | error err => simp [decodeList, hr, bind, Except.bind] at h
    | ok qs =>
      simp only [decodeList, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨ih₁, ih₂⟩ := decodeList_collect s (i + 1) es qs hr
      refine ⟨?_, ?_⟩
      · simp [Source.Syn.collect, ih₁, entryOf]
      · intro d hd
        simp only [Source.Syn.collect, List.cons_append, List.nil_append,
          List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact ⟨n, m, ms, rfl⟩
        · exact ih₂ d hd

/-- **Exactly the raw declarations**: the collected declarations read back as
the raw entries, names and members in order, with none missing or added. -/
theorem decode_collect {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) (s : String) :
    (ps.collect (some s)).map entryOf = C.enums.map some :=
  (decodeList_collect s 0 C.enums ps h).1

/-- Every collected declaration is a contract-level enum of scope `s`, whose
declared name is the name its node carries. -/
theorem decode_collect_shape {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) (s : String) :
    ∀ d ∈ ps.collect (some s), ∃ n f r, d = ⟨.enum, n, some s, false, .enum n f r⟩ :=
  (decodeList_collect s 0 C.enums ps h).2

/-- The number of declarations is the number of raw entries. -/
theorem decode_length {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) (s : String) :
    (ps.collect (some s)).length = C.enums.length := by
  simpa using congrArg List.length (decode_collect h s)

/-! ## Lookup agreement -/

private theorem find?_nonEnum {dn : Source.DeclName} (post : List Source.Decl)
    (hpost : ∀ d ∈ post, d.kind ≠ .enum) :
    post.find? (fun d => d.kind == .enum && d.scope == dn.scope && d.name == dn.name) = none := by
  rw [List.find?_eq_none]
  intro d hd
  simp [hpost d hd]

private theorem membersOf_find? (s : String) (dn : Source.DeclName) (hs : dn.scope = some s)
    (post : List Source.Decl) (hpost : ∀ d ∈ post, d.kind ≠ .enum) :
    ∀ (i : Nat) (es : List (Name × List Name)) (ps : Source.Syn (.list (.part false))),
      decodeList i es = .ok ps →
        membersOf ((ps.collect (some s) ++ post).find?
          (fun d => d.kind == .enum && d.scope == dn.scope && d.name == dn.name)) =
          lookupBy dn.name es
  | _, [], ps, h => by
    simp only [decodeList, Except.ok.injEq] at h
    subst h
    simp [Source.Syn.collect, find?_nonEnum post hpost, membersOf, lookupBy]
  | _, (n, []) :: _, _, h => by simp [decodeList] at h
  | i, (n, m :: ms) :: es, ps, h => by
    cases hr : decodeList (i + 1) es with
    | error err => simp [decodeList, hr, bind, Except.bind] at h
    | ok qs =>
      simp only [decodeList, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      have ih := membersOf_find? s dn hs post hpost (i + 1) es qs hr
      by_cases hn : dn.name = n
      · subst hn
        simp [Source.Syn.collect, hs, membersOf, lookupBy]
      · have hn' : (n == dn.name) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h' => hn h'.symm
        simp only [Source.Syn.collect, List.cons_append, List.nil_append, List.find?_cons,
          hn', Bool.and_false] at ih ⊢
        simpa [lookupBy, hn] using ih

/-- **Member lists agree**: in an environment that adds only non-enum
declarations around the decoded ones, Source lookup of the enum `n` in the
decoded scope returns exactly the raw member list, and nothing when the raw
table has no such enum. -/
theorem sourceMembers_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (n : Name) :
    sourceMembers E ⟨some s, n⟩ = lookupBy n C.enums := by
  unfold sourceMembers Source.Env.declOf
  rw [hE, List.append_assoc, List.find?_append, find?_nonEnum (dn := ⟨some s, n⟩) pre hpre,
    Option.none_or]
  exact membersOf_find? s ⟨some s, n⟩ rfl post hpost 0 C.enums ps h

/-- **Member indices agree**, including unsuccessful lookup: an unknown enum
or an unknown member is `none` on both sides. -/
theorem sourceMember?_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (n m : Name) :
    sourceMember? E ⟨some s, n⟩ m = rawMember? C n m := by
  simp only [sourceMember?, rawMember?, sourceMembers_eq h hE hpre hpost n, List.idxOf?]

/-- The Source layout's member count is the raw member count (`0` for an enum
the table lacks, as `Env.layout` reads a missing declaration). -/
theorem enumSize_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (n : Name) :
    E.layout.enumSize ⟨some s, n⟩ = ((lookupBy n C.enums).map List.length).getD 0 := by
  rw [← sourceMembers_eq h hE hpre hpost n]
  simp only [Source.Env.layout, sourceMembers]
  split <;> simp_all [membersOf]

end Solidity.Correctness.Lowering.Total.EnumDecode
