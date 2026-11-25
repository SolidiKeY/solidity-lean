import Solidity.Correctness.Lowering.Total.StructDecode

/-!
# Struct member rows: support and first-failure correspondence

Row support of the actual `ReferenceDecode.spellType`/`spellRef` and
`StructDecode.members`: two width tables whose first rows (`Semantics.lookupBy`)
agree at the keys `ReferenceDecode.readTy` lists give the same complete `Except`
result (`spellType_congr`, `spellRef_congr`, `members_congr`). Lookup is first
match, so rows after the first of a key are irrelevant (`agree_shadow`), and rows
whose key is outside the support can be filtered away (`members_filter`,
`members_filter_support`). A struct reference reads no row (`spellRef_struct`).
`readTy` is conservative: these lemmas use only that every row read is listed,
never that every listed key is read or matters.

First failure of `StructDecode.members`, `part`, `parts` and `decode`, branch by
branch in the definitions' priority: `members_error_iff` (the first member, by
position, without a spelling, and its `ReferenceDecode.Error`); `stray_eq_some_iff`
(the first width row outside the support); `part_error_iff` (a name that is not
written, then a member failure, then no members, then a stray row);
`parts_error_iff`, `decode_error_iff` (the first entry, by position offset from
the starting index, that is not `Representable`). `Error.index`, `Error.written`,
`Error.table` name the entry (`part_error_entry`, `parts_error_index`).

Complete-unit assembly, nested resolved-table agreement, retained `RawTy`
agreement, frame correspondence and semantic binding are not here.
-/
namespace Solidity.Correctness.Lowering.Total.StructRows

open Solidity.Semantics (lookupBy structDef structWidths isEnc)
open Source (Syn DataLoc)
open ReferenceDecode (spellType spellRef readTy readRef leafKeys)
open StructDecode (members stray part parts decode Representable)

/-! ## Row support -/

/-- Two width tables have the same first row at every key of `keys`. -/
def Agree (keys : List Name) (w w' : List (Name × Nat)) : Prop :=
  ∀ k ∈ keys, lookupBy k w = lookupBy k w'

/-- The keys the members' spellings may read: what `StructDecode.stray` checks rows against. -/
def support (fs : List (Name × Ty)) : List Name := fs.flatMap fun x => readTy x.1 x.2

variable {keys keys' : List Name} {w w' : List (Name × Nat)}

theorem Agree.mono (h : Agree keys w w') (sub : ∀ k ∈ keys', k ∈ keys) : Agree keys' w w' :=
  fun k hk => h k (sub k hk)
theorem Agree.left {ks : List Name} (h : Agree (keys ++ ks) w w') : Agree keys w w' :=
  h.mono fun _ hk => List.mem_append_left _ hk
theorem Agree.right {ks : List Name} (h : Agree (ks ++ keys) w w') : Agree keys w w' :=
  h.mono fun _ hk => List.mem_append_right _ hk
theorem Agree.symm (h : Agree keys w w') : Agree keys w' w := fun k hk => (h k hk).symm

/-- `elemB` reads exactly the first rows of `leafKeys`. -/
theorem elemB_congr {key : Name} (h : Agree (leafKeys key) w w') (p : PrimTy) :
    Decode.elemB w key p = Decode.elemB w' key p := by
  have h0 := h key (by simp [leafKeys])
  have h1 := h (key ++ "#address") (by simp [leafKeys])
  have h2 := h (key ++ "#bytes") (by simp [leafKeys])
  simp only [Decode.elemB, Decode.elemA, Decode.isAddress, Decode.stateBits, h0, h1, h2]

/-- A struct reference reads no row: its spelling is the written name only. -/
theorem spellRef_struct (C : Contract) (key : Name) (loc : DataLoc) (s : Name) :
    spellRef C w key loc (.struct s) = spellRef C w' key loc (.struct s) := by
  simp only [spellRef]

mutual
/-- **Row support of a spelling**: agreement at the keys `readTy` lists gives the same
complete result, success or error. -/
theorem spellType_congr (C : Contract) : (T : Ty) → (key : Name) → (loc : DataLoc) →
    Agree (readTy key T) w w' → spellType C w key loc T = spellType C w' key loc T
  | .prim p, key, _, h => by
      simp only [readTy] at h
      simp only [spellType, elemB_congr h p]
  | .ref R, key, loc, h => by
      simp only [readTy] at h
      simpa only [spellType] using spellRef_congr C R key loc h
theorem spellRef_congr (C : Contract) : (R : RefTy) → (key : Name) → (loc : DataLoc) →
    Agree (readRef key R) w w' → spellRef C w key loc R = spellRef C w' key loc R
  | .struct s, key, loc, _ => spellRef_struct C key loc s
  | .array T, key, loc, h | .fixed T _, key, loc, h => by
      simp only [readRef] at h
      simp only [spellRef, spellType_congr C T _ loc h]
  | .mapping K V, key, loc, h => by
      simp only [readRef] at h
      simp only [spellRef, elemB_congr h.left K, spellType_congr C V _ .storage h.right]
end

/-- **Row support of the members**, in order. -/
theorem members_congr (C : Contract) :
    (fs : List (Name × Ty)) → Agree (support fs) w w' → members C w fs = members C w' fs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [support, List.flatMap_cons] at h
      simp only [members, spellType_congr C x.2 x.1 .storage h.left,
        members_congr C xs h.right]

/-- Filtering keeps the first row of every key it keeps. -/
theorem lookupBy_filter_of {α : Type} {k : Name} {p : Name × α → Bool}
    (hp : ∀ v, p (k, v) = true) : ∀ l : List (Name × α), lookupBy k (l.filter p) = lookupBy k l
  | [] => rfl
  | (k', v) :: l => by
      by_cases hk : k = k'
      · subst hk; simp [hp, lookupBy]
      · simp only [List.filter_cons]
        split <;> simp [lookupBy, hk, lookupBy_filter_of hp l]

/-- Filtering away rows outside `keys` keeps agreement at `keys`. -/
theorem agree_filter {p : Name × Nat → Bool} (hp : ∀ k ∈ keys, ∀ v, p (k, v) = true)
    (w : List (Name × Nat)) : Agree keys (w.filter p) w :=
  fun k hk => lookupBy_filter_of (hp k hk) w

/-- First match: the rows after the first row of a key do not matter. -/
theorem agree_shadow (keys : List Name) (k : Name) (v : Nat) (w : List (Name × Nat)) :
    Agree keys ((k, v) :: w) ((k, v) :: w.filter (·.1 != k)) := by
  intro k' _
  by_cases hk : k' = k
  · subst hk; simp [lookupBy]
  · simp only [lookupBy, hk, if_false]
    exact (lookupBy_filter_of (fun _ => by simpa using hk) w).symm

/-- **Filtering**: members spell the same at the rows whose key a predicate covering the
support keeps. -/
theorem members_filter (C : Contract) (fs : List (Name × Ty)) {S : Name → Bool}
    (hS : ∀ k ∈ support fs, S k = true) (w : List (Name × Nat)) :
    members C (w.filter fun r => S r.1) fs = members C w fs :=
  members_congr C fs (agree_filter (fun k hk _ => hS k hk) w)

theorem members_filter_support (C : Contract) (fs : List (Name × Ty)) (w : List (Name × Nat)) :
    members C (w.filter fun r => (support fs).contains r.1) fs = members C w fs :=
  members_filter C fs (fun k hk => by simpa using hk) w

theorem spellType_filter (C : Contract) (T : Ty) (key : Name) (loc : DataLoc) {S : Name → Bool}
    (hS : ∀ k ∈ readTy key T, S k = true) (w : List (Name × Nat)) :
    spellType C (w.filter fun r => S r.1) key loc T = spellType C w key loc T :=
  spellType_congr C T key loc (agree_filter (fun k hk _ => hS k hk) w)

/-! ## Stray rows -/

/-- `stray` is exactly the support check: the first row outside the support. -/
theorem stray_eq_some_iff {fs : List (Name × Ty)} {r : Name × Nat} :
    stray w fs = some r ↔ ∃ pre post, w = pre ++ r :: post ∧
      (∀ r' ∈ pre, r'.1 ∈ support fs) ∧ r.1 ∉ support fs := by
  simp only [stray, List.find?_eq_some_iff_append, support]
  constructor
  · rintro ⟨hr, pre, post, rfl, hpre⟩
    exact ⟨pre, post, rfl, fun r' m => by simpa using hpre r' m, by simpa using hr⟩
  · rintro ⟨pre, post, rfl, hpre, hr⟩
    exact ⟨by simpa using hr, pre, post, rfl, fun r' m => by simpa using hpre r' m⟩

theorem stray_eq_none_iff {fs : List (Name × Ty)} :
    stray w fs = none ↔ ∀ r ∈ w, r.1 ∈ support fs := by
  simp [stray, support]

/-- After filtering to the support no row is stray. -/
theorem stray_filter_support (fs : List (Name × Ty)) (w : List (Name × Nat)) :
    stray (w.filter fun r => (support fs).contains r.1) fs = none :=
  stray_eq_none_iff.2 fun r m => by simpa using (List.mem_filter.1 m).2

/-! ## First failure -/

/-- **First failing member**: the earlier members spell, this one fails with `e`, and
the error names it. Duplicate member names are told apart by position. -/
theorem members_error_iff (C : Contract) (w : List (Name × Nat)) :
    ∀ (fs : List (Name × Ty)) (n : Name) (e : ReferenceDecode.Error),
      members C w fs = .error (n, e) ↔ ∃ pre x post, fs = pre ++ x :: post ∧
        (∀ y ∈ pre, ∃ t, spellType C w y.1 .storage y.2 = .ok t) ∧
        spellType C w x.1 .storage x.2 = .error e ∧ n = x.1
  | [], n, e => by
      simp only [members, reduceCtorEq, false_iff]
      rintro ⟨pre, x, post, h, -⟩
      cases pre <;> cases h
  | x :: xs, n, e => by
      have ih := members_error_iff C w xs n e
      cases hx : spellType C w x.1 .storage x.2 with
      | error e0 =>
        simp only [members, hx, Except.error.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨[], x, xs, rfl, by simp, hx, rfl⟩
        · rintro ⟨pre, y, post, h, hpre, hy, rfl⟩
          cases pre with
          | nil =>
            cases h; rw [hx] at hy; cases hy; exact ⟨rfl, rfl⟩
          | cons z pre =>
            cases h
            obtain ⟨t, ht⟩ := hpre x List.mem_cons_self
            rw [hx] at ht; cases ht
      | ok t =>
        have step : members C w (x :: xs) = .error (n, e) ↔ members C w xs = .error (n, e) := by
          simp only [members, hx]
          cases members C w xs <;> simp [bind, Except.bind]
        rw [step, ih]
        constructor
        · rintro ⟨pre, y, post, rfl, hpre, hy, rfl⟩
          refine ⟨x :: pre, y, post, rfl, ?_, hy, rfl⟩
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact ⟨t, hx⟩
          · exact hpre z hz
        · rintro ⟨pre, y, post, h, hpre, hy, rfl⟩
          cases pre with
          | nil => cases h; rw [hx] at hy; cases hy
          | cons z pre =>
            cases h
            exact ⟨pre, y, post, rfl, fun z hz => hpre z (List.mem_cons_of_mem _ hz), hy, rfl⟩

/-- The entry position an error names. -/
def Error.index : StructDecode.Error → Nat
  | .notWritten i .. | .noMembers i .. | .member i .. | .unreadRow i .. => i
/-- The written name of the entry an error names. -/
def Error.written : StructDecode.Error → Name
  | .notWritten _ w _ | .noMembers _ w _ | .member _ w .. | .unreadRow _ w .. => w
/-- The table type of the entry an error names. -/
def Error.table : StructDecode.Error → Name
  | .notWritten _ _ t | .noMembers _ _ t | .member _ _ t .. | .unreadRow _ _ t .. => t

/-- **Why an entry fails**, in `part`'s priority: an unwritten name, then the first
failing member, then no members, then the first stray row. -/
theorem part_error_iff {C : Contract} {i : Nat} {entry : Name × Name} {err : StructDecode.Error} :
    part C i entry = .error err ↔
      ((isEnc entry.1 = true ∨ entry.1 = "") ∧ err = .notWritten i entry.1 entry.2) ∨
      (isEnc entry.1 = false ∧ entry.1 ≠ "" ∧
        ((∃ m e, members C (structWidths entry.2) (structDef entry.2) = .error (m, e) ∧
            err = .member i entry.1 entry.2 m e) ∨
          (members C (structWidths entry.2) (structDef entry.2) = .ok .nil ∧
            err = .noMembers i entry.1 entry.2) ∨
          (∃ m ms r, members C (structWidths entry.2) (structDef entry.2) = .ok (.cons m ms) ∧
            stray (structWidths entry.2) (structDef entry.2) = some r ∧
            err = .unreadRow i entry.1 entry.2 r.1 r.2))) := by
  by_cases plain : isEnc entry.1 = true ∨ entry.1 = ""
  · have b : (isEnc entry.1 || entry.1 == "") = true := by
      rcases plain with h | h <;> simp [h]
    simp only [part, b, if_true, Except.error.injEq, plain, true_and]
    constructor
    · intro h; exact .inl h.symm
    · rintro (h | ⟨h, hn, -⟩)
      · exact h.symm
      · rcases plain with p | p
        · rw [p] at h; cases h
        · exact absurd p hn
  · have b : (isEnc entry.1 || entry.1 == "") = false := by
      simp only [not_or] at plain; simp [plain.1, plain.2]
    have enc : isEnc entry.1 = false := by simp only [not_or] at plain; simpa using plain.1
    have name : entry.1 ≠ "" := by simp only [not_or] at plain; exact plain.2
    have nb : (entry.1 == "") = false := by simpa using name
    simp only [part, enc, nb, Bool.or_false, Bool.false_eq_true, if_false, false_and, false_or,
      name, true_and, ne_eq, not_false_eq_true]
    match hm : members C (structWidths entry.2) (structDef entry.2) with
    | .error (m, e) =>
      simp only [Except.error.injEq, Prod.mk.injEq, reduceCtorEq, false_and, exists_false,
        or_false]
      exact ⟨fun h => ⟨m, e, ⟨rfl, rfl⟩, h.symm⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h.symm⟩
    | .ok .nil =>
      simp only [Except.error.injEq, Except.ok.injEq, reduceCtorEq, false_and, exists_false,
        false_or, true_and, or_false]
      exact eq_comm
    | .ok (.cons m ms) =>
      simp only [reduceCtorEq, false_and, exists_false, false_or, Except.ok.injEq]
      cases hs : stray (structWidths entry.2) (structDef entry.2) with
      | none => simp only [reduceCtorEq, false_and, and_false, exists_false]
      | some r =>
        simp only [Except.error.injEq, Option.some.injEq]
        constructor
        · intro h; exact ⟨m, ms, r, rfl, rfl, h.symm⟩
        · rintro ⟨_, _, _, -, rfl, h⟩; exact h.symm

/-- The error of an entry names its position, written name and table type. -/
theorem part_error_entry {C : Contract} {i : Nat} {entry : Name × Name}
    {err : StructDecode.Error} (h : part C i entry = .error err) :
    Error.index err = i ∧ Error.written err = entry.1 ∧ Error.table err = entry.2 := by
  rcases part_error_iff.1 h with ⟨-, rfl⟩ | ⟨-, -, ⟨_, _, -, rfl⟩ | ⟨-, rfl⟩ | ⟨_, _, _, -, -, rfl⟩⟩ <;>
    exact ⟨rfl, rfl, rfl⟩

/-- An entry is representable exactly when it has a declaration, at any position. -/
theorem representable_iff_part {C : Contract} (i : Nat) (entry : Name × Name) :
    Representable C entry ↔ ∃ p, part C i entry = .ok p := by
  constructor
  · rintro ⟨⟨m, ms, hm⟩, r⟩
    exact ⟨_, StructDecode.part_ok_iff.2 ⟨⟨m, ms, rfl, hm⟩, r⟩⟩
  · rintro ⟨p, hp⟩
    obtain ⟨⟨m, ms, -, hm⟩, r⟩ := StructDecode.part_ok_iff.1 hp
    exact ⟨⟨m, ms, hm⟩, r⟩

/-- **First failing entry**: the earlier entries are representable, and this one, at
the starting index plus its position, fails with the error. -/
theorem parts_error_iff {C : Contract} :
    ∀ (i : Nat) (es : List (Name × Name)) (err : StructDecode.Error),
      parts C i es = .error err ↔ ∃ pre e post, es = pre ++ e :: post ∧
        (∀ e' ∈ pre, Representable C e') ∧ part C (i + pre.length) e = .error err
  | _, [], err => by
      simp only [parts, reduceCtorEq, false_iff]
      rintro ⟨pre, e, post, h, -⟩
      cases pre <;> cases h
  | i, e :: es, err => by
      have ih := parts_error_iff (C := C) (i + 1) es err
      cases he : part C i e with
      | error e0 =>
        simp only [parts, he]
        change Except.error e0 = Except.error err ↔ _
        simp only [Except.error.injEq]
        constructor
        · rintro rfl; exact ⟨[], e, es, rfl, by simp, by simpa using he⟩
        · rintro ⟨pre, y, post, h, hpre, hy⟩
          cases pre with
          | nil => cases h; simp only [List.length_nil, Nat.add_zero, he] at hy; cases hy; rfl
          | cons z pre =>
            cases h
            obtain ⟨p, hp⟩ := (representable_iff_part i e).1 (hpre e List.mem_cons_self)
            rw [he] at hp; cases hp
      | ok p =>
        have step : parts C i (e :: es) = .error err ↔ parts C (i + 1) es = .error err := by
          simp only [parts, he]
          cases parts C (i + 1) es <;> simp [bind, Except.bind]
        rw [step, ih]
        constructor
        · rintro ⟨pre, y, post, rfl, hpre, hy⟩
          refine ⟨e :: pre, y, post, rfl, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hy⟩
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact (representable_iff_part i _).2 ⟨p, he⟩
          · exact hpre z hz
        · rintro ⟨pre, y, post, h, hpre, hy⟩
          cases pre with
          | nil => cases h; simp only [List.length_nil, Nat.add_zero, he] at hy; cases hy
          | cons z pre =>
            cases h
            exact ⟨pre, y, post, rfl, fun z hz => hpre z (List.mem_cons_of_mem _ hz),
              by simpa [Nat.add_assoc, Nat.add_comm 1] using hy⟩

/-- The error of `parts` names the failing entry's position offset by the start. -/
theorem parts_error_index {C : Contract} {i : Nat} {es : List (Name × Name)}
    {err : StructDecode.Error} (h : parts C i es = .error err) :
    ∃ pre e post, es = pre ++ e :: post ∧ (∀ e' ∈ pre, Representable C e') ∧
      Error.index err = i + pre.length ∧ Error.written err = e.1 ∧ Error.table err = e.2 ∧
      part C (i + pre.length) e = .error err := by
  obtain ⟨pre, e, post, rfl, hpre, he⟩ := (parts_error_iff i es err).1 h
  exact ⟨pre, e, post, rfl, hpre, (part_error_entry he).1, (part_error_entry he).2.1,
    (part_error_entry he).2.2, he⟩

/-- **First failure of `decode`**: the entry of `Contract.structs` at the position the
error names, after representable entries. -/
theorem decode_error_iff (C : Contract) (err : StructDecode.Error) :
    decode C = .error err ↔ ∃ pre e post, C.structs = pre ++ e :: post ∧
      (∀ e' ∈ pre, Representable C e') ∧ part C pre.length e = .error err := by
  simpa only [decode, Nat.zero_add] using parts_error_iff (C := C) 0 C.structs err

end Solidity.Correctness.Lowering.Total.StructRows
