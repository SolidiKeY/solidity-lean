import Solidity.Correctness.Lowering.Total.RawTypeAgreement.Rows
import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Strings
import Solidity.Syntax.Elab.Context

/-!
# A leaf name as `elabTyW` and as `rawType` read it

`leaf_elem`: a name `Decode.typeNameB` reads as an elementary type, not an enum of
the contract, is a primitive to `elabTyW`, and `Decode.elemB` reads that elementary
type back from the generated rows (a narrow width, the `#address` or `#bytes`
marker). `leaf_struct`: a name `rawLeaf` spells as a struct is, to `elabTyW`, the
struct `Contract.structName?` gives, with no rows. The readers test names with
`String` operations the kernel does not reduce; the tests are compared through the
first character of the name (`hd`).
-/
namespace Solidity.Correctness.Lowering.Total.RawTypeAgreement

open Solidity.Semantics (lookupBy)
open ReferenceDecode (rawElem rawLeaf)
open FunctionTypeParserLaws (Str.startsWith_mk Str.drop_mk)

/-- The first character of a name. -/
def hd (s : String) : Option Char := s.data.head?

theorem startsWith_data (s p : String) :
    s.startsWith p = decide (s.data.take p.data.length = p.data) := Str.startsWith_mk s.data p.data

theorem drop_data (s : String) (n : Nat) : s.drop n = ⟨s.data.drop n⟩ := Str.drop_mk s.data n

theorem hd_of_startsWith {s p : String} {c : Char} (h : s.startsWith p = true)
    (hp : hd p = some c) : hd s = some c := by
  rw [startsWith_data] at h
  have h := of_decide_eq_true h
  unfold hd at *
  cases hs : s.data with
  | nil => rw [hs, List.take_nil] at h; rw [← h] at hp; cases hp
  | cons a l =>
    cases hpd : p.data with
    | nil => rw [hpd] at hp; cases hp
    | cons b r =>
      rw [hs, hpd] at h; rw [hpd] at hp
      simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at h
      simpa [h.1] using hp

/-- No narrow width is written with no digits, or as `256`. -/
theorem repr_narrow : ∀ n, n < 256 → toString n ≠ "" ∧ toString n ≠ "256" := by decide +kernel

theorem narrowTy?_some {s : String} {p : PrimTy} {n : Nat} (h : narrowTy? s = some (p, n)) :
    p ≠ .bool ∧ 8 ≤ n ∧ n < 256 ∧ n % 8 = 0 ∧
      ((s.startsWith "uint" = true ∧ toString n = s.drop 4) ∨
        (s.startsWith "int" = true ∧ toString n = s.drop 3)) := by
  unfold narrowTy? at h
  by_cases hu : s.startsWith "uint" = true
  · simp only [hu, if_true] at h
    cases ht : (s.drop 4).toNat? with
    | none => rw [ht] at h; cases h
    | some m =>
      rw [ht] at h
      simp at h
      obtain ⟨c, rfl, rfl⟩ := h
      simp [c, hu]
  · by_cases hi : s.startsWith "int" = true
    · simp only [hu, hi, Bool.false_eq_true, if_true, if_false] at h
      cases ht : (s.drop 3).toNat? with
      | none => rw [ht] at h; cases h
      | some m =>
        rw [ht] at h
        simp at h
        obtain ⟨c, rfl, rfl⟩ := h
        simp [c, hi]
    · simp only [hu, hi] at h
      split at h <;> cases h

theorem bytesTy?_some {s : String} {n : Nat} (h : bytesTy? s = some n) :
    1 ≤ n ∧ n ≤ 32 ∧ s.startsWith "bytes" = true ∧ toString n = s.drop 5 := by
  unfold bytesTy? at h
  split at h
  · rename_i sw
    split at h
    · split at h
      · rename_i ok; cases h; simp at ok; exact ⟨ok.1.1, ok.1.2, sw, ok.2⟩
      · cases h
    · cases h
  · cases h

theorem narrowTy?_hd {s : String} {x : PrimTy × Nat} (h : narrowTy? s = some x) :
    hd s = some 'u' ∨ hd s = some 'i' := by
  obtain ⟨-, -, -, -, ⟨sw, -⟩ | ⟨sw, -⟩⟩ := narrowTy?_some (p := x.1) (n := x.2) h
  · exact .inl (hd_of_startsWith sw rfl)
  · exact .inr (hd_of_startsWith sw rfl)

theorem narrowTy?_none_of_hd {s : String} (u : hd s ≠ some 'u') (i : hd s ≠ some 'i') :
    narrowTy? s = none := by
  cases h : narrowTy? s with
  | none => rfl
  | some x => exact (narrowTy?_hd h).elim (absurd · u) (absurd · i)

theorem fn_false_of_hd {s : String} (f : hd s ≠ some 'f') : s.startsWith "function(" = false := by
  cases h : s.startsWith "function(" with
  | false => rfl
  | true => exact absurd (hd_of_startsWith h rfl) f

/-- `uint`, `uint256`, `int` and `int256` are not narrow names. -/
theorem narrowTy?_full {s : String} (h : s = "uint" ∨ s = "uint256" ∨ s = "int" ∨ s = "int256") :
    narrowTy? s = none := by
  cases hn : narrowTy? s with
  | none => rfl
  | some x =>
    obtain ⟨-, -, lt, -, digits⟩ := narrowTy?_some (p := x.1) (n := x.2) hn
    have no := repr_narrow x.2 lt
    rcases h with rfl | rfl | rfl | rfl
    · rcases digits with ⟨-, d⟩ | ⟨sw, -⟩
      · exact absurd (d.trans (drop_data "uint" 4)) no.1
      · exact absurd (hd_of_startsWith sw rfl) (by decide)
    · rcases digits with ⟨-, d⟩ | ⟨sw, -⟩
      · exact absurd (d.trans (drop_data "uint256" 4)) no.2
      · exact absurd (hd_of_startsWith sw rfl) (by decide)
    · rcases digits with ⟨sw, -⟩ | ⟨-, d⟩
      · exact absurd (hd_of_startsWith sw rfl) (by decide)
      · exact absurd (d.trans (drop_data "int" 3)) no.1
    · rcases digits with ⟨sw, -⟩ | ⟨-, d⟩
      · exact absurd (hd_of_startsWith sw rfl) (by decide)
      · exact absurd (d.trans (drop_data "int256" 3)) no.2

theorem primElem_narrow {p : PrimTy} {n : Nat} (h : narrowTy? s = some (p, n)) :
    (Decode.primElem p n).isSome = true := by
  obtain ⟨nb, lo, hi, m, -⟩ := narrowTy?_some h
  have ok : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 := ⟨m, lo, Nat.le_of_lt hi⟩
  cases p <;> simp_all [Decode.primElem]

/-- `rawElem`, as its tests in order. -/
theorem rawElem_eq (s : String) : rawElem s =
    match bytesTy? s with
    | some n => Decode.bytesElem n
    | none =>
      if s = "address" then some .address else if s = "bool" then some .bool
      else if s = "uint" ∨ s = "uint256" then Decode.primElem .uint 256
      else if s = "int" ∨ s = "int256" then Decode.primElem .int 256
      else match narrowTy? s with
        | some (p, bits) => Decode.primElem p bits
        | none => none := by
  unfold rawElem Decode.typeNameB
  cases hb : bytesTy? s with
  | some n => simp only [hb]; cases Decode.bytesElem n <;> rfl
  | none =>
    simp only [hb, Decode.typeNameA, Decode.typeNameW]
    by_cases a : s = "address"
    · rw [if_pos a, if_pos a]
    rw [if_neg a, if_neg a]
    by_cases b : s = "bool"
    · rw [if_pos b, if_pos b]
    rw [if_neg b, if_neg b]
    by_cases u : s = "uint" ∨ s = "uint256"
    · rw [if_pos u, if_pos u]; rfl
    rw [if_neg u, if_neg u]
    by_cases i : s = "int" ∨ s = "int256"
    · rw [if_pos i, if_pos i]; rfl
    rw [if_neg i, if_neg i]
    cases narrowTy? s with
    | none => rfl
    | some x => simp only []; cases Decode.primElem x.1 x.2 <;> rfl

/-- A name with no elementary reading is no value-type name of `valueRows?` either,
unless a function type's. -/
theorem rawElem_none {s : String} (h : rawElem s = none) :
    bytesTy? s = none ∧ narrowTy? s = none ∧ s ≠ "address" ∧ PrimTy.ofName? s = none := by
  rw [rawElem_eq] at h
  cases hb : bytesTy? s with
  | some n =>
    rw [hb] at h
    obtain ⟨lo, hi, -⟩ := bytesTy?_some hb
    simp [Decode.bytesElem, lo, hi] at h
  | none =>
    rw [hb] at h
    simp only at h
    repeat' split at h
    all_goals first | cases h | skip
    · rename_i a b u i p bits hn
      have := primElem_narrow hn; rw [h] at this; cases this
    · rename_i a b u i _ hn
      refine ⟨rfl, hn, a, ?_⟩
      unfold PrimTy.ofName?
      split <;> simp_all

/-! ## The rows `Decode.elemB` reads at the empty path -/

theorem elemB_nil (p : PrimTy) : Decode.elemB [] "" p = Decode.primElem p 256 := by
  simp [Decode.elemB, Decode.elemA, Decode.isAddress, Decode.stateBits, lookupBy]

theorem elemB_width (p : PrimTy) (bits : Nat) :
    Decode.elemB [("", bits)] "" p = Decode.primElem p bits := by
  simp [Decode.elemB, Decode.elemA, Decode.isAddress, Decode.stateBits, lookupBy]

theorem elemB_address : Decode.elemB addressRows "" .uint = some .address := by decide +kernel

theorem elemB_bytes {n : Nat} (lo : 1 ≤ n) (hi : n ≤ 32) :
    Decode.elemB ((if n < 32 then [("", 8 * n)] else []) ++ [("#bytes", n)]) "" .uint =
      Decode.bytesElem n := by
  by_cases lt : n < 32
  · simp [Decode.elemB, Decode.isAddress, Decode.stateBits, lookupBy, lt]
  · have : n = 32 := by omega
    subst this
    decide +kernel

/-- `elemB` at the key of rebased rows reads the generated rows at the empty path. -/
theorem elemB_rebase (key : Name) (ws : List (String × Nat)) (p : PrimTy) :
    Decode.elemB (rebase key ws) key p = Decode.elemB ws "" p := by
  simp only [Decode.elemB, Decode.elemA, Decode.isAddress, Decode.stateBits, lookupBy_rebase,
    lookupBy_rebase_self, String.empty_append]

variable {C : Contract}

/-- A full-width primitive name: no rows. -/
theorem elabTyW_word {s : String} {p : PrimTy} (dyn : dynBytesTy s = false)
    (plain : lookupBy s C.enums = none) (vr : valueRows? s = none)
    (pn : PrimTy.ofName? s = some p) : elabTyW C (.named s) = .ok (.prim p, []) := by
  rw [elabTyW]
  simp [dyn, plain, vr, elabTy, pn, pure, Except.pure, bind, Except.bind]

theorem dyn_false_of_hd {s : String} (b : s ≠ "bytes") (st : hd s ≠ some 's') :
    dynBytesTy s = false := by
  simp only [dynBytesTy, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨b, fun e => st (e ▸ rfl)⟩

/-- **An elementary leaf**: the name is a primitive to `elabTyW`, and the generated
rows spell the elementary type `rawType` writes. An enum of that name is excluded:
`elabTyW` would read the enum, `rawType` the elementary type. -/
theorem leaf_elem {s : String} {e : Source.Elem} (he : rawElem s = some e)
    (plain : lookupBy s C.enums = none) :
    ∃ p ws, elabTyW C (.named s) = .ok (.prim p, ws) ∧ Decode.elemB ws "" p = some e := by
  rw [rawElem_eq] at he
  cases hb : bytesTy? s with
  | some n =>
    rw [hb] at he
    obtain ⟨lo, hi, sw, digits⟩ := bytesTy?_some hb
    have h := hd_of_startsWith (c := 'b') sw rfl
    have dyn : dynBytesTy s = false := dyn_false_of_hd
      (fun e => (repr_narrow n (by omega)).1 (digits.trans (e ▸ drop_data "bytes" 5)))
      (by rw [h]; decide)
    have vr : valueRows? s =
        some (.uint, (if n < 32 then [("", 8 * n)] else []) ++ [("#bytes", n)]) := by
      unfold valueRows?
      rw [if_neg (by rw [fn_false_of_hd (by rw [h]; decide)]; decide),
        if_neg (by simpa using fun e : s = "address" => by rw [e] at h; cases h),
        narrowTy?_none_of_hd (by rw [h]; decide) (by rw [h]; decide), hb]
    exact ⟨.uint, _, by rw [elabTyW]; simp [dyn, plain, vr, pure, Except.pure],
      (elemB_bytes lo hi).trans he⟩
  | none =>
    rw [hb] at he
    simp only at he
    by_cases a : s = "address"
    · subst a
      rw [if_pos rfl] at he; cases he
      exact ⟨.uint, addressRows, by
        have vr : valueRows? "address" = some (.uint, addressRows) := by
          unfold valueRows?
          rw [if_neg (by rw [fn_false_of_hd (by decide)]; decide), if_pos (by decide)]
        rw [elabTyW]; simp [plain, vr, dynBytesTy, pure, Except.pure], elemB_address⟩
    rw [if_neg a] at he
    cases hn : narrowTy? s with
    | some x =>
      obtain ⟨p, bits⟩ := x
      have h := narrowTy?_hd hn
      have dyn : dynBytesTy s = false := dyn_false_of_hd
        (fun e => by subst e; rcases h with h | h <;> cases h)
        (fun e => by rw [e] at h; rcases h with h | h <;> cases h)
      have vr : valueRows? s = some (p, [("", bits)]) := by
        unfold valueRows?
        rw [if_neg (by
            rw [fn_false_of_hd fun e => by rw [e] at h; rcases h with h | h <;> cases h]; decide),
          if_neg (by simpa using a), hn]
      have full : ¬(s = "uint" ∨ s = "uint256" ∨ s = "int" ∨ s = "int256") := fun f => by
        rw [narrowTy?_full f] at hn; cases hn
      have nb : s ≠ "bool" := fun e => by subst e; rcases h with h | h <;> cases h
      rw [if_neg nb, if_neg fun u => full (u.elim .inl (.inr ∘ .inl)),
        if_neg fun i => full (.inr (.inr i)), hn] at he
      exact ⟨p, _, by rw [elabTyW]; simp [dyn, plain, vr, pure, Except.pure],
        (elemB_width p bits).trans he⟩
    | none =>
      rw [hn] at he
      have word : s = "bool" ∨ s = "uint" ∨ s = "uint256" ∨ s = "int" ∨ s = "int256" := by
        false_or_by_contra; rename_i no
        simp only [not_or] at no
        rw [if_neg no.1, if_neg (by simp [no]), if_neg (by simp [no])] at he
        cases he
      have vr : valueRows? s = none := by
        unfold valueRows?
        rw [if_neg (by rcases word with rfl | rfl | rfl | rfl | rfl <;> decide +kernel),
          if_neg (by simpa using a), hn, hb]
      have dyn : dynBytesTy s = false := by
        rcases word with rfl | rfl | rfl | rfl | rfl <;> decide
      rcases word with rfl | rfl | rfl | rfl | rfl
      · exact ⟨.bool, [], elabTyW_word dyn plain vr rfl, by rw [elemB_nil]; simpa [Decode.primElem] using he⟩
      · exact ⟨.uint, [], elabTyW_word dyn plain vr rfl, by rw [elemB_nil]; simpa [Decode.primElem] using he⟩
      · exact ⟨.uint, [], elabTyW_word dyn plain vr rfl, by rw [elemB_nil]; simpa [Decode.primElem] using he⟩
      · exact ⟨.int, [], elabTyW_word dyn plain vr rfl, by rw [elemB_nil]; simpa [Decode.primElem] using he⟩
      · exact ⟨.int, [], elabTyW_word dyn plain vr rfl, by rw [elemB_nil]; simpa [Decode.primElem] using he⟩

/-- **A struct leaf**: a name `rawLeaf` writes as a struct is, to `elabTyW`, the
struct type `Contract.structName?` gives it, with no rows. -/
theorem leaf_struct {s : String} {t : Source.Syn .typeName} (h : rawLeaf C s = .ok t)
    (he : rawElem s = none) : ∃ table, C.structName? s = some table ∧ Semantics.isEnc s = false ∧
      t = .userType ⟨s, []⟩ ∧ elabTyW C (.named s) = .ok (.ref (.struct table), []) := by
  obtain ⟨hb, hn, a, prim⟩ := rawElem_none he
  unfold rawLeaf at h; rw [he] at h
  simp only at h
  split at h; · cases h
  rename_i guard
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at guard
  obtain ⟨⟨⟨enum, fn⟩, dyn⟩, enc⟩ := guard
  split at h
  · rename_i table ht; cases h
    have vr : valueRows? s = none := by
      unfold valueRows?
      rw [if_neg (by simpa [fnTy?] using fn), if_neg (by simpa using a), hn, hb]
    refine ⟨table, ht, enc, rfl, ?_⟩
    rw [elabTyW]
    simp [dyn, enum, vr, elabTy, prim, hn, hb, fn, ht, pure, Except.pure, bind, Except.bind]
  · cases h

end Solidity.Correctness.Lowering.Total.RawTypeAgreement
