import Solidity.Frontend.LiteralGrammarH28.HexEncoding

/-! # Independent string body grammar

Single-character escapes are explicit constructors. An escaped CR followed
by LF is one CRLF escape; the CR-only constructor excludes that overlap.
Raw unicode bytes and surrogate escapes retain the existing byte semantics.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive Escape : UInt8 → Bytes → Prop where
  | single : Escape 39 [39]
  | double : Escape 34 [34]
  | slash : Escape 92 [92]
  | n : Escape 110 [10]
  | r : Escape 114 [13]
  | t : Escape 116 [9]
  | lf : Escape 10 []
  | cr : Escape 13 []

theorem escape_complete {c : UInt8} {out : Bytes} (h : Escape c out) :
    escapeChar c = some out := by
  cases h <;> rfl

/-- Every successful simple-escape decoder branch has a grammar constructor. -/
theorem escape_sound (c : UInt8) (out : Bytes) (h : escapeChar c = some out) :
    Escape c out := by
  dsimp only [escapeChar] at h
  split at h
  · rename_i tag
    simp only [Bool.or_eq_true, beq_iff_eq] at tag
    rcases tag with (tag | tag) | tag
    · have e : c = 39 := UInt8.toNat_inj.mp tag
      subst c; cases h; exact .single
    · have e : c = 34 := UInt8.toNat_inj.mp tag
      subst c; cases h; exact .double
    · have e : c = 92 := UInt8.toNat_inj.mp tag
      subst c; cases h; exact .slash
  · split at h
    · rename_i tag
      have e : c = 110 := UInt8.toNat_inj.mp (beq_iff_eq.mp tag)
      subst c; cases h; exact .n
    · split at h
      · rename_i tag
        have e : c = 114 := UInt8.toNat_inj.mp (beq_iff_eq.mp tag)
        subst c; cases h; exact .r
      · split at h
        · rename_i tag
          have e : c = 116 := UInt8.toNat_inj.mp (beq_iff_eq.mp tag)
          subst c; cases h; exact .t
        · split at h
          · rename_i tag
            simp only [Bool.or_eq_true, beq_iff_eq] at tag
            rcases tag with tag | tag
            · have e : c = 10 := UInt8.toNat_inj.mp tag
              subst c; cases h; exact .lf
            · have e : c = 13 := UInt8.toNat_inj.mp tag
              subst c; cases h; exact .cr
          · cases h

inductive Body (allowed : UInt8 → Bool) : Bytes → Bytes → Prop where
  | nil : Body allowed [] []
  | char {b : UInt8} {raw out : Bytes} : allowed b = true → b ≠ 92 →
      Body allowed raw out → Body allowed (b :: raw) (b :: out)
  | crlf {raw out : Bytes} : Body allowed raw out →
      Body allowed (92 :: 13 :: 10 :: raw) out
  | esc {c : UInt8} {raw out o : Bytes} : Escape c o →
      (c = 13 → raw.head? ≠ some 10) → Body allowed raw out →
      Body allowed (92 :: c :: raw) (o ++ out)
  | hex {a b : UInt8} {raw out : Bytes} :
      isHexDigit a = true → isHexDigit b = true → Body allowed raw out →
      Body allowed (92 :: 120 :: a :: b :: raw) (pairValue a b :: out)
  | uni {a b c d : UInt8} {raw out : Bytes} :
      isHexDigit a = true → isHexDigit b = true →
      isHexDigit c = true → isHexDigit d = true → Body allowed raw out →
      Body allowed (92 :: 117 :: a :: b :: c :: d :: raw)
        (utf8 (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d) ++ out)

/-- Exact value completeness, with no restriction on the byte predicate. -/
theorem body_complete {allowed : UInt8 → Bool} {raw out : Bytes}
    (h : Body allowed raw out) : strBody allowed raw = some out := by
  induction h with
  | nil => rfl
  | @char b raw out allowedB noSlash h ih =>
    have noSlashNat : b.toNat ≠ 92 := by
      intro e
      exact noSlash (UInt8.toNat_inj.mp e)
    simp only [noSlash, imp_false, false_implies, implies_true, strBody, allowedB,
      Bool.true_and, bne_iff_ne, ne_eq, noSlashNat, not_false_eq_true, ite_true,
      ih, Option.map_some]
  | crlf h ih => exact ih
  | @hex a b raw out ha hb h ih =>
    simp only [strBody, ha, hb, Bool.and_self, ite_true, ih, Option.map_some, pairValue]
  | @uni a b c d raw out ha hb hc hd h ih =>
    simp only [strBody, ha, hb, hc, hd, Bool.and_self, ite_true, ih, Option.map_some]
  | @esc c raw out o esc boundary h ih =>
    cases esc with
    | cr =>
      cases raw with
      | nil =>
        have e : out = [] := by simpa only [strBody, Option.some.injEq] using ih.symm
        subst out; rfl
      | cons d tail =>
        have hd : d ≠ 10 := by
          intro e
          exact boundary rfl (congrArg some e)
        have notX : (13 : UInt8) ≠ 120 := by decide +kernel
        have notU : (13 : UInt8) ≠ 117 := by decide +kernel
        unfold strBody
        split
        · rename_i eq
          cases eq
        · rename_i eq
          exact False.elim (notX (List.cons.inj (List.cons.inj eq).2).1)
        · rename_i eq
          exact False.elim (notU (List.cons.inj (List.cons.inj eq).2).1)
        · rename_i eq
          exact False.elim (hd (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).1)
        · rename_i eq
          obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj eq).2
          change (strBody allowed (d :: tail)).map ([] ++ ·) = some ([] ++ out)
          rw [ih]
          rfl
        · rename_i noX noU noCR noEsc eq
          obtain ⟨rfl, rfl⟩ := List.cons.inj eq
          exact False.elim (noEsc 13 (d :: tail) rfl rfl)
    | single => change (strBody _ _).map ([39] ++ ·) = _; rw [ih]; rfl
    | double => change (strBody _ _).map ([34] ++ ·) = _; rw [ih]; rfl
    | slash => change (strBody _ _).map ([92] ++ ·) = _; rw [ih]; rfl
    | n => change (strBody _ _).map ([10] ++ ·) = _; rw [ih]; rfl
    | r => change (strBody _ _).map ([13] ++ ·) = _; rw [ih]; rfl
    | t => change (strBody _ _).map ([9] ++ ·) = _; rw [ih]; rfl
    | lf => change (strBody _ _).map ([] ++ ·) = _; rw [ih]; rfl

/-- Reuse the pinned existing string-body soundness theorem. -/
theorem Body.toStrBody {allowed : UInt8 → Bool} {raw out : Bytes}
    (h : Body allowed raw out) : StrBody allowed raw out :=
  strBody_sound allowed raw out (body_complete h)

/-- Every accepted body inhabits the independent grammar with the exact value. -/
theorem body_sound (allowed : UInt8 → Bool) (raw : Bytes) :
    ∀ out, strBody allowed raw = some out → Body allowed raw out := by
  fun_induction strBody allowed raw <;> intro out h
  case case1 => cases h; exact .nil
  case case2 digits ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at digits
    exact .hex digits.1 digits.2 (ih v hv)
  case case4 digits ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at digits
    exact .uni digits.1.1.1 digits.1.1.2 digits.1.2 digits.2 (ih v hv)
  case case6 ih => exact .crlf (ih out h)
  case case7 c raw notHex notUni notCRLF n decoded o ho ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    apply Body.esc (escape_sound c o (by simpa only [escapeChar] using ho))
    · intro hc first
      subst c
      cases raw with
      | nil => cases first
      | cons d tail =>
        have e : d = 10 := Option.some.inj first
        subst d
        exact notCRLF tail rfl rfl
    · exact ih v hv
  case case9 allowedB ih =>
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at allowedB
    apply Body.char allowedB.1
    · intro e
      subst e
      exact allowedB.2 rfl
    · exact ih v hv
  all_goals cases h

/-- Unrestricted acceptance/value equivalence, including CRLF priority. -/
theorem body_iff (allowed : UInt8 → Bool) (raw out : Bytes) :
    strBody allowed raw = some out ↔ Body allowed raw out :=
  ⟨body_sound allowed raw out, body_complete⟩

/-- Grammar values are unique even with arbitrary raw-byte predicates. -/
theorem Body.deterministic {allowed : UInt8 → Bool} {raw x y : Bytes}
    (hx : Body allowed raw x) (hy : Body allowed raw y) : x = y :=
  Option.some.inj ((body_complete hx).symm.trans (body_complete hy))

theorem body_none_iff (allowed : UInt8 → Bool) (raw : Bytes) :
    strBody allowed raw = none ↔ ∀ out, ¬ Body allowed raw out := by
  constructor
  · intro hn out h
    have e : strBody allowed raw = some out := body_complete h
    rw [hn] at e
    cases e
  · intro h
    cases e : strBody allowed raw with
    | none => rfl
    | some out => exact False.elim (h out (body_sound allowed raw out e))

/-- Exact encoding widths, including surrogate code points. No scalar check. -/
theorem utf8_length (cp : Nat) :
    (utf8 cp).length = if cp < 0x80 then 1 else if cp < 0x800 then 2 else 3 := by
  unfold utf8
  split
  · rfl
  · split <;> rfl

theorem utf8_length_le (cp : Nat) : (utf8 cp).length ≤ 3 := by
  rw [utf8_length]
  split
  · decide
  · split <;> decide

theorem Escape.length_le {c : UInt8} {out : Bytes} (h : Escape c out) :
    out.length ≤ 1 := by
  cases h <;> decide

/-- Decoding never expands a string body in bytes. -/
theorem Body.length_le {allowed : UInt8 → Bool} {raw out : Bytes}
    (h : Body allowed raw out) : out.length ≤ raw.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | char _ _ _ ih => simp only [List.length_cons]; omega
  | crlf _ ih => simp only [List.length_cons]; omega
  | @esc c raw out o esc _ _ ih =>
    have small : o.length ≤ 1 := Escape.length_le esc
    simp only [List.length_append, List.length_cons]
    omega
  | hex _ _ _ ih => simp only [List.length_cons]; omega
  | @uni a b c d raw out _ _ _ _ _ ih =>
    have small : (utf8 (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d)).length ≤ 3 :=
      utf8_length_le _
    simp only [List.length_append, List.length_cons]
    omega

/-- Canonical byte spelling using a two-digit x escape for every byte. -/
def encodeBody : Bytes → Bytes
  | [] => []
  | b :: rest => 92 :: 120 :: highDigit b :: lowDigit b :: encodeBody rest

theorem encodeBody_grammar (allowed : UInt8 → Bool) (bytes : Bytes) :
    Body allowed (encodeBody bytes) bytes := by
  induction bytes with
  | nil => exact .nil
  | cons b rest ih =>
    obtain ⟨hi, lo, value, _⟩ := byteEncoding_facts b
    have h : Body allowed (92 :: 120 :: highDigit b :: lowDigit b :: encodeBody rest)
        (pairValue (highDigit b) (lowDigit b) :: rest) := .hex hi lo ih
    simpa only [encodeBody, value] using h

/-- Every byte value has a constructive accepted spelling for every predicate. -/
theorem encodeBody_roundtrip (allowed : UInt8 → Bool) (bytes : Bytes) :
    strBody allowed (encodeBody bytes) = some bytes :=
  body_complete (encodeBody_grammar allowed bytes)

theorem encodeBody_length (bytes : Bytes) : (encodeBody bytes).length = 4 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp only [encodeBody, List.length_cons, ih]; omega

end Solidity.Frontend.LiteralGrammarH28


