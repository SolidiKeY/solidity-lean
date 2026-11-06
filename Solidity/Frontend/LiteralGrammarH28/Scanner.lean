import Solidity.Frontend.LiteralGrammarH28.Quoted

/-! # Independent quote scanner and exact suffixes

Scan relates input bytes, consumed bytes through the closer and the untouched
suffix. It admits arbitrary escaped bytes, matching scanning before decoding.
All scanner equivalence theorems quantify over actual literal delimiters.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive Scan (q : UInt8) : Bytes → Bytes → Bytes → Prop where
  | close {suffix : Bytes} : Scan q (q :: suffix) [q] suffix
  | char {b : UInt8} {raw pre suffix : Bytes} :
      b ≠ q → b ≠ 92 → isNewline b = false → Scan q raw pre suffix →
      Scan q (b :: raw) (b :: pre) suffix
  | esc {c : UInt8} {raw pre suffix : Bytes} :
      (c = 13 → raw.head? ≠ some 10) → Scan q raw pre suffix →
      Scan q (92 :: c :: raw) (92 :: c :: pre) suffix
  | crlf {raw pre suffix : Bytes} : Scan q raw pre suffix →
      Scan q (92 :: 13 :: 10 :: raw) (92 :: 13 :: 10 :: pre) suffix

theorem Scan.input_nonempty {q : UInt8} {raw pre suffix : Bytes}
    (h : Scan q raw pre suffix) : raw ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem Scan.partition {q : UInt8} {raw pre suffix : Bytes}
    (h : Scan q raw pre suffix) : raw = pre ++ suffix := by
  induction h with
  | close => rfl
  | char _ _ _ _ ih => simp only [List.cons_append, ih]
  | esc _ _ ih => simp only [List.cons_append, ih]
  | crlf _ ih => simp only [List.cons_append, ih]

theorem untilQuote_complete {q : UInt8} (quote : IsQuote q)
    {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    untilQuote q raw = some (pre, suffix) := by
  induction h with
  | close => rcases quote with rfl | rfl <;> rfl
  | char noQuote noSlash noNewline h ih =>
    simp only [noSlash, imp_false, false_implies, implies_true, untilQuote,
      beq_iff_eq, noQuote, ite_false, noNewline, Bool.false_eq_true, ih, Option.map_some]
  | @esc c raw pre suffix boundary h ih =>
    unfold untilQuote
    split
    · rename_i eq
      cases eq
    · rename_i eq
      obtain ⟨hc, hr⟩ := List.cons.inj (List.cons.inj eq).2
      exact False.elim (boundary hc (by rw [hr]; rfl))
    · rename_i eq
      obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj eq).2
      rw [ih]
      rfl
    · rename_i noCR noEsc eq
      obtain ⟨rfl, rfl⟩ := List.cons.inj eq
      exact False.elim (noEsc c raw rfl rfl)
  | crlf h ih =>
    change (untilQuote _ _).map _ = _
    rw [ih]
    rfl

/-- Every scanner success yields independent Scan evidence, even for arbitrary q. -/
theorem untilQuote_sound (q : UInt8) (raw : Bytes) :
    ∀ pre suffix, untilQuote q raw = some (pre, suffix) → Scan q raw pre suffix := by
  fun_induction untilQuote q raw <;> intro pre suffix h
  case case1 => cases h
  case case2 ih =>
    obtain ⟨pair, hp, eq⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨p, s⟩
    cases eq
    exact .crlf (ih p s hp)
  case case3 c raw noCR ih =>
    obtain ⟨pair, hp, eq⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨p, s⟩
    cases eq
    apply Scan.esc
    · intro hc first
      cases raw with
      | nil => cases first
      | cons d tail =>
        have e : d = 10 := Option.some.inj first
        subst d
        exact noCR tail hc rfl
    · exact ih p s hp
  case case4 b raw noCR noEsc isQuote =>
    have eq : b = q := beq_iff_eq.mp isQuote
    subst b
    cases h
    exact .close
  case case6 b raw noCR noEsc notQuote noNewline ih =>
    obtain ⟨pair, hp, eq⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨p, s⟩
    cases eq
    have tailScan : Scan q raw p s := ih p s hp
    apply Scan.char
    · exact (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr notQuote))
    · intro hb
      cases raw with
      | nil => exact tailScan.input_nonempty rfl
      | cons c tail => exact noEsc c tail hb rfl
    · exact Bool.eq_false_iff.mpr noNewline
    · exact tailScan
  all_goals cases h

theorem untilQuote_iff (q : UInt8) (quote : IsQuote q) (raw pre suffix : Bytes) :
    untilQuote q raw = some (pre, suffix) ↔ Scan q raw pre suffix :=
  ⟨untilQuote_sound q raw pre suffix, untilQuote_complete quote⟩

/-- Every consumed scanner prefix contains a closing byte. -/
theorem Scan.closer {q : UInt8} {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    ∃ body, pre = body ++ [q] := by
  induction h with
  | close => exact ⟨[], rfl⟩
  | @char b raw pre suffix _ _ _ _ ih =>
    obtain ⟨body, rfl⟩ := ih
    exact ⟨b :: body, rfl⟩
  | @esc c raw pre suffix _ _ ih =>
    obtain ⟨body, rfl⟩ := ih
    exact ⟨92 :: c :: body, rfl⟩
  | crlf _ ih =>
    obtain ⟨body, rfl⟩ := ih
    exact ⟨92 :: 13 :: 10 :: body, rfl⟩

/-- Arbitrary bytes appended beyond the closer remain entirely in the suffix. -/
theorem Scan.append_suffix {q : UInt8} {raw pre suffix : Bytes}
    (h : Scan q raw pre suffix) (extra : Bytes) :
    Scan q (raw ++ extra) pre (suffix ++ extra) := by
  induction h with
  | close => exact .close
  | char noQ noSlash noLine _ ih => exact .char noQ noSlash noLine ih
  | crlf _ ih => exact .crlf ih
  | @esc c raw pre suffix boundary h ih =>
    apply Scan.esc
    · intro hc
      cases raw with
      | nil => exact False.elim (h.input_nonempty rfl)
      | cons b rest => exact boundary hc
    · exact ih

theorem untilQuote_append_suffix {q : UInt8} (quote : IsQuote q)
    {raw pre suffix : Bytes} (h : untilQuote q raw = some (pre, suffix)) (extra : Bytes) :
    untilQuote q (raw ++ extra) = some (pre, suffix ++ extra) :=
  untilQuote_complete quote ((untilQuote_sound q raw pre suffix h).append_suffix extra)

/-- Raw-byte predicates that are safe between literal delimiters. -/
def SafeFor (allowed : UInt8 → Bool) (q : UInt8) : Prop :=
  ∀ b, allowed b = true → b ≠ q ∧ isNewline b = false

theorem printable_safe (q : UInt8) : SafeFor (printable q) q := by
  intro b hb
  simp only [printable, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  refine ⟨hb.2, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro line
  have lines : b.toNat = 10 ∨ b.toNat = 13 := by
    simpa only [isNewline, Bool.or_eq_true, beq_iff_eq] using line
  rcases lines with low | low <;> omega

theorem unicode_safe (q : UInt8) : SafeFor (unicodeChar q) q := by
  intro b hb
  simp only [unicodeChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  refine ⟨hb.1, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro line
  simp only [line, Bool.not_true, Bool.false_eq_true] at hb
  exact hb.2

theorem hexDigit_safe {q b : UInt8} (quote : IsQuote q) (digit : isHexDigit b = true) :
    b ≠ q ∧ b ≠ 92 ∧ isNewline b = false := by
  constructor
  · intro e
    subst b
    rcases quote with rfl | rfl <;> cases digit
  · constructor
    · intro e
      subst b
      cases digit
    · apply Bool.eq_false_iff.mpr
      intro line
      have lines : b.toNat = 10 ∨ b.toNat = 13 := by
        simpa only [isNewline, Bool.or_eq_true, beq_iff_eq] using line
      rcases lines with eq | eq
      · have e : b = 10 := UInt8.toNat_inj.mp eq
        subst b; cases digit
      · have e : b = 13 := UInt8.toNat_inj.mp eq
        subst b; cases digit

/-- A decoded body's exact raw bytes scan to the closer with any suffix. -/
theorem Body.scan {allowed : UInt8 → Bool} {q : UInt8}
    (quote : IsQuote q) (safe : SafeFor allowed q)
    {raw out : Bytes} (h : Body allowed raw out) (suffix : Bytes) :
    Scan q (raw ++ q :: suffix) (raw ++ [q]) suffix := by
  induction h with
  | nil => exact .close
  | char allowedB noSlash _ ih =>
    exact .char (safe _ allowedB).1 noSlash (safe _ allowedB).2 ih
  | crlf _ ih => exact .crlf ih
  | @esc c raw out o esc boundary _ ih =>
    apply Scan.esc
    · intro hc
      cases raw with
      | nil =>
        intro eq
        have e : q = 10 := Option.some.inj eq
        rcases quote with rfl | rfl <;> cases e
      | cons b rest => exact boundary hc
    · exact ih
  | @hex a b raw out ha hb _ ih =>
    have aSafe : a ≠ q ∧ a ≠ 92 ∧ isNewline a = false := hexDigit_safe quote ha
    have bSafe : b ≠ q ∧ b ≠ 92 ∧ isNewline b = false := hexDigit_safe quote hb
    apply Scan.esc
    · intro e
      have diff : (120 : UInt8) ≠ 13 := by decide +kernel
      exact False.elim (diff e)
    · exact .char aSafe.1 aSafe.2.1 aSafe.2.2 (.char bSafe.1 bSafe.2.1 bSafe.2.2 ih)
  | @uni a b c d raw out ha hb hc hd _ ih =>
    have aSafe : a ≠ q ∧ a ≠ 92 ∧ isNewline a = false := hexDigit_safe quote ha
    have bSafe : b ≠ q ∧ b ≠ 92 ∧ isNewline b = false := hexDigit_safe quote hb
    have cSafe : c ≠ q ∧ c ≠ 92 ∧ isNewline c = false := hexDigit_safe quote hc
    have dSafe : d ≠ q ∧ d ≠ 92 ∧ isNewline d = false := hexDigit_safe quote hd
    apply Scan.esc
    · intro e
      have diff : (117 : UInt8) ≠ 13 := by decide +kernel
      exact False.elim (diff e)
    · exact .char aSafe.1 aSafe.2.1 aSafe.2.2
        (.char bSafe.1 bSafe.2.1 bSafe.2.2
        (.char cSafe.1 cSafe.2.1 cSafe.2.2 (.char dSafe.1 dSafe.2.1 dSafe.2.2 ih)))

/-- Simultaneous exact consumed raw bytes, untouched suffix and decoded value. -/
theorem body_scan_value {allowed : UInt8 → Bool} {q : UInt8}
    (quote : IsQuote q) (safe : SafeFor allowed q) {raw out : Bytes}
    (h : Body allowed raw out) (suffix : Bytes) :
    untilQuote q (raw ++ q :: suffix) = some (raw ++ [q], suffix) ∧
      strBody allowed raw = some out :=
  ⟨untilQuote_complete quote (h.scan quote safe suffix), body_complete h⟩

/-- Exact hex-body scanning preserves the independently proved hex value. -/
theorem HexBody.scan {q : UInt8} (quote : IsQuote q)
    {raw out : Bytes} (h : HexBody raw out) (suffix : Bytes) :
    Scan q (raw ++ q :: suffix) (raw ++ [q]) suffix := by
  induction h with
  | nil => exact .close
  | @pair a b raw out ha hb _ _ ih =>
    have aSafe : a ≠ q ∧ a ≠ 92 ∧ isNewline a = false := hexDigit_safe quote ha
    have bSafe : b ≠ q ∧ b ≠ 92 ∧ isNewline b = false := hexDigit_safe quote hb
    exact .char aSafe.1 aSafe.2.1 aSafe.2.2 (.char bSafe.1 bSafe.2.1 bSafe.2.2 ih)
  | @sep a b raw out ha hb _ _ ih =>
    have aSafe : a ≠ q ∧ a ≠ 92 ∧ isNewline a = false := hexDigit_safe quote ha
    have bSafe : b ≠ q ∧ b ≠ 92 ∧ isNewline b = false := hexDigit_safe quote hb
    have underscoreQ : (95 : UInt8) ≠ q := by
      rcases quote with rfl | rfl <;> decide +kernel
    have underscoreSlash : (95 : UInt8) ≠ 92 := by decide +kernel
    have underscoreLine : isNewline 95 = false := by decide +kernel
    exact .char aSafe.1 aSafe.2.1 aSafe.2.2
      (.char bSafe.1 bSafe.2.1 bSafe.2.2 (.char underscoreQ underscoreSlash underscoreLine ih))

theorem hex_scan_value {q : UInt8} (quote : IsQuote q) {raw out : Bytes}
    (h : HexBody raw out) (suffix : Bytes) :
    untilQuote q (raw ++ q :: suffix) = some (raw ++ [q], suffix) ∧
      hexBody raw = some out :=
  ⟨untilQuote_complete quote (h.scan quote suffix), hexBody_complete h⟩

/-- Exact scan of a constructive spelling for any byte value list and suffix. -/
theorem encodePlain_scan (q : UInt8) (quote : IsQuote q) (bytes suffix : Bytes) :
    untilQuote q (encodeBody bytes ++ q :: suffix) =
      some (encodeBody bytes ++ [q], suffix) ∧
      plainString (quoteBytes q (encodeBody bytes)) = some bytes :=
  ⟨(body_scan_value quote (printable_safe q) (encodeBody_grammar _ bytes) suffix).1,
    encodePlain_roundtrip q quote bytes⟩

end Solidity.Frontend.LiteralGrammarH28


