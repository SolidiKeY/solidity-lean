import Solidity.Frontend.LiteralGrammarH28.Body

/-! # Independent escape encoding values

CodepointBytes states byte arithmetic without invoking utf8. It deliberately
models the pinned helper for every Nat, not a Unicode scalar validator. In
particular the three-byte arm has no surrogate or upper-range exclusion.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive CodepointBytes : Nat → Bytes → Prop where
  | one {cp : Nat} : cp < 128 → CodepointBytes cp [cp.toUInt8]
  | two {cp : Nat} : 128 ≤ cp → cp < 2048 →
      CodepointBytes cp [(192 + cp / 64).toUInt8, (128 + cp % 64).toUInt8]
  | three {cp : Nat} : 2048 ≤ cp →
      CodepointBytes cp [(224 + cp / 4096).toUInt8,
        (128 + cp / 64 % 64).toUInt8, (128 + cp % 64).toUInt8]

theorem codepoint_complete {cp : Nat} {out : Bytes} (h : CodepointBytes cp out) : utf8 cp = out := by
  cases h with
  | one small => simp only [utf8, if_pos small]
  | two lower upper =>
    have large : ¬cp < 128 := by omega
    simp only [utf8, if_neg large, if_pos upper]
  | three lower =>
    have first : ¬cp < 128 := by omega
    have second : ¬cp < 2048 := by omega
    simp only [utf8, if_neg first, if_neg second]

theorem codepoint_sound (cp : Nat) : CodepointBytes cp (utf8 cp) := by
  unfold utf8
  split
  · exact .one (by assumption)
  · split
    · exact .two (by omega) (by assumption)
    · exact .three (by omega)

theorem codepoint_iff (cp : Nat) (out : Bytes) : utf8 cp = out ↔ CodepointBytes cp out := by
  constructor
  · intro h; subst out; exact codepoint_sound cp
  · exact codepoint_complete

theorem codepoint_nonempty {cp : Nat} {out : Bytes} (h : CodepointBytes cp out) : out ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem hexVal_lt16 {b : UInt8} (digit : isHexDigit b = true) : hexVal b < 16 := by
  simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at digit
  dsimp only [hexVal]
  split
  · omega
  · split <;> omega

theorem hexPair_lt256 {a b : UInt8} (ha : isHexDigit a = true) (hb : isHexDigit b = true) :
    hexVal a * 16 + hexVal b < 256 := by
  have first : hexVal a < 16 := hexVal_lt16 ha
  have second : hexVal b < 16 := hexVal_lt16 hb
  omega

theorem hexPair_exactNat {a b : UInt8} (ha : isHexDigit a = true) (hb : isHexDigit b = true) :
    (pairValue a b).toNat = hexVal a * 16 + hexVal b := by
  simpa only [pairValue, Nat.toUInt8_eq] using
    (UInt8.toNat_ofNat_of_lt' (hexPair_lt256 ha hb))

theorem hexQuad_lt65536 {a b c d : UInt8}
    (ha : isHexDigit a = true) (hb : isHexDigit b = true)
    (hc : isHexDigit c = true) (hd : isHexDigit d = true) :
    ((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d < 65536 := by
  have aBound : hexVal a < 16 := hexVal_lt16 ha
  have bBound : hexVal b < 16 := hexVal_lt16 hb
  have cBound : hexVal c < 16 := hexVal_lt16 hc
  have dBound : hexVal d < 16 := hexVal_lt16 hd
  omega

theorem Body.uni_value {allowed : UInt8 → Bool} {a b c d : UInt8} {raw out bytes : Bytes}
    (ha : isHexDigit a = true) (hb : isHexDigit b = true)
    (hc : isHexDigit c = true) (hd : isHexDigit d = true)
    (value : CodepointBytes (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d) bytes)
    (tail : Body allowed raw out) :
    Body allowed (92 :: 117 :: a :: b :: c :: d :: raw) (bytes ++ out) := by
  rw [← codepoint_complete value]
  exact .uni ha hb hc hd tail

end Solidity.Frontend.LiteralGrammarH28
