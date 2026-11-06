import Solidity.Frontend.LiteralGrammarH28.Classification

/-! # Constructive tagged literal encodings

Raw canonical escape spellings pass the existing line/bidi guards. This is
an exact round trip of the pinned byte decoder, including arbitrary decoded
bytes; it does not assert solc's downstream Unicode-validation acceptance.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def RegularByte (b : UInt8) : Prop := b ≠ 11 ∧ b ≠ 12 ∧ b ≠ 226

theorem hex_regular {b : UInt8} (h : isHexDigit b = true) : RegularByte b := by
  constructor
  · intro e; subst b; cases h
  · constructor
    · intro e; subst b; cases h
    · intro e; subst b; cases h

theorem encodeBody_regular (bytes : Bytes) : ∀ b, b ∈ encodeBody bytes → RegularByte b := by
  induction bytes with
  | nil => intro b member; cases member
  | cons byte rest ih =>
    intro b member
    simp only [encodeBody, List.mem_cons] at member
    rcases member with rfl | rfl | rfl | rfl | member
    · unfold RegularByte; decide +kernel
    · unfold RegularByte; decide +kernel
    · exact hex_regular (byteEncoding_facts byte).1
    · exact hex_regular (byteEncoding_facts byte).2.1
    · exact ih b member

theorem regular_irregularBreak (raw : Bytes) (regular : ∀ b, b ∈ raw → RegularByte b) :
    irregularBreak raw = false := by
  have first : raw.any (fun c => c.toNat == 11 || c.toNat == 12) = false := by
    apply List.any_eq_false.mpr
    intro b member bad
    have eqs : b.toNat = 11 ∨ b.toNat = 12 := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using bad
    rcases eqs with eq | eq
    · exact (regular b member).1 (UInt8.toNat_inj.mp eq)
    · exact (regular b member).2.1 (UInt8.toNat_inj.mp eq)
  have second : (List.range raw.length).any (fun i =>
      (raw.drop i).take 3 == [226, 128, 168] || (raw.drop i).take 3 == [226, 128, 169]) = false := by
    apply List.any_eq_false.mpr
    intro i _ bad
    have eqs : (raw.drop i).take 3 = [226, 128, 168] ∨ (raw.drop i).take 3 = [226, 128, 169] := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using bad
    rcases eqs with eq | eq
    all_goals
      have member : (226 : UInt8) ∈ (raw.drop i).take 3 := by rw [eq]; exact List.mem_cons_self
      exact (regular 226 (List.mem_of_mem_drop (List.mem_of_mem_take member))).2.2 rfl
  simp only [irregularBreak, first, second, Bool.or_self]

theorem bidi_walk_noE2 (raw : Bytes) : ∀ depth,
    (∀ b, b ∈ raw → b ≠ 226) → bidiBalanced.walk raw depth = (depth == 0) := by
  induction raw with
  | nil => intro depth _; rfl
  | cons b rest ih =>
    intro depth avoid
    have head : b ≠ 226 := avoid b List.mem_cons_self
    have tail : ∀ c, c ∈ rest → c ≠ 226 := fun c member => avoid c (List.mem_cons_of_mem b member)
    simp only [head, imp_false, false_implies, implies_true, bidiBalanced.walk, ih depth tail]

theorem regular_bidiBalanced (raw : Bytes) (regular : ∀ b, b ∈ raw → RegularByte b) :
    bidiBalanced raw = true :=
  bidi_walk_noE2 raw 0 (fun b member => (regular b member).2.2)

theorem encodeHexLiteral_grammar (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    HexLiteral (hexPrefix ++ quoteBytes q (encodeHex bytes)) bytes :=
  ⟨q, encodeHex bytes, quote, rfl, encodeHex_grammar bytes⟩

theorem encodeUnicodeLiteral_grammar (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    UnicodeLiteral (unicodePrefix ++ quoteBytes q (encodeBody bytes)) bytes :=
  ⟨q, encodeBody bytes, quote, rfl, regular_irregularBreak _ (encodeBody_regular bytes),
    regular_bidiBalanced _ (encodeBody_regular bytes), encodeBody_grammar _ bytes⟩

theorem encodeHexLiteral_roundtrip (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    solTok (hexPrefix ++ quoteBytes q (encodeHex bytes)) = some (.hexStr bytes) :=
  (encodeHexLiteral_grammar q quote bytes).solTok

theorem encodeUnicodeLiteral_roundtrip (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    solTok (unicodePrefix ++ quoteBytes q (encodeBody bytes)) = some (.unicodeStr bytes) :=
  (encodeUnicodeLiteral_grammar q quote bytes).solTok

theorem encodeHexLiteral_length (q : UInt8) (bytes : Bytes) :
    (hexPrefix ++ quoteBytes q (encodeHex bytes)).length = 2 * bytes.length + 5 := by
  simp only [List.length_append, quoteBytes_length, encodeHex_length, hexPrefix,
    List.length_cons, List.length_nil]
  omega

theorem encodeUnicodeLiteral_length (q : UInt8) (bytes : Bytes) :
    (unicodePrefix ++ quoteBytes q (encodeBody bytes)).length = 4 * bytes.length + 9 := by
  simp only [List.length_append, quoteBytes_length, encodeBody_length, unicodePrefix,
    List.length_cons, List.length_nil]
  omega

end Solidity.Frontend.LiteralGrammarH28
