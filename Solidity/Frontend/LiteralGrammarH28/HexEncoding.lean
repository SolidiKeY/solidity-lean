import Solidity.Frontend.LiteralGrammarH28.Hex

/-! # Constructive hexadecimal body encoding

All 256 byte encodings are checked by the kernel. The list round trip is a
universal induction over arbitrary byte lists, not a finite sample bound.
-/

namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Lowercase hexadecimal digit spelling. Only nibbles are supplied below. -/
def hexDigit (n : Nat) : UInt8 :=
  if n < 10 then (48 + n).toUInt8 else (87 + n).toUInt8

def highDigit (b : UInt8) : UInt8 := hexDigit (b.toNat / 16)
def lowDigit (b : UInt8) : UInt8 := hexDigit (b.toNat % 16)

/-- Independent pair spelling/value facts for a byte. -/
def ByteEncodingFacts (b : UInt8) : Prop :=
  isHexDigit (highDigit b) = true ∧ isHexDigit (lowDigit b) = true ∧
  pairValue (highDigit b) (lowDigit b) = b ∧ highDigit b ≠ 95
  deriving Decidable

/-- Exhaustive finite kernel control, no decoder occurs in its predicate. -/
theorem byteEncoding_table :
    (List.range 256).all (fun n => decide (ByteEncodingFacts n.toUInt8)) = true := by
  decide +kernel

/-- Every byte has a pair spelling with its exact value. -/
theorem byteEncoding_facts (b : UInt8) : ByteEncodingFacts b := by
  have h : decide (ByteEncodingFacts b.toNat.toUInt8) = true :=
    List.all_eq_true.mp byteEncoding_table b.toNat
    (List.mem_range.mpr b.toNat_lt_size)
  have h' : ByteEncodingFacts b.toNat.toUInt8 := of_decide_eq_true h
  simpa only [Nat.toUInt8_eq, UInt8.ofNat_toNat] using h'

/-- Two lowercase digits per byte, without separators. -/
def encodeHex : Bytes → Bytes
  | [] => []
  | b :: rest => highDigit b :: lowDigit b :: encodeHex rest

/-- The encoding inhabits the independent grammar for every byte list. -/
theorem encodeHex_grammar (bytes : Bytes) : HexBody (encodeHex bytes) bytes := by
  induction bytes with
  | nil => exact .nil
  | cons b rest ih =>
    obtain ⟨hi, lo, value, _⟩ := byteEncoding_facts b
    have boundary : (encodeHex rest).head? ≠ some 95 := by
      cases rest with
      | nil => intro e; cases e
      | cons c tail =>
        intro e
        exact (byteEncoding_facts c).2.2.2 (Option.some.inj e)
    have h : HexBody (highDigit b :: lowDigit b :: encodeHex rest)
        (pairValue (highDigit b) (lowDigit b) :: rest) := .pair hi lo boundary ih
    simpa only [encodeHex, value] using h

/-- Constructive round trip against the existing decoder, for arbitrary length. -/
theorem encodeHex_roundtrip (bytes : Bytes) : hexBody (encodeHex bytes) = some bytes :=
  hexBody_complete (encodeHex_grammar bytes)

/-- The canonical encoding has exactly two source bytes per value byte. -/
theorem encodeHex_length (bytes : Bytes) : (encodeHex bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp only [encodeHex, List.length_cons, ih]; omega

end Solidity.Frontend.LiteralGrammarH28
