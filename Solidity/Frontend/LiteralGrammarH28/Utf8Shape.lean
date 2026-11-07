import Solidity.Frontend.LiteralGrammarH28.EncodingValue

/-! # Byte shape and value recovery of unicode escapes

Backfill for the literal grammar lane. A `\uHHHH` escape names a code point
below 65536; the original arithmetic (`utf8`, related independently by
`CodepointBytes`) emits a lead byte and continuation bytes with the UTF-8 bit
patterns, never an overlong form, and the code point is recoverable from the
bytes. Surrogate code points 0xD800–0xDFFF have the same shape: this is a
statement about byte patterns, not scalar-value validation, which the model
deliberately does not add (`docs/feature-work/h28-literal-grammar.md`).
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- A UTF-8 continuation byte, `10xxxxxx`. -/
def Continuation (b : UInt8) : Prop := 128 ≤ b.toNat ∧ b.toNat < 192

/-- Lead/continuation bit patterns of a one-, two- or three-byte sequence,
excluding overlong two-byte (lead 0xC0/0xC1) and three-byte (0xE0 with a
second byte below 0xA0) forms. -/
def Utf8Shape : Bytes → Prop
  | [a] => a.toNat < 128
  | [a, b] => 194 ≤ a.toNat ∧ a.toNat < 224 ∧ Continuation b
  | [a, b, c] => 224 ≤ a.toNat ∧ a.toNat < 240 ∧ (a.toNat = 224 → 160 ≤ b.toNat) ∧
      Continuation b ∧ Continuation c
  | _ => False

/-- The code point read back from a shaped sequence. -/
def utf8Value : Bytes → Nat
  | [a] => a.toNat
  | [a, b] => (a.toNat - 192) * 64 + (b.toNat - 128)
  | [a, b, c] => (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)
  | _ => 0

private theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := rfl

theorem CodepointBytes.shape {cp : Nat} {out : Bytes} (bound : cp < 65536)
    (h : CodepointBytes cp out) : Utf8Shape out := by
  cases h with
  | one lt =>
    simp only [Utf8Shape, toNat_toUInt8]
    omega
  | two lo hi =>
    simp only [Utf8Shape, Continuation, toNat_toUInt8]
    omega
  | three lo =>
    simp only [Utf8Shape, Continuation, toNat_toUInt8]
    omega

theorem CodepointBytes.value {cp : Nat} {out : Bytes} (bound : cp < 65536)
    (h : CodepointBytes cp out) : utf8Value out = cp := by
  cases h with
  | one lt =>
    simp only [utf8Value, toNat_toUInt8]
    omega
  | two lo hi =>
    simp only [utf8Value, toNat_toUInt8]
    omega
  | three lo =>
    simp only [utf8Value, toNat_toUInt8]
    omega

/-- Distinct four-digit escape values never collide in bytes (surrogates included). -/
theorem utf8_injective {cp cp' : Nat} (bound : cp < 65536) (bound' : cp' < 65536)
    (e : utf8 cp = utf8 cp') : cp = cp' := by
  have v : utf8Value (utf8 cp) = cp := (codepoint_sound cp).value bound
  have v' : utf8Value (utf8 cp') = cp' := (codepoint_sound cp').value bound'
  rw [e] at v
  exact v.symm.trans v'

/-- Every `\uHHHH` escape emits a well-shaped, non-overlong byte sequence. -/
theorem uniEscape_shape {a b c d : UInt8}
    (ha : isHexDigit a = true) (hb : isHexDigit b = true)
    (hc : isHexDigit c = true) (hd : isHexDigit d = true) :
    Utf8Shape (utf8 (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d)) :=
  (codepoint_sound _).shape (hexQuad_lt65536 ha hb hc hd)

/-- The escape's code point is recovered exactly from its emitted bytes. -/
theorem uniEscape_value {a b c d : UInt8}
    (ha : isHexDigit a = true) (hb : isHexDigit b = true)
    (hc : isHexDigit c = true) (hd : isHexDigit d = true) :
    utf8Value (utf8 (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d)) =
      ((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d :=
  (codepoint_sound _).value (hexQuad_lt65536 ha hb hc hd)

/-- Inhabited controls: a surrogate keeps the three-byte shape (no scalar check). -/
example : utf8 0xD800 = [0xED, 0xA0, 0x80] := by decide
example : Utf8Shape (utf8 0xD800) := (codepoint_sound _).shape (by decide)
/-- Negative control: an overlong two-byte spelling of NUL is not a shape. -/
example : ¬ Utf8Shape [0xC0, 0x80] := by
  simp only [Utf8Shape, Continuation]
  decide

/-- Negative control: an overlong three-byte spelling (lead 0xE0, second byte below 0xA0). -/
example : ¬ Utf8Shape [0xE0, 0x80, 0x80] := by
  simp only [Utf8Shape, Continuation]
  decide
/-- Inhabited two-byte control. -/
example : utf8 0x80 = [0xC2, 0x80] ∧ Utf8Shape (utf8 0x80) :=
  ⟨by decide, (codepoint_sound _).shape (by decide)⟩

end Solidity.Frontend.LiteralGrammarH28
