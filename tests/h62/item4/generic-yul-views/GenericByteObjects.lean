import Solidity.Yul.Views.ByteObjects

/-! Additive typed control schema. No source representation, admission rule,
interface or proof budget changes. The schema quantifies over arbitrary bytes,
addresses and residual memory; its proof does not decide a fixture table. -/
namespace Solidity.Yul.Views.H62

structure ByteObjectFixture (D : Source.Layout) where
  bytes : List UInt8
  length_bound : bytes.length < 2 ^ 256
  residual : ByteView
  base : Nat

def ByteObjectFixture.view {D : Source.Layout} (f : ByteObjectFixture D) : ByteView :=
  bytesObjectView f.bytes f.length_bound f.residual f.base

/-- One semantic packet, including both intrinsically typed decoders and all
live payload/residual positions. No restriction on alignment or padding. -/
structure ByteObjectFacts {D : Source.Layout} (f : ByteObjectFixture D) : Prop where
  header : mload f.view f.base = ⟨f.bytes.length, f.length_bound⟩
  bytes : decodeBytesObject D f.view f.base = .bytes f.bytes
  string : decodeStringObject D f.view f.base = .string f.bytes
  payload : ∀ i (hi : i < f.bytes.length), f.view (f.base + 32 + i) = f.bytes[i]
  residual : ∀ a, a < f.base ∨ f.base + 32 + f.bytes.length ≤ a →
    f.view a = f.residual a
  source_payload : ∀ off v,
    ObjectByte (Source.Data.bytes (D := D) (l := .memory) f.bytes) off v →
      f.view (f.base + off) = v
  idempotent : bytesObjectView f.bytes f.length_bound f.view f.base = f.view

/-- The proof uses the existing semantic laws over arbitrary fixtures. -/
theorem byteObjectFacts {D : Source.Layout} (f : ByteObjectFixture D) : ByteObjectFacts f where
  header := bytesObject_header f.bytes f.length_bound f.residual f.base
  bytes := decode_bytesObjectView D f.bytes f.length_bound f.residual f.base
  string := decode_stringObjectView D f.bytes f.length_bound f.residual f.base
  payload := bytesObject_payload f.bytes f.length_bound f.residual f.base
  residual := bytesObject_residual f.bytes f.length_bound f.residual f.base
  source_payload := bytesObject_source_payload f.bytes f.length_bound f.residual f.base
  idempotent := bytesObject_idempotent f.bytes f.length_bound f.residual f.base

/-- Regression guard against collapsing distinct payloads into one image at the
same base. Decoding recovers arbitrary bytes despite residual/alignment choices;
this does not assert allocator or compiler adequacy. -/
theorem byteObjectBytes_injective {D : Source.Layout}
    (left right : ByteObjectFixture D) (same_base : left.base = right.base)
    (same_view : left.view = right.view) : left.bytes = right.bytes := by
  have observed : decodeBytesObject D left.view left.base =
      decodeBytesObject D right.view left.base :=
    congrArg (fun memory => decodeBytesObject D memory left.base) same_view
  rw [(byteObjectFacts left).bytes] at observed
  rw [same_base, (byteObjectFacts right).bytes] at observed
  exact Source.Data.bytes.inj observed

#print axioms byteObjectBytes_injective
#print axioms byteObjectFacts
end Solidity.Yul.Views.H62
