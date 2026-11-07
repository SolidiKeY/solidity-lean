import «tests».h62.item4.«generic-yul-views».GenericByteObjects
import Solidity.Yul.Views.ReadControls

/-! Typed table, original-statement instances, and additional boundary coverage.
The original Controls declarations remain read-only and are checked below. -/
namespace Solidity.Yul.Views.H62
open Controls

def unaligned : ByteObjectFixture layout :=
  ⟨[0xaa, 0xbb], by decide, ascending, 129⟩

def fixtures : List (ByteObjectFixture layout) := [
  ⟨[], by decide, zero, 96⟩,
  ⟨[0xaa, 0xbb], by decide, ascending, 129⟩,
  ⟨[0], by decide, (fun _ => 0xa5), 0⟩,
  ⟨List.replicate 31 0xff, by decide, ascending, 127⟩,
  ⟨List.replicate 32 0xaa, by decide, ascending, 128⟩,
  ⟨List.replicate 33 0xbb, by decide, (fun _ => 0xa5), 129⟩,
  ⟨List.replicate 64 0xcc, by decide, ascending, 256⟩]

theorem all_fixtures : ∀ f ∈ fixtures, ByteObjectFacts f := by
  intro f _
  exact byteObjectFacts f

/-- Exact original statement from ReadControls.byte_component_decode. -/
theorem original_byte_component_decode :
    decodeBytesObject layout unalignedBytes 129 = byteObject :=
  (byteObjectFacts unaligned).bytes

/-- Exact original statement, including both live bytes and residual positions. -/
theorem original_byte_component : mload unalignedBytes 129 = 2 ∧ unalignedBytes 162 = 0xbb ∧
    unalignedBytes 163 = 163 ∧ unalignedBytes 128 = 128 := by
  refine ⟨(byteObjectFacts unaligned).header, ?_, ?_, ?_⟩
  · exact (byteObjectFacts unaligned).payload 1 (by decide)
  · exact (byteObjectFacts unaligned).residual 163 (Or.inr (by decide))
  · exact (byteObjectFacts unaligned).residual 128 (Or.inl (by decide))

/-- Correspondence is at the exact existing declaration types, not a weaker
observation or a Bool acceptance flag. -/
example : decodeBytesObject layout unalignedBytes 129 = byteObject := byte_component_decode
example : mload unalignedBytes 129 = 2 ∧ unalignedBytes 162 = 0xbb ∧
    unalignedBytes 163 = 163 ∧ unalignedBytes 128 = 128 := byte_component

/-- Retain existing refusal/negative coverage unchanged. -/
example (f : Field) : ¬ (f.offset = 31 ∧ f.width = 2) := crossing_slot_refused f
example : boolBytes.decode (fun _ => 2) = none := dirty_bool_not_canonical
example : readBytes (mstore zero 128 ⟨0x12345678, by decide⟩) 156 4 ≠
    [0x78, 0x56, 0x34, 0x12] := not_little_endian

/-- Regression guard: the existing short and long unaligned rows share base 129
but cannot share an image. This instantiates the semantic decoder law, rather
than deciding equality of an enumerated byte table. -/
theorem unaligned_images_distinct :
    (fixtures[1]'(by decide)).view ≠ (fixtures[5]'(by decide)).view := by
  intro same
  have bytes := byteObjectBytes_injective
    (fixtures[1]'(by decide)) (fixtures[5]'(by decide)) rfl same
  have lengths : 2 = 33 := congrArg List.length bytes
  omega

/-- Joint inhabitance of the entire bytesObject_payload parameter telescope.
The nonempty payload makes the live-index premise inhabited; this is neither
per-input feasibility nor compiler totality. -/
theorem byte_payload_joint :
    ∃ (bs : List UInt8) (_hl : bs.length < 2 ^ 256) (_m : ByteView)
      (_base i : Nat) (_hi : i < bs.length), True :=
  ⟨[0], by decide, zero, 0, 0, by decide, True.intro⟩

#print axioms byte_payload_joint
#print axioms unaligned_images_distinct
#print axioms all_fixtures
#print axioms original_byte_component
#print axioms original_byte_component_decode
end Solidity.Yul.Views.H62
