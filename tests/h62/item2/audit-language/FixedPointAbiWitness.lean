import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Language.FixedPoint.Abi

/-!
Guarded regression: clean ABI success and dirty-upper-bit rejection must not
be conflated, or coder v1 cleanup mistaken for strict coder v2 validation.
Joint tuples instantiate every imported leading parameter and hypothesis; byte
examples are nonempty, decoder success follows reduction or the existing
round-trip theorem, and
signed values exercise sign extension. Packed-byte inversion is a reference
inverse, not a Solidity packed decoder or compiler-success theorem.
-/
set_option autoImplicit false

namespace Solidity.H62.AuditLanguage.FixedPointAbiWitness
open Solidity.Language.FixedPoint

def ty : FxTy := ⟨false, 8, 1, by decide⟩
def signedTy : FxTy := ⟨true, 16, 1, by decide⟩
def seven : Fx ty := ⟨7, by decide⟩
def negativeSeven : Fx signedTy := ⟨-7, by decide⟩
def bytes : List UInt8 := [18, 52]
def word : Fin (2 ^ 256) := ⟨7, by decide⟩
def dirtyWord : Fin (2 ^ 256) := ⟨256, by decide⟩
def head : List UInt8 := Fx.abiEncode seven

theorem byte_length_full : hypotheses_of% beBytes_length := by
  exact ⟨2, 4660, True.intro⟩
#verify_hypotheses byte_length_full for Solidity.Language.FixedPoint.beBytes_length
#print axioms byte_length_full

theorem append_byte_full : hypotheses_of% beNat_append_single := by
  exact ⟨bytes, 86, True.intro⟩
#verify_hypotheses append_byte_full for Solidity.Language.FixedPoint.beNat_append_single
#print axioms append_byte_full

theorem byte_value_full : hypotheses_of% beNat_beBytes := by
  exact ⟨2, 74565, True.intro⟩
#verify_hypotheses byte_value_full for Solidity.Language.FixedPoint.beNat_beBytes
#print axioms byte_value_full

theorem accumulator_bound_full : hypotheses_of% beNat_lt_aux := by
  exact ⟨bytes, 9, True.intro⟩
#verify_hypotheses accumulator_bound_full for Solidity.Language.FixedPoint.beNat_lt_aux
#print axioms accumulator_bound_full

theorem byte_bound_full : hypotheses_of% beNat_lt := by
  exact ⟨bytes, True.intro⟩
#verify_hypotheses byte_bound_full for Solidity.Language.FixedPoint.beNat_lt
#print axioms byte_bound_full

theorem byte_fold_full : hypotheses_of% beBytes_foldl := by
  exact ⟨bytes, 1, 9, True.intro⟩
#verify_hypotheses byte_fold_full for Solidity.Language.FixedPoint.beBytes_foldl
#print axioms byte_fold_full

theorem byte_roundtrip_full : hypotheses_of% beBytes_beNat := by
  exact ⟨bytes, True.intro⟩
#verify_hypotheses byte_roundtrip_full for Solidity.Language.FixedPoint.beBytes_beNat
#print axioms byte_roundtrip_full

theorem word_power_full : hypotheses_of% pow_256 := by
  exact True.intro
#verify_hypotheses word_power_full for Solidity.Language.FixedPoint.pow_256
#print axioms word_power_full

theorem type_byte_power_full : hypotheses_of% pow_bits_bytes := by
  exact ⟨signedTy, True.intro⟩
#verify_hypotheses type_byte_power_full for Solidity.Language.FixedPoint.pow_bits_bytes
#print axioms type_byte_power_full

theorem integer_decode_full : hypotheses_of% Fx.ofInt?_val := by
  exact ⟨ty, 7, seven, rfl, True.intro⟩
#verify_hypotheses integer_decode_full for Solidity.Language.FixedPoint.Fx.ofInt?_val
#print axioms integer_decode_full

theorem integer_acceptance_full : hypotheses_of% Fx.ofInt?_isSome := by
  exact ⟨ty, 256, True.intro⟩
#verify_hypotheses integer_acceptance_full for Solidity.Language.FixedPoint.Fx.ofInt?_isSome
#print axioms integer_acceptance_full

theorem word_bound_full : hypotheses_of% Fx.toWord_toNat_lt := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses word_bound_full for Solidity.Language.FixedPoint.Fx.toWord_toNat_lt
#print axioms word_bound_full

theorem encoding_value_full : hypotheses_of% Fx.encode_val := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses encoding_value_full for Solidity.Language.FixedPoint.Fx.encode_val
#print axioms encoding_value_full

theorem strict_word_roundtrip_full : hypotheses_of% Fx.decodeV2_encode := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses strict_word_roundtrip_full for Solidity.Language.FixedPoint.Fx.decodeV2_encode
#print axioms strict_word_roundtrip_full

theorem canonical_word_full : hypotheses_of% Fx.encode_of_decodeV2 := by
  exact ⟨ty, word, seven, rfl, True.intro⟩
#verify_hypotheses canonical_word_full for Solidity.Language.FixedPoint.Fx.encode_of_decodeV2
#print axioms canonical_word_full

theorem strict_rejection_full : hypotheses_of% Fx.decodeV2_eq_none_iff := by
  exact ⟨ty, dirtyWord, True.intro⟩
#verify_hypotheses strict_rejection_full for Solidity.Language.FixedPoint.Fx.decodeV2_eq_none_iff
#print axioms strict_rejection_full

theorem strict_acceptance_full : hypotheses_of% Fx.decodeV2_isSome_iff := by
  exact ⟨ty, dirtyWord, True.intro⟩
#verify_hypotheses strict_acceptance_full for Solidity.Language.FixedPoint.Fx.decodeV2_isSome_iff
#print axioms strict_acceptance_full

theorem word_cleaning_full : hypotheses_of% Fx.wrapInt_emod_eq := by
  exact ⟨signedTy, -65543, True.intro⟩
#verify_hypotheses word_cleaning_full for Solidity.Language.FixedPoint.Fx.wrapInt_emod_eq
#print axioms word_cleaning_full

theorem lenient_word_full : hypotheses_of% Fx.decodeV1_eq_ofBits := by
  exact ⟨signedTy, Fx.encode negativeSeven, True.intro⟩
#verify_hypotheses lenient_word_full for Solidity.Language.FixedPoint.Fx.decodeV1_eq_ofBits
#print axioms lenient_word_full

theorem coder_agreement_full : hypotheses_of% Fx.decodeV1_of_decodeV2 := by
  exact ⟨ty, word, seven, rfl, True.intro⟩
#verify_hypotheses coder_agreement_full for Solidity.Language.FixedPoint.Fx.decodeV1_of_decodeV2
#print axioms coder_agreement_full

theorem lenient_roundtrip_full : hypotheses_of% Fx.decodeV1_encode := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses lenient_roundtrip_full for Solidity.Language.FixedPoint.Fx.decodeV1_encode
#print axioms lenient_roundtrip_full

theorem head_length_full : hypotheses_of% Fx.abiEncode_length := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses head_length_full for Solidity.Language.FixedPoint.Fx.abiEncode_length
#print axioms head_length_full

theorem head_bound_full : hypotheses_of% Fx.beNat_mod_of_length := by
  exact ⟨head, by decide, True.intro⟩
#verify_hypotheses head_bound_full for Solidity.Language.FixedPoint.Fx.beNat_mod_of_length
#print axioms head_bound_full

theorem head_roundtrip_full : hypotheses_of% Fx.abiDecodeV2_abiEncode := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses head_roundtrip_full for Solidity.Language.FixedPoint.Fx.abiDecodeV2_abiEncode
#print axioms head_roundtrip_full

theorem canonical_head_full : hypotheses_of% Fx.abiEncode_of_abiDecodeV2 := by
  exact ⟨ty, head, seven, Fx.abiDecodeV2_abiEncode seven, True.intro⟩
#verify_hypotheses canonical_head_full for Solidity.Language.FixedPoint.Fx.abiEncode_of_abiDecodeV2
#print axioms canonical_head_full

theorem packed_length_full : hypotheses_of% Fx.encodePacked_length := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses packed_length_full for Solidity.Language.FixedPoint.Fx.encodePacked_length
#print axioms packed_length_full

theorem packed_inverse_full : hypotheses_of% Fx.ofPackedBytes_encodePacked := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses packed_inverse_full for Solidity.Language.FixedPoint.Fx.ofPackedBytes_encodePacked
#print axioms packed_inverse_full

/-- Dirty upper bits are refused by v2 but cleaned to zero by v1. -/
theorem dirty_coder_difference : Fx.decodeV2 ty dirtyWord = none ∧
    (Fx.decodeV1 ty dirtyWord).val = 0 := by
  decide
#print axioms dirty_coder_difference
end Solidity.H62.AuditLanguage.FixedPointAbiWitness
