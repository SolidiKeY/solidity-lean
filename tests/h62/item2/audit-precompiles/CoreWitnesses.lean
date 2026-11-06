import Solidity.Precompiles.Modexp
import Solidity.Precompiles.Blake2f
import Solidity.Precompiles.P256
import Solidity.Precompiles.Basic

/-! Independent witness backfill where the frozen import closure builds.
A valid input plus its successful output is one joint witness, never independent
inhabitance claims for hypotheses about different inputs. -/
namespace H62.AuditPrecompiles
open Solidity.Precompiles Solidity.Roadmap.Evm

theorem modexp_length_witness : ∃ d o : Bytes,
    Modexp.modexp d = some o ∧ o.length = Modexp.modLen d := by
  have h : Modexp.modexp [] = some [] := by decide
  exact ⟨[], [], h, Modexp.modexp_length h⟩

theorem modexp_gas_ge_witness : ∃ d : Bytes,
    ¬ Modexp.Malformed d ∧ 500 ≤ Modexp.gas d := by
  have h : ¬ Modexp.Malformed [] := by decide
  exact ⟨[], h, Modexp.gas_ge h⟩

/-- The frozen Osaka MODEXP empty input succeeds at its 500-gas price. -/
theorem modexp_empty_success :
    Modexp.modexp [] = some [] ∧ Modexp.gas [] = 500 := by decide

/-- The exact public failure law also supplies total success on its valid domain. -/
theorem blake_supported_success (d : Bytes) (size : d.length = 213)
    (flag : Blake2f.flag d ≤ 1) :
    ∃ o : Bytes, Blake2f.blake2f d = some o ∧ o.length = 64 := by
  have not_none : Blake2f.blake2f d ≠ none := by
    intro bad
    have malformed : d.length ≠ 213 ∨ 1 < Blake2f.flag d :=
      (Blake2f.blake2f_eq_none_iff d).mp bad
    rcases malformed with bad_size | bad_flag
    · exact bad_size size
    · exact (Nat.not_lt_of_ge flag) bad_flag
  rcases Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr not_none) with ⟨o, h⟩
  exact ⟨o, h, Blake2f.blake2f_length h⟩

theorem blake2f_length_witness : ∃ d o : Bytes,
    Blake2f.blake2f d = some o ∧ o.length = 64 := by
  rcases blake_supported_success (List.replicate 213 0)
    (by rw [List.length_replicate])
    (by simp only [Blake2f.flag, readNat, readPad, List.drop_replicate, List.take_replicate,
          List.map_replicate, List.length_replicate]
        decide) with ⟨o, h, len⟩
  exact ⟨List.replicate 213 0, o, h, len⟩

/-- A size-boundary failure is observable independently of the successful witness. -/
theorem blake_short_failure : Blake2f.blake2f [] = none :=
  (Blake2f.blake2f_eq_none_iff []).mpr (Or.inl (by decide))

theorem p256_total (d : Bytes) : ∃ o : Bytes, P256.p256Verify d = some o :=
  Option.isSome_iff_exists.mp (P256.p256Verify_isSome d)

theorem ecrecover_total (d : Bytes) : ∃ o : Bytes, ecrecover d = some o :=
  Option.isSome_iff_exists.mp (ecrecover_isSome d)

theorem sha256_total (d : Bytes) : ∃ o : Bytes, sha256 d = some o :=
  Option.isSome_iff_exists.mp (sha256_isSome d)

theorem ripemd160_total (d : Bytes) : ∃ o : Bytes, ripemd160 d = some o :=
  Option.isSome_iff_exists.mp (ripemd160_isSome d)

#print axioms modexp_length_witness
#print axioms modexp_gas_ge_witness
#print axioms modexp_empty_success
#print axioms blake_supported_success
#print axioms blake2f_length_witness
#print axioms blake_short_failure
#print axioms p256_total
#print axioms ecrecover_total
#print axioms sha256_total
#print axioms ripemd160_total
end H62.AuditPrecompiles
