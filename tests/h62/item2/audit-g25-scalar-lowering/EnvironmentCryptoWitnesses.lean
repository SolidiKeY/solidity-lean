import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.Crypto

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentCrypto
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.keccak_bound
theorem witness_keccak_bound : jointType% Solidity.Backend.Environment.keccak_bound :=
  jointProof% Solidity.Backend.Environment.keccak_bound [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.digest_nat
theorem witness_digest_nat : jointType% Solidity.Backend.Environment.digest_nat :=
  jointProof% Solidity.Backend.Environment.digest_nat [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.wireBytes_values
theorem witness_wireBytes_values : jointType% Solidity.Backend.Environment.wireBytes_values :=
  jointProof% Solidity.Backend.Environment.wireBytes_values [
    ([])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.source_digest
theorem witness_source_digest : jointType% Solidity.Backend.Environment.source_digest :=
  jointProof% Solidity.Backend.Environment.source_digest [
    ([])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.digest_fixed
theorem witness_digest_fixed : jointType% Solidity.Backend.Environment.digest_fixed :=
  jointProof% Solidity.Backend.Environment.digest_fixed [
    ([1,2])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.wrap_nat
theorem witness_wrap_nat : jointType% Solidity.Backend.Environment.wrap_nat :=
  jointProof% Solidity.Backend.Environment.wrap_nat [
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.runCrypto_append
theorem witness_runCrypto_append : jointType% Solidity.Backend.Environment.runCrypto_append :=
  jointProof% Solidity.Backend.Environment.runCrypto_append [
    ([]),
    ([]),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.cryptoStep_constant
theorem witness_cryptoStep_constant : jointType% Solidity.Backend.Environment.cryptoStep_constant :=
  jointProof% Solidity.Backend.Environment.cryptoStep_constant [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.keccak_correct
theorem witness_keccak_correct : jointType% Solidity.Backend.Environment.keccak_correct :=
  jointProof% Solidity.Backend.Environment.keccak_correct [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.intrinsic_keccak
theorem witness_intrinsic_keccak : jointType% Solidity.Backend.Environment.intrinsic_keccak :=
  jointProof% Solidity.Backend.Environment.intrinsic_keccak [
    (default),
    (bytesΓ),
    (bytesR),
    (bytesState),
    (bytesPath),
    (bytesRef),
    (by first | rfl | decide +kernel),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice),
    (heapHashInput)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.intrinsic_hash_failure
theorem witness_intrinsic_hash_failure : jointType% Solidity.Backend.Environment.intrinsic_hash_failure :=
  jointProof% Solidity.Backend.Environment.intrinsic_hash_failure [
    (default),
    (bytesΓ),
    (bytesR),
    (unsetBytesState),
    (bytesPath),
    (.keccak),
    (.revert),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.precompile_operands
theorem witness_precompile_operands : jointType% Solidity.Backend.Environment.precompile_operands :=
  jointProof% Solidity.Backend.Environment.precompile_operands [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.lowerHash_failure
theorem witness_lowerHash_failure : jointType% Solidity.Backend.Environment.lowerHash_failure :=
  jointProof% Solidity.Backend.Environment.lowerHash_failure [
    (default),
    (bytesΓ),
    (bytesR),
    (unsetBytesState),
    (bytesPath),
    (.keccak),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (.revert),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.HashInput.length_eq
theorem witness_HashInput_length_eq : jointType% Solidity.Backend.Environment.HashInput.length_eq :=
  jointProof% Solidity.Backend.Environment.HashInput.length_eq [
    (targetSlice),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    ([]),
    (emptyHashInput)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.lowerHash_success
theorem witness_lowerHash_success : jointType% Solidity.Backend.Environment.lowerHash_success :=
  jointProof% Solidity.Backend.Environment.lowerHash_success [
    (default),
    (bytesΓ),
    (bytesR),
    (bytesState),
    (bytesPath),
    (bytesRef),
    (by first | rfl | decide +kernel),
    (.keccak),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice),
    (heapHashInput)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.ecrecover_wrong_length
theorem witness_ecrecover_wrong_length : jointType% Solidity.Backend.Environment.ecrecover_wrong_length :=
  jointProof% Solidity.Backend.Environment.ecrecover_wrong_length [
    ([]),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.precompile_preimage
theorem witness_precompile_preimage : jointType% Solidity.Backend.Environment.precompile_preimage :=
  jointProof% Solidity.Backend.Environment.precompile_preimage [
    (targetSlice),
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    ([]),
    (emptyHashInput),
    (.keccak)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentCrypto
