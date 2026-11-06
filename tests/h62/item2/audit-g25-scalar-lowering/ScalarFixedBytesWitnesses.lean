import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.FixedBytes

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarFixedBytes
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesResize_correct
theorem witness_bytesResize_correct : jointType% Solidity.Backend.Scalar.bytesResize_correct :=
  jointProof% Solidity.Backend.Scalar.bytesResize_correct [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesResize_range
theorem witness_bytesResize_range : jointType% Solidity.Backend.Scalar.bytesResize_range :=
  jointProof% Solidity.Backend.Scalar.bytesResize_range [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesResize_nat
theorem witness_bytesResize_nat : jointType% Solidity.Backend.Scalar.bytesResize_nat :=
  jointProof% Solidity.Backend.Scalar.bytesResize_nat [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.widthShift_word
theorem witness_widthShift_word : jointType% Solidity.Backend.Scalar.widthShift_word :=
  jointProof% Solidity.Backend.Scalar.widthShift_word [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesWiden_intrinsic
theorem witness_bytesWiden_intrinsic : jointType% Solidity.Backend.Scalar.bytesWiden_intrinsic :=
  jointProof% Solidity.Backend.Scalar.bytesWiden_intrinsic [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (by first | rfl | decide +kernel),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesNarrow_intrinsic
theorem witness_bytesNarrow_intrinsic : jointType% Solidity.Backend.Scalar.bytesNarrow_intrinsic :=
  jointProof% Solidity.Backend.Scalar.bytesNarrow_intrinsic [
    (⟨1, by decide⟩),
    (⟨0, by decide⟩),
    (by decide +kernel),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.bytesResize_roundtrip
theorem witness_bytesResize_roundtrip : jointType% Solidity.Backend.Scalar.bytesResize_roundtrip :=
  jointProof% Solidity.Backend.Scalar.bytesResize_roundtrip [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarFixedBytes
