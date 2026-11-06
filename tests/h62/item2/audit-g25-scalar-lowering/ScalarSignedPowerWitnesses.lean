import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.SignedPower

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarSignedPower
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_correct
theorem witness_signedPower_correct : jointType% Solidity.Backend.Scalar.signedPower_correct :=
  jointProof% Solidity.Backend.Scalar.signedPower_correct [
    (i0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerSourceResult_map
theorem witness_powerSourceResult_map : jointType% Solidity.Backend.Scalar.powerSourceResult_map :=
  jointProof% Solidity.Backend.Scalar.powerSourceResult_map [
    (i0),
    (u0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_source
theorem witness_signedPower_source : jointType% Solidity.Backend.Scalar.signedPower_source :=
  jointProof% Solidity.Backend.Scalar.signedPower_source [
    (default),
    ([]),
    (state0),
    (.simple (.lit 0 (by decide))),
    (.simple (.lit 0 (by decide))),
    (i0),
    (u0),
    (by first | rfl | decide +kernel),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.SignedPowerInvocation.correct
theorem witness_SignedPowerInvocation_correct : jointType% Solidity.Backend.Scalar.SignedPowerInvocation.correct :=
  jointProof% Solidity.Backend.Scalar.SignedPowerInvocation.correct [
    (⟨-2, by decide⟩),
    (u3),
    ([99]),
    (signedPowerWitness)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_negative_three_source
theorem witness_signedPower_negative_three_source : jointType% Solidity.Backend.Scalar.signedPower_negative_three_source :=
  jointProof% Solidity.Backend.Scalar.signedPower_negative_three_source []

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_minimum_one_source
theorem witness_signedPower_minimum_one_source : jointType% Solidity.Backend.Scalar.signedPower_minimum_one_source :=
  jointProof% Solidity.Backend.Scalar.signedPower_minimum_one_source []

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_positive_boundary_source
theorem witness_signedPower_positive_boundary_source : jointType% Solidity.Backend.Scalar.signedPower_positive_boundary_source :=
  jointProof% Solidity.Backend.Scalar.signedPower_positive_boundary_source []

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_unsigned_overflow_source
theorem witness_signedPower_unsigned_overflow_source : jointType% Solidity.Backend.Scalar.signedPower_unsigned_overflow_source :=
  jointProof% Solidity.Backend.Scalar.signedPower_unsigned_overflow_source []

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_negative_three_target
theorem witness_signedPower_negative_three_target : jointType% Solidity.Backend.Scalar.signedPower_negative_three_target :=
  jointProof% Solidity.Backend.Scalar.signedPower_negative_three_target [
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_minimum_one_target
theorem witness_signedPower_minimum_one_target : jointType% Solidity.Backend.Scalar.signedPower_minimum_one_target :=
  jointProof% Solidity.Backend.Scalar.signedPower_minimum_one_target [
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_positive_boundary_target
theorem witness_signedPower_positive_boundary_target : jointType% Solidity.Backend.Scalar.signedPower_positive_boundary_target :=
  jointProof% Solidity.Backend.Scalar.signedPower_positive_boundary_target [
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signedPower_unsigned_overflow_target
theorem witness_signedPower_unsigned_overflow_target : jointType% Solidity.Backend.Scalar.signedPower_unsigned_overflow_target :=
  jointProof% Solidity.Backend.Scalar.signedPower_unsigned_overflow_target [
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarSignedPower
