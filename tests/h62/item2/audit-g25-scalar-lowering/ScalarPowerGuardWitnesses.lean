import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.PowerGuard

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarPowerGuard
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.threshold_accept
theorem witness_threshold_accept : jointType% Solidity.Backend.Scalar.threshold_accept :=
  jointProof% Solidity.Backend.Scalar.threshold_accept [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerFits_correct
theorem witness_powerFits_correct : jointType% Solidity.Backend.Scalar.powerFits_correct :=
  jointProof% Solidity.Backend.Scalar.powerFits_correct [
    (⟨0, by decide⟩),
    (0),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.flag_and
theorem witness_flag_and : jointType% Solidity.Backend.Scalar.flag_and :=
  jointProof% Solidity.Backend.Scalar.flag_and [
    (false),
    (false)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerCell_correct
theorem witness_powerCell_correct : jointType% Solidity.Backend.Scalar.powerCell_correct :=
  jointProof% Solidity.Backend.Scalar.powerCell_correct [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (false),
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerRows_correct
theorem witness_powerRows_correct : jointType% Solidity.Backend.Scalar.powerRows_correct :=
  jointProof% Solidity.Backend.Scalar.powerRows_correct [
    (⟨0, by decide⟩),
    ([⟨0, by decide⟩]),
    (false),
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerStart_correct
theorem witness_powerStart_correct : jointType% Solidity.Backend.Scalar.powerStart_correct :=
  jointProof% Solidity.Backend.Scalar.powerStart_correct [
    (0),
    (0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.powerTest_correct
theorem witness_powerTest_correct : jointType% Solidity.Backend.Scalar.powerTest_correct :=
  jointProof% Solidity.Backend.Scalar.powerTest_correct [
    (⟨0, by decide⟩),
    (0),
    (0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarPowerGuard
