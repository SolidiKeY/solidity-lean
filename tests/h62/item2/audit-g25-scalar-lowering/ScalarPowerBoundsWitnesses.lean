import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.PowerBounds

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarPowerBounds
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.threshold_bounds
theorem witness_threshold_bounds : jointType% Solidity.Backend.Scalar.threshold_bounds :=
  jointProof% Solidity.Backend.Scalar.threshold_bounds [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.thresholdWord_nat
theorem witness_thresholdWord_nat : jointType% Solidity.Backend.Scalar.thresholdWord_nat :=
  jointProof% Solidity.Backend.Scalar.thresholdWord_nat [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.exponentWord_nat
theorem witness_exponentWord_nat : jointType% Solidity.Backend.Scalar.exponentWord_nat :=
  jointProof% Solidity.Backend.Scalar.exponentWord_nat [
    (⟨0, by decide⟩)
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarPowerBounds
