import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.ArithmeticWidths

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.ScalarArithmeticWidths
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.ofInt_low
theorem witness_ofInt_low : jointType% Solidity.Backend.Scalar.ofInt_low :=
  jointProof% Solidity.Backend.Scalar.ofInt_low [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.clean_ofInt_unsigned
theorem witness_clean_ofInt_unsigned : jointType% Solidity.Backend.Scalar.clean_ofInt_unsigned :=
  jointProof% Solidity.Backend.Scalar.clean_ofInt_unsigned [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.clean_ofInt_signed
theorem witness_clean_ofInt_signed : jointType% Solidity.Backend.Scalar.clean_ofInt_signed :=
  jointProof% Solidity.Backend.Scalar.clean_ofInt_signed [
    (⟨0, by decide⟩),
    (0)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_addAt_correct
theorem witness_unsigned_addAt_correct : jointType% Solidity.Backend.Scalar.unsigned_addAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_addAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_subAt_correct
theorem witness_unsigned_subAt_correct : jointType% Solidity.Backend.Scalar.unsigned_subAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_subAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_mulAt_correct
theorem witness_unsigned_mulAt_correct : jointType% Solidity.Backend.Scalar.unsigned_mulAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_mulAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_addAt_correct
theorem witness_signed_addAt_correct : jointType% Solidity.Backend.Scalar.signed_addAt_correct :=
  jointProof% Solidity.Backend.Scalar.signed_addAt_correct [
    (⟨0, by decide⟩),
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_subAt_correct
theorem witness_signed_subAt_correct : jointType% Solidity.Backend.Scalar.signed_subAt_correct :=
  jointProof% Solidity.Backend.Scalar.signed_subAt_correct [
    (⟨0, by decide⟩),
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_mulAt_correct
theorem witness_signed_mulAt_correct : jointType% Solidity.Backend.Scalar.signed_mulAt_correct :=
  jointProof% Solidity.Backend.Scalar.signed_mulAt_correct [
    (⟨0, by decide⟩),
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_divAt_correct
theorem witness_unsigned_divAt_correct : jointType% Solidity.Backend.Scalar.unsigned_divAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_divAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_modAt_correct
theorem witness_unsigned_modAt_correct : jointType% Solidity.Backend.Scalar.unsigned_modAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_modAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_divAt_correct
theorem witness_signed_divAt_correct : jointType% Solidity.Backend.Scalar.signed_divAt_correct :=
  jointProof% Solidity.Backend.Scalar.signed_divAt_correct [
    (⟨0, by decide⟩),
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.signed_modAt_correct
theorem witness_signed_modAt_correct : jointType% Solidity.Backend.Scalar.signed_modAt_correct :=
  jointProof% Solidity.Backend.Scalar.signed_modAt_correct [
    (⟨0, by decide⟩),
    (i0),
    (i0),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.unsigned_powAt_correct
theorem witness_unsigned_powAt_correct : jointType% Solidity.Backend.Scalar.unsigned_powAt_correct :=
  jointProof% Solidity.Backend.Scalar.unsigned_powAt_correct [
    (⟨0, by decide⟩),
    (u0),
    (u0),
    ([99])
  ]

end Solidity.Backend.Scalar.H62Audit.ScalarArithmeticWidths
