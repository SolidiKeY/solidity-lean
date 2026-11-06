import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Scalar.Slice

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_append
theorem witness_run_append : jointType% Solidity.Backend.Scalar.run_append :=
  jointProof% Solidity.Backend.Scalar.run_append [
    ([.op .POP]),
    ([.op .POP]),
    ([7,3,99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_comp
theorem witness_run_comp : jointType% Solidity.Backend.Scalar.run_comp :=
  jointProof% Solidity.Backend.Scalar.run_comp [
    ([.op .POP]),
    ([.op .POP]),
    ([7,3,99]),
    ([3,99]),
    ([99]),
    (rfl),
    (rfl)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_pushByte
theorem witness_step_pushByte : jointType% Solidity.Backend.Scalar.step_pushByte :=
  jointProof% Solidity.Backend.Scalar.step_pushByte [
    (7),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyUnary_frame
theorem witness_applyUnary_frame : jointType% Solidity.Backend.Scalar.applyUnary_frame :=
  jointProof% Solidity.Backend.Scalar.applyUnary_frame [
    (id),
    ([7]),
    ([7]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyBinary_frame
theorem witness_applyBinary_frame : jointType% Solidity.Backend.Scalar.applyBinary_frame :=
  jointProof% Solidity.Backend.Scalar.applyBinary_frame [
    (fun a _ => a),
    ([7,3]),
    ([7]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyTernary_frame
theorem witness_applyTernary_frame : jointType% Solidity.Backend.Scalar.applyTernary_frame :=
  jointProof% Solidity.Backend.Scalar.applyTernary_frame [
    (fun a _ _ => a),
    ([7,3,2]),
    ([7]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.duplicate_frame
theorem witness_duplicate_frame : jointType% Solidity.Backend.Scalar.duplicate_frame :=
  jointProof% Solidity.Backend.Scalar.duplicate_frame [
    (0),
    ([7]),
    ([7,7]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.exchange_frame
theorem witness_exchange_frame : jointType% Solidity.Backend.Scalar.exchange_frame :=
  jointProof% Solidity.Backend.Scalar.exchange_frame [
    (3),
    (0),
    ([7]),
    ([3]),
    (7),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.swap_frame
theorem witness_swap_frame : jointType% Solidity.Backend.Scalar.swap_frame :=
  jointProof% Solidity.Backend.Scalar.swap_frame [
    (0),
    ([7,3]),
    ([3,7]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.pop_frame
theorem witness_pop_frame : jointType% Solidity.Backend.Scalar.pop_frame :=
  jointProof% Solidity.Backend.Scalar.pop_frame [
    ([7]),
    ([]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.numericStep_frame
theorem witness_numericStep_frame : jointType% Solidity.Backend.Scalar.numericStep_frame :=
  jointProof% Solidity.Backend.Scalar.numericStep_frame [
    (.ISZERO),
    ([0]),
    ([1]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_frame
theorem witness_step_frame : jointType% Solidity.Backend.Scalar.step_frame :=
  jointProof% Solidity.Backend.Scalar.step_frame [
    (.op .POP),
    ([7]),
    ([]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_frame
theorem witness_run_frame : jointType% Solidity.Backend.Scalar.run_frame :=
  jointProof% Solidity.Backend.Scalar.run_frame [
    ([.op .POP]),
    ([7]),
    ([]),
    (rfl),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_pushWord
theorem witness_step_pushWord : jointType% Solidity.Backend.Scalar.step_pushWord :=
  jointProof% Solidity.Backend.Scalar.step_pushWord [
    (7),
    ([99])
  ]

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_pushWord
theorem witness_encode_pushWord : jointType% Solidity.Backend.Scalar.encode_pushWord :=
  jointProof% Solidity.Backend.Scalar.encode_pushWord [
    (7)
  ]

end Solidity.Backend.Scalar.H62Audit
