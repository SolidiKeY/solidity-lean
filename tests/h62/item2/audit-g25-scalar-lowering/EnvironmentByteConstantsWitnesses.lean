import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand
import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures
import Solidity.Backend.Environment.ByteConstants

/-! Generated explicit candidate choices for the full frozen theorem telescopes.
Kernel checking and final exact-type/axiom census are required for proof credit. -/
namespace Solidity.Backend.Scalar.H62Audit.EnvironmentByteConstants
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Environment
open Solidity.Backend.Scalar.H62Audit
open Solidity.Backend.Scalar.H62Audit.Fixtures

-- AUDIT-WITNESS: Solidity.Backend.Environment.runData_append
theorem witness_runData_append : jointType% Solidity.Backend.Environment.runData_append :=
  jointProof% Solidity.Backend.Environment.runData_append [
    ([]),
    ([]),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.dataStep_constant
theorem witness_dataStep_constant : jointType% Solidity.Backend.Environment.dataStep_constant :=
  jointProof% Solidity.Backend.Environment.dataStep_constant [
    (⟨0, by decide⟩),
    (⟨0, by decide⟩),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.byteCode_correct
theorem witness_byteCode_correct : jointType% Solidity.Backend.Environment.byteCode_correct :=
  jointProof% Solidity.Backend.Environment.byteCode_correct [
    (⟨0, by decide⟩),
    (7),
    (targetSlice)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.materialize_correct
theorem witness_materialize_correct : jointType% Solidity.Backend.Environment.materialize_correct :=
  jointProof% Solidity.Backend.Environment.materialize_correct [
    ([1,2]),
    (0),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.name_correct
theorem witness_name_correct : jointType% Solidity.Backend.Environment.name_correct :=
  jointProof% Solidity.Backend.Environment.name_correct [
    ("AB"),
    (0),
    (targetSlice),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.writeBytes_frame
theorem witness_writeBytes_frame : jointType% Solidity.Backend.Environment.writeBytes_frame :=
  jointProof% Solidity.Backend.Environment.writeBytes_frame [
    ([1,2]),
    (0),
    (2),
    (emptyMemory),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.writeBytes_at
theorem witness_writeBytes_at : jointType% Solidity.Backend.Environment.writeBytes_at :=
  jointProof% Solidity.Backend.Environment.writeBytes_at [
    ([1]),
    (0),
    (0),
    (emptyMemory),
    (by first | rfl | decide +kernel)
  ]

-- AUDIT-WITNESS: Solidity.Backend.Environment.read_written
theorem witness_read_written : jointType% Solidity.Backend.Environment.read_written :=
  jointProof% Solidity.Backend.Environment.read_written [
    ([1,2]),
    (0),
    (emptyMemory)
  ]

end Solidity.Backend.Scalar.H62Audit.EnvironmentByteConstants
