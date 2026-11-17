import Solidity.Tools.Goal
import Solidity.Yul.OpcodeSpec

/-! The plan goal `opcodeEvalUniversal` (`v1-yul-checks-universal`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

/-! Arithmetic vocabulary for the universal opcode contract: wrappers of the
pure statements in `Solidity.Yul.OpcodeSpec`, which proofs in the core use
without importing goal tooling. -/
namespace OpcodeSpec

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := Solidity.Yul.OpcodeSpec.modulus

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := Solidity.Yul.OpcodeSpec.residue z

/-- CLZ shared by Arithmetic and Bytes (`Solidity.Yul.OpcodeSpec.clz`). -/
def clz : Prop := Solidity.Yul.OpcodeSpec.clz

end OpcodeSpec

/-- SHL, SHR and SAR over every input (`Solidity.Yul.OpcodeSpec.shifts`). -/
def opcodeShifts : Prop := Solidity.Yul.OpcodeSpec.shifts

/-- The twenty arithmetic, comparison and bitwise opcodes over every input
(`Solidity.Yul.OpcodeSpec.arithmetic`). -/
def opcodeArithmetic : Prop := Solidity.Yul.OpcodeSpec.arithmetic

/-- BYTE, SIGNEXTEND, CLZ and EXP over every input
(`Solidity.Yul.OpcodeSpec.bytesPowers`). -/
def opcodeBytesPowers : Prop := Solidity.Yul.OpcodeSpec.bytesPowers

/-- Universal arithmetic agreement for the 26 distinct opcodes in the finite
Checks families. CLZ has two memberships with one identical specification.
The three family obligations are independently usable by Checks-only proofs. -/
@[goal Solidity.Yul.opcode_eval_universal "v1-yul-checks-universal"]
def opcodeEvalUniversal : Prop :=
  opcodeShifts ∧ opcodeArithmetic ∧ opcodeBytesPowers

end Solidity.Goals
