import Solidity.Goals.PanicProvenance

namespace Solidity.Goals

open Solidity.Panic Solidity.Semantics.Panic

/--
info: open Solidity.Goals.panicCodeProvenance ← Solidity.Correctness.Panic.code_provenance plan w3y-panic-provenance
-/
#guard_msgs in
#roadmap_goal panicCodeProvenance

/-- The nine original sites carry the nine solc `Panic(uint256)` codes. -/
example : (siteCode .assertion).code = 0x01 ∧ (siteCode .arithmetic).code = 0x11 ∧
    (siteCode .zeroDivisor).code = 0x12 ∧ (siteCode .enumConversion).code = 0x21 ∧
    (siteCode .storageEncoding).code = 0x22 ∧ (siteCode .emptyPop).code = 0x31 ∧
    (siteCode .bounds).code = 0x32 ∧ (siteCode .allocation).code = 0x41 ∧
    (siteCode .zeroInternalFunction).code = 0x51 := by decide

/-- External bytes that encode `Panic(uint256)` select the panic handler with the decoded
word; they are not an intrinsic halt. -/
example (code : Code) (origin : Raised) (data : List UInt8) :
    Halt.intrinsic code origin ≠ .externalRevert data := Halt.intrinsic_ne_external code origin data

end Solidity.Goals
