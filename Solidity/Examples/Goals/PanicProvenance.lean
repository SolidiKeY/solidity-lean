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

end Solidity.Goals
