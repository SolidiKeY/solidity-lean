import Solidity.Backend.Opcode
import Solidity.RevertBytes

/-! Pre-implementation control: opcode encoding is not payload emission.
The existing panic observation crosses a word boundary; bare REVERT contains
neither stores nor its offset and length. This imports only base interfaces. -/
namespace Solidity.Backend.Failure.Gap
example : encode [.op .REVERT] = [0xfd] := by decide
example : (Semantics.encodePanic 1).length = 36 := by decide
example : (Semantics.encodePanic 1).drop 32 = [0, 0, 0, 1] := by decide
example : Semantics.encodePanic 1 ≠ Semantics.encodePanic 0 := by decide
end Solidity.Backend.Failure.Gap
