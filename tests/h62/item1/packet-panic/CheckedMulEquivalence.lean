import Solidity.Backend.PrimitivePackets.CheckedMul.Controls
import «tests».h62.item1.«packet-panic».PanicBytes

/-! Candidate proof-term equality checks. These import the unchanged CheckedMul
controls; they do not assert any selected target panic payload. -/
namespace Solidity.Backend.PrimitivePackets.PanicBytes

theorem checkedMul_exact_same :
    CheckedMul.Controls.exact_panic_bytes = exact_panic_bytes := rfl

theorem checkedMul_truncated_same :
    CheckedMul.Controls.panic_not_truncated = panic_not_truncated := rfl

theorem checkedMul_nonempty_same :
    CheckedMul.Controls.panic_not_empty = panic_not_empty := rfl

#print axioms checkedMul_exact_same
#print axioms checkedMul_truncated_same
#print axioms checkedMul_nonempty_same
end Solidity.Backend.PrimitivePackets.PanicBytes
