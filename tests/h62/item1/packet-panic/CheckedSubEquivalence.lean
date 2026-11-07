import Solidity.Backend.PrimitivePackets.CheckedSub.Controls
import «tests».h62.item1.«packet-panic».PanicBytes

/-! Candidate proof-term equality checks. These import the unchanged CheckedSub
controls; they do not assert any selected target panic payload. -/
namespace Solidity.Backend.PrimitivePackets.PanicBytes

theorem checkedSub_exact_same :
    CheckedSub.Controls.exact_panic_bytes = exact_panic_bytes := rfl

theorem checkedSub_truncated_same :
    CheckedSub.Controls.panic_not_truncated = panic_not_truncated := rfl

theorem checkedSub_nonempty_same :
    CheckedSub.Controls.panic_not_empty = panic_not_empty := rfl

#print axioms checkedSub_exact_same
#print axioms checkedSub_truncated_same
#print axioms checkedSub_nonempty_same
end Solidity.Backend.PrimitivePackets.PanicBytes
