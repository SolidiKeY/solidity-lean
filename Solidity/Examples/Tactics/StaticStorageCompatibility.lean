import Solidity.Calculus.StaticStorageTransport
import Solidity.Examples.Tactics.PrimitiveReturnProjection

/-! Fresh-master conditional compatibility controls. The operational frame is
supplied; these controls do not assert that opaque static execution produces it. -/
namespace Solidity.Examples.Tactics.StaticStorageCompatibility
open Solidity.StaticInvocation Semantics
abbrev C := Solidity.Examples.Tactics.ExternalReturnBytes.C
def entry : State C [] := State.init C
def credited := entry.havoc entry.storage [(⟨9,rfl⟩,11)] ⟨13,rfl⟩
theorem actual_frame : Frame .static entry (.returned (wordBytes 1)) credited :=
  static_credit _ _ _ _
theorem exact_resume : entry.resumeCall .static credited.storage credited.net credited.selfBalance =
    entry.havoc credited.storage credited.net credited.selfBalance := by rfl
theorem changed_balance : credited.selfBalance ≠ entry.selfBalance := by decide
theorem refused_attempt : Frame .static entry (.halted .revert) entry :=
  static_noop_write_refused _
theorem inherited_reentry : Frame .static entry (.returned [1]) entry :=
  static_reentry_write_refused _ entry.storage _
theorem malformed_declaration :
    PrimitiveReturnConsumer.consume (C := C) (H := [])
      Solidity.Examples.Tactics.PrimitiveReturnConsumer.integer (.discard _) [1] =
        .error .revert := rfl
end Solidity.Examples.Tactics.StaticStorageCompatibility

#print axioms Solidity.ExecS.static_tryOk_storage_only
#print axioms Solidity.StaticInvocation.Frame.resumeCall_eq_havoc
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.actual_frame
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.exact_resume
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.changed_balance
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.refused_attempt
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.inherited_reentry
#print axioms Solidity.Examples.Tactics.StaticStorageCompatibility.malformed_declaration
