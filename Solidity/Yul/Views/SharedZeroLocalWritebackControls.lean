import Solidity.Yul.Views.SharedZeroLocalWriteback
import Solidity.Yul.Views.SharedZeroReadControls

/-! Actual allocated empty-array IDs enter three typed bindings: two distinct
references and a same-ID alias. Shared physical checks retain each binding's
identity through real Source local writes, including static frames. Physical
preparation failures do not become Source refusal or successful no-ops. -/
namespace Solidity.Yul.Views.SharedZeroLocalWriteback.Controls
open SharedZeroRead SharedZeroRead.Controls

def aliases : Source.EMState E [ty,ty,ty] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) .nil)),allocated.2)

theorem all_bindings (fuel : Nat) :
    writeback aliases frame fuel .here pointer memory=some (.ok (),aliases) ∧
    writeback aliases frame fuel (.there .here) pointer memory=some (.ok (),aliases) ∧
    writeback aliases frame fuel (.there (.there .here)) pointer memory=some (.ok (),aliases) := by
  first | omega | decide | skip
  exact ⟨unchanged aliases frame fuel .here memory 128 reserved,
    unchanged aliases frame fuel (.there .here) memory 128 reserved,
    unchanged aliases frame fuel (.there (.there .here)) memory 128 reserved⟩

theorem static_local_success (fuel : Nat) :
    writeback aliases {frame with static:=true} fuel (.there .here) pointer memory=some (.ok (),aliases) := by
  first | omega | decide | skip
  exact unchanged aliases _ fuel (.there .here) memory 128 reserved

theorem actual_read_agreement (fuel : Nat) :
    writeback aliases frame fuel (.there .here) pointer memory=some (.ok (),aliases) ∧
    (Source.readLoc frame (.local (.there .here))).run aliases=(.ok (.memRef rfl 1),aliases) ∧
    (Source.lengthOf frame (aliases.1.get (.there .here))).run aliases=(.ok 0,aliases) ∧
    mload memory pointer.val=0 := by
  first | omega | decide | skip
  exact read_agreement aliases frame fuel 1 (.there .here) rfl found_one memory 128 reserved

theorem distinct_prepared :
    prepare (aliases.1.get .here) pointer memory=some (.memRef rfl 0) ∧
    prepare (aliases.1.get (.there .here)) pointer memory=some (.memRef rfl 1) ∧
    prepare (aliases.1.get (.there (.there .here))) pointer memory=some (.memRef rfl 0) := by
  first | omega | decide | skip
  exact ⟨prepared _ memory 128 reserved,prepared _ memory 128 reserved,prepared _ memory 128 reserved⟩

theorem not_first_identity :
    prepare (aliases.1.get (.there .here)) pointer memory≠some (.memRef rfl 0) := by
  first | omega | decide | skip
  rw [distinct_prepared.2.1]
  intro same
  have values := Option.some.inj same
  exact distinct_source values.symm

theorem wrong_pointer (fuel : Nat) :
    writeback aliases frame fuel .here ⟨97,by decide⟩ memory=none := by
  first | (simp only;done) | decide | omega | rfl |
    (rw [writeback,rejected _ _ _ (Or.inl (by decide))];rfl)

theorem dirty_header (fuel : Nat) :
    writeback aliases frame fuel .here pointer corrupted=none := by
  first | (simp only;done) | decide | omega | rfl |
    (rw [writeback,rejected _ _ _ (Or.inr wrong_header)];rfl)

/-- Even a wrong incoming provenance passes physical checks: current locals,
not raw96, must supply the retained identity used by the adapter. -/
theorem raw_does_not_validate_origin :
    prepare (Source.Val.memRef (D:=E.layout) (τ:=ty) rfl 99) pointer memory=some (.memRef rfl 99) :=
  prepared _ memory 128 reserved
end Solidity.Yul.Views.SharedZeroLocalWriteback.Controls
