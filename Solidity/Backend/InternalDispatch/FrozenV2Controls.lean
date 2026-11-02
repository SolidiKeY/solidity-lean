import Solidity.Backend.InternalDispatch.FrozenV2
import Solidity.Backend.InternalDispatch.FrozenV1Controls

/-! Positive dependent selector controls are inherited unchanged. No Pending
instance is constructed; the new predicate control uses actual Stmt.run. -/
namespace Solidity.Backend.InternalDispatch.FrozenV2Controls
open FrozenV1 FrozenV1Controls Controls
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1 (Emission)
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV2 (SuccessfulEntry)

theorem first : select table (fun i => Fin (i.val+1)) token (Evm.wmod 1) =
    some ⟨⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩ := FrozenV1Controls.first

theorem second : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2) =
    some ⟨⟨1, by decide +kernel⟩, ⟨1, by decide +kernel⟩⟩ := FrozenV1Controls.second

theorem wrong_payload : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2) ≠
    some ⟨⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩ := FrozenV1Controls.wrong_payload_refused

theorem zero : select table (fun i => Fin (i.val+1)) token (Evm.wmod 0) = none :=
  FrozenV1Controls.zero

theorem foreign : select table (fun i => Fin (i.val+1)) token (Evm.wmod 5) = none :=
  FrozenV1Controls.foreign

def C : Contract := {vars := []}

theorem actual_revert : (Stmt.revert : Stmt C [] []).run (State.init C) = .error .revert := by
  with_unfolding_all rfl

/-- A represented-but-failing caller cannot satisfy V2 success admission. -/
theorem revert_not_successful {C : Contract} {Γ : Ctx}
    (b : Nat) (F : Evm.Frag Γ) (plan : Emission C Γ Γ) :
    ¬ SuccessfulEntry b F (Stmt.revert : Stmt C Γ Γ) plan := by
  intro witness
  obtain ⟨L, frame, caller, base, machine, start, out, entry, success⟩ := witness
  have failure : (Stmt.revert : Stmt C Γ Γ).run caller = .error .revert := by
    with_unfolding_all rfl
  rw [failure] at success
  cases success

#print axioms first
#print axioms second
#print axioms wrong_payload
#print axioms actual_revert
#print axioms revert_not_successful
end Solidity.Backend.InternalDispatch.FrozenV2Controls
