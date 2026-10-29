import Solidity.Calculus.PaymentConditions

/-!
# Approved conditional payment controls

Concrete controls complement the generic iff theorems. The receiver reason is
the source fixture's no_receive string, but this is oracle/kernel evidence:
no deployed receiver or gas execution is asserted here.
-/
namespace Solidity.Examples.Tactics.PaymentConditions
open Semantics
open Solidity.PaymentConditions

private abbrev funded : State StandardExample [] :=
  { State.ofStorage Storage.standardExample with selfBalance := ⟨10, rfl⟩ }
private def reason : List UInt8 := "no_receive".toUTF8.data.toList
private abbrev rejecting : State StandardExample [] :=
  { funded with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨1, rfl⟩, .error reason)] } }

/-- Missing response accepts only when funded. -/
theorem missing_response_success : funded.canPay ⟨9, rfl⟩ ⟨1, rfl⟩ = true := rfl

/-- Explicit callee failure still reverts despite sufficient caller funds. -/
theorem recipient_error_refuses :
    TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 1 rfl)) rejecting = .error .revert := rfl

/-- A recipient panic is also refusal, not caller success or a bubbled panic. -/
theorem recipient_panic_refuses :
    TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 1 rfl))
      { funded with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨1, rfl⟩, .panic ⟨17, rfl⟩)] } } =
      .error .revert := rfl

/-- Zero value does not override an explicit rejecting recipient. -/
theorem zero_refusal :
    TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 0 rfl))
      { State.ofStorage Storage.standardExample with
        tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨0, rfl⟩, .error reason)] } } = .error .revert := rfl

/-- The original h() amount fails funding independently of recipient data. -/
theorem hundred_ether_unfunded :
    TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit (100 * 10^18) rfl)) funded =
      .error .revert := rfl

/-- Self-payment still requires funds in this model. -/
theorem self_payment_requires_funding :
    funded.canPay funded.tx.selfAddress ⟨11, rfl⟩ = false := rfl

/-- The original Error(no_receive) observation is nonempty ABI data. -/
theorem expected_error_nonempty : encodeError reason ≠ [] := by decide +kernel

/-- The unchanged transfer cannot produce that source observation, even with
an oracle containing its recipient reason. A source-world frame is required. -/
theorem recipient_payload_not_reconstructed :
    TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 1 rfl)) rejecting ≠
      .error (.revertWith (encodeError reason)) :=
  transfer_does_not_bubble rejecting (.lit 9 rfl) (.lit 1 rfl) _

/-- A full-gas call keeps the failure branch under the noCallback stipend option. -/
theorem full_gas_can_fail :
    ExecS ((Fml.tt : Fml StandardExample []).stateInv false) (funded.push (t := .val .bool) (true : Bool))
      (.send .here (.simple (.lit 9 rfl)) (.simple (.lit 1 rfl)) true)
      (.ok ⟨(funded.push (t := .val .bool) (true : Bool)).setLocal .here (false : Bool), List.prefix_refl _⟩) :=
  send_failure_outcome _ true rfl _ .here (.lit 9 rfl) (.lit 1 rfl)

#print axioms missing_response_success
#print axioms zero_refusal
#print axioms hundred_ether_unfunded
#print axioms expected_error_nonempty
#print axioms recipient_error_refuses
#print axioms recipient_payload_not_reconstructed
#print axioms full_gas_can_fail
end Solidity.Examples.Tactics.PaymentConditions
