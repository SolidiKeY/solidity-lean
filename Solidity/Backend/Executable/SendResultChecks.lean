import Solidity.Backend.Executable.SendResult
import Solidity.Backend.Executable.PaymentReceiptChecks
import Solidity.Backend.Executable.ValueCallChecks

/-! Actual intrinsic/world send clients carried through physical bool assignment.
These do not identify a numeric slice run with actual fetched CALL execution. -/
namespace Solidity.Backend.Executable.SendResultChecks
open ContractWorld Semantics Scalar SendResult
open PaymentCheckpointChecks (contracts sender fresh reference)
open PaymentCases (C w one four receive caller)
open PaymentReceiptChecks (successCaller successOut missing exhausting)

/-- Actual successful source statement and full existing world settlement are
retained while the real result suffix produces its entire encoded local frame. -/
theorem paid_client :
    TRun.send .here PaymentCases.recipientValue (PaymentCases.amountValue one) successCaller = .ok successOut ∧
    w.finish sender successOut.st = .ok PaymentCases.paid.1 ∧
    run store (1 :: frame successCaller [17,29]) = some (frame successOut.st [17,29]) ∧
    frame successOut.st [17,29] = [1,99,17,29] := by
  refine ⟨PaymentReceiptChecks.source_success.1,?_,?_,?_⟩
  · change w.finish sender (PaymentCases.sent false one).st = _
    exact PaymentCases.payment_client.2.1
  · exact source_store (caller true) [17,29] fresh.1 one (.ok [])
  · decide +kernel

/-- Initial true is overwritten by the actual failed receiver's false result;
the non-result uint and all populated spill words remain unchanged. -/
def trueCaller : State C SendResult.Γ := (caller false).setLocal .here true

def rejectedCaller : State C SendResult.Γ :=
  PaymentReceipt.install trueCaller fresh.1 one (.other [0xde,0xad])
def rejectedOut : Out C rejectedCaller.H SendResult.Γ := sendT rejectedCaller .here fresh.1 one

theorem rejected_client :
    PaymentReceipt.prepare w reference (receive true) sender one = some (.other [0xde,0xad]) ∧
    TRun.send .here PaymentCases.recipientValue (PaymentCases.amountValue one) rejectedCaller = .ok rejectedOut ∧
    run store (0 :: frame trueCaller [17,29]) = some (frame rejectedOut.st [17,29]) ∧
    frame rejectedOut.st [17,29] = [0,99,17,29] ∧
    rejectedOut.st.selfBalance.val = 3 ∧ rejectedOut.st.net = [] := by
  refine ⟨?_,rfl,?_,?_,?_,?_⟩
  · unfold PaymentReceipt.prepare
    rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, PaymentCases.funded_receive, PaymentReceipt.reply]
    rfl
  · exact source_store trueCaller [17,29] fresh.1 one (.other [0xde,0xad])
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The failed source send's actual unchanged fields settle to the same full
world that the real rejecting receiver send returns, not merely equal balances. -/
theorem rejected_world_settles : w.finish sender rejectedOut.st = .ok w ∧
    w.stipend .send reference (receive true) sender one = .ok (w,false) := by
  constructor
  · apply finish_unchanged
    · rfl
    · rfl
    · rfl
  · exact PaymentCases.rejected_send.2.2.2.2

/-- Full Bool/None observation transport is inhabited by a real paid world. -/
theorem paid_world_store :
    (PaymentReceipt.prepare w reference (receive false) sender one).bind (fun r =>
      run store (encodeValue .bool ((PaymentReceipt.install (caller true) fresh.1 one r).canPay fresh.1 one) ::
        frame (caller true) [17,29])) = some [1,99,17,29] := by
  have mapped := world_store w reference (receive false) sender one (caller true) [17,29] rfl
  rw [PaymentReceiptChecks.actual_success.2] at mapped
  exact mapped

/-- No receipt/stack is fabricated at actual installed-code refusal or actual
assumeFalse exhaustion. These are preparation refusals, not stored false. -/
theorem world_refusals :
    (PaymentReceipt.prepare missing reference (receive false) sender one).bind (fun r =>
      run store (encodeValue .bool ((PaymentReceipt.install (caller false) fresh.1 one r).canPay fresh.1 one) ::
        frame (caller false) [17,29])) = none ∧
    (PaymentReceipt.prepare w reference exhausting sender one).bind (fun r =>
      run store (encodeValue .bool ((PaymentReceipt.install (caller false) fresh.1 one r).canPay fresh.1 one) ::
        frame (caller false) [17,29])) = none := by
  rw [PaymentReceiptChecks.missing_code_first.2.1, PaymentReceiptChecks.actual_exhaustion.2.2]
  constructor <;> rfl

theorem wrong_store :
    run [.op .POP] (1 :: frame successCaller [17,29]) = some [0,99,17,29] ∧
    run [.op (.SWAP ⟨1,by decide⟩),.op .POP] (1 :: frame successCaller [17,29]) = some [0,1,17,29] ∧
    run store (1 :: frame successCaller [17,29]) = some [1,99,17,29] := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

theorem capacity_edges :
    stackBound store 1024 = true ∧ stackBound store 1025 = false ∧
    stackBound (ValueCall.operandCode (StipendCall.requested one) ValueCallChecks.recipient one) 1017 = true ∧
    stackBound (ValueCall.operandCode (StipendCall.requested one) ValueCallChecks.recipient one) 1018 = false := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

theorem bytes_control : Backend.encode store = [0x90,0x50] ∧
    (Backend.encode (SendResult.code ValueCallChecks.recipient one)).length = 107 ∧
    Backend.decode (Backend.encode (SendResult.code ValueCallChecks.recipient one)) =
      some (SendResult.code ValueCallChecks.recipient one) :=
  ⟨rfl,byte_length _ _,decode_bytes _ _⟩

/-- info: 'Solidity.Backend.Executable.SendResultChecks.paid_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_client

/-- info: 'Solidity.Backend.Executable.SendResultChecks.rejected_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_client

/-- info: 'Solidity.Backend.Executable.SendResultChecks.paid_world_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_world_store

/-- info: 'Solidity.Backend.Executable.SendResultChecks.world_refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_refusals

/-- info: 'Solidity.Backend.Executable.SendResultChecks.wrong_store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_store

/-- info: 'Solidity.Backend.Executable.SendResultChecks.capacity_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_edges

/-- info: 'Solidity.Backend.Executable.SendResultChecks.bytes_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_control

/-- info: 'Solidity.Backend.Executable.SendResultChecks.rejected_world_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_world_settles

end Solidity.Backend.Executable.SendResultChecks
