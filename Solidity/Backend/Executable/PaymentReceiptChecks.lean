import Solidity.Backend.Executable.PaymentReceipt
import Solidity.Backend.Executable.PaymentCases

/-! Inhabited actual receiver-result receipt clients. No machine execution or
world/caller journal reconciliation is inferred from Bool agreement. -/
namespace Solidity.Backend.Executable.PaymentReceiptChecks
open ContractWorld Semantics
open PaymentCheckpointChecks (contracts sender fresh reference)
open PaymentCases (C Γ w one four caller receive receiveWorld overflowWorld)
open PaymentReceipt

def successRun : TRes (World contracts × Unit) := w.receiveRun reference (receive false) sender one
def failureRun : TRes (World contracts × Unit) := w.receiveRun reference (receive true) sender one
def overflowRun : TRes (World contracts × Unit) := overflowWorld.receiveRun reference (receive false) sender one

/-- A stale failure receipt is shadowed by an actual successful receiver run. -/
def successCaller : State C Γ := install (caller true) fresh.1 one (.ok [])
def successOut : Out C successCaller.H Γ := sendT successCaller .here fresh.1 one

theorem success_prepared : reply successRun = some (.ok []) := by
  unfold successRun
  rw [PaymentCases.receive_normal]
  rfl

theorem actual_success :
    ((prepare w reference (receive false) sender one).map fun r =>
      (install (caller true) fresh.1 one r).canPay fresh.1 one) = some true ∧
    w.stipend .send reference (receive false) sender one = .ok (receiveWorld,true) := by
  have actual : w.stipend .send reference (receive false) sender one = .ok (receiveWorld,true) :=
    PaymentCases.world_paid.trans (congrArg Except.ok PaymentCases.paid_normal)
  exact ⟨(world_observation w reference (receive false) sender one (caller true) rfl).trans
    (congrArg (fun r => r.toOption.map Prod.snd) actual), actual⟩

theorem source_success :
    TRun.send .here PaymentCases.recipientValue (PaymentCases.amountValue one) successCaller =
      .ok successOut ∧
    TEnv.get .here successOut.st.env = true ∧
    (TEnv.get (.there .here) successOut.st.env).val = 99 ∧
    successOut.st.net = [(fresh.1,-1)] ∧ successOut.st.selfBalance.val = 2 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Actual receiver body bytes are classified into a rejecting
receipt, rather than defaulting to missing-entry acceptance. -/
theorem actual_failure : reply failureRun = some (.other [0xde,0xad]) ∧
    observe (caller false) fresh.1 one failureRun = some false := by
  unfold failureRun
  rw [PaymentCases.funded_receive]
  constructor <;> decide +kernel

theorem entry_overflow : reply overflowRun = some (.other []) ∧
    observe (caller false) fresh.1 one overflowRun = some false := by
  unfold overflowRun
  rw [PaymentCases.overflow_entry_failure]
  constructor <;> decide +kernel

/-- Funding refusal is classified before the otherwise nonempty body bytes. -/
theorem funding_first :
    reply (w.receiveRun reference (receive true) sender four) = some (.other []) ∧
    observe (caller false) fresh.1 four (w.receiveRun reference (receive true) sender four) = some false := by
  rw [PaymentCases.unfunded_receive]
  constructor <;> decide +kernel

/-- Installing at the wrong end retains the stale rejection and disagrees
with the successfully executed receive; head-first receipt installation matters. -/
def appendedCaller : State C Γ := {caller true with tx :=
  {(caller true).tx with ext := (caller true).tx.ext ++ [(sendKey fresh.1 one,.ok [])]}}
theorem wrong_order : appendedCaller.canPay fresh.1 one = false ∧
    successCaller.canPay fresh.1 one = true := by decide +kernel

/-- A caller's unrelated receipt is preserved, even with a conflicting actual
payment receipt and a populated protected local. -/
def otherKey : ExtKey := sendKey fresh.1 four
def populatedCaller : State C Γ := {caller true with tx :=
  {(caller true).tx with ext := (otherKey,.panic ⟨17,by decide⟩) :: (caller true).tx.ext}}
def preparedPopulated : State C Γ := install populatedCaller fresh.1 one (.ok [])
theorem other_key_preserved :
    lookupBy otherKey preparedPopulated.tx.ext = some (.panic ⟨17,by decide⟩) ∧
    (TEnv.get (.there .here) preparedPopulated.env).val = 99 ∧
    preparedPopulated.canPay fresh.1 one = true := by
  refine ⟨?_, rfl, by decide +kernel⟩
  exact (other_lookup populatedCaller fresh.1 one (.ok []) otherKey (by decide +kernel)).trans
    (by simp only [populatedCaller, lookupBy, ↓reduceIte])

/-- Exhaustion and divergence have no ordinary send receipt. These cannot be
silently represented by leaving the original table's accepting entry absent. -/
theorem resource_refused :
    reply (α := Unit) (.error .exhausted) = none ∧
    reply (α := Unit) (.error .diverge) = none ∧
    observe (caller false) fresh.1 one (.error .exhausted : TRes Unit) = none ∧
    (caller false).canPay fresh.1 one = true := by decide +kernel

/-- The raw receiver failure is catchable, but code admission fails first.
Only the complete preparation boundary refuses this missing-code call. -/
def missing : World contracts := {w with accounts := fun _ => none}
theorem missing_code_first :
    reply (missing.receiveRun reference (receive false) sender one) = some (.other []) ∧
    prepare missing reference (receive false) sender one = none ∧
    missing.stipend .send reference (receive false) sender one = .error .exhausted := by
  constructor
  · change reply (.error .revert : TRes (World contracts × Unit)) = _
    rfl
  · constructor <;> rfl

theorem prepared_success : prepare w reference (receive false) sender one = some (.ok []) := by
  unfold prepare
  rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact success_prepared

theorem prepared_overflow : prepare overflowWorld reference (receive false) sender one = some (.other []) := by
  unfold prepare
  rw [show (overflowWorld.isLibrary () || (overflowWorld.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact entry_overflow.1

/-- An actual entered receiver reaches the existing assumeFalse model stop.
The existing intrinsic send
statement itself always returns normally, so no receipt can reproduce that halt. -/
def exhausting : Entry C Unit := Entry.unit (.cons .assumeFalse .nil) true
theorem actual_exhaustion :
    w.receiveRun reference exhausting sender one = .error .exhausted ∧
    w.stipend .send reference exhausting sender one = .error .exhausted ∧
    prepare w reference exhausting sender one = none := by
  constructor
  · rfl
  · constructor <;> rfl

theorem exhausted_not_ordinary_send (r : ExtResult) :
    TRun.send .here PaymentCases.recipientValue (PaymentCases.amountValue one)
      (install (caller false) fresh.1 one r) ≠ .error .exhausted := by
  intro impossible
  cases impossible

/-- Even a receipt derived from the actual failure cannot turn the published
bare source-transfer halt into the world's nonempty failure bytes. -/
theorem derived_transfer_boundary :
    prepare w reference (receive true) sender one = some (.other [0xde,0xad]) ∧
    TRun.transfer PaymentCases.recipientValue (PaymentCases.amountValue one)
      (install (caller false) fresh.1 one (.other [0xde,0xad])) = .error .revert ∧
    w.stipend .transfer reference (receive true) sender one = .error (.revertWith [0xde,0xad]) := by
  refine ⟨?_, failed_transfer (caller false) fresh.1 one (.revertWith [0xde,0xad]),
    PaymentCases.transfer_failure_boundary.2⟩
  unfold prepare
  rw [show (w.isLibrary () || (w.storage? reference).isNone) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact actual_failure.1

/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.derived_transfer_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derived_transfer_boundary
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.actual_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_success
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_success
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.actual_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_failure
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.entry_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_overflow
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.funding_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms funding_first
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.wrong_order' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_order
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.other_key_preserved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms other_key_preserved
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.resource_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms resource_refused
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.missing_code_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_code_first
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.prepared_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepared_success
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.prepared_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepared_overflow
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.actual_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_exhaustion
/-- info: 'Solidity.Backend.Executable.PaymentReceiptChecks.exhausted_not_ordinary_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exhausted_not_ordinary_send
end Solidity.Backend.Executable.PaymentReceiptChecks
