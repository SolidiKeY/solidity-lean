import Solidity.Backend.Executable.PaymentReceiptChecks

/-! Actual repeated same-key payments distinguish a pointwise receipt adapter
from execution with one immutable intrinsic transaction table. This is finite
payment/world preparation, not G36.03 or a new source execution semantics. -/
namespace Solidity.Backend.Executable.PaymentHistory
open ContractWorld Semantics
open PaymentCheckpointChecks (contracts sender fresh reference)
open PaymentCases (C Γ one w receive caller)

/-- One credit below the actual uint256 capacity, with a funded sender. -/
def almostMaximum : ContractWorld.Word := ⟨(2 : Int)^256 - 2,by decide +kernel⟩
def before : World contracts := {w with funds := fun a =>
  if a = fresh then almostMaximum else w.funds a}
def firstRun : TRes (World contracts × Bool) := before.stipend .send reference (receive false) sender one
private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok value => value | .error _ => fallback
private theorem recover {α : Type} (r : TRes α) (fallback : α)
    (ok : r.toOption.isSome = true) : r = .ok (valueOr r fallback) := by
  cases r with | ok value => rfl | error e => cases ok

def first : World contracts × Bool := valueOr firstRun (before,false)
theorem first_runs : firstRun = .ok first := recover _ _ (by decide +kernel)
theorem first_observations : first.2 = true ∧
    (first.1.funds sender).val = 2 ∧ (first.1.funds fresh).val = (2 : Int)^256-1 ∧
    (before.funds sender).val = 3 := by decide +kernel

private def halt {α : Type} : TRes α → Option THalt
  | .ok _ => none | .error e => some e
private theorem failed {α : Type} (r : TRes α) (e : THalt)
    (observed : halt r = some e) : r = .error e := by
  cases r with | ok x => cases observed | error e' => cases Option.some.inj observed; rfl

/-- The refusal occurs at actual second paid entry, before its empty body. -/
theorem second_enter_fails :
    first.1.enter fresh {sender,mode := .ordinary one} (Storage.init C) true = .error .revert :=
  failed _ _ (by decide +kernel)

/-- Both sender funding and body success remain available; second entry
refuses because the actual recipient balance would overflow. -/
theorem second_entry_fails :
    first.1.receiveRun reference (receive false) sender one = .error .revert :=
  failed _ _ (by decide +kernel)
theorem second_runs :
    first.1.stipend .send reference (receive false) sender one = .ok (first.1,false) := by
  unfold World.stipend
  rw [show (first.1.isLibrary () || (first.1.storage? reference).isNone) = false from by decide +kernel]
  simp only [Bool.false_eq_true, ↓reduceIte, second_entry_fails, sendResult, catchable]

/-- Execute both actual world operations, preserving the exact first paid
world after the caught second failure and both ordered Bool observations. -/
def two : TRes (World contracts × (Bool × Bool)) := do
  let (middle,a) ← firstRun
  let (last,b) ← middle.stipend .send reference (receive false) sender one
  pure (last,(a,b))
theorem two_runs : two = .ok (first.1,(true,false)) := by
  unfold two
  rw [first_runs]
  simp only [bind, Except.bind]
  rw [second_runs, first_observations.1]
  simp only [pure, Except.pure]

/-- Same typed sender frame can be entered against the almost-full world. -/
theorem actual_caller_entry :
    before.enter sender (PaymentCases.ctx false) (Storage.init C) true = .ok (PaymentCases.entered false) := rfl

def prepared (r : ExtResult) : State C Γ := PaymentReceipt.install (caller false) fresh.1 one r
def once (r : ExtResult) : Out C (prepared r).H Γ := sendT (prepared r) .here fresh.1 one
def twice (r : ExtResult) : Out C (once r).st.H Γ := sendT (once r).st .here fresh.1 one

/-- Intrinsic execution keeps its original transaction receipt table. Actual
caller funding permits both sends, but the actual world changes its outcome. -/
theorem source_both :
    TEnv.get .here (once (.ok [])).st.env = true ∧
    TEnv.get .here (twice (.ok [])).st.env = true ∧
    (twice (.ok [])).st.net = [(fresh.1,-2)] ∧
    (twice (.ok [])).st.selfBalance.val = 1 ∧
    (TEnv.get (.there .here) (twice (.ok [])).st.env).val = 99 := by decide +kernel

/-- The same two actual intrinsic statements, with no between-call table edit. -/
def sourceProgram : Prog C Γ Γ :=
  .cons (.send .here PaymentCases.recipientValue (PaymentCases.amountValue one) false)
    (.cons (.send .here PaymentCases.recipientValue (PaymentCases.amountValue one) false) .nil)
theorem source_program_runs (r : ExtResult) : sourceProgram.run (prepared r) = .ok (twice r) := rfl

/-- No fixed single-key receipt reproduces the ordered world observations
for this funded caller, even though each call separately has a derived receipt. -/
theorem no_fixed_receipt (r : ExtResult) :
    ¬ (TEnv.get .here (once r).st.env = true ∧
       TEnv.get .here (twice r).st.env = false) := by
  have base : ¬ (TEnv.get .here (once (.ok [])).st.env = true ∧
      TEnv.get .here (twice (.ok [])).st.env = false) := by
    rintro ⟨_,second⟩
    have impossible : true = false := source_both.2.1.symm.trans second
    cases impossible
  cases r <;>
    simp only [once, twice, sendT, State.setLocal, TEnv.get, State.canPay, prepared,
      PaymentReceipt.install, lookupBy, ↓reduceIte, Bool.and_false, State.pay, TEnv.set] at *
  all_goals first | exact base | (rintro ⟨bad,_⟩; cases bad)

private theorem true_pair {α : Type} (p : α × Bool) (h : p.2 = true) : p = (p.1,true) := by
  cases p with | mk a b => cases h; rfl

/-- The actual pointwise producer changes its answer only after the actual
first world execution; it is not a fixed whole-program transaction table. -/
theorem pointwise_receipts :
    PaymentReceipt.prepare before reference (receive false) sender one = some (.ok []) ∧
    PaymentReceipt.prepare first.1 reference (receive false) sender one = some (.other []) := by
  constructor
  · unfold PaymentReceipt.prepare
    rw [show (before.isLibrary () || (before.storage? reference).isNone) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- The receive itself is successful, independently of sendResult's Bool.
    have ran := World.stipend_send_true (first_runs.trans
      (congrArg Except.ok (true_pair first first_observations.1)))
    rw [ran]
    rfl
  · unfold PaymentReceipt.prepare
    rw [show (first.1.isLibrary () || (first.1.storage? reference).isNone) = false from by decide +kernel]
    simp only [Bool.false_eq_true, ↓reduceIte, second_entry_fails, PaymentReceipt.reply, catchable, THalt.data]

/-- The actual two sends never edit the installed receipt table. -/
theorem source_table_unchanged (r : ExtResult) : (twice r).st.tx.ext = (prepared r).tx.ext := rfl

/-- Missing entries also accept both calls. This is a source-table default,
not the adapter's explicit None refusal and not deployed-code evidence. -/
def absent : State C Γ := {caller false with tx := {(caller false).tx with ext := []}}
theorem absent_table_accepts : absent.canPay fresh.1 one = true ∧
    ((sourceProgram.run absent).toOption.map fun out =>
      (TEnv.get (C := C) (H := out.st.H) (.here : Idx Γ (.val .bool)) out.st.env,out.st.selfBalance.val)) = some (true,1) := by decide +kernel

/-- Normal intrinsic execution does not imply successful deferred world
settlement: its two-credit ledger overflows the original recipient balance. -/
theorem deferred_settlement_fails : before.finish sender (twice (.ok [])).st = .error .revert :=
  failed _ _ (by decide +kernel)

/-- info: 'Solidity.Backend.Executable.PaymentHistory.second_enter_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_enter_fails
/-- info: 'Solidity.Backend.Executable.PaymentHistory.deferred_settlement_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deferred_settlement_fails
/-- info: 'Solidity.Backend.Executable.PaymentHistory.two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_runs
/-- info: 'Solidity.Backend.Executable.PaymentHistory.source_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_both
/-- info: 'Solidity.Backend.Executable.PaymentHistory.no_fixed_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_fixed_receipt
/-- info: 'Solidity.Backend.Executable.PaymentHistory.pointwise_receipts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pointwise_receipts
/-- info: 'Solidity.Backend.Executable.PaymentHistory.first_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_runs
/-- info: 'Solidity.Backend.Executable.PaymentHistory.first_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_observations
/-- info: 'Solidity.Backend.Executable.PaymentHistory.second_entry_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_entry_fails
/-- info: 'Solidity.Backend.Executable.PaymentHistory.second_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_runs
/-- info: 'Solidity.Backend.Executable.PaymentHistory.actual_caller_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms actual_caller_entry
/-- info: 'Solidity.Backend.Executable.PaymentHistory.source_program_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_program_runs
/-- info: 'Solidity.Backend.Executable.PaymentHistory.source_table_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_table_unchanged
/-- info: 'Solidity.Backend.Executable.PaymentHistory.absent_table_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_table_accepts
end Solidity.Backend.Executable.PaymentHistory
