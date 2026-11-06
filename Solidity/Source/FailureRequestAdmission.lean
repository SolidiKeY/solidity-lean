import Solidity.Source.FailureRequest
import Solidity.Source.FailureMachineControls

/-! Exact-Nat value admission controls on the actual request scope. This is
not balance installation, a transaction/session driver, or native evidence. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx}
/-- Admission is not a new resource choice: the TxFate contract already
requires value to fit the exact post-fee balance before code may run. -/
def admitRequestFate (value : Roadmap.Word) : Roadmap.Evm.TxFate → Roadmap.Evm.TxFate
  | .dropped => .dropped
  | .runs balance cut => if balance < value.val then .dropped else .runs balance cut

/-- Only the currently issued request is normalized; every frame choice and
all other request choices remain the original immutable plan's. -/
def admitRequestAt (points : Roadmap.Evm.FailurePoints) (index : Nat)
    (value : Roadmap.Word) : Roadmap.Evm.FailurePoints :=
  { points with tx := fun i => if i = index then admitRequestFate value (points.tx i)
      else points.tx i }

/-- Exact value admission around the EXISTING actual request scope. The body
receives its original full Nat balance and keeps its original plan closure.
No balance is installed or projected; no evaluator/session is replaced. -/
def requestValueScope {α : Type} (points : Roadmap.Evm.FailurePoints)
    (q : Roadmap.Request) (body : Nat → EM E Γ α) : EM E Γ (Option α) := do
  let cursor := (← st).resource
  requestScope (admitRequestAt points cursor.nextRequest q.value) body

theorem admission_frames (points : Roadmap.Evm.FailurePoints) (index : Nat)
    (value : Roadmap.Word) : (admitRequestAt points index value).frame = points.frame := by rfl

theorem admission_other (points : Roadmap.Evm.FailurePoints) (index i : Nat)
    (value : Roadmap.Word) (other : i ≠ index) :
    (admitRequestAt points index value).tx i = points.tx i := by
  simp only [admitRequestAt, other, if_false]

/-- Exact invalid-value suppression for arbitrary typed callers/states and
arbitrary bodies. The initial cursor is explicit, not a general Session law. -/
theorem request_value_unfunded {α : Type} (balance : Nat) (cut : Option Nat) (q : Roadmap.Request)
    (bad : balance < q.value.val) (body : Nat → EM E Γ α)
    (l : Locals E.layout Γ) (s : St E) :
    (requestValueScope (constantRequestPlan (.runs balance cut)) q body).run
      (l,{ s with resource := Cursor.empty }) =
      (.ok none,(l,{ s with resource := requestFinished })) := by
  simp only [requestValueScope, admitRequestAt, admitRequestFate,
    constantRequestPlan, bad, if_true]
  rfl

/-- A genuinely affordable constant fate executes exactly the old scope,
including every body halt/state effect and resource-cut behavior. -/
theorem request_value_admitted {α : Type} (balance : Nat) (cut : Option Nat)
    (q : Roadmap.Request) (good : q.value.val ≤ balance) (body : Nat → EM E Γ α) :
    requestValueScope (constantRequestPlan (.runs balance cut)) q body =
      requestScope (constantRequestPlan (.runs balance cut)) body := by
  simp only [requestValueScope, admitRequestAt, admitRequestFate,
    constantRequestPlan, Nat.not_lt.mpr good, if_false, ite_self]
  rfl

end Solidity.Source.FailureExecution

namespace Solidity.Source.FailureExecution.AdmissionControls
open EM Controls

def q (value : Roadmap.Word) : Roadmap.Request :=
  ⟨⟨1,by decide⟩,⟨2,by decide⟩,value,⟨0,by decide⟩,[0xDE,0xAD]⟩
def finished : St E := { journalSeed with resource := requestFinished }
def poison : Nat → EM E [.bytes .memory,.bool] Nat :=
  fun _ => do modSt (fun s => { s with logs := [] }); halt (.stuck "poison")

theorem insufficient_before_cut :
    (requestValueScope (constantRequestPlan (.runs 1 (some 0)))
      (q ⟨2,by decide⟩) poison).run (caller,journalSeed) =
      (.ok none,(caller,finished)) := by rfl

theorem insufficient_no_cut :
    (requestValueScope (constantRequestPlan (.runs 1 none))
      (q ⟨2,by decide⟩) poison).run (caller,journalSeed) =
      (.ok none,(caller,finished)) := by rfl

theorem exact_value :
    (requestValueScope (constantRequestPlan (.runs 257 none))
      (q ⟨257,by decide⟩) (fun b => pure b : Nat → EM E [.bytes .memory,.bool] Nat)).run
      (caller,journalSeed) = (.ok (some 257),(caller,finished)) := by rfl

theorem sufficient_zero_cut :
    (requestValueScope (constantRequestPlan (.runs 257 (some 0)))
      (q ⟨257,by decide⟩) poison).run (caller,journalSeed) =
      (.error (.revert []),(caller,finished)) := by rfl

theorem dropped :
    (requestValueScope (constantRequestPlan .dropped)
      (q ⟨0,by decide⟩) poison).run (caller,journalSeed) =
      (.ok none,(caller,finished)) := by rfl

def changedCaller : Locals E.layout [.bytes .memory,.bool] :=
  .cons (.memRef rfl 0) (.cons (.bool false) .nil)
def written : St E := { finished with ex := finished.ex.apply childOp }
def mutateHalt (why : Halt) : Nat → EM E [.bytes .memory,.bool] Nat := fun _ => do
  setLocals changedCaller
  modSt (fun s => { s with ex := s.ex.apply childOp })
  halt why

theorem full_revert (bytes : Roadmap.Bytes) :
    (requestValueScope (constantRequestPlan (.runs 257 none))
      (q ⟨1,by decide⟩) (mutateHalt (.revert bytes))).run (caller,journalSeed) =
      (.error (.revert bytes),(changedCaller,written)) := by rfl

theorem timeout :
    (requestValueScope (constantRequestPlan (.runs 257 none))
      (q ⟨1,by decide⟩) (mutateHalt .timeout)).run (caller,journalSeed) =
      (.error .timeout,(changedCaller,written)) := by rfl

theorem stuck :
    (requestValueScope (constantRequestPlan (.runs 257 none))
      (q ⟨1,by decide⟩) (mutateHalt (.stuck "entered"))).run (caller,journalSeed) =
      (.error (.stuck "entered"),(changedCaller,written)) := by rfl

theorem full_nat_balance :
    (requestValueScope (constantRequestPlan (.runs (2^256) none))
      (q ⟨2^256-1,by decide⟩) (fun b => pure b : Nat → EM E [.bytes .memory,.bool] Nat)).run
      (caller,journalSeed) = (.ok (some (2^256)),(caller,finished)) := by rfl

theorem active_refused :
    let active : St E := { journalSeed with resource := Cursor.empty.enterFrame ownPlan }
    (requestValueScope (constantRequestPlan (.runs 1 none))
      (q ⟨2,by decide⟩) poison).run (caller,active) =
      (.error (.stuck "active request/frame at request entry"),(caller,active)) := by rfl

theorem dropped_then_next :
    let points : Roadmap.Evm.FailurePoints := {
      tx := fun i => if i = 0 then .runs 0 (some 0) else .runs 257 none
      frame := fun _ => none }
    ((do
      let _ ← requestValueScope points (q ⟨1,by decide⟩) poison
      requestValueScope points (q ⟨257,by decide⟩)
        (fun b => pure b : Nat → EM E [.bytes .memory,.bool] Nat))).run (caller,journalSeed) =
      (.ok (some 257),(caller,{ journalSeed with resource := ⟨2,0,none,[],none⟩ })) := by rfl

end Solidity.Source.FailureExecution.AdmissionControls

/-- info: 'Solidity.Source.FailureExecution.admitRequestFate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.admitRequestFate

/-- info: 'Solidity.Source.FailureExecution.admitRequestAt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.admitRequestAt

/-- info: 'Solidity.Source.FailureExecution.requestValueScope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.requestValueScope

/-- info: 'Solidity.Source.FailureExecution.admission_frames' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.admission_frames

/-- info: 'Solidity.Source.FailureExecution.admission_other' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.admission_other

/-- info: 'Solidity.Source.FailureExecution.request_value_unfunded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_value_unfunded

/-- info: 'Solidity.Source.FailureExecution.request_value_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_value_admitted

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.insufficient_before_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.insufficient_before_cut

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.insufficient_no_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.insufficient_no_cut

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.exact_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.exact_value

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.sufficient_zero_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.sufficient_zero_cut

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.dropped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.dropped

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.full_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.full_revert

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.timeout

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.stuck

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.full_nat_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.full_nat_balance

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.active_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.active_refused

/-- info: 'Solidity.Source.FailureExecution.AdmissionControls.dropped_then_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.AdmissionControls.dropped_then_next
