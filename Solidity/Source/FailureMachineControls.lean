import Solidity.Source.FailureMachine
import Solidity.Source.Semantics

/-! Independent expected actual-EM controls. No Source/EVM correspondence. -/
namespace Solidity.Source.FailureExecution.Controls
open EM

def E : Env := ⟨[]⟩
def event : Roadmap.Event := .credit ⟨9, by decide⟩ ⟨3, by decide⟩
def caller : Locals E.layout [.bytes .memory, .bool] :=
  .cons (.memRef rfl 0) (.cons (.bool true) .nil)
def seed : St E := { St.init E with
  heap := (Heap.empty.alloc ⟨.bytes .memory, Data.bytes [0xDE,0xAD]⟩).1
  events := [event]
  logs := [(⟨1, by decide⟩,[0xAA,0xBB])]
  fnLocals := ⟨[.bytes .memory, .bool], caller⟩ }
def ownPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := some 1

def swallowed (plan : RuntimePlan) : EM E [.bytes .memory, .bool] Nat := do
  let _ ← attempt (emit plan event)
  pure 7

def ownActual := (frame (some ownPlan) (swallowed (some ownPlan))).run (caller,seed)
def ownExpected : St E := { seed with events := [event,event], resource := ⟨0,1,none,[],none⟩ }

def stale : St E := { seed with resource := (Cursor.empty.enterFrame ownPlan).advanceEvent }
def noneActual := (frame none (emit none event)).run (caller,stale)
def noneExpected : St E := { stale with events := [event,event] }

def childPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame i := if i = 1 then some 1 else none

def nested (plan : RuntimePlan) : EM E [.bytes .memory, .bool] (Except Halt Nat) :=
  attempt (frame plan (swallowed plan))
def childActual := (frame (some childPlan) (nested (some childPlan))).run (caller,seed)
def childExpected : St E := { seed with events := [event,event], resource := ⟨0,2,none,[],none⟩ }
def ancestorActual := (frame (some ownPlan) (nested (some ownPlan))).run (caller,seed)

def requestPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 (some 1)
  frame _ := none

def requestSeed : St E := { seed with resource := (Cursor.empty.enterRequest requestPlan rfl).2 }
def requestActual := (frame (some requestPlan) (nested (some requestPlan))).run (caller,requestSeed)
def requestExpected : St E := { seed with events := [event,event], resource :=
  ⟨1,2,some ⟨⟨0,by decide⟩,257,some 1,1⟩,[],some (.request ⟨0,by decide⟩)⟩ }

def zeroPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := some 0

def zeroActual := (frame (some zeroPlan) (emit (some zeroPlan) event)).run (caller,seed)
def preStopped : St E := { seed with resource := Cursor.empty.enterFrame zeroPlan }
def refusedActual := (frame (some zeroPlan) (pure 7)).run (caller,preStopped)
def refusedExpected : St E := { preStopped with resource :=
  { preStopped.resource with pending := some (.frame ⟨0,by decide⟩) } }

def haltActual (why : Halt) :=
  (frame (some ownPlan) (halt why : EM E [.bytes .memory, .bool] Nat)).run (caller,seed)


-- Independent complete expected post-state, with no body events added.
def startedExpected : St E := { seed with resource := ⟨0,1,none,[],none⟩ }

def F : Fr := { this := ⟨1,by decide⟩, sender := ⟨2,by decide⟩, value := ⟨0,by decide⟩, static := false, contract := "" }

def readCallerAfter : EM E [.bytes .memory, .bool] (List UInt8) := do
  let _ ← attempt (frame (some ownPlan) (swallowed (some ownPlan)))
  let value ← lift ((← locals).getAt 0 (.bytes .memory))
  bytesOfRV F 1 (.val value)

def danglingAfter : EM E [.bytes .memory, .bool] (List UInt8) := do
  let _ ← attempt (frame (some ownPlan) (swallowed (some ownPlan)))
  heapBytes 1

-- Successful automation branches from retained scratch trials. No execution
-- outcome is a premise of these closed actual-Source controls.
theorem own_complete : ownActual = (.error (.revert []),(caller,ownExpected)) := by rfl
theorem disabled_complete : noneActual = (.ok (),(caller,noneExpected)) := by rfl
theorem child_complete : childActual = (.ok (.error (.revert [])),(caller,childExpected)) := by rfl
theorem ancestor_complete : ancestorActual = (.error (.revert []),(caller,childExpected)) := by rfl
theorem request_complete : requestActual = (.error (.revert []),(caller,requestExpected)) := by rfl
theorem zero_complete : zeroActual = (.error (.revert []),(caller,startedExpected)) := by rfl
theorem refused_complete : refusedActual = (.error (.revert []),(caller,refusedExpected)) := by rfl
theorem timeout_complete : haltActual .timeout = (.error .timeout,(caller,startedExpected)) := by rfl
theorem stuck_complete : haltActual (.stuck "control") = (.error (.stuck "control"),(caller,startedExpected)) := by rfl
theorem full_bytes_complete : haltActual (.revert [0xDE,0xAD]) = (.error (.revert [0xDE,0xAD]),(caller,startedExpected)) := by rfl
theorem empty_bytes_complete : haltActual (.revert []) = (.error (.revert []),(caller,startedExpected)) := by rfl
theorem no_false_success : ownActual.1 ≠ .ok 7 := by
  simp only [ne_eq, own_complete, reduceCtorEq, not_false_eq_true]
theorem wrong_full_bytes : (haltActual (.revert [0xDE,0xAD])).1 ≠ .error (.revert [0xAA,0xBB]) := by
  simp only [ne_eq, full_bytes_complete, Except.error.injEq, Halt.revert.injEq]
  decide
theorem wrong_child_owner : ancestorActual.1 ≠ .ok (.error (.revert [])) := by
  simp only [ne_eq, ancestor_complete, reduceCtorEq, not_false_eq_true]
theorem actual_local_read : readCallerAfter.run (caller,seed) = (.ok [0xDE,0xAD],(caller,ownExpected)) := by rfl
theorem dangling_read : danglingAfter.run (caller,seed) = (.error (.stuck "dangling memory reference"),(caller,ownExpected)) := by rfl
theorem disabled_check : (check none : EM E [.bytes .memory,.bool] Unit).run (caller,stale) = (.ok (),(caller,stale)) := by rfl
theorem disabled_pending : (pending none : EM E [.bytes .memory,.bool] Bool).run (caller,stale) = (.ok false,(caller,stale)) := by rfl


-- These control inputs are frozen before execution. The existing mark and
-- rollbackTo restore the logical account/log journal; frame only pops cursor.
def prefixEvent : Roadmap.Event := .credit ⟨7,by decide⟩ ⟨11,by decide⟩
def prefixOp : Op E.layout E.lay E.lay := .account ⟨3,by decide⟩ fun a => { a with nonce := 5 }
def childOp : Op E.layout E.lay E.lay := .account F.this fun a => { a with nonce := 99 }
def journalSeed : St E := { seed with ex := seed.ex.apply prefixOp, events := [prefixEvent] }
def childBody : EM E [.bytes .memory,.bool] Nat := do
  applyOp F childOp
  modSt fun s => { s with logs := (F.this,[0x08]) :: s.logs }
  emit (some ownPlan) event
  pure 7

def journalRun (wrongMark : Bool) : EM E [.bytes .memory,.bool] (Except Halt Nat) := do
  let m ← mark
  let result ← attempt (frame (some ownPlan) childBody)
  rollbackTo (if wrongMark then (0,0,m.2.2) else m)
  pure result

def journalActual := (journalRun false).run (caller,journalSeed)
def wrongJournalActual := (journalRun true).run (caller,journalSeed)
def journalExpected : St E := { journalSeed with events := [prefixEvent,event], resource := ⟨0,1,none,[],none⟩ }
def journalRawExpected : St E := { journalExpected with ex := (journalSeed.ex.apply childOp).undoN 1 }

theorem journal_raw : journalActual = (.ok (.error (.revert [])),(caller,journalRawExpected)) := by rfl
theorem journal_complete : journalActual = (.ok (.error (.revert [])),(caller,journalExpected)) := by
  simp only [journal_raw, journalRawExpected, journalExpected, ExecState.undoN, ExecState.undo_apply]

theorem caller_prefix_retained : (journalActual.2.2.ex.world.accounts ⟨3,by decide⟩).nonce = 5 := by rfl
theorem child_write_reverted : (journalActual.2.2.ex.world.accounts F.this).nonce = 0 := by rfl
theorem wrong_mark_loses_prefix : (wrongJournalActual.2.2.ex.world.accounts ⟨3,by decide⟩).nonce = 0 := by rfl
theorem request_not_frame : requestActual.2.2.resource.pending.map (fun s => s.isFrame 0) = some false := by rfl


/-- Actual pure Source panic, with every encoded byte retained. -/
theorem panic_complete (c : PanicCode) :
    (frame (some ownPlan) (lift (panic c) : EM E [.bytes .memory,.bool] Nat)).run (caller,seed) =
      (.error (.revert (panicData c)),(caller,startedExpected)) := by rfl

theorem panic_bytes : panicData .arithmetic =
    [0x4E,0x48,0x7B,0x71] ++ List.replicate 31 0 ++ [0x11] := by decide

/-- The real dispatch horizon guard inside the actual local-context adapter. -/
theorem dispatch_zero_complete (G : Glob E) :
    (frame (some ownPlan) (do
      let _ ← sub (.nil : Locals E.layout []) (dispatch G F 0 [])
      pure 7 : EM E [.bytes .memory,.bool] Nat)).run (caller,seed) =
      (.error .timeout,(caller,startedExpected)) := by rfl

/- BEGIN GENERATED H16 AXIOM PINS -/
/-- info: 'Solidity.Source.FailureExecution.Controls.own_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.own_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.disabled_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.disabled_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.child_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.child_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.ancestor_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.ancestor_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.request_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.request_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.zero_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.zero_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.refused_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.refused_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.timeout_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.timeout_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.stuck_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.stuck_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.full_bytes_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.full_bytes_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.empty_bytes_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.empty_bytes_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.no_false_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.no_false_success
/-- info: 'Solidity.Source.FailureExecution.Controls.wrong_full_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.wrong_full_bytes
/-- info: 'Solidity.Source.FailureExecution.Controls.wrong_child_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.wrong_child_owner
/-- info: 'Solidity.Source.FailureExecution.Controls.actual_local_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.actual_local_read
/-- info: 'Solidity.Source.FailureExecution.Controls.dangling_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.dangling_read
/-- info: 'Solidity.Source.FailureExecution.Controls.disabled_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.disabled_check
/-- info: 'Solidity.Source.FailureExecution.Controls.disabled_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.disabled_pending
/-- info: 'Solidity.Source.FailureExecution.Controls.journal_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.journal_raw
/-- info: 'Solidity.Source.FailureExecution.Controls.journal_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.journal_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.caller_prefix_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.caller_prefix_retained
/-- info: 'Solidity.Source.FailureExecution.Controls.child_write_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.child_write_reverted
/-- info: 'Solidity.Source.FailureExecution.Controls.wrong_mark_loses_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.wrong_mark_loses_prefix
/-- info: 'Solidity.Source.FailureExecution.Controls.request_not_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.request_not_frame
/-- info: 'Solidity.Source.FailureExecution.Controls.panic_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.panic_complete
/-- info: 'Solidity.Source.FailureExecution.Controls.panic_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.panic_bytes
/-- info: 'Solidity.Source.FailureExecution.Controls.dispatch_zero_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Controls.dispatch_zero_complete
/- END GENERATED H16 AXIOM PINS -/

end Solidity.Source.FailureExecution.Controls
