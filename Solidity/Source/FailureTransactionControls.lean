import Solidity.Source.FailureRuntimeControls

/-! Actual explicit-plan transaction/root dispatch controls. The same registered
intrinsic program, Fixed hash and strategy as RuntimeControls are used. No
request-fate scope, post-fee balance installation or P8 realization is claimed.
Completed reverts finalize transient state; propagated resource stops and
horizon exhaustion retain their exceptional state and emit no receipt. -/
namespace Solidity.Source.FailureExecution.TransactionControls
open EM SemanticsExamples
open RuntimeControls (input glob data priorEvent callEvent answerEvent points requestPlan requestInput ancestorPlan ancestorInput)

private instance {α : Type} [DecidableEq α] : DecidableEq (Except Halt α) := fun a b =>
  match a,b with
  | .error x,.error y => decidable_of_iff (x=y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .ok x,.ok y => decidable_of_iff (x=y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .error _,.ok _ => isFalse (by intro h; cases h)
  | .ok _,.error _ => isFalse (by intro h; cases h)

def run (p : Roadmap.Pipeline) (cut : Option Nat) (fuel : Nat := 20) :=
  (runTxWithPlan (glob p) fuel (tx data) (points cut)).run (L0 EB,input)
def receipt (o : Roadmap.Outcome) : Roadmap.Event := .tx user thisC (word 0) (word 0) data o

theorem uncut (p : Roadmap.Pipeline) :
    let r := run p none
    r.1 = .ok (.success []) ∧
    r.2.2.events = [priorEvent,callEvent,answerEvent,receipt (.success [])] ∧
    readX r.2.2 = some 3 ∧ readT r.2.2 = some 0 ∧
    r.2.2.ex.journal.length = 0 ∧ r.2.2.resource.nextFrame = 1 ∧ r.2.2.heap.next = 0 := by
  cases p <;> decide +kernel

theorem own_cut1 (p : Roadmap.Pipeline) :
    let r := run p (some 1)
    r.1 = .ok (.revert []) ∧ r.2.2.events = [priorEvent,callEvent,receipt (.revert [])] ∧
    readX r.2.2 = some 3 ∧ readT r.2.2 = some 0 ∧
    r.2.2.ex.journal.length = 0 ∧ r.2.2.resource.nextFrame = 1 ∧ r.2.2.resource.pending.isNone = true := by
  cases p <;> decide +kernel

theorem own_cut0 (p : Roadmap.Pipeline) :
    let r := run p (some 0)
    r.1 = .ok (.revert []) ∧ r.2.2.events = [priorEvent,receipt (.revert [])] := by
  cases p <;> decide +kernel

theorem zero_horizon (p : Roadmap.Pipeline) :
    let r := run p none 0
    r.1 = .error .timeout ∧ r.2.2.events = [priorEvent] ∧
    readT r.2.2 = some 4 ∧ r.2.2.resource.nextFrame = 1 := by
  cases p <;> decide +kernel

def requestRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (glob p) 20 (tx data) requestPlan).run (L0 EB,requestInput)
def ancestorRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (glob p) 20 (tx data) ancestorPlan).run (L0 EB,ancestorInput)

theorem request_propagates (p : Roadmap.Pipeline) :
    let r := requestRun p
    r.1 = .error (.revert []) ∧ r.2.2.events = [priorEvent,callEvent] ∧
    readT r.2.2 = some 4 ∧ r.2.2.ex.journal.length = 1 ∧
    r.2.2.resource.nextRequest = 2 ∧ r.2.2.resource.nextFrame = 1 ∧
    r.2.2.resource.pending.map (fun stop => (stop.isRequest 1,stop.isFrame 0)) = some (true,false) := by
  cases p <;> decide +kernel

theorem ancestor_propagates (p : Roadmap.Pipeline) :
    let r := ancestorRun p
    r.1 = .error (.revert []) ∧ r.2.2.events = [priorEvent,callEvent] ∧
    readT r.2.2 = some 4 ∧ r.2.2.ex.journal.length = 1 ∧
    r.2.2.resource.nextFrame = 2 ∧ r.2.2.resource.frames.length = 1 ∧
    r.2.2.resource.pending.map (fun stop => (stop.isFrame 0,stop.isRequest 1)) = some (true,false) := by
  cases p <;> decide +kernel

/-- Independent expected final state from actual root rollback/finalization:
transient and journal are cleared, caller heap is cleared, and every other
state field is the original input except the counted cursor and event list. -/
def finalized (events : List Roadmap.Event) : St EB :=
  { input with
    ex := input.ex.endTx
    heap := Heap.empty
    events := events
    resource := ⟨0,1,none,[],none⟩ }

theorem own_cut1_full_state (p : Roadmap.Pipeline) :
    run p (some 1) = (.ok (.revert []),(.nil,
      finalized [priorEvent,callEvent,receipt (.revert [])])) := by
  cases p <;>
    change ((.ok (.revert []),(.nil,
      { finalized [priorEvent,callEvent,receipt (.revert [])] with
        ex := (input.ex.apply (.account thisC (fun a => a.withBalance (word 0)))).undo.endTx })) : Except Halt Roadmap.Outcome × (Locals EB.layout [] × St EB)) = _
  all_goals rw [ExecState.undo_apply]; rfl

theorem own_cut0_full_state (p : Roadmap.Pipeline) :
    run p (some 0) = (.ok (.revert []),(.nil,
      finalized [priorEvent,receipt (.revert [])])) := by
  cases p <;> rfl

theorem request_full_state (p : Roadmap.Pipeline) :
    requestRun p = (.error (.revert []),(.nil,
      { RuntimeControls.requestExpected with heap := Heap.empty })) := by
  cases p <;>
    change ((.error (.revert []),(.nil,
      { RuntimeControls.requestExpected with
        heap := Heap.empty
        ex := (input.ex.apply (.account thisC (fun a => a.withBalance (word 0)))).undo })) : Except Halt Roadmap.Outcome × (Locals EB.layout [] × St EB)) = _
  all_goals rw [ExecState.undo_apply]; rfl

theorem ancestor_full_state (p : Roadmap.Pipeline) :
    ancestorRun p = (.error (.revert []),(.nil,
      { RuntimeControls.ancestorExpected with heap := Heap.empty })) := by
  cases p <;>
    change ((.error (.revert []),(.nil,
      { RuntimeControls.ancestorExpected with
        heap := Heap.empty
        ex := (input.ex.apply (.account thisC (fun a => a.withBalance (word 0)))).undo })) : Except Halt Roadmap.Outcome × (Locals EB.layout [] × St EB)) = _
  all_goals rw [ExecState.undo_apply]; rfl

/-- Missing code refuses before starting a frame: unlike an entered halt,
the root has not cleared the caller heap. Finalization still clears transient
state/journal and emits a completed refusal receipt. -/
def missingInput : St EB :=
  { input with ex := input.ex.apply (.account thisC (fun a => { a with code := none })) }
def missingRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (glob p) 20 (tx data) (points none)).run (L0 EB,missingInput)
def missingExpected : St EB :=
  { missingInput with
    ex := missingInput.ex.endTx
    events := [priorEvent,receipt (.revert [])] }

theorem missing_code_full_state (p : Roadmap.Pipeline) :
    missingRun p = (.ok (.revert []),(.nil,missingExpected)) := by
  cases p <;> rfl

/-- A reached request stop is checked before instance lookup/root entry.
The complete source heap, logs, nonword function locals, transient state and
journal survive exceptionally; there is no transaction receipt. -/
def entryPoints : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 (some 0)
  frame _ := none
def entryCursor : Cursor := (Cursor.empty.enterRequest entryPoints rfl).2
def entryInput : St EB := { input with resource := entryCursor }
def entryExpected : St EB :=
  { entryInput with resource := { entryCursor with pending := some (.request ⟨0,by decide⟩) } }
def entryRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (glob p) 20 (tx data) entryPoints).run (L0 EB,entryInput)

theorem entry_stop_full_state (p : Roadmap.Pipeline) :
    entryRun p = (.error (.revert []),(.nil,entryExpected)) := by
  cases p <;> rfl

/-- A real registered declaration with a mismatched body frame stays stuck,
not a completed revert; the credit journal and transient cells are not
finalized or rolled back, while the entered root has cleared its heap. -/
def stuckRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (RuntimeControls.wrongFrameGlob p) 20 (tx data) (points none)).run
    (L0 EB,input)
def stuckExpected : St EB :=
  { input with
    ex := input.ex.apply (.account thisC (fun a => a.withBalance (word 0)))
    heap := Heap.empty
    resource := ⟨0,1,none,[],none⟩ }

theorem stuck_full_state (p : Roadmap.Pipeline) :
    stuckRun p = (.error (.stuck "call frame"),(.nil,stuckExpected)) := by
  cases p <;> rfl

/-- Ordinary panic data remains the complete selector and32-byte payload,
not the empty data used for scheduled resource stops. -/
def panicRun (p : Roadmap.Pipeline) :=
  (runTxWithPlan (RuntimeControls.panicGlob p) 20 (tx (selOf "cb()")) (points none)).run
    (L0 EB,input)
def panicReceipt : Roadmap.Event :=
  .tx user thisC (word 0) (word 0) (selOf "cb()") (.revert RuntimeControls.panicBytes)

theorem panic_full_state (p : Roadmap.Pipeline) :
    panicRun p = (.ok (.revert RuntimeControls.panicBytes),(.nil,
      finalized [priorEvent,panicReceipt])) := by
  cases p <;>
    change ((.ok (.revert RuntimeControls.panicBytes),(.nil,
      { finalized [priorEvent,panicReceipt] with
        ex := (input.ex.apply (.account thisC (fun a => a.withBalance (word 0)))).undo.endTx })) :
      Except Halt Roadmap.Outcome × (Locals EB.layout [] × St EB)) = _
  all_goals rw [ExecState.undo_apply]; rfl

end Solidity.Source.FailureExecution.TransactionControls

/- BEGIN GENERATED TRANSACTION PINS -/
/-- info: 'Solidity.Source.runTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runTx
/-- info: 'Solidity.Source.runTxWithPlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runTxWithPlan
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.uncut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.uncut
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.own_cut1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.own_cut1
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.own_cut0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.own_cut0
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.zero_horizon
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.request_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.request_propagates
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.ancestor_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.ancestor_propagates
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.own_cut1_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.own_cut1_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.own_cut0_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.own_cut0_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.request_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.request_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.ancestor_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.ancestor_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.missing_code_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.missing_code_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.entry_stop_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.entry_stop_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.stuck_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.stuck_full_state
/-- info: 'Solidity.Source.FailureExecution.TransactionControls.panic_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.TransactionControls.panic_full_state
/- END GENERATED TRANSACTION PINS -/
