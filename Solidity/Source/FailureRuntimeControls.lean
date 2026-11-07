import Solidity.Source.SemanticsExamples
import Solidity.Source.FailureEventLaws

/-! Actual explicit-plan Source execution through existing registered code.
These controls consume the intrinsic SemanticsExamples program, bodies and
strategy unchanged (including its toy Fixed hash); they do not build another
interpreter or assert compiler/EVM correspondence. Expected full states are
source-derived. Request/ancestor examples use preinitialized typed cursors,
not a deployment/session execution; H18 root wiring and H19 funding remain
open. Heap indices are logical Source references, not physical EVM pointers.
The entered-transfer composition is proved; the outer CALL-prefix lemma is
not supplied. No final Y10/P8 or fixed-plan horizon adequacy is claimed. -/
namespace Solidity.Source.FailureExecution.RuntimeControls
open EM SemanticsExamples
abbrev Ctx : RCtx := [.bytes .memory,.bool]
def caller : Locals EB.layout Ctx := .cons (.memRef rfl 0) (.cons (.bool true) .nil)
def priorEvent : Roadmap.Event := .answer (.success [0xA1]) none
def input : St EB := { sB with
  ex := sB.ex.apply (.account user fun a => { a with nonce := 17 })
  heap := (Heap.empty.alloc ⟨.bytes .memory,Data.bytes [0xDE,0xAD]⟩).1
  events := [priorEvent]
  logs := [(user,[0xAA,0xBB])]
  fnLocals := ⟨Ctx,caller⟩ }
def points (cut : Option Nat) : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := cut
def glob (p : Roadmap.Pipeline) : Glob EB :=
  { GB (fun _ => .answer (.success [0xDE,0xAD])) with pipeline := p }
def data : Roadmap.Bytes := selOf "callOut(address)" ++ wordBytes (toWord ext.val)
def run (p : Roadmap.Pipeline) (cut : Option Nat) (fuel : Nat := 20) :=
  ((do
    let m ← mark
    sub (L0 EB) (enterInstance (plan := some (points cut)) (glob p) fuel thisC user (word 0) data false "C" 1 m)
    : EM EB Ctx (Roadmap.Outcome × Locals EB.layout []))).run (caller,input)
def endState (events : List Roadmap.Event) (frames : Nat) : St EB :=
  { input with events := events, resource := ⟨0,frames,none,[],none⟩ }
def callEvent : Roadmap.Event := .call ext (word 0) (selOf "ping()") false
def answerEvent : Roadmap.Event := .answer (.success [0xDE,0xAD]) none
theorem zero_cut (p : Roadmap.Pipeline) : run p (some 0) = (.ok (.revert [],.nil),(caller,endState [priorEvent] 1)) := by cases p <;> rfl
theorem first_event_cut (p : Roadmap.Pipeline) : run p (some 1) = (.ok (.revert [],.nil),(caller,endState [priorEvent,callEvent] 1)) := by cases p <;> rfl
theorem second_event_cut (p : Roadmap.Pipeline) : run p (some 2) = (.ok (.revert [],.nil),(caller,endState [priorEvent,callEvent,answerEvent] 1)) := by cases p <;> rfl
theorem uncut_success (p : Roadmap.Pipeline) : run p none = (.ok (.success [],.nil),(caller,endState [priorEvent,callEvent,answerEvent] 1)) := by cases p <;> rfl
theorem zero_horizon (p : Roadmap.Pipeline) : run p none 0 = (.error .timeout,(caller,input)) := by cases p <;> rfl
theorem entered_timeout (p : Roadmap.Pipeline) : run p none 1 = (.error .timeout,(caller,endState [priorEvent] 1)) := by cases p <;> rfl

def badGlob (p : Roadmap.Pipeline) : Glob EB :=
  { glob p with prog := { PB with body := fun _ => none } }
def runWith (g : Glob EB) (schedule : Roadmap.Evm.FailurePoints) (start : St EB)
    (bytes : Roadmap.Bytes := data) (static : Bool := false) (fuel : Nat := 20) :=
  ((do
    let m ← mark
    sub (L0 EB) (enterInstance (plan := some schedule) g fuel thisC user (word 0) bytes static "C" 1 m)
    : EM EB Ctx (Roadmap.Outcome × Locals EB.layout []))).run (caller,start)
theorem bodyless_refusal (p : Roadmap.Pipeline) : runWith (badGlob p) (points none) input =
    (.ok (.revert [],.nil),(caller,endState [priorEvent] 1)) := by
  cases p <;> rfl
def assertBody : RBody EB := body0 [] (.stmt (.expr (.builtin .assert (.cons (.bool false) .nil) rfl)) .nil)
def panicGlob (p : Roadmap.Pipeline) : Glob EB :=
  { glob p with prog := { PB with body := fun d => if d.name = "cb" then some assertBody else PB.body d } }
def panicBytes : Roadmap.Bytes := [0x4E,0x48,0x7B,0x71] ++ List.replicate 31 0 ++ [0x01]
theorem panic_full_bytes (p : Roadmap.Pipeline) : runWith (panicGlob p) (points none) input (selOf "cb()") =
    (.ok (.revert panicBytes,.nil),(caller,endState [priorEvent] 1)) := by
  cases p <;> rfl
def requestPlan : Roadmap.Evm.FailurePoints where
  tx i := if i = 1 then .runs 257 (some 1) else .runs 0 none
  frame _ := none
def reservedRequestSlot : Cursor := (Cursor.empty.enterRequest requestPlan rfl).2.leaveRequest
def requestInput : St EB := { input with resource := (reservedRequestSlot.enterRequest requestPlan rfl).2 }
def requestExpected : St EB := { input with events := [priorEvent,callEvent], resource :=
  ⟨2,1,some ⟨⟨1,by decide⟩,257,some 1,1⟩,[],some (.request ⟨1,by decide⟩)⟩ }
theorem request_propagates (p : Roadmap.Pipeline) : runWith (glob p) requestPlan requestInput =
    (.error (.revert []),(caller,requestExpected)) := by
  cases p <;> rfl
def ancestorPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame i := if i = 0 then some 1 else none
def ancestorInput : St EB := { input with resource := Cursor.empty.enterFrame ancestorPlan }
def ancestorExpected : St EB := { input with events := [priorEvent,callEvent], resource :=
  ⟨0,2,none,[⟨⟨0,by decide⟩,some 1,1⟩],some (.frame ⟨0,by decide⟩)⟩ }
theorem ancestor_propagates (p : Roadmap.Pipeline) : runWith (glob p) ancestorPlan ancestorInput =
    (.error (.revert []),(caller,ancestorExpected)) := by
  cases p <;> rfl
theorem static_event_cut (p : Roadmap.Pipeline) : runWith (glob p) (points (some 1)) input data true =
    (.ok (.revert [],.nil),(caller,endState [priorEvent,.call ext (word 0) (selOf "ping()") true] 1)) := by
  cases p <;> rfl


def wrongFrameGlob (p : Roadmap.Pipeline) : Glob EB :=
  { glob p with prog := { PB with body := fun d => if d.name = "callOut" then some (body0 [] .nil) else PB.body d } }
theorem wrong_frame_stuck (p : Roadmap.Pipeline) : runWith (wrongFrameGlob p) (points none) input =
    (.error (.stuck "call frame"),(caller,endState [priorEvent] 1)) := by
  cases p <;> rfl


def debitOp : Op EB.layout EB.lay EB.lay := .account user fun a => a.withBalance (word 0)
def creditOp : Op EB.layout EB.lay EB.lay := .account thisC fun a => a.withBalance (word 0)
def transferred : St EB := { input with ex := (input.ex.apply debitOp).apply creditOp }
def knownEntered (p : Roadmap.Pipeline) :=
  (sub (Γ := Ctx) (L0 EB) (enterInstance (plan := some (points (some 1))) (glob p) 19 thisC user (word 0) data false "C" 1 (1,1,input.heap))).run (caller,transferred)
def knownRawState : St EB := { endState [priorEvent,callEvent] 1 with
  ex := ((input.ex.apply debitOp).apply creditOp).undoN 2 }
theorem transfer_exact : input.ex.transfer user thisC (word 0) = some transferred.ex := by rfl
theorem transferred_entered_raw (p : Roadmap.Pipeline) : knownEntered p = (.ok (.revert [],.nil),(caller,knownRawState)) := by
  cases p <;> rfl
theorem transferred_entered_complete (p : Roadmap.Pipeline) : knownEntered p = (.ok (.revert [],.nil),(caller,endState [priorEvent,callEvent] 1)) := by
  rw [transferred_entered_raw]
  simp only [knownRawState, ExecState.undoN, ExecState.undo_apply, endState]
theorem registered_receiver (p : Roadmap.Pipeline) : (instanceAt (Γ := Ctx) (glob p) thisC).run (caller,input) =
    (.ok (some "C"),(caller,input)) := by rfl
theorem request_not_catchable (p : Roadmap.Pipeline) : (runWith (glob p) requestPlan requestInput).1 ≠ .ok (.revert [],.nil) := by
  simp only [ne_eq,request_propagates,reduceCtorEq,not_false_eq_true]
theorem ancestor_not_child_owner (p : Roadmap.Pipeline) : (runWith (glob p) ancestorPlan ancestorInput).2.2.resource.pending.map (fun owner => owner.isFrame 1) = some false := by
  rw [ancestor_propagates]
  rfl
theorem caller_heap_alias (p : Roadmap.Pipeline) : (heapBytes 0 : EM EB Ctx Roadmap.Bytes).run (run p (some 1)).2 =
    (.ok [0xDE,0xAD],(caller,endState [priorEvent,callEvent] 1)) := by
  rw [first_event_cut]
  rfl
def failureBytes : Except Halt (Roadmap.Outcome × Locals EB.layout []) → Option Roadmap.Bytes
  | .ok (.revert data,_) => some data
  | _ => none
theorem panic_data (p : Roadmap.Pipeline) : failureBytes (runWith (panicGlob p) (points none) input (selOf "cb()")).1 = some panicBytes := by
  rw [panic_full_bytes]
  rfl
theorem wrong_panic_payload_rejected (p : Roadmap.Pipeline) : failureBytes (runWith (panicGlob p) (points none) input (selOf "cb()")).1 ≠
    some ([0x4E,0x48,0x7B,0x71] ++ List.replicate 31 0 ++ [0x11]) := by
  rw [panic_data]
  decide


def nestedPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame i := if i = 1 then some 0 else none
def nestedGlob (p : Roadmap.Pipeline) : Glob EB := { GB reenterOnce with pipeline := p }
def nestedEvents : List Roadmap.Event := [priorEvent,callEvent,
  .reenter thisC ext (word 0) (selOf "cb()") false,
  .reentered (.revert []),.answer (.success []) none]
def nestedRaw : St EB := { endState nestedEvents 2 with ex := (input.ex.apply creditOp).undoN 1 }
theorem nested_raw (p : Roadmap.Pipeline) : runWith (nestedGlob p) nestedPlan input =
    (.ok (.success [],.nil),(caller,nestedRaw)) := by
  cases p <;> rfl
theorem nested_complete (p : Roadmap.Pipeline) : runWith (nestedGlob p) nestedPlan input =
    (.ok (.success [],.nil),(caller,endState nestedEvents 2)) := by
  rw [nested_raw]
  simp only [nestedRaw,ExecState.undoN,ExecState.undo_apply,endState]

/- BEGIN GENERATED RUNTIME PINS -/
/-- info: 'Solidity.Source.FailureExecution.preflight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.preflight
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.zero_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.zero_cut
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.first_event_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.first_event_cut
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.second_event_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.second_event_cut
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.uncut_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.uncut_success
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.zero_horizon
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.entered_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.entered_timeout
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.bodyless_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.bodyless_refusal
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.panic_full_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.panic_full_bytes
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.request_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.request_propagates
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.ancestor_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.ancestor_propagates
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.static_event_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.static_event_cut
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.wrong_frame_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.wrong_frame_stuck
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.transfer_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.transfer_exact
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.transferred_entered_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.transferred_entered_raw
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.transferred_entered_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.transferred_entered_complete
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.registered_receiver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.registered_receiver
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.request_not_catchable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.request_not_catchable
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.ancestor_not_child_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.ancestor_not_child_owner
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.caller_heap_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.caller_heap_alias
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.panic_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.panic_data
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.wrong_panic_payload_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.wrong_panic_payload_rejected
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.nested_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.nested_raw
/-- info: 'Solidity.Source.FailureExecution.RuntimeControls.nested_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.RuntimeControls.nested_complete
/- END GENERATED RUNTIME PINS -/

end Solidity.Source.FailureExecution.RuntimeControls
