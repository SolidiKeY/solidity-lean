import Solidity.Lowering.V08.UnsignedUpdateCallable
import Solidity.Lowering.V08.SignedCallableControls
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited wraparound callable arguments. Full machine equality retains
populated accounts, storage/transients, heap objects, logs/events and fnLocals.
This is argument/caller transport, not general target callee compilation. -/
namespace Solidity.Lowering.V08.UnsignedUpdateCallable.Controls
open Solidity Source
open Solidity.Lowering.V07
abbrev t : Source.IntTy := ⟨false,8,by decide +kernel⟩
def intSyntax : Syn .typeName := .elem (.int false 8 (by decide +kernel))
def params : Syn (.list .param) := .cons (.param intSyntax none (some "n")) .nil
def returns : Syn (.list .param) := .cons (.param intSyntax none (some "answer")) .nil
def fnSyntax : Syn (.part false) :=
  .function (.ident "echoU8") params (some .pub) none .nil false none returns
    (.some (.block (.cons ScalarCallableTransport.returnSyntax .nil)))
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons ScalarCallableTransport.savedSyntax (.cons ScalarCallableTransport.scratchSyntax
    (.cons fnSyntax .nil)))) .nil)
def E : Source.Env := unit.env
def declaration : Source.Decl := ⟨.function,"echoU8",some "C",false,fnSyntax⟩
def program : Source.Program E :=
  {body:=fun _ => some (IntegerCallable.body E t),consts:=fun _ => none,
    inits:=fun _ => [],ctor:=fun _ => none,ctorLocals:=fun _ => [],
    baseArgs:=fun _ => [],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => ScalarCallableTransport.word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=ScalarCallableTransport.word 12345}
abbrev frame := ScalarCallableTransport.frame

def populated (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account frame.sender (fun a => {a with balance:=ScalarCallableTransport.word 93,nonce:=3}),
      .account frame.this (fun a => {a with balance:=ScalarCallableTransport.word 12,nonce:=1,code:=some 0,storage:=a.storage.write ScalarCallableTransport.saved.path (.int 42 (by decide +kernel))}),
      .transient frame.this (fun a => a.write ScalarCallableTransport.scratch.path (.int 9 (by decide +kernel))),
      .transient frame.sender (fun a => a.write ScalarCallableTransport.scratch.path (.int 17 (by decide +kernel)))]
    heap:=((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1.alloc
      ⟨.bytes .memory,.bytes [128,255]⟩).1
    events:=[.call frame.sender (ScalarCallableTransport.word 7) bytes false]
    logs:=[(frame.this,bytes),(frame.sender,[0xab,0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}

theorem inputs (p : Roadmap.Pipeline) : IntegerCallable.Inputs (global p) frame declaration t :=
  ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    rfl,rfl,rfl⟩

abbrev ctx : Source.RCtx := [.int t,.bool]
def locals (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) : Source.Locals E.layout ctx :=
  .cons (.int x hx) (.cons (.bool true) .nil)
def expression (p : Roadmap.Pipeline) (inc pre : Bool) : Source.RExpr E ctx (.int t) :=
  .call declaration (inputs p).signature (arguments 8 (by decide +kernel) inc pre .here)

theorem wrapped_call (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (inc pre : Bool) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) :
    (Source.evalE (global p) frame (extra+17) (expression p inc pre)).run
      (locals x hx,populated bytes) =
      (.ok (.val (if pre then Source.intWrap t (UnsignedLocalUpdate.changed inc x) else .int x hx)),
        ((locals x hx).set .here (Source.intWrap t (UnsignedLocalUpdate.changed inc x)),populated bytes)) := by
  exact source_expression 8 (by decide +kernel) (global p) frame declaration (inputs p)
    extra (locals x hx,populated bytes) inc pre .here x hx rfl

theorem postfix_max (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame (extra+17) (expression p true false)).run
      (locals 255 (by decide +kernel),populated bytes) =
      (.ok (.val (.int 255 (by decide +kernel))),
        (locals 0 (by decide +kernel),populated bytes)) := by
  first | exact wrapped_call p extra bytes true false 255 (by decide +kernel) | decide | omega | rfl

theorem prefix_max (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame (extra+17) (expression p true true)).run
      (locals 255 (by decide +kernel),populated bytes) =
      (.ok (.val (.int 0 (by decide +kernel))),
        (locals 0 (by decide +kernel),populated bytes)) := by
  first | exact wrapped_call p extra bytes true true 255 (by decide +kernel) | decide | omega | rfl

theorem decrement_zero (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame (extra+17) (expression p false true)).run
      (locals 0 (by decide +kernel),populated bytes) =
      (.ok (.val (.int 255 (by decide +kernel))),
        (locals 255 (by decide +kernel),populated bytes)) := by
  first | exact wrapped_call p extra bytes false true 0 (by decide +kernel) | decide | omega | rfl

theorem zero_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 0 (expression p true false)).run
      (locals 255 (by decide +kernel),populated bytes) =
      (.error .timeout,(locals 255 (by decide +kernel),populated bytes)) := by rfl

theorem argument_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 1 (expression p true false)).run
      (locals 255 (by decide +kernel),populated bytes) =
      (.error .timeout,(locals 255 (by decide +kernel),populated bytes)) := by rfl

theorem wrong_postfix_return (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame (extra+17) (expression p true false)).run
      (locals 255 (by decide +kernel),populated bytes) ≠
      (.ok (.val (.int 0 (by decide +kernel))),
        (locals 0 (by decide +kernel),populated bytes)) := by
  rw [postfix_max]
  intro bad
  cases bad


/-- Static mode does not refuse ordinary caller-local assignment. -/
theorem static_call (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (mode pre : Bool) :
    (Source.evalE (global p) {frame with static := mode} (extra+17)
      (expression p true pre)).run (locals 255 (by decide +kernel),populated bytes) =
      (.ok (.val (if pre then (.int 0 (by decide +kernel)) else (.int 255 (by decide +kernel)))),
        (locals 0 (by decide +kernel),populated bytes)) := by
  exact source_expression 8 (by decide +kernel) (global p) {frame with static := mode}
    declaration (by exact ⟨(inputs p).member,(inputs p).kind,(inputs p).signature,rfl⟩) extra (locals 255 (by decide +kernel),populated bytes)
    true pre .here 255 (by decide +kernel) rfl

/-- Reading after the actual call sees the updated caller value even when
postfix returned the old value. No callee-local slot escapes its subframe. -/
theorem reached_read (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (do
      let _ ← Source.evalE (global p) frame (extra+17) (expression p true false)
      Source.evalE (global p) frame 1 (.local (.here : Source.Idx ctx (.int t)))).run
        (locals 255 (by decide +kernel),populated bytes) =
      (.ok (.val (.int 0 (by decide +kernel))),
        (locals 0 (by decide +kernel),populated bytes)) := by
  first | rw [Source.Hoare.run_bind,postfix_max]; rfl | decide | omega | rfl

theorem wrong_caller_snapshot (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame (extra+17) (expression p true false)).run
      (locals 255 (by decide +kernel),populated bytes) ≠
      (.ok (.val (.int 255 (by decide +kernel))),
        (locals 255 (by decide +kernel),populated bytes)) := by
  rw [postfix_max]
  intro bad
  have slot := congrArg (fun result => result.2.1.get (.here : Source.Idx ctx (.int t))) bad
  cases slot

def pairLocals : Source.Locals E.layout [.int t,.int t] :=
  .cons (.int 255 (by decide +kernel)) (.cons (.int 7 (by decide +kernel)) .nil)
def pairSlot (k : Bool) : Source.Idx [.int t,.int t] (.int t) :=
  if k then .here else .there .here
abbrev target := WordCastControls.target t 255 7 (by decide +kernel) (by decide +kernel)
theorem initial : IntegerLocalFamily t pairSlot (WordCastControls.ti t) pairLocals target.env := by
  refine ⟨?_,?_⟩
  · intro k; cases k <;> exact integer_related t _ _
  · intro k l; cases k <;> cases l <;> rfl

/-- Inhabits all four clauses of the generic joint transport, with a real
nonempty target heap, unrelated integer slot and preserved memory aliases. -/
def inhabited_transport (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (inc pre : Bool) :=
  transport_context 8 (by decide +kernel) (global p) frame declaration (inputs p) extra
    (pairLocals,populated bytes) target inc pre pairSlot (WordCastControls.ti t)
    initial true 255 (by decide +kernel) rfl

end Solidity.Lowering.V08.UnsignedUpdateCallable.Controls

/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.intSyntax' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.intSyntax
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.params' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.params
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.returns' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.returns
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.fnSyntax' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.fnSyntax
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.unit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.unit
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.E' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.E
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.declaration' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.declaration
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.program
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.global' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.global
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.populated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.populated
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.inputs
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.locals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.locals
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.expression
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrapped_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrapped_call
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.postfix_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.postfix_max
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.prefix_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.prefix_max
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.decrement_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.decrement_zero
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.zero_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.zero_timeout
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.argument_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.argument_timeout
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrong_postfix_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrong_postfix_return
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.static_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.static_call
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.reached_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.reached_read
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrong_caller_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.wrong_caller_snapshot
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.pairLocals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.pairLocals
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.pairSlot' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.pairSlot
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.initial
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.inhabited_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.Controls.inhabited_transport
