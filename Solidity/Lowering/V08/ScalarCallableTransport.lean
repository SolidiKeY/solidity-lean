import Solidity.Lowering.V08.ConstructorScalarTransport
import Solidity.Lowering.V08.SourceCallable

/-! Actual scalar argument/result callable-frame component. Source evalE and
callInternal are independent of Entry.body/result. The target body specializes
one transported argument as a typed literal. This is neither external-call
lowering nor a canonical whole-body/ABI/admission certificate. -/
namespace Solidity.Lowering.V08.ScalarCallableTransport
open Solidity Source
open Solidity.Lowering.V07
abbrev uint : Source.STy := .int Source.IntTy.u256
abbrev range (n : Int) := Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi

def savedSyntax : Syn (.part false) := .stateVar Source.Examples.u256 none none none false "saved" .none
def scratchSyntax : Syn (.part false) := .stateVar Source.Examples.u256 none none none true "scratch" .none
def ps : Syn (.list .param) := .cons (.param Source.Examples.u256 none (some "n")) .nil
def rs : Syn (.list .param) := .cons (.param Source.Examples.u256 none (some "answer")) .nil
def returnSyntax : Syn (.item .body) := .stmtItem (.returnStmt (.some (.ident "n")))
def fnSyntax : Syn (.part false) :=
  .function (.ident "echo") ps (some .pub) none .nil false none rs
    (.some (.block (.cons returnSyntax .nil)))

def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons savedSyntax (.cons scratchSyntax (.cons fnSyntax .nil)))) .nil)
def E : Source.Env := unit.env
def saved : Source.Decl := ⟨.stateVar,"saved",some "C",false,savedSyntax⟩
def scratch : Source.Decl := ⟨.stateVar,"scratch",some "C",false,scratchSyntax⟩
def declaration : Source.Decl := ⟨.function,"echo",some "C",false,fnSyntax⟩
def body : Source.RBody E :=
  ⟨[uint],[uint],false,[uint,uint],[uint,uint],
    .stmt (.retVal rfl (.local (.there .here)) rfl) .nil,[]⟩
def program : Source.Program E :=
  {body:=fun d => if d.name="echo" then some body else none,
    consts:=fun _ => none,inits:=fun _ => [],ctor:=fun _ => none,
    ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=["C"]}
def word (n : Nat) (h : n<2^256 := by decide +kernel) : Roadmap.Word := ⟨n,h⟩
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=word 12345}
def frame : Source.Fr :=
  {this:=ConstructorScalarTransport.frame.this,sender:=ConstructorScalarTransport.frame.sender,
    value:=word 7,static:=false,contract:="C",checked:=false}
def value (n : Int) (h : range n) : Source.Val E.layout uint := .int n h
def arguments (n : Int) (h : range n) : Source.Vals E.layout [uint] := .cons (value n h) .nil
def locals (n : Int) (h : range n) : Source.Locals E.layout [uint] := .cons (value n h) .nil

def populated (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account frame.sender (fun a => {a with balance:=word 93,nonce:=3}),
      .account frame.this (fun a => {a with balance:=word 12,nonce:=1,code:=some 0,storage:=a.storage.write saved.path (.int 42 (by decide +kernel))}),
      .transient frame.this (fun t => t.write scratch.path (.int 9 (by decide +kernel))),
      .transient frame.sender (fun t => t.write scratch.path (.int 17 (by decide +kernel)))]
    heap:=((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1.alloc
      ⟨.bytes .memory,.bytes [128,255]⟩).1
    events:=[.call frame.sender (word 7) bytes false]
    logs:=[(frame.this,bytes),(frame.sender,[0xab,0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}

structure BodySelection (g : Source.Glob E) (f : Source.Fr) : Prop where
  selected : g.prog.body (g.dispatchFn f.contract declaration) = some body

theorem declaration_member : declaration ∈ E.decls :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem body_selection (p : Roadmap.Pipeline) : BodySelection (global p) frame := ⟨rfl⟩

/-- Actual source call from a selected body at ANY entire Source machine and
frame. Only input body selection is required, never its desired execution. -/
theorem selected_internal (g : Source.Glob E) (f : Source.Fr) (inputs : BodySelection g f)
    (extra : Nat) (state : Source.St E) (n : Int) (h : range n) :
    (Source.callInternal g f (extra+12) declaration (arguments n h) [uint]).run
      (Source.L0 E,state) = (.ok (.val (value n h)),(Source.L0 E,state)) :=
  SourceCallable.complete g f (extra+11) declaration (arguments n h) body inputs.selected
    (.cons (.int 0 (by decide +kernel)) .nil) rfl
    (.cons (value n h) (.cons (value n h) .nil)) (.cons (.val (value n h)) .nil)
    state state state (by rfl) (by rfl) rfl

theorem signature : declaration.fnSig E = some ([uint],[uint]) := rfl

theorem source_internal (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.callInternal (global p) frame (extra+12) declaration (arguments n h) [uint]).run
      (Source.L0 E,populated bytes) =
      (.ok (.val (value n h)),(Source.L0 E,populated bytes)) := by cases p <;> rfl

def callArgs : Source.RConvArgs E [uint] [uint] := .cons (.local .here) rfl .nil

theorem source_expression (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.evalE (global p) frame (extra+13) (.call declaration signature callArgs)).run
      (locals n h,populated bytes) = (.ok (.val (value n h)),(locals n h,populated bytes)) := by
  cases p <;> rfl

def entry (C : Contract) (n : Int) (h : range n) : ContractWorld.Entry C PrimTy.uint.Denote :=
  {locals:=[.val .uint],
    body:=.cons (.declLocal .uint (.user "argument") (some (.simple (.lit n (integer_range Source.IntTy.u256 n h))))) .nil,
    result:=fun state => (Solidity.Val.simple (.local .here) : Solidity.Val C [.val .uint] .uint).evalT state,
    payable:=false}

theorem target_body (C : Contract) (state : State C []) (n : Int) (h : range n) :
    (entry C n h).body.run state =
      .ok ⟨state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h),List.prefix_refl _⟩ := rfl

theorem target_result (C : Contract) (state : State C []) (n : Int) (h : range n) :
    (entry C n h).result (state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h)) =
      .ok (integerValue Source.IntTy.u256 n h) := rfl

theorem target_drop (C : Contract) (state : State C []) (n : Int) (h : range n) :
    (state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h)).drop (entry C n h).body.ext = state := rfl

theorem nonpayable_metadata (C : Contract) (n : Int) (h : range n) :
    (entry C n h).payable = false := rfl

/-- Source caller locals and entire machine survive; target caller state is
restored after dropping its actual temporary. The scalar relation is V07's. -/
theorem callable_transport (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (C : Contract) (state : State C []) (n : Int) (h : range n) :
    (Source.evalE (global p) frame (extra+13) (.call declaration signature callArgs)).run
      (locals n h,populated bytes) = (.ok (.val (value n h)),(locals n h,populated bytes)) ∧
    (entry C n h).body.run state =
      .ok ⟨state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h),List.prefix_refl _⟩ ∧
    (entry C n h).result (state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h)) =
      .ok (integerValue Source.IntTy.u256 n h) ∧
    IntValueRel Source.IntTy.u256 (value n h) (integerValue Source.IntTy.u256 n h) ∧
    (state.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h)).drop (entry C n h).body.ext = state :=
  ⟨source_expression p extra bytes n h,target_body C state n h,target_result C state n h,
    integer_related _ _ _,target_drop C state n h⟩

theorem zero_internal (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.callInternal (global p) frame 0 declaration (arguments n h) [uint]).run
      (Source.L0 E,populated bytes) = (.error .timeout,(Source.L0 E,populated bytes)) := rfl

theorem missing_body (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.callInternal {global p with prog:={program with body:=fun _ => none}} frame (extra+1)
      declaration (arguments n h) [uint]).run (Source.L0 E,populated bytes) =
      (.error (.stuck "function without a body"),(Source.L0 E,populated bytes)) :=
  SourceCallable.missing_body _ _ extra _ _ _ rfl

theorem wrong_value (state : State ConstructorScalarTransport.Cell []) :
    (entry ConstructorScalarTransport.Cell 7 (by decide +kernel)).result
      (state.push (t:=.val .uint) (integerValue Source.IntTy.u256 8 (by decide +kernel))) ≠
      .ok (integerValue Source.IntTy.u256 7 (by decide +kernel)) := by
  intro same
  have observed := congrArg (fun out => out.toOption.map PrimTy.num?) same
  change some (some (8 : Int)) = some (some 7) at observed
  cases observed

def wrongBody : Source.RBody E := ⟨[uint],[uint],false,[uint],[uint],.nil,[]⟩
def wrongGlobal (p : Roadmap.Pipeline) : Source.Glob E :=
  {global p with prog:={program with body:=fun _ => some wrongBody}}

theorem wrong_frame (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.callInternal (wrongGlobal p) frame (extra+12)
      declaration (arguments n h) [uint]).run (Source.L0 E,populated bytes) =
      (.error (.stuck "call frame"),(Source.L0 E,populated bytes)) := rfl

theorem paid_frame_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    ConstructorScalarTransport.targetInitial.enter (k:=()) Controls.self
      ConstructorScalarTransport.targetContext (Storage.init ConstructorScalarTransport.Cell) true =
      .ok ConstructorScalarTransport.entered ∧
    (Source.evalE (global p) frame (extra+13) (.call declaration signature callArgs)).run
      (locals n h,populated bytes) = (.ok (.val (value n h)),(locals n h,populated bytes)) ∧
    (entry ConstructorScalarTransport.Cell n h).body.run ConstructorScalarTransport.entered =
      .ok ⟨ConstructorScalarTransport.entered.push (t:=.val .uint)
        (integerValue Source.IntTy.u256 n h),List.prefix_refl _⟩ ∧
    (entry ConstructorScalarTransport.Cell n h).result
      (ConstructorScalarTransport.entered.push (t:=.val .uint) (integerValue Source.IntTy.u256 n h)) =
      .ok (integerValue Source.IntTy.u256 n h) :=
  ⟨ConstructorScalarTransport.entry_actual,source_expression p extra bytes n h,
    target_body _ _ n h,target_result _ _ n h⟩

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.declaration_member' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.declaration_member

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.body_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.body_selection

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.selected_internal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.selected_internal

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.signature

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.source_internal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.source_internal

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.source_expression

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.target_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.target_body

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.target_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.target_result

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.target_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.target_drop

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.nonpayable_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.nonpayable_metadata

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.callable_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.callable_transport

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.zero_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.zero_internal

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.missing_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.missing_body

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.wrong_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.wrong_value

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.wrong_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.wrong_frame

/-- info: 'Solidity.Lowering.V08.ScalarCallableTransport.paid_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ScalarCallableTransport.paid_frame_client
end Solidity.Lowering.V08.ScalarCallableTransport
