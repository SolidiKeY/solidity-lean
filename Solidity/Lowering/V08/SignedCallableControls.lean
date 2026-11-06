import Solidity.Lowering.V08.IntegerCallable

/-! Inhabited signed boundary client of the generic G20 interface. The target
entry specializes its argument as a typed literal; ABI ingress, arbitrary body
lowering, SourceSpec and external-call admission are not established here. -/
namespace Solidity.Lowering.V08.SignedCallableControls
open Solidity Source
open Solidity.Lowering.V07
abbrev t : Source.IntTy := ⟨true,8,by decide +kernel⟩
def intSyntax : Syn .typeName := .elem (.int true 8 (by decide +kernel))
def params : Syn (.list .param) := .cons (.param intSyntax none (some "n")) .nil
def returns : Syn (.list .param) := .cons (.param intSyntax none (some "answer")) .nil
def fnSyntax : Syn (.part false) :=
  .function (.ident "echo8") params (some .pub) none .nil false none returns
    (.some (.block (.cons ScalarCallableTransport.returnSyntax .nil)))
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons ScalarCallableTransport.savedSyntax (.cons ScalarCallableTransport.scratchSyntax
    (.cons fnSyntax .nil)))) .nil)
def E : Source.Env := unit.env
def declaration : Source.Decl := ⟨.function,"echo8",some "C",false,fnSyntax⟩
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

def minimum : Source.Val E.layout (.int t) := .int (-128) (by decide +kernel)

theorem minimum_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.callInternal (global p) frame (extra+12) declaration
      (.cons minimum .nil) [.int t]).run (Source.L0 E,populated bytes) =
      (.ok (.val minimum),(Source.L0 E,populated bytes)) :=
  IntegerCallable.source_call _ _ _ _ (inputs p) extra _ (-128) (by decide +kernel)

theorem minimum_transport (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (C : Contract) (target : State C []) :
    (Source.callInternal (global p) frame (extra+12) declaration (.cons minimum .nil) [.int t]).run
      (Source.L0 E,populated bytes) = (.ok (.val minimum),(Source.L0 E,populated bytes)) ∧
    (IntegerCallable.entry C declaration t (-128) (by decide +kernel)).body.run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t (-128) (by decide +kernel)),
        List.prefix_refl _⟩ ∧
    IntValueRel t minimum (integerValue t (-128) (by decide +kernel)) :=
  ⟨minimum_client p extra bytes,IntegerCallable.target_body C target declaration t (-128) (by decide +kernel),
    integer_related t (-128) (by decide +kernel)⟩

theorem wrong_signed_result :
    PrimTy.num? (integerValue t (-128) (by decide +kernel)) ≠ some 128 := by
  rw [integer_observe]
  decide +kernel

/-- info: 'Solidity.Lowering.V08.SignedCallableControls.inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.SignedCallableControls.inputs

/-- info: 'Solidity.Lowering.V08.SignedCallableControls.minimum_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.SignedCallableControls.minimum_client

/-- info: 'Solidity.Lowering.V08.SignedCallableControls.minimum_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.SignedCallableControls.minimum_transport

/-- info: 'Solidity.Lowering.V08.SignedCallableControls.wrong_signed_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.SignedCallableControls.wrong_signed_result
end Solidity.Lowering.V08.SignedCallableControls
