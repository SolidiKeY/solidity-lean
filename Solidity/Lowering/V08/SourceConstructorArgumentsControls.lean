import Solidity.Lowering.V08.SourcePayableDeploymentControls
import Solidity.Lowering.V08.SourceTransient

/-! Actual nonempty base-argument frames and constructor transient lifetime.
The supplied Program/base-argument map is not a canonical elaboration certificate.
The priority probe tests the published giveArgs branch, not admission of duplicate
Solidity constructor arguments. No ABI decoder or source-call lowering is added. -/
namespace Solidity.Lowering.V08.SourceConstructorArgumentsControls
open Solidity Source

def savedSyntax : Syn (.part false) := .stateVar (.elem .bool) none none none false "saved" .none
def scratchSyntax : Syn (.part false) := .stateVar (.elem .bool) none none none true "scratch" .none
def params : Syn (.list .param) := .cons (.param (.elem .bool) none (some "enabled")) .nil
def unit : Syn .unit :=
  .unit (.cons (.contract false "Base" .none .nil
    (.cons savedSyntax (.cons scratchSyntax (.cons (.constructor params .nil false none (.block .nil)) .nil))))
    (.cons (.contract false "Derived" .none (.cons (.inherit ⟨"Base",[]⟩ .none) .nil)
      (.cons (.constructor params .nil false none (.block .nil)) .nil)) .nil))
def E : Source.Env := unit.env
def savedDecl : Source.Decl := ⟨.stateVar,"saved",some "Base",false,savedSyntax⟩
def scratchDecl : Source.Decl := ⟨.stateVar,"scratch",some "Base",false,scratchSyntax⟩
def sender : Roadmap.Address := ⟨1,by decide +kernel⟩
def self : Roadmap.Address := ⟨2,by decide +kernel⟩
def word (n : Nat) (h : n < 2^256 := by decide +kernel) : Roadmap.Word := ⟨n,h⟩
def body : Source.RBody E :=
  ⟨[.bool],[],false,[.bool],[.bool],
    .stmt (.expr (.assign (.state scratchDecl rfl rfl) (.local .here)))
      (.stmt (.expr (.assign (.state savedDecl rfl rfl) (.state scratchDecl rfl))) .nil),[]⟩
def derivedBody : Source.RBody E := ⟨[.bool],[],false,[.bool],[.bool],.nil,[]⟩
def argument : Source.RBaseArg E [.bool] := ⟨"Base",[.bool],.cons (.local .here) rfl .nil⟩
def program : Source.Program E :=
  {body:=fun _ => none,consts:=fun _ => none,inits:=fun _ => [],
    ctor:=fun c => if c="Base" then some body else if c="Derived" then some derivedBody else none,
    ctorLocals:=fun _ => [.bool],baseArgs:=fun c => if c="Derived" then [argument] else [],
    contracts:=["Base","Derived"]}
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=word 0}
def frame : Source.Fr := {this:=self,sender,value:=word 0,static:=false,contract:="Derived"}
def locals (b : Bool) : Source.Locals E.layout [.bool] := .cons (.bool b) .nil

def populated (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account sender (fun a => {a with balance:=word 93,nonce:=3}),
      .account self (fun a => {a with balance:=word 7}),
      .transient sender (fun t => t.write scratchDecl.path (.bool true))]
    heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1
    events:=[.call sender (word 5) bytes false]
    logs:=[(self,bytes),(sender,[0xab,0,255])]
    fnLocals:=⟨[.bool],locals true⟩}
def after (bytes : Roadmap.Bytes) (b : Bool) : Source.St E :=
  {populated bytes with ex:=((populated bytes).ex.apply (.transient self (fun t => t.write scratchDecl.path (.bool b)))).apply (.account self (fun a => {a with storage:=a.storage.write savedDecl.path (.bool b)}))}

def collected (p : Roadmap.Pipeline) (b : Bool) : Source.CtorLocals (global p) :=
  [⟨"Derived",locals b⟩,⟨"Base",locals b⟩]

theorem collect_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (b : Bool) :
    (Source.collectArgs (global p) frame (extra+12) ["Derived","Base"] [⟨"Derived",locals b⟩]).run
      (Source.L0 E,populated bytes) = (.ok (collected p b),(Source.L0 E,populated bytes)) := rfl

theorem construct_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (b : Bool) :
    (Source.construct (global p) frame (extra+12) "Derived" (locals b)).run
      (Source.L0 E,populated bytes) = (.ok (),(Source.L0 E,after bytes b)) := by cases p <;> rfl

theorem static_refusal (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (b : Bool) :
    (Source.construct (global p) {frame with static:=true} 12 "Derived" (locals b)).run
      (Source.L0 E,populated bytes) = (.error (.revert []),(Source.L0 E,populated bytes)) := by
  cases p <;> rfl

theorem missing_base_arguments (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.runCtorBody (global p) frame 12 [] "Base").run (Source.L0 E,populated bytes) =
      (.error (.revert []),(Source.L0 E,populated bytes)) := rfl

theorem zero_horizon (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (b : Bool) :
    (Source.construct (global p) frame 0 "Derived" (locals b)).run (Source.L0 E,populated bytes) =
      (.error .timeout,(Source.L0 E,populated bytes)) := by cases p <;> rfl

def effectArgs : Source.RConvArgs E [.bool] [.bool] :=
  .cons (.assign (.state savedDecl rfl rfl) (.bool false)) rfl .nil
def effectArg : Source.RBaseArg E [.bool] := ⟨"Base",[.bool],effectArgs⟩
def dirty (bytes : Roadmap.Bytes) : Source.St E :=
  {after bytes true with ex:=(after bytes true).ex.apply (.account self (fun a => {a with storage:=a.storage.write savedDecl.path (.bool false)}))}

theorem argument_effect_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalConvArgs (global p) frame 4 effectArgs).run (locals true,after bytes true) =
      (.ok (.cons (.bool false) .nil),(locals true,dirty bytes)) := by cases p <;> rfl

theorem already_given_priority (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.giveArgs (global p) frame 0 "Derived" (locals true) [effectArg] (collected p true)).run
      (Source.L0 E,after bytes true) = (.ok (collected p true),(Source.L0 E,after bytes true)) := rfl

theorem complete_vector (bytes : Roadmap.Bytes) (b : Bool) :
    ((after bytes b).ex.world.accounts sender).balance.val = 93 ∧
    ((after bytes b).ex.world.accounts self).balance.val = 7 ∧
    ((after bytes b).ex.world.accounts sender).nonce = 3 ∧
    ((after bytes b).ex.world.accounts self).storage.read savedDecl.path = some (.bool b) ∧
    ((after bytes b).ex.transient.cells self).read scratchDecl.path = some (.bool b) ∧
    ((after bytes b).ex.transient.cells sender).read scratchDecl.path = some (.bool true) ∧
    (after bytes b).ex.journal.length = 5 ∧ (after bytes b).heap = (populated bytes).heap ∧
    (after bytes b).logs = (populated bytes).logs ∧ (after bytes b).events = (populated bytes).events ∧
    (after bytes b).fnLocals = (populated bytes).fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem explicit_end (bytes : Roadmap.Bytes) (b : Bool) :
    let finished := SourceTransient.endExecution (after bytes b)
    finished.ex.world = (after bytes b).ex.world ∧
    (finished.ex.transient.cells self).read scratchDecl.path = some (.bool false) ∧
    (finished.ex.transient.cells sender).read scratchDecl.path = some (.bool false) ∧
    finished.ex.journal = [] ∧ finished.heap = (populated bytes).heap ∧
    finished.logs = (populated bytes).logs ∧ finished.events = (populated bytes).events ∧
    finished.fnLocals = (populated bytes).fnLocals := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_priority_effect (bytes : Roadmap.Bytes) : (after bytes true).ex ≠ (dirty bytes).ex := by
  intro same
  have n := congrArg (fun x => x.journal.length) same
  change 5 = 6 at n
  cases n

theorem payload_clients (p : Roadmap.Pipeline) :
    (Source.construct (global p) frame 12 "Derived" (locals true)).run (Source.L0 E,populated []) =
      (.ok (),(Source.L0 E,after [] true)) ∧
    (Source.construct (global p) frame 12 "Derived" (locals true)).run (Source.L0 E,populated [0,255,128]) =
      (.ok (),(Source.L0 E,after [0,255,128] true)) ∧
    (Source.construct (global p) frame 12 "Derived" (locals false)).run
      (Source.L0 E,populated (List.replicate 33 0x81)) =
      (.ok (),(Source.L0 E,after (List.replicate 33 0x81) false)) :=
  ⟨construct_actual p 0 [] true,construct_actual p 0 [0,255,128] true,
    construct_actual p 0 (List.replicate 33 0x81) false⟩

/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.collect_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms collect_actual
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.construct_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms construct_actual
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.static_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms static_refusal
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.missing_base_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms missing_base_arguments
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_horizon
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.argument_effect_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms argument_effect_actual
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.already_given_priority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms already_given_priority
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.complete_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_vector
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.explicit_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms explicit_end
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.wrong_priority_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_priority_effect
/-- info: 'Solidity.Lowering.V08.SourceConstructorArgumentsControls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms payload_clients
end Solidity.Lowering.V08.SourceConstructorArgumentsControls
