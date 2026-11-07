import Solidity.Lowering.V08.SourceDeploymentControls
import Solidity.Lowering.V08.Controls

/-! Two independent actual executions, related only by the stated candidate
observations. The Source program supplies a typed body, not a canonical parser/
compiler certificate, even though its literal assignment matches the supplied
typed body. Source.deploy's credit is not a sender-funded transaction;
the intrinsic run independently performs its actual funded entry. -/
namespace Solidity.Lowering.V08.SourcePayableDeploymentControls
open Solidity Source

def savedSyntax : Syn (.part false) :=
  .stateVar (.elem .bool) none none none false "saved" .none
def savedWriteSyntax : Syn (.item .body) :=
  .stmtItem (.simpleStmt (.exprStmt (.assign .assign (.ident "saved") (.lit (.bool true)))))
def sourceUnit : Syn .unit :=
  .unit (.cons (.contract false "Pay" .none .nil
    (.cons savedSyntax (.cons (.constructor .nil .nil true none (.block (.cons savedWriteSyntax .nil))) .nil))) .nil)
def E : Source.Env := sourceUnit.env
def savedDecl : Source.Decl := ⟨.stateVar,"saved",some "Pay",false,savedSyntax⟩
theorem saved_type : savedDecl.varTy E = some .bool := rfl
def sourceBody : Source.RBody E :=
  ⟨[],[],false,[],[],.stmt (.expr (.assign (.state savedDecl saved_type rfl) (.bool true))) .nil,[]⟩
def program : Source.Program E :=
  {body:=fun _ => none, consts:=fun _ => none, inits:=fun _ => [],
    ctor:=fun c => if c="Pay" then some sourceBody else none,
    ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=["Pay"]}
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => ⟨93,by decide +kernel⟩,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def sender : Roadmap.Address := ⟨1,by decide +kernel⟩
def self : Roadmap.Address := ⟨2,by decide +kernel⟩
def word (n : Nat) (h : n < 2^256 := by decide +kernel) : Roadmap.Word := ⟨n,h⟩
def populated : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account sender (fun a => {a with balance:=word 93,nonce:=3}),
      .account self (fun a => {a with balance:=word 5})]
    heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0,255,128]⟩).1
    events:=[.call sender (word 5) [0,255] false]
    logs:=[(self,[0xab,0,255]),(sender,[9])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def placed : Source.St E :=
  {populated with ex:=populated.ex.apply (.account self (fun _ =>
    {balance:=word 12,nonce:=1,code:=none,storage:=Source.Storage.empty}))}
def written : Source.St E :=
  {placed with ex:=placed.ex.apply (.account self (fun a =>
    {a with storage:=a.storage.write savedDecl.path (.bool true)}))}
def installed : Source.St E :=
  {written with
    ex:=written.ex.apply (.account self (fun a => {a with code:=some 0}))
    heap:=Source.Heap.empty}

theorem payable_metadata : E.ctorPayable "Pay" = true := rfl

theorem source_construct (p : Roadmap.Pipeline) (extra : Nat) :
    (Source.construct (global p)
      {this:=self,sender,value:=word 7,static:=false,contract:="Pay"}
      (extra+10) "Pay" (Source.L0 E)).run (Source.L0 E,placed) =
      (.ok (),(Source.L0 E,written)) := by cases p <;> rfl

theorem source_deployment (p : Roadmap.Pipeline) (extra : Nat) :
    (Source.deploy (global p) (extra+10) "Pay" self sender (word 7) []).run
      (Source.L0 E,populated) = (.ok (.success []),(Source.L0 E,installed)) := by
  cases p <;> rfl

theorem source_complete_vector :
    (installed.ex.world.accounts sender).balance = 93 ∧
    (installed.ex.world.accounts self).balance = 12 ∧
    (installed.ex.world.accounts self).nonce = 1 ∧
    (installed.ex.world.accounts self).code = some 0 ∧
    (installed.ex.world.accounts self).storage.read savedDecl.path = some (.bool true) ∧
    installed.ex.journal.length = 5 ∧ installed.ex.transient = populated.ex.transient ∧
    installed.heap = Source.Heap.empty ∧ installed.events = populated.events ∧
    installed.logs = populated.logs ∧ installed.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

-- Existing intrinsic typed contract/program, never a replacement Source state.
def Cell : Contract := contract!{ bool saved; constructor() payable { saved = true; } }
def catalog : Unit → Contract := fun _ => Cell
def targetInitial : ContractWorld.World catalog := ContractWorld.World.empty catalog
  (fun a => if a=Controls.sender then ⟨93,by decide +kernel⟩
    else if a=Controls.self then ⟨5,by decide +kernel⟩ else ⟨0,by decide +kernel⟩)
def targetBody : Prog Cell [] [] := sol[Cell]{ saved = true; }
def targetContext : ContractWorld.Context :=
  {sender:=Controls.sender,mode:=.ordinary ⟨7,by decide +kernel⟩}
def targetRun := targetInitial.create () Controls.self targetBody targetContext

def sourceObservation (p : Roadmap.Pipeline) : Option (Nat × Bool × Bool) := do
  let result := (Source.deploy (global p) 10 "Pay" self sender (word 7) []).run
    (Source.L0 E,populated)
  match result.1 with
  | .ok (.success _) =>
    let .bool saved ← (result.2.2.ex.world.accounts self).storage.read savedDecl.path
    pure ((result.2.2.ex.world.accounts self).balance,saved,
      (result.2.2.ex.world.accounts self).code == some 0)
  | _ => none

def targetObservation : Option (Nat × Bool × Bool) := do
  let (world,handle) ← targetRun.toOption
  let store ← world.storage? handle
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  pure ((world.balance Controls.self).1.toNat,saved,(world.accounts Controls.self).isSome)

/-- Candidate observations only; no equality of Source and intrinsic whole worlds. -/
theorem concrete_observation_transport (p : Roadmap.Pipeline) :
    sourceObservation p = targetObservation := by cases p <;> decide +kernel

theorem source_observation_complete (p : Roadmap.Pipeline) :
    sourceObservation p = some (12,true,true) := by cases p <;> decide +kernel

theorem target_funding :
    (targetRun.toOption.map (fun out => ((out.1.balance Controls.sender).1,
      (out.1.balance Controls.self).1))) = some (86,12) := by decide +kernel

theorem wrong_skipped_payment (p : Roadmap.Pipeline) :
    sourceObservation p ≠ some (5,true,true) := by cases p <;> decide +kernel

theorem wrong_installation (p : Roadmap.Pipeline) :
    sourceObservation p ≠ some (12,true,false) := by cases p <;> decide +kernel

theorem source_other_account (address : Roadmap.Address) (other : address ≠ self) :
    installed.ex.world.accounts address = populated.ex.world.accounts address := by
  simp only [installed,written,placed,Source.ExecState.apply,Source.World.set,dif_neg other]

/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.saved_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms saved_type
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.payable_metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms payable_metadata
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.source_construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_construct
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.source_deployment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_deployment
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.source_complete_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_complete_vector
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.concrete_observation_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms concrete_observation_transport
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.source_observation_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_observation_complete
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.target_funding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_funding
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.wrong_skipped_payment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_skipped_payment
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.wrong_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_installation
/-- info: 'Solidity.Lowering.V08.SourcePayableDeploymentControls.source_other_account' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_other_account
end Solidity.Lowering.V08.SourcePayableDeploymentControls
