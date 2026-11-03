import Solidity.Source.SemanticsExamples

/-! Actual published Source.deploy over its published inherited constructor
program. Operation lists below describe the generated journal, not an evaluator.
No canonical source/intrinsic layout, admission, body or bytecode claim is made. -/
namespace Solidity.Lowering.V08.SourceDeploymentControls
open Solidity Source
open Source.SemanticsExamples

abbrev E := EAB

def v1 : Source.Val E.layout uint := .int 1 (by decide +kernel)
def v2 : Source.Val E.layout uint := .int 2 (by decide +kernel)
def v77 : Source.Val E.layout uint := .int 77 (by decide +kernel)

def populated : Source.St E :=
  { Source.St.init E with
    ex := (Source.St.init E).ex.run [
      .account user (fun a => { a with balance := word 93, nonce := 3, code := some 0, storage := a.storage.write dA.path v77 }),
      .account thisC (fun a => { a with balance := word 7 })]
    heap := ((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0,255]⟩).1.alloc
      ⟨.bytes .memory,.bytes [128,0,255]⟩).1
    events := [.call user (word 5) [1,0] false]
    logs := [(thisC,[0xab,0,255]),(user,[9])]
    fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩ }

def placement : Source.Op E.layout E.lay E.lay :=
  .account thisC (fun _ => {balance:=word 7,nonce:=1,code:=none,storage:=Source.Storage.empty})
def prepared : Source.St E := {populated with ex:=populated.ex.apply placement}
def writeA (v : Source.Val E.layout uint) : Source.Op E.layout E.lay E.lay :=
  .account thisC (fun a => {a with storage:=a.storage.write dA.path v})
def writeB (v : Source.Val E.layout uint) : Source.Op E.layout E.lay E.lay :=
  .account thisC (fun a => {a with storage:=a.storage.write dB.path v})
def ctorOps : Roadmap.Pipeline → List (Source.Op E.layout E.lay E.lay)
  | .legacy => [writeA v1,writeB v1,writeA v2]
  | .viaIR => [writeA v1,writeA v2,writeB v2]
def built (p : Roadmap.Pipeline) : Source.St E :=
  {prepared with ex:=prepared.ex.run (ctorOps p)}
def installed (p : Roadmap.Pipeline) : Source.St E :=
  {built p with
    ex:=(built p).ex.apply (.account thisC (fun a => {a with code:=some 1}))
    heap:=Source.Heap.empty}
def nonpayablePlacement : Source.Op E.layout E.lay E.lay :=
  .account thisC (fun _ => {balance:=word 12,nonce:=1,code:=none,storage:=Source.Storage.empty})
def refused : Source.St E :=
  {populated with ex:=(populated.ex.apply nonpayablePlacement).undo,heap:=Source.Heap.empty}
def timed : Source.St E := {prepared with heap:=Source.Heap.empty}

/-- Existing initializers and nonempty base constructor at the reached placement. -/
theorem construct_actual (p : Roadmap.Pipeline) (extra : Nat := 0) :
    (Source.construct (GAB p)
      {this:=thisC,sender:=user,value:=word 0,static:=false,contract:="B"}
      (extra+20) "B" (Source.L0 E)).run (Source.L0 E,prepared) =
      (.ok (),(Source.L0 E,built p)) := by
  cases p <;> rfl

/-- Exact whole-machine result, including code installation and clearing both old objects. -/
theorem deployment_actual (p : Roadmap.Pipeline) (extra : Nat := 0) :
    (Source.deploy (GAB p) (extra+20) "B" thisC user (word 0) []).run (Source.L0 E,populated) =
      (.ok (.success []),(Source.L0 E,installed p)) := by
  cases p <;> rfl

theorem nonpayable_actual (p : Roadmap.Pipeline) (horizon : Nat) :
    (Source.deploy (GAB p) horizon "B" thisC user (word 5) []).run (Source.L0 E,populated) =
      (.ok (.revert []),(Source.L0 E,refused)) := by
  cases p <;> rfl

theorem timeout_actual (p : Roadmap.Pipeline) :
    (Source.deploy (GAB p) 0 "B" thisC user (word 0) []).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,timed)) := by
  cases p <;> rfl

theorem refused_restores_execution : refused.ex = populated.ex :=
  Source.ExecState.undo_apply populated.ex nonpayablePlacement

theorem installed_vector (p : Roadmap.Pipeline) :
    ((installed p).ex.world.accounts user).balance.val = 93 ∧
    ((installed p).ex.world.accounts thisC).balance.val = 7 ∧
    ((installed p).ex.world.accounts thisC).nonce = 1 ∧
    ((installed p).ex.world.accounts thisC).code = some 1 ∧
    ((installed p).ex.world.accounts thisC).storage.read dA.path = some v2 ∧
    ((installed p).ex.world.accounts thisC).storage.read dB.path =
      some (match p with | .legacy => v1 | .viaIR => v2) ∧
    ((installed p).ex.world.accounts user).nonce = 3 ∧
    ((installed p).ex.world.accounts user).code = some 0 ∧
    ((installed p).ex.world.accounts user).storage.read dA.path = some v77 ∧
    (installed p).ex.journal.length = 7 ∧
    (installed p).ex.transient = populated.ex.transient ∧
    (installed p).heap = Source.Heap.empty ∧
    (installed p).events = populated.events ∧ (installed p).logs = populated.logs ∧
    (installed p).fnLocals = populated.fnLocals := by
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem old_objects_and_timeout :
    populated.heap.next = 2 ∧
    populated.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    populated.heap.get 1 = some ⟨.bytes .memory,.bytes [128,0,255]⟩ ∧
    timed.ex.journal.length = 3 ∧ timed.heap.next = 0 ∧
    (timed.ex.world.accounts thisC).code = none ∧
    (timed.ex.world.accounts thisC).nonce = 1 ∧
    timed.logs = populated.logs ∧ timed.events = populated.events ∧
    timed.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_installed_code (p : Roadmap.Pipeline) :
    ((installed p).ex.world.accounts thisC).code ≠ some 0 := by
  cases p <;> decide +kernel

theorem wrong_timeout_rollback : timed.ex ≠ populated.ex := by
  intro same
  have lengths := congrArg (fun x => x.journal.length) same
  change 3 = 2 at lengths
  cases lengths

theorem wrong_pipeline_order :
    ((installed .legacy).ex.world.accounts thisC).storage.read dB.path ≠
      ((installed .viaIR).ex.world.accounts thisC).storage.read dB.path := by
  intro same
  have values := congrArg (fun (x : Option (Source.Val E.layout uint)) =>
    x.map (fun | .int i _ => i)) same
  change some (1 : Int) = some 2 at values
  cases values

def overflowInput : Source.St E :=
  {populated with ex:=populated.ex.apply (.account thisC (fun a =>
    {a with balance:=word (2^256-1) (by decide +kernel)}))}

/-- Receiver overflow is BEFORE placement, constructor attempt and heap clearing. -/
theorem overflow_actual (p : Roadmap.Pipeline) (horizon : Nat) :
    (Source.deploy (GAB p) horizon "B" thisC user (word 1) []).run
      (Source.L0 E,overflowInput) =
      (.error (.revert []),(Source.L0 E,overflowInput)) := rfl

theorem installed_other_account (p : Roadmap.Pipeline) (address : Roadmap.Address)
    (other : address ≠ thisC) :
    (installed p).ex.world.accounts address = populated.ex.world.accounts address := by
  cases p <;> simp only [installed,built,prepared,placement,ctorOps,writeA,writeB,
    Source.ExecState.run,Source.ExecState.apply,Source.World.set,dif_neg other]

theorem overflow_keeps_objects : overflowInput.heap = populated.heap ∧
    overflowInput.logs = populated.logs ∧ overflowInput.events = populated.events ∧
    overflowInput.fnLocals = populated.fnLocals ∧ overflowInput.ex.journal.length = 3 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.construct_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms construct_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.deployment_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms deployment_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.nonpayable_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nonpayable_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.timeout_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.refused_restores_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms refused_restores_execution
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.installed_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms installed_vector
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.old_objects_and_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_objects_and_timeout
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.wrong_installed_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_installed_code
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.wrong_timeout_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_timeout_rollback
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.wrong_pipeline_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_pipeline_order
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.overflow_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.installed_other_account' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms installed_other_account
/-- info: 'Solidity.Lowering.V08.SourceDeploymentControls.overflow_keeps_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_keeps_objects
end Solidity.Lowering.V08.SourceDeploymentControls
