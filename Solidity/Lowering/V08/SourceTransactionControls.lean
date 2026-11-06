import Solidity.Lowering.V08.SourceDeploymentControls

/-! Actual transaction-end semantics over published g/poke bodies. No new source
call/callback lowering or ABI decoder: the already-published program is consumed.
Full Source machines retain arbitrary old bytes/events/logs; only a completed
runTx reaches its end/reset/event step. toyFixed is not a real-selector pin. -/
namespace Solidity.Lowering.V08.SourceTransactionControls
open Solidity Source
open Source.SemanticsExamples

def v1 : Source.Val EB.layout uint := .int 1 (by decide +kernel)
def v2 : Source.Val EB.layout uint := .int 2 (by decide +kernel)
def v5 : Source.Val EB.layout uint := .int 5 (by decide +kernel)
def v7 : Source.Val EB.layout uint := .int 7 (by decide +kernel)
def v9 : Source.Val EB.layout uint := .int 9 (by decide +kernel)
def initial (bytes : Roadmap.Bytes) : Source.St EB :=
  {sB with
    ex:=sB.ex.run [
      .account thisC (fun a => {a with balance:=word 7}),
      .account user (fun a => {a with balance:=word 93,nonce:=3}),
      .transient user (fun t => t.write dT.path v9)]
    heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1
    events:=[.call user (word 5) bytes false]
    logs:=[(thisC,bytes),(user,[0xab,0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def global (p : Roadmap.Pipeline) : Source.Glob EB := {GB answerOnly with pipeline:=p}
def request (input : Roadmap.Bytes) : Roadmap.Request := ⟨user,thisC,word 0,word 12345,input⟩
def creditOp : Source.Op EB.layout EB.lay EB.lay :=
  .account thisC (fun a => a.withBalance (word 7))
def xOp (v : Source.Val EB.layout uint) : Source.Op EB.layout EB.lay EB.lay :=
  .account thisC (fun a => {a with storage:=a.storage.write dX.path v})
def tOp (v : Source.Val EB.layout uint) : Source.Op EB.layout EB.lay EB.lay :=
  .transient thisC (fun t => t.write dT.path v)
def credited (bytes : Roadmap.Bytes) : Source.St EB :=
  {initial bytes with ex:=(initial bytes).ex.apply creditOp}
def success (bytes : Roadmap.Bytes) : Source.St EB :=
  {initial bytes with
    ex:=((initial bytes).ex.run [creditOp,xOp v5,tOp v7]).endTx
    heap:=Source.Heap.empty
    events:=(initial bytes).events ++ [.tx user thisC (word 0) (word 12345) (selOf "g()")
      (.success (wordBytes (toWord 12)))]}
def reverted (bytes : Roadmap.Bytes) : Source.St EB :=
  {initial bytes with
    ex:=((initial bytes).ex.run [creditOp,xOp v1,tOp v2]).undoN 3 |>.endTx
    heap:=Source.Heap.empty
    events:=(initial bytes).events ++ [.tx user thisC (word 0) (word 12345) (selOf "poke()") (.revert [])]}
def timed (bytes : Roadmap.Bytes) : Source.St EB := {credited bytes with heap:=Source.Heap.empty}

theorem success_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) (extra+20) (request (selOf "g()"))).run (Source.L0 EB,initial bytes) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,success bytes)) := by cases p <;> rfl

theorem revert_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) (extra+20) (request (selOf "poke()"))).run (Source.L0 EB,initial bytes) =
      (.ok (.revert []),(Source.L0 EB,reverted bytes)) := by cases p <;> rfl

theorem timeout_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) 0 (request (selOf "g()"))).run (Source.L0 EB,initial bytes) =
      (.error .timeout,(Source.L0 EB,timed bytes)) := by cases p <;> rfl

theorem revert_world (bytes : Roadmap.Bytes) : (reverted bytes).ex.world = (initial bytes).ex.world := by
  have undo := Source.ExecState.undoN_run (initial bytes).ex [creditOp,xOp v1,tOp v2]
  exact congrArg (fun x => x.world) undo

theorem success_vector (bytes : Roadmap.Bytes) :
    ((success bytes).ex.world.accounts user).balance = 93 ∧
    ((success bytes).ex.world.accounts thisC).balance = 7 ∧
    readX (success bytes) = some 5 ∧ readT (success bytes) = some 0 ∧
    ((success bytes).ex.transient.cells user).read dT.path = some (show Source.Val EB.layout uint from .int 0 (by decide +kernel)) ∧
    (success bytes).ex.journal = [] ∧ (success bytes).heap.next = 0 ∧
    (success bytes).logs = (initial bytes).logs ∧
    (success bytes).fnLocals = (initial bytes).fnLocals := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem timeout_vector (bytes : Roadmap.Bytes) :
    readX (timed bytes) = some 3 ∧ readT (timed bytes) = some 4 ∧
    ((timed bytes).ex.transient.cells user).read dT.path = some v9 ∧
    (timed bytes).ex.journal.length = 4 ∧ (timed bytes).heap.next = 0 ∧
    (timed bytes).events = (initial bytes).events ∧ (timed bytes).logs = (initial bytes).logs ∧
    (timed bytes).fnLocals = (initial bytes).fnLocals := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_timeout_end (bytes : Roadmap.Bytes) : (timed bytes).ex.journal ≠ [] := by
  intro same
  have lengths := congrArg List.length same
  change 4 = 0 at lengths
  cases lengths

theorem wrong_success_return : wordBytes (toWord 12) ≠ wordBytes (toWord 13) := by decide +kernel

theorem revert_vector (bytes : Roadmap.Bytes) :
    (reverted bytes).ex.world = (initial bytes).ex.world ∧
    readT (reverted bytes) = some 0 ∧
    ((reverted bytes).ex.transient.cells user).read dT.path =
      some (show Source.Val EB.layout uint from .int 0 (by decide +kernel)) ∧
    (reverted bytes).ex.journal = [] ∧ (reverted bytes).heap.next = 0 ∧
    (reverted bytes).logs = (initial bytes).logs ∧
    (reverted bytes).fnLocals = (initial bytes).fnLocals :=
  ⟨revert_world bytes,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem payload_clients (p : Roadmap.Pipeline) :
    (Source.runTx (global p) 20 (request (selOf "g()"))).run (Source.L0 EB,initial []) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,success [])) ∧
    (Source.runTx (global p) 20 (request (selOf "poke()"))).run (Source.L0 EB,initial [0,255,128]) =
      (.ok (.revert []),(Source.L0 EB,reverted [0,255,128])) ∧
    (Source.runTx (global p) 0 (request (selOf "g()"))).run
      (Source.L0 EB,initial (List.replicate 33 0x81)) =
      (.error .timeout,(Source.L0 EB,timed (List.replicate 33 0x81))) :=
  ⟨success_actual p 0 [],revert_actual p 0 [0,255,128],timeout_actual p (List.replicate 33 0x81)⟩

/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.success_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_actual
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.revert_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms revert_actual
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.timeout_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_actual
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.revert_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms revert_world
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.success_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_vector
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.timeout_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_vector
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.wrong_timeout_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_timeout_end
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.wrong_success_return' does not depend on any axioms -/
#guard_msgs in
#print axioms wrong_success_return
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.revert_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms revert_vector
/-- info: 'Solidity.Lowering.V08.SourceTransactionControls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransactionControls
