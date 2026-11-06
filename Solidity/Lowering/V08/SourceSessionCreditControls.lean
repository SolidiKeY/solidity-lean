import Solidity.Lowering.V08.SourceSessionControls

/-! Actual installed-instance environmental credit followed by a reached runTx.
No external funding ledger or source-to-compiled-frame relation is inferred. -/
namespace Solidity.Lowering.V08.SourceSessionCreditControls
open Solidity Source
open Source.SemanticsExamples SourceTransactionControls

def accountCredit : Source.Op EB.layout EB.lay EB.lay :=
  .account thisC (fun a => a.withBalance (word 16))
def credited (bytes : Roadmap.Bytes) : Source.St EB :=
  {success bytes with ex:=(success bytes).ex.apply accountCredit}
def recorded (bytes : Roadmap.Bytes) : Source.St EB :=
  {credited bytes with events:=(success bytes).events ++ [.credit thisC (word 9)]}
def creditAgain : Source.Op EB.layout EB.lay EB.lay :=
  .account thisC (fun a => a.withBalance (word 16))
def next (bytes : Roadmap.Bytes) : Source.St EB :=
  {recorded bytes with
    ex:=((recorded bytes).ex.run [creditAgain,xOp v5,tOp v7]).endTx
    heap:=Source.Heap.empty
    events:=(recorded bytes).events ++ [.tx user thisC (word 0) (word 12345) (selOf "g()")
      (.success (wordBytes (toWord 12)))]}

theorem installed_credit_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    Source.runAt (fun _ => do
      if (← Source.instanceAt (global p) thisC).isSome then Source.credit thisC (word 9))
      (success bytes) 0 = (.ok (),credited bytes) := by cases p <;> rfl

theorem next_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (global p) (extra+20) (request (selOf "g()"))).run
      (Source.L0 EB,recorded bytes) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,next bytes)) := by cases p <;> rfl

theorem complete_vector (bytes : Roadmap.Bytes) :
    ((credited bytes).ex.world.accounts thisC).balance = 16 ∧
    ((credited bytes).ex.world.accounts user).balance = 93 ∧
    (credited bytes).ex.journal.length = 1 ∧
    (credited bytes).heap = (success bytes).heap ∧
    (credited bytes).logs = (success bytes).logs ∧
    (credited bytes).fnLocals = (success bytes).fnLocals ∧
    ((next bytes).ex.world.accounts thisC).balance = 16 ∧
    ((next bytes).ex.world.accounts user).balance = 93 ∧
    readX (next bytes) = some 5 ∧ readT (next bytes) = some 0 ∧
    (next bytes).ex.journal = [] ∧ (next bytes).logs = (success bytes).logs ∧
    (next bytes).events = (success bytes).events ++ [.credit thisC (word 9)] ++
      [.tx user thisC (word 0) (word 12345) (selOf "g()") (.success (wordBytes (toWord 12)))] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_event_only (bytes : Roadmap.Bytes) :
    (credited bytes).ex.world ≠ (success bytes).ex.world := by
  intro same
  have balances := congrArg (fun w => (w.accounts thisC).balance) same
  change 16 = 7 at balances
  cases balances

theorem payload_clients (p : Roadmap.Pipeline) :
    (Source.runTx (global p) 20 (request (selOf "g()"))).run (Source.L0 EB,recorded []) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,next [])) ∧
    (Source.runTx (global p) 20 (request (selOf "g()"))).run (Source.L0 EB,recorded [0,255,128]) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,next [0,255,128])) ∧
    (Source.runTx (global p) 20 (request (selOf "g()"))).run
      (Source.L0 EB,recorded (List.replicate 33 0x81)) =
      (.ok (.success (wordBytes (toWord 12))),(Source.L0 EB,next (List.replicate 33 0x81))) :=
  ⟨next_actual p 0 [],next_actual p 0 [0,255,128],next_actual p 0 (List.replicate 33 0x81)⟩

def sessionEnvironment : Roadmap.SessionEnv :=
  {SourceSessionControls.environment with
    requests:=fun _ i => if i=0 then some (.credit thisC (word 9)) else if i=1 then some (.request (request (selOf "g()"))) else none}

/-- The event extension above is also produced by the actual sessionGo branch.
The actual request timestamp is retained in the exact history. -/
theorem session_credit_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    Source.sessionGo (SourceSessionControls.sourceProgram p) sessionEnvironment 20 3 0
      (success bytes) (.success (wordBytes (toWord 12))) =
      ⟨(success bytes).events ++ [.credit thisC (word 9)] ++
        [.tx user thisC (word 0) (word 12345) (selOf "g()") (.success (wordBytes (toWord 12)))],
       some (.success (wordBytes (toWord 12)))⟩ := by cases p <;> rfl

/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.installed_credit_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms installed_credit_actual
/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.next_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms next_actual
/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.complete_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_vector
/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.wrong_event_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_event_only
/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms payload_clients
/-- info: 'Solidity.Lowering.V08.SourceSessionCreditControls.session_credit_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms session_credit_actual
end Solidity.Lowering.V08.SourceSessionCreditControls
