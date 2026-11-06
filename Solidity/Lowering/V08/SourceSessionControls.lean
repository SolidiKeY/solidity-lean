import Solidity.Lowering.V08.SourceTransactionControls

/-! Actual finite source deployment/session history and a second transaction at
its genuinely committed input. Existing published bodies/strategy are consumed;
no new call/callback lowering or compiler/world correspondence is supplied. -/
namespace Solidity.Lowering.V08.SourceSessionControls
open Solidity Source
open Source.SemanticsExamples

def requests : Nat → Option Roadmap.Action
  | 0 => some (.request (tx (selOf "g()")))
  | 1 => some (.request (tx (selOf "poke()")))
  | 2 => some (.request (tx (selOf "g()")))
  | _ => none

def environment : Roadmap.SessionEnv :=
  {deployer:=user,deployNonce:=⟨0,by decide⟩,deployValue:=word 0,deployArgs:=[],
    balance:=fun _ => word 0,hasCode:=fun _ _ => true,
    requests:=fun _ i => requests i,callee:=answerOnly}
def sourceProgram (p : Roadmap.Pipeline) : Source.SrcProg EB := ⟨PB,p,toyFixed,"C"⟩
def expected : List Roadmap.Event :=
  [.deploy user (word 0) [] (.success []) (some thisC),
   .tx user thisC (word 0) (word 0) (selOf "g()") (.success (wordBytes (toWord 12))),
   .tx user thisC (word 0) (word 0) (selOf "poke()") (.revert []),
   .tx user thisC (word 0) (word 0) (selOf "g()") (.success (wordBytes (toWord 12)))]

/-- sessionFrom's explicit address is not asserted to be the EVM creation hash. -/
theorem session_actual (p : Roadmap.Pipeline) :
    (Source.sessionFrom (sourceProgram p) environment thisC 30).events = expected ∧
    (Source.sessionFrom (sourceProgram p) environment thisC 30).final =
      some (.success (wordBytes (toWord 12))) := by cases p <;> decide +kernel

theorem no_transaction_budget (p : Roadmap.Pipeline) :
    (Source.sessionFrom (sourceProgram p) environment thisC 0).events =
      [.deploy user (word 0) [] (.success []) (some thisC)] ∧
    (Source.sessionFrom (sourceProgram p) environment thisC 0).final = none := by
  cases p <;> decide +kernel

def secondRevert (bytes : Roadmap.Bytes) : Source.St EB :=
  {SourceTransactionControls.success bytes with
    ex:=((SourceTransactionControls.success bytes).ex.run
      [SourceTransactionControls.creditOp,SourceTransactionControls.xOp SourceTransactionControls.v1,
       SourceTransactionControls.tOp SourceTransactionControls.v2]).undoN 3 |>.endTx
    events:=(SourceTransactionControls.success bytes).events ++
      [.tx user thisC (word 0) (word 12345) (selOf "poke()") (.revert [])]}

theorem second_transaction_actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.runTx (SourceTransactionControls.global p) (extra+20)
      (SourceTransactionControls.request (selOf "poke()"))).run
      (Source.L0 EB,SourceTransactionControls.success bytes) =
      (.ok (.revert []),(Source.L0 EB,secondRevert bytes)) := by cases p <;> rfl

theorem second_world (bytes : Roadmap.Bytes) :
    (secondRevert bytes).ex.world = (SourceTransactionControls.success bytes).ex.world := by
  have undo := Source.ExecState.undoN_run (SourceTransactionControls.success bytes).ex
    [SourceTransactionControls.creditOp,SourceTransactionControls.xOp SourceTransactionControls.v1,
     SourceTransactionControls.tOp SourceTransactionControls.v2]
  exact congrArg (fun x => x.world) undo

theorem wrong_ancestor_snapshot (bytes : Roadmap.Bytes) :
    (secondRevert bytes).ex.world ≠ (SourceTransactionControls.initial bytes).ex.world := by
  rw [second_world]
  intro same
  have cells := congrArg (fun w => (w.accounts thisC).storage.read dX.path) same
  have values := congrArg (fun (v : Option (Source.Val EB.layout uint)) =>
    v.map (fun | .int i _ => i)) cells
  change some (5 : Int) = some 3 at values
  cases values

theorem wrong_final_outcome (p : Roadmap.Pipeline) :
    (Source.sessionFrom (sourceProgram p) environment thisC 30).final ≠ some (.revert []) := by
  rw [(session_actual p).2]
  intro wrong
  cases wrong

/-- info: 'Solidity.Lowering.V08.SourceSessionControls.session_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms session_actual
/-- info: 'Solidity.Lowering.V08.SourceSessionControls.no_transaction_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_transaction_budget
/-- info: 'Solidity.Lowering.V08.SourceSessionControls.second_transaction_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_transaction_actual
/-- info: 'Solidity.Lowering.V08.SourceSessionControls.second_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms second_world
/-- info: 'Solidity.Lowering.V08.SourceSessionControls.wrong_ancestor_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_ancestor_snapshot
/-- info: 'Solidity.Lowering.V08.SourceSessionControls.wrong_final_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_final_outcome
end Solidity.Lowering.V08.SourceSessionControls
