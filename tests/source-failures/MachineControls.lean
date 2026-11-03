import Solidity.Source.FailureMachine
import Solidity.Source.Semantics

/-! Independent expected actual-EM controls. No Source/EVM correspondence. -/
namespace Solidity.Source.FailureExecution.Controls
open EM

def E : Env := ⟨[]⟩
def event : Roadmap.Event := .credit ⟨9, by decide⟩ ⟨3, by decide⟩
def caller : Locals E.layout [.bytes .memory, .bool] :=
  .cons (.memRef rfl 0) (.cons (.bool true) .nil)
def seed : St E := { St.init E with
  heap := (Heap.empty.alloc ⟨.bytes .memory, Data.bytes [0xDE,0xAD]⟩).1
  events := [event]
  logs := [(⟨1, by decide⟩,[0xAA,0xBB])]
  fnLocals := ⟨[.bytes .memory, .bool], caller⟩ }
def ownPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := some 1

def swallowed (plan : RuntimePlan) : EM E [.bytes .memory, .bool] Nat := do
  let _ ← attempt (emit plan event)
  pure 7

def ownActual := (frame (some ownPlan) (swallowed (some ownPlan))).run (caller,seed)
def ownExpected : St E := { seed with events := [event,event], resource := ⟨0,1,none,[],none⟩ }

def stale : St E := { seed with resource := (Cursor.empty.enterFrame ownPlan).advanceEvent }
def noneActual := (frame none (emit none event)).run (caller,stale)
def noneExpected : St E := { stale with events := [event,event] }

def childPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame i := if i = 1 then some 1 else none

def nested (plan : RuntimePlan) : EM E [.bytes .memory, .bool] (Except Halt Nat) :=
  attempt (frame plan (swallowed plan))
def childActual := (frame (some childPlan) (nested (some childPlan))).run (caller,seed)
def childExpected : St E := { seed with events := [event,event], resource := ⟨0,2,none,[],none⟩ }
def ancestorActual := (frame (some ownPlan) (nested (some ownPlan))).run (caller,seed)

def requestPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 (some 1)
  frame _ := none

def requestSeed : St E := { seed with resource := (Cursor.empty.enterRequest requestPlan rfl).2 }
def requestActual := (frame (some requestPlan) (nested (some requestPlan))).run (caller,requestSeed)
def requestExpected : St E := { seed with events := [event,event], resource :=
  ⟨1,2,some ⟨⟨0,by decide⟩,257,some 1,1⟩,[],some (.request ⟨0,by decide⟩)⟩ }

def zeroPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := some 0

def zeroActual := (frame (some zeroPlan) (emit (some zeroPlan) event)).run (caller,seed)
def preStopped : St E := { seed with resource := Cursor.empty.enterFrame zeroPlan }
def refusedActual := (frame (some zeroPlan) (pure 7)).run (caller,preStopped)
def refusedExpected : St E := { preStopped with resource :=
  { preStopped.resource with pending := some (.frame ⟨0,by decide⟩) } }

def haltActual (why : Halt) :=
  (frame (some ownPlan) (halt why : EM E [.bytes .memory, .bool] Nat)).run (caller,seed)

end Solidity.Source.FailureExecution.Controls
