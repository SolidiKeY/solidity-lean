import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! Source-only caller-heap boundary. The proof uses the actual current Source
entry body and its calldata-bearing frame. It has no physical Views imports.
Heap restoration is not universal MemOK/world adequacy or call eligibility. -/
namespace Solidity.Yul.World.SourceHeapBoundary
open Solidity.Source
open Solidity.Roadmap (Outcome)

theorem enterInstance_heap {E} (G : Glob E) (s : EMState E []) (n : Nat)
    a sender value input static contract depth (mark : Nat × Nat × Source.Heap E.layout) :
    ((Source.enterInstance G (n+1) a sender value input static contract depth mark).run s).2.2.heap=mark.2.2 := by
  let F : Fr := {this:=a,sender:=sender,value:=value,static:=static,contract:=contract,depth:=depth,cd:=input}
  let resume : Except Halt Solidity.Roadmap.Bytes → EM E [] Outcome := fun result => do
    Source.EM.modSt (fun state=>{state with heap:=mark.2.2})
    match result with
    | .ok data => pure (.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (.revert data)
    | .error h => Source.EM.halt h
  change ((do
    Source.EM.modSt (fun state=>{state with heap:=Source.Heap.empty})
    let result ← Source.EM.attempt (Source.dispatch G F n input)
    resume result).run s).2.2.heap=mark.2.2
  rw [Source.Hoare.run_bind]
  change ((do let result ← Source.EM.attempt (Source.dispatch G F n input); resume result).run
    (s.1,{s.2 with heap:=Source.Heap.empty})).2.2.heap=mark.2.2
  rw [Source.Hoare.run_bind]
  change (match (Source.dispatch G F n input).run (s.1,{s.2 with heap:=Source.Heap.empty}) with
    | (result,child)=>(resume result).run child).2.2.heap=mark.2.2
  cases run : (Source.dispatch G F n input).run (s.1,{s.2 with heap:=Source.Heap.empty}) with
  | mk status child =>
    cases status with
    | ok data => rfl
    | error h => cases h <;> rfl

end Solidity.Yul.World.SourceHeapBoundary
