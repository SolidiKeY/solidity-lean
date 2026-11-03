import Solidity.Yul.World.EffectfulEmitDispatch

/-! Actual current published Source entry API (including frame calldata).
The private source snapshot is older; final source/cache joint rebuild remains
required. Account/code selection and transfer belong to callAddr. -/
namespace Solidity.Yul.World.EffectfulEmitEntry
open Solidity.Source
open Solidity.Roadmap (Bytes Word Address Outcome)
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitFunction
open Solidity.Yul.World.EffectfulEmitDispatch

theorem enter_revert_of_dispatch {E : Env} (G : Glob E) (s : EMState E []) (n : Nat)
    (owner sender : Address) (value : Word) (input : Bytes) (static : Bool) (contract : String)
    (depth : Nat) (mark : Nat × Nat × Source.Heap E.layout) (bytes : Bytes) (after : EMState E [])
    (ran : (Source.dispatch G {this:=owner,sender:=sender,value:=value,static:=static,contract:=contract,depth:=depth,cd:=input} n input).run
      (s.1,{s.2 with heap:=Source.Heap.empty})=(.error (.revert bytes),after)) :
    (Source.enterInstance G (n+1) owner sender value input static contract depth mark).run s=
      (.ok (.revert bytes),((Source.rollbackTo mark).run
        (after.1,{after.2 with heap:=mark.2.2})).2) := by
  let child : Fr := {this:=owner,sender:=sender,value:=value,static:=static,contract:=contract,depth:=depth,cd:=input}
  let cleared : EMState E [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch G child n input)).run cleared=
      (.ok (.error (.revert bytes)),after) := by
    change (match (Source.dispatch G child n input).run cleared with
      | (result,state)=>((Except.ok result : Except Halt (Except Halt Bytes)),state))=_
    rw [ran]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let result ← Source.EM.attempt (Source.dispatch G child n input)
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match result with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error other => Source.EM.halt other).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

/-- Concrete selected producer instantiation: no assumed dispatch/run premise. -/
theorem actual {indexed anonymous} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) []) (owner sender : Address) (value : Word) (depth : Nat) :
    (Source.enterInstance (glob G) 9 owner sender value (input G) false "Finite" depth
      (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run s=
      (.ok (.revert (EffectfulEmitRevert.data G)),s) := by
  let child : Fr := {this:=owner,sender:=sender,value:=value,static:=false,contract:="Finite",depth:=depth,cd:=input G}
  let cleared : EMState (env indexed anonymous) [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have dispatched:=EffectfulEmitDispatch.actual G child cleared rfl rfl
  have entered:=enter_revert_of_dispatch (glob G) s 8 owner sender value (input G) false "Finite" depth
    (s.2.ex.journal.length,s.2.logs.length,s.2.heap) (EffectfulEmitRevert.data G)
    (after G child cleared) dispatched
  change (Source.enterInstance (glob G) 9 owner sender value (input G) false "Finite" depth
      (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run s=
    (.ok (.revert (EffectfulEmitRevert.data G)),
      ((Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run (after G child s)).2) at entered
  rw [EffectfulEmitRollback.rollback_after G child s] at entered
  exact entered

end Solidity.Yul.World.EffectfulEmitEntry
