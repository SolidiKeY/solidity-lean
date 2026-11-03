import Solidity.Yul.World.DelegatePhysical
import Solidity.Yul.World.EffectfulEmitEntry
namespace Solidity.Yul.World.DelegateStatic
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.ReturningCall (answerDecl uint)
def staticFrame (a sender : Address) (v : Word) (depth : Nat) (cd : Bytes := []) : Fr :=
  {DelegateBody.frame a sender v depth cd with static:=true}
theorem static_internal (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob failed G) (staticFrame a sender v depth cd) 7 answerDecl .nil [uint]).run s=
      (.error (.revert []),s) := by
  cases failed <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem static_dispatch (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob failed G) (staticFrame a sender v depth cd) 8 (input G)).run s=(.error (.revert []),s) := by
  have picked : (glob failed G).pickFn (staticFrame a sender v depth cd) (input G)=some answerDecl := DelegateBody.picked failed G a sender v depth cd
  rw [Source.dispatch,picked,input_nonempty]
  simp only [signature,input_length,show answerDecl.fnMut=some .payable from rfl,bne_self_eq_false,Bool.and_false,Bool.false_eq_true,if_false]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob failed G) (staticFrame a sender v depth cd) 7 answerDecl .nil [uint])
    Source.encodeVals (staticFrame a sender v depth cd) 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,static_internal failed G a sender v depth _ cd]

theorem static_enter (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (E:=env) (glob failed G) 9 a sender v (input G) true "Finite" depth mark).run s=
      (.ok (.revert []),((Source.rollbackTo (E:=env) mark).run (s.1,{s.2 with heap:=mark.2.2})).2) := by
  let cleared : EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have dispatched := static_dispatch failed G a sender v depth cleared (input G)
  simp only [staticFrame,DelegateBody.frame] at dispatched
  have entered := EffectfulEmitEntry.enter_revert_of_dispatch (E:=env) (glob failed G) s 8
    a sender v (input G) true "Finite" depth mark [] cleared dispatched
  exact entered

def execute (failed : Bool) (G : Glob env) (a sender target : Address) (v : Word)
    (depth : Nat) (bytes : Bytes) (s : EMState env []) : Option (Except Halt Outcome × EMState env []) :=
  match (Source.instanceAt (glob failed G) target).run s with
  | (.ok (some "Finite"),selected) => some ((Source.enterInstance (glob failed G) 9 a sender v bytes true "Finite" depth
      (selected.2.ex.journal.length,selected.2.logs.length,selected.2.heap)).run selected)
  | _ => none

theorem execute_revert (failed : Bool) (G : Glob env) (a sender target : Address) (v : Word)
    (depth : Nat) (s : EMState env []) (code : (s.2.ex.world.accounts target).code=some 0) :
    execute failed G a sender target v depth (input G) s=some (.ok (.revert []),s) := by
  simp only [execute,DelegateEntry.selection failed G target s code,static_enter]
  change some ((Except.ok (Outcome.revert []) : Except Halt Outcome),
    (s.1,{s.2 with ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length),logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,List.drop_zero]
end Solidity.Yul.World.DelegateStatic
