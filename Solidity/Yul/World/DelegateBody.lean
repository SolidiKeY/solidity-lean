import Solidity.Yul.World.StateCallRules

/-! Selected known-code DELEGATECALL body transport. The existing typed body
runs at the caller storage address with inherited sender/value; no transfer is
performed. This module does not establish environment/deployment adequacy. -/
namespace Solidity.Yul.World.DelegateBody
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.ReturningCall (answerDecl uint)

def frame (a sender : Roadmap.Address) (v : Word) (depth : Nat) (cd : Bytes := []) : Fr :=
  {this:=a,sender:=sender,value:=v,static:=false,contract:="Finite",checked:=true,depth:=depth,cd:=cd}

theorem internal_success (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat)
    (s : EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob false G) (frame a sender v depth cd) 7 answerDecl .nil [uint]).run s=
      (.ok (.val (.int (ReturningCall.value : Int) (by decide))),changed s a) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem internal_revert (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat)
    (s : EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob true G) (frame a sender v depth cd) 7 answerDecl .nil [uint]).run s=
      (.error (.revert (errorData G)),changed s a) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem picked (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (cd : Bytes := []) : (glob failed G).pickFn (frame a sender v depth cd) (input G)=some answerDecl := by
  rw [Glob.pickFn]
  change ([answerDecl].find? (fun d=>((glob failed G).prog.body ((glob failed G).dispatchFn "Finite" d)).isSome &&
    match d.fnSig env with
    | some (ps,_) => (glob failed G).selector (sigOf env.layout d.name ps)==(input G).take 4
    | none => false))=_
  simp only [List.find?_cons,resolved,found,Option.isSome_some,signature,Bool.true_and]
  rw [List.take_of_length_le (by rw [input_length]; exact Nat.le_refl _)]
  simp only [input,glob,Glob.selector,answerDecl,BEq.rfl]

theorem dispatch_success (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob false G) (frame a sender v depth cd) 8 (input G)).run s=(.ok ReturningCall.output,changed s a) := by
  rw [Source.dispatch,picked false G a sender v depth cd,input_nonempty]
  simp only [signature,input_length,show answerDecl.fnMut=some .payable from rfl,bne_self_eq_false,Bool.and_false,Bool.false_eq_true,if_false]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob false G) (frame a sender v depth cd) 7 answerDecl .nil [uint])
    Source.encodeVals (frame a sender v depth cd) 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_success G a sender v depth _ cd]
  rfl

theorem enter_success (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob false G) 9 a sender v (input G) false "Finite" depth mark).run s=
      (.ok (.success ReturningCall.output),((changed s a).1,{(changed s a).2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob false G) (frame a sender v depth (input G)) 8 (input G))).run cleared=
      (.ok (.ok ReturningCall.output),changed cleared a) := by
    change (match (Source.dispatch (glob false G) (frame a sender v depth (input G)) 8 (input G)).run cleared with | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_success G a sender v depth cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob false G) (frame a sender v depth (input G)) 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem dispatch_revert (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob true G) (frame a sender v depth cd) 8 (input G)).run s=(.error (.revert (errorData G)),changed s a) := by
  rw [Source.dispatch,picked true G a sender v depth cd,input_nonempty]
  simp only [signature,input_length,show answerDecl.fnMut=some .payable from rfl,bne_self_eq_false,Bool.and_false,Bool.false_eq_true,if_false]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob true G) (frame a sender v depth cd) 7 answerDecl .nil [uint])
    Source.encodeVals (frame a sender v depth cd) 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_revert G a sender v depth _ cd]
  rfl

theorem enter_revert (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob true G) 9 a sender v (input G) false "Finite" depth mark).run s=
      (.ok (.revert (errorData G)),((Source.rollbackTo mark).run ((changed s a).1,{(changed s a).2 with heap:=mark.2.2})).2) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob true G) (frame a sender v depth (input G)) 8 (input G))).run cleared=
      (.ok (.error (.revert (errorData G))),changed cleared a) := by
    change (match (Source.dispatch (glob true G) (frame a sender v depth (input G)) 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_revert G a sender v depth cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob true G) (frame a sender v depth (input G)) 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem internal_timeout (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob failed G) (frame a sender v depth cd) 3 answerDecl .nil [uint]).run s=(.error .timeout,s) := by
  cases failed <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_timeout (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob failed G) (frame a sender v depth cd) 4 (input G)).run s=(.error .timeout,s) := by
  rw [Source.dispatch,picked failed G a sender v depth cd,input_nonempty]
  simp only [signature,input_length,show answerDecl.fnMut=some .payable from rfl,bne_self_eq_false,Bool.and_false,Bool.false_eq_true,if_false]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob failed G) (frame a sender v depth cd) 3 answerDecl .nil [uint])
    Source.encodeVals (frame a sender v depth cd) 3 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_timeout failed G a sender v depth _ cd]

theorem enter_timeout (failed : Bool) (G : Glob env) (a sender : Roadmap.Address) (v : Word) (depth : Nat) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob failed G) 5 a sender v (input G) false "Finite" depth mark).run s=
      (.error .timeout,(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob failed G) (frame a sender v depth (input G)) 4 (input G))).run cleared=
      (.ok (.error .timeout),cleared) := by
    change (match (Source.dispatch (glob failed G) (frame a sender v depth (input G)) 4 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_timeout failed G a sender v depth cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob failed G) (frame a sender v depth (input G)) 4 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

/-- Conditional storage-read variant really exhausts the unchanged horizon
AFTER writing; this is not recoded into EVM revert or success. -/
theorem read_body_timeout (G : Glob env) (sender : Roadmap.Address) (v : Word) (depth : Nat)
    (s : EMState env []) (cd : Bytes := []) :
    (Source.runMods (glob false G) (frame CallerFrameChecks.owner sender v depth cd) 6 readBody [] (.cons (.int 0 (by decide)) .nil)).run s=
      (.error .timeout,changed s CallerFrameChecks.owner) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl
end Solidity.Yul.World.DelegateBody
