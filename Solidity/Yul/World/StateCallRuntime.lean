import Solidity.Yul.World.StateCall

namespace Solidity.Yul.World.StateCall
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (answerDecl uint child)

theorem input_length (G : Glob env) : (input G).length=4 := by
  simp only [input,Glob.selector,List.length_take,wordBytes_length]
  rfl

theorem input_nonempty (G : Glob env) : (input G).isEmpty=false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro nil
  have impossible : (4 : Nat)=0 := (input_length G).symm.trans (congrArg List.length nil)
  exact (by decide : (4 : Nat)≠0) impossible

theorem exposed : env.exposed "Finite"=[answerDecl] := rfl

theorem signature : answerDecl.fnSig env=some ([],[uint]) := rfl

theorem found (failed : Bool) (G : Glob env) : (glob failed G).prog.body answerDecl=some (body failed) := rfl

theorem picked (failed : Bool) (G : Glob env) : (glob failed G).pickFn child (input G)=some answerDecl := by
  rw [Glob.pickFn]
  change ([answerDecl].find? (fun d=>((glob failed G).prog.body ((glob failed G).dispatchFn "Finite" d)).isSome &&
    match d.fnSig env with
    | some (ps,_) => (glob failed G).selector (sigOf env.layout d.name ps)==(input G).take 4
    | none => false))=_
  simp only [List.find?_cons,resolved,found,Option.isSome_some,signature,Bool.true_and]
  rw [List.take_of_length_le (by rw [input_length]; exact Nat.le_refl _)]
  simp only [input,glob,Glob.selector,answerDecl,BEq.rfl]

theorem dispatch_success (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (glob false G) child 8 (input G)).run s=(.ok ReturningCall.output,changed s CallerFrameChecks.receiver) := by
  rw [Source.dispatch,picked false G,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob false G) child 7 answerDecl .nil [uint])
    Source.encodeVals child 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_success]
  rfl

theorem enter_success (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob false G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.ok (.success ReturningCall.output),((changed s CallerFrameChecks.receiver).1,{(changed s CallerFrameChecks.receiver).2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob false G) child 8 (input G))).run cleared=
      (.ok (.ok ReturningCall.output),changed cleared CallerFrameChecks.receiver) := by
    change (match (Source.dispatch (glob false G) child 8 (input G)).run cleared with | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_success]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob false G) child 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem dispatch_revert (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (glob true G) child 8 (input G)).run s=(.error (.revert (errorData G)),changed s CallerFrameChecks.receiver) := by
  rw [Source.dispatch,picked true G,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob true G) child 7 answerDecl .nil [uint])
    Source.encodeVals child 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_revert]
  rfl

theorem enter_revert (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob true G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.ok (.revert (errorData G)),((Source.rollbackTo mark).run ((changed s CallerFrameChecks.receiver).1,{(changed s CallerFrameChecks.receiver).2 with heap:=mark.2.2})).2) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob true G) child 8 (input G))).run cleared=
      (.ok (.error (.revert (errorData G))),changed cleared CallerFrameChecks.receiver) := by
    change (match (Source.dispatch (glob true G) child 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_revert]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob true G) child 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

def transferred {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay) : EMState env Γ :=
  ⟨s.1,{s.2 with ex:=next}⟩

theorem selected (failed : Bool) (G : Glob env) (s : EMState env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) :
    (Source.instanceAt (glob failed G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  simp only [Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,code,ReturningCall.run_pure]
  rfl

theorem source_success (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (glob false G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.ok (.success ReturningCall.output),changed (transferred s next) CallerFrameChecks.receiver) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0≥1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    selected false G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.false_or]
  rw [enter_success]
  rfl

theorem transfer_length (ex next : ExecState env.layout env.lay env.lay)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    next.journal.length=ex.journal.length+2 := by
  simp only [ExecState.transfer,show CallerFrameChecks.owner≠CallerFrameChecks.receiver from by decide,if_false] at transfer
  split at transfer
  · cases transfer
    simp only [ExecState.journal_apply]
  · cases transfer

theorem rollback_write_transfer (ex next : ExecState env.layout env.lay env.lay)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (next.apply (writeOp CallerFrameChecks.receiver)).undoN
      ((next.apply (writeOp CallerFrameChecks.receiver)).journal.length-ex.journal.length)=ex := by
  have back:=Source.rollback_transfer ex next (src:=CallerFrameChecks.owner) (dst:=CallerFrameChecks.receiver)
    (by decide) 7 transfer CallerFrameChecks.receiver CallerFrameChecks.owner [] false
  change next.undoN (next.journal.length-ex.journal.length)=ex at back
  have len:=transfer_length ex next transfer
  have count : (next.apply (writeOp CallerFrameChecks.receiver)).journal.length-ex.journal.length=
      (next.journal.length-ex.journal.length)+1 := by rw [ExecState.journal_apply]; omega
  rw [count,ExecState.undoN,ExecState.undo_apply]
  exact back

theorem source_revert (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (glob true G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.ok (.revert (errorData G)),s) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0≥1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    selected true G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.false_or]
  rw [enter_revert]
  change ((Except.ok (.revert (errorData G)) : Except Source.Halt Outcome),
    (s.1,{s.2 with
      ex:=(next.apply (writeOp CallerFrameChecks.receiver)).undoN
        ((next.apply (writeOp CallerFrameChecks.receiver)).journal.length-s.2.ex.journal.length)
      logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  rw [rollback_write_transfer s.2.ex next transfer]
  simp only [Nat.sub_self,List.drop_zero]

end Solidity.Yul.World.StateCall
