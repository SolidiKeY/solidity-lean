import Solidity.Yul.World.ReturningPort

namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Outcome Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

theorem internal_timeout (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal (glob G) child 3 answerDecl .nil [uint]).run s=(.error .timeout,s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_timeout (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (glob G) child 4 (input G)).run s=(.error .timeout,s) := by
  rw [Source.dispatch,picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob G) child 3 answerDecl .nil [uint])
    Source.encodeVals child 3 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_timeout]

theorem enter_timeout (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob G) 5 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.error .timeout,(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob G) child 4 (input G))).run cleared=
      (.ok (.error .timeout),cleared) := by
    change (match (Source.dispatch (glob G) child 4 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_timeout]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob G) child 4 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem source_timeout (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 6 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.error .timeout,after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  simp only [Source.callAddr,parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,run_pure,
    selected G (l,⟨entryExecution,h,events,logs,fn⟩) rfl,run_mark,run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer_actual,run_modSt,Bool.not_true,Bool.false_or,after]
  rw [enter_timeout]

theorem timeout_invoke (G : Glob env) :
    CallerFrame.liftInvoke (invokeAt 6 G) (observed G)
      (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=
      some ((.error .timeout,⟨⟨after (caller G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),[]) := by
  have ready : invokeAt 6 G (observed G)
      (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G)
      ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=
      some ((.error .timeout,⟨⟨after (⟨Source.L0 env,(caller G).2⟩ : Source.EMState env []),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),[]) := by
    unfold invokeAt invokeTemplateAt template
    change some (pack ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
      ((Source.callAddr (glob G) parentFrame 6 CallerFrameChecks.receiver 7 (input G) false).run (Source.L0 env,(caller G).2)))=_
    rw [source_timeout G _ rfl]
    simp only [pack,after,List.drop_length,List.map_nil]
  exact CallerFrame.liftInvoke_exact (invokeAt 6 G) (observed G)
    (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
    (.error .timeout) ⟨⟨after (⟨Source.L0 env,(caller G).2⟩ : Source.EMState env []),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] ready

theorem timeout_call (G : Glob env) :
    call (CallerFrame.liftInvoke (invokeAt 6 G)) (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed G) rfl (memory G) (parent (caller G)) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending (observed G) ⟨⟨after (caller G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []) :=
  call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (input_load G) (timeout_invoke G)

end Solidity.Yul.World.ReturningCall
