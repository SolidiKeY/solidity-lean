import Solidity.Yul.World.ReturningFailurePort

/-! Actual selected nonempty STATICCALL. The source zero transfer records
no-op journal entries; world equality is not full execution-state equality. -/
namespace Solidity.Yul.World.ReturningStatic
open Solidity.Source
open Solidity.Roadmap (Outcome Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env uint answerDecl body glob input output parentFrame entryExecution)

def child : Fr := ⟨CallerFrameChecks.receiver,CallerFrameChecks.owner,0,true,"Finite",true,1⟩

theorem picked (G : Glob env) : (glob G).pickFn child (input G)=some answerDecl := by
  rw [Glob.pickFn]
  change ([answerDecl].find? (fun d=>((glob G).prog.body ((glob G).dispatchFn "Finite" d)).isSome &&
    match d.fnSig env with
    | some (ps,_) => (glob G).selector (sigOf env.layout d.name ps)==(input G).take 4
    | none => false))=_
  simp only [List.find?_cons,ReturningCall.resolved,ReturningCall.found,Option.isSome_some,ReturningCall.signature,Bool.true_and]
  rw [List.take_of_length_le (by rw [ReturningCall.input_length]; exact Nat.le_refl _)]
  simp only [ReturningCall.input,ReturningCall.answerDecl,BEq.rfl]

theorem internal_run (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal (glob G) child 7 answerDecl .nil [uint]).run s=
      (.ok (.val (.int (ReturningCall.value : Int) (by decide))),s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_run (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (glob G) child 8 (input G)).run s=(.ok output,s) := by
  rw [Source.dispatch,picked,ReturningCall.input_nonempty]
  simp only [ReturningCall.signature,ReturningCall.input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob G) child 7 answerDecl .nil [uint])
    Source.encodeVals child 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_run]
  rfl

theorem enter_run (G : Glob env) (s : Source.EMState env []) (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true "Finite" 1 mark).run s=
      (.ok (.success output),(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob G) child 8 (input G))).run cleared=
      (.ok (.ok output),cleared) := by
    change (match (Source.dispatch (glob G) child 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_run]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob G) child 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

def zeroMoved := (entryExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 11))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 23))
def after {Γ} (s : Source.EMState env Γ) : Source.EMState env Γ := ⟨s.1,{s.2 with ex:=zeroMoved}⟩

theorem transfer_zero : entryExecution.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some zeroMoved := rfl

theorem source_run (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 (input G) true).run s=
      (.ok (.success output),after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  simp only [Source.callAddr,parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    ReturningCall.selected G (l,⟨entryExecution,h,events,logs,fn⟩) rfl,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer_zero,ReturningCall.run_modSt,Bool.not_true,Bool.true_or,after]
  rw [enter_run]

/-- Only the actual proved return template is admitted here. No arbitrary
source log/store body is treated as an adequate event-only producer. -/
def invokeAt (horizon : Nat) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .staticcall =>
      if decide (target=CallerFrameChecks.receiver) &&
          !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
          decide (frame.source.value.val=0) && frame.source.static &&
          decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        some (ReturningCall.pack c ((Source.callAddr (glob G) parentFrame horizon target 0 bytes true).run c.1.1))
      else none
    | .call | .delegatecall => none

def invoke (G : Glob env) : Invoke env [] := invokeAt 10 G

theorem invoke_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke G o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  have ran := source_run G (⟨l,⟨entryExecution,h,events,logs,fn⟩⟩ : Source.EMState env []) rfl
  unfold invoke invokeAt
  change some (ReturningCall.pack ⟨⟨(l,⟨entryExecution,h,events,logs,fn⟩),r⟩,b⟩
    ((Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 (input G) true).run
      (l,⟨entryExecution,h,events,logs,fn⟩)))=_
  rw [ran]
  simp only [ReturningCall.pack,after,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke G) o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke G) o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩ (.ok (.success output))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : Source.EMState env []),r⟩,b⟩ [] (invoke_empty G ⟨Source.L0 env,s.2⟩ entry r b o)

def result (G : Glob env) : Result env [.bytes .memory,.bytes .memory] :=
  (⟨⟨after (ReturningCall.caller G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨zeroMoved,committedLogs (ReturningCall.observed G).trace,output⟩,(ReturningCall.observed G).trace,rfl⟩)

theorem call_actual (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke G)) (ReturningCall.caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
      (ReturningCall.observed G) rfl (ReturningCall.memory G) (ReturningCall.parent (ReturningCall.caller G))
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=some (.ok (.success output),result G) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (ReturningCall.input_load G)
    (invoke_actual G (ReturningCall.caller G) rfl _ _ (ReturningCall.observed G))]
  simp only [finish_success,List.append_nil,result,after]

end Solidity.Yul.World.ReturningStatic
