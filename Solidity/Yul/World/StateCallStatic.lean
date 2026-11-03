import Solidity.Yul.World.StateCallPort

namespace Solidity.Yul.World.StateCall
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (answerDecl uint)

theorem static_internal (failed : Bool) (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob failed G) (ReturningStatic.child cd) 7 answerDecl .nil [uint]).run s=
      (.error (.revert []),s) := by
  cases failed <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem static_dispatch (failed : Bool) (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob failed G) (ReturningStatic.child cd) 8 (input G)).run s=(.error (.revert []),s) := by
  have picked : (glob failed G).pickFn (ReturningStatic.child cd) (input G)=some answerDecl := StateCall.picked failed G cd
  rw [Source.dispatch,picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob failed G) (ReturningStatic.child cd) 7 answerDecl .nil [uint])
    Source.encodeVals (ReturningStatic.child cd) 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,static_internal failed G _ cd]

theorem static_enter (failed : Bool) (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob failed G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true "Finite" 1 mark).run s=
      (.ok (.revert []),((Source.rollbackTo mark).run (s.1,{s.2 with heap:=mark.2.2})).2) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob failed G) (ReturningStatic.child (input G)) 8 (input G))).run cleared=
      (.ok (.error (.revert [])),cleared) := by
    change (match (Source.dispatch (glob failed G) (ReturningStatic.child (input G)) 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [static_dispatch failed G cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob failed G) (ReturningStatic.child (input G)) 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem static_source (failed : Bool) (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next) :
    (Source.callAddr (glob failed G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 0 (input G) true).run s=
      (.ok (.revert []),s) := by
  have back := Source.rollback_transfer s.2.ex next (src:=CallerFrameChecks.owner) (dst:=CallerFrameChecks.receiver)
    (by decide) 0 transfer CallerFrameChecks.receiver CallerFrameChecks.owner (input G) true
  change next.undoN (next.journal.length-s.2.ex.journal.length)=s.2.ex at back
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,selected failed G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,ReturningCall.run_modSt,Bool.not_true,Bool.true_or]
  rw [static_enter]
  change ((Except.ok (.revert []) : Except Halt Outcome),
    (s.1,{s.2 with ex:=next.undoN (next.journal.length-s.2.ex.journal.length),logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  rw [back]
  simp only [Nat.sub_self,List.drop_zero]

theorem static_physical (s : EMState env []) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) (same : o.effects.execution=s.2.ex) :
    let result:=PhysicalSlotPort.step StateCallPhysical.registry StateCallPhysical.registry StateCallPhysical.request
      StateCallPhysical.encodingPrefix ReturningStatic.child StateCallPhysical.plan s r o same rfl
    result.1=(((.error (.revert []),s),r),StateCallPhysical.encodingPrefix) ∧
      result.2.effects.execution=o.effects.execution ∧ result.2.trace=o.trace ∧ result.2.effects.returndata=o.effects.returndata :=
  PhysicalSlotPort.static_result ReturningStatic.child StateCallPhysical.plan s r o same rfl rfl

end Solidity.Yul.World.StateCall

namespace Solidity.Yul.World.StateCallPort
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall

def staticResult {Γ} (_G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,[]⟩,o.trace,rfl⟩)

def staticPack (c : Carrier env []) (actual : Except Source.Halt Outcome × EMState env []) :=
  ((actual.1,(⟨⟨actual.2,c.1.2⟩,c.2⟩ : Carrier env [])),
    (actual.2.2.events.drop c.1.1.2.events.length).map Observation.event)

def staticInvoke (failed : Bool) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .staticcall =>
      if decide (target=CallerFrameChecks.receiver) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
        decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
        decide (frame.source.value.val=0) && frame.source.static &&
        decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        some (staticPack c ((Source.callAddr (glob failed G) ReturningCall.parentFrame 10 target 0 bytes true).run c.1.1))
      else none
    | .call | .delegatecall => none



theorem static_invoke_empty (failed : Bool) (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    staticInvoke failed G o (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) := by
  unfold staticInvoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (staticPack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob failed G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s)) else none)=_
  rw [code]
  change some (staticPack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob failed G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s))=_
  rw [StateCall.static_source failed G s next code transfer]
  simp only [staticPack,List.drop_length,List.map_nil]

theorem static_invoke_actual (failed : Bool) (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (staticInvoke failed G) o
      (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (staticInvoke failed G) o
    (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert []))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] (static_invoke_empty failed G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

theorem static_finish (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    finish s b o (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      ⟨⟨s,r⟩,b⟩ [] (.revert [])=staticResult G s r b o := by
  have clean := finish_runs_revert s r b o [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true [] []
  simpa only [Source.ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using clean

theorem static_call (failed : Bool) (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (staticInvoke failed G)) s r b o shared m (parent s)
      .staticcall CallerFrameChecks.receiver gas 0 offset size=some (.ok (.revert []),staticResult G s r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (static_invoke_actual failed G s next code transfer r b o gas),static_finish]

end Solidity.Yul.World.StateCallPort
