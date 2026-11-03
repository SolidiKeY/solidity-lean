import Solidity.Yul.World.GeneralFailure

/-! Real entered ordinary-error producer timeout, distinct from revert and
adapter refusal. The source transfer remains pending; it is not rolled back. -/
namespace Solidity.Yul.World.FailureFuel
open Solidity.Source
open Solidity.Roadmap (Outcome Bytes Word)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall

theorem internal_timeout (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal (failingGlob G) child 3 answerDecl .nil [uint]).run s=(.error .timeout,s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_timeout (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (failingGlob G) child 4 (input G)).run s=(.error .timeout,s) := by
  rw [Source.dispatch,ReturningCall.failure_picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (failingGlob G) child 3 answerDecl .nil [uint])
    Source.encodeVals child 3 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_timeout]

theorem enter_timeout (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (failingGlob G) 5 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.error .timeout,(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (failingGlob G) child 4 (input G))).run cleared=
      (.ok (.error .timeout),cleared) := by
    change (match (Source.dispatch (failingGlob G) child 4 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_timeout]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (failingGlob G) child 4 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl



theorem invoke_run (G : Glob env) (horizon : Nat) (s out : EMState env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) (status : Except Halt Outcome)
    (ran : (Source.callAddr (failingGlob G) ReturningCall.parentFrame horizon CallerFrameChecks.receiver 7 (input G) false).run s=(status,out)) :
    ReturningCall.invokeTemplateAt horizon true G o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((status,⟨⟨out,r⟩,b⟩),(out.2.events.drop s.2.events.length).map Observation.event) := by
  unfold ReturningCall.invokeTemplateAt ReturningCall.template
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame horizon
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame horizon
      CallerFrameChecks.receiver 7 (input G) false).run s))=_
  rw [ran]
  rfl

theorem source_timeout (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (failingGlob G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.error .timeout,GeneralReturning.after s next) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    GeneralFailure.selected G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.false_or,GeneralReturning.after]
  rw [enter_timeout]

theorem timeout_invoke (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invokeTemplateAt 6 true G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.error .timeout,⟨⟨GeneralReturning.after s next,r⟩,b⟩),[]) := by
  have ran := invoke_run G 6 (⟨Source.L0 env,s.2⟩ : EMState env []) (GeneralReturning.after ⟨Source.L0 env,s.2⟩ next)
    code r b o gas (.error .timeout) (source_timeout G ⟨Source.L0 env,s.2⟩ next code transfer)
  simp only [GeneralReturning.after,List.drop_length,List.map_nil] at ran
  exact CallerFrame.liftInvoke_exact (ReturningCall.invokeTemplateAt 6 true G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.error .timeout)
    ⟨⟨GeneralReturning.after (⟨Source.L0 env,s.2⟩ : EMState env []) next,r⟩,b⟩ [] ran

theorem call_timeout (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeTemplateAt 6 true G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=
      some (.error .timeout,pending o ⟨⟨GeneralReturning.after s next,r⟩,b⟩ []) :=
  call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (timeout_invoke G s next code transfer r b o gas)

theorem prefixed_timeout (G : Glob env) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeTemplateAt 6 true G))
      (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution) CallerFrameChecks.residual CallerFrameChecks.encoding
      (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution) rfl (ReturningCall.memory G)
      (ReturningCall.parent (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution))
      .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution)
        ⟨⟨GeneralReturning.after (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution) SourceBoundaryRules.prefixedMoved,
          CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []) :=
  call_timeout G _ SourceBoundaryRules.prefixedMoved rfl rfl _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem pending_controls (G : Glob env) :
    let c : Carrier env [.bytes .memory,.bytes .memory] :=
      ⟨⟨GeneralReturning.after (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution) SourceBoundaryRules.prefixedMoved,
        CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
    let o:=pending (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution) c []
    o.1=c ∧ o.2.trace=GeneralReturningChecks.tracePrefix ∧
      o.2.effects.returndata=(GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution).effects.returndata ∧
      o.1.1.1.2.ex.journal.length=6 ∧ SourceBoundaryRules.prefixedExecution.journal.length=4 := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.World.FailureFuel
