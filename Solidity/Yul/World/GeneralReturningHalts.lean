import Solidity.Yul.World.GeneralReturning

namespace Solidity.Yul.World.GeneralReturning
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output)

/-- Transport an actual Source run through the unchanged invocation body.
The explicit run equality is discharged by concrete source proofs below; it
is not a generic callee or observation-adequacy certificate. -/
theorem invoke_run (G : Glob env) (horizon : Nat) (s out : EMState env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) (status : Except Halt Outcome)
    (ran : (Source.callAddr (glob G) ReturningCall.parentFrame horizon CallerFrameChecks.receiver 7 (input G) false).run s=(status,out)) :
    ReturningCall.invokeAt horizon G o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((status,⟨⟨out,r⟩,b⟩),(out.2.events.drop s.2.events.length).map Observation.event) := by
  unfold ReturningCall.invokeAt ReturningCall.invokeTemplateAt ReturningCall.template
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame horizon
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame horizon
      CallerFrameChecks.receiver 7 (input G) false).run s))=_
  rw [ran]
  rfl

def refusedResult {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,[]⟩,o.trace,rfl⟩)

theorem refused_invoke (G : Glob env) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invoke G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) := by
  have ran := invoke_run G 10 (⟨Source.L0 env,s.2⟩ : EMState env []) ⟨Source.L0 env,s.2⟩ code r b o gas (.ok (.revert []))
    (SourceBoundaryRules.source_transfer_refused G ⟨Source.L0 env,s.2⟩ code transfer)
  simp only [List.drop_length,List.map_nil] at ran
  exact CallerFrame.liftInvoke_exact (ReturningCall.invoke G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert []))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] ran

theorem refused_finish (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    finish s b o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      ⟨⟨s,r⟩,b⟩ [] (.revert [])=refusedResult s r b o := by
  have clean := finish_runs_revert s r b o [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] []
  simpa only [Source.ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using clean

theorem call_refused (G : Glob env) {Γ} (s : EMState env Γ)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=some (.ok (.revert []),refusedResult s r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (refused_invoke G s code transfer r b o gas),refused_finish]

/-- Actual smaller source horizon, with successful value transfer still dirty.
Neither the transfer nor caller frame is erased on this non-revert halt. -/
theorem source_timeout (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (glob G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.error .timeout,after s next) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    SourceBoundaryRules.selected_at_code G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.false_or,after]
  rw [ReturningCall.enter_timeout]

theorem timeout_invoke (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invokeAt 6 G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.error .timeout,⟨⟨after s next,r⟩,b⟩),[]) := by
  have ran := invoke_run G 6 (⟨Source.L0 env,s.2⟩ : EMState env []) (after ⟨Source.L0 env,s.2⟩ next)
    code r b o gas (.error .timeout) (source_timeout G ⟨Source.L0 env,s.2⟩ next code transfer)
  simp only [after,List.drop_length,List.map_nil] at ran
  exact CallerFrame.liftInvoke_exact (ReturningCall.invokeAt 6 G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.error .timeout)
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : EMState env []) next,r⟩,b⟩ [] ran

theorem call_timeout (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeAt 6 G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=
      some (.error .timeout,pending o ⟨⟨after s next,r⟩,b⟩ []) :=
  call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (timeout_invoke G s next code transfer r b o gas)

/-- Adapter input refusal precedes the source call, and is not an EVM revert. -/
theorem input_refused (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (bad : PhysicalHeapPort.port.load m offset size=none) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=none := by
  simp only [call,show callPreflight (ReturningCall.parent s) .call 7=true from rfl,if_true,bad,bind,Option.bind_none]

end Solidity.Yul.World.GeneralReturning
