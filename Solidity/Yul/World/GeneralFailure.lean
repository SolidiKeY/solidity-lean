import Solidity.Yul.World.ScalarEmitRules

/-! General actual ordinary-function Denied(uint256) producer. Reuses the
existing intrinsic failureBody and unchanged invokeFailure; no requested
Outcome or source-run premise. Static and decoding integration remain separate. -/
namespace Solidity.Yul.World.GeneralFailure
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env input errorData failingGlob)

theorem selected (G : Glob env) (s : EMState env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) :
    (Source.instanceAt (failingGlob G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  simp only [Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,code,ReturningCall.run_pure]
  rfl

/-- Actual transfer then actual internal revert/catcher/rollback to the source
entry mark; all caller fields and arbitrary journal prefixes restored. -/
theorem source_run (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (failingGlob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.ok (.revert (errorData G)),s) := by
  have back := Source.rollback_transfer s.2.ex next (src:=CallerFrameChecks.owner) (dst:=CallerFrameChecks.receiver)
    (by decide) 7 transfer CallerFrameChecks.receiver CallerFrameChecks.owner (input G) false
  change next.undoN (next.journal.length-s.2.ex.journal.length)=s.2.ex at back
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,selected G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,ReturningCall.run_modSt,Bool.not_true,Bool.false_or]
  rw [ReturningCall.failure_enter]
  change ((Except.ok (.revert (errorData G)) : Except Halt Outcome),
    (s.1,{s.2 with ex:=next.undoN (next.journal.length-s.2.ex.journal.length),logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  rw [back]
  simp only [Nat.sub_self,List.drop_zero]

def result {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,errorData G⟩,o.trace,rfl⟩)

theorem invoke_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    ReturningCall.invokeFailure G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) := by
  unfold ReturningCall.invokeFailure ReturningCall.invokeTemplateAt ReturningCall.template
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s))=_
  rw [source_run G s next code transfer]
  simp only [ReturningCall.pack,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invokeFailure G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (ReturningCall.invokeFailure G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert (errorData G)))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] (invoke_empty G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

theorem finish_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    finish s b o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      ⟨⟨s,r⟩,b⟩ [] (.revert (errorData G))=result G s r b o := by
  have clean := finish_runs_revert s r b o [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] (errorData G)
  simpa only [Source.ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using clean

theorem call_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeFailure G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=some (.ok (.revert (errorData G)),result G s r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (invoke_actual G s next code transfer r b o gas),finish_actual]

open Solidity.Yul.World.ReturningCall
theorem static_internal (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.callInternal (failingGlob G) (ReturningStatic.child cd) 7 answerDecl .nil [uint]).run s=
      (.error (.revert (errorData G)),s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem static_dispatch (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (failingGlob G) (ReturningStatic.child cd) 8 (input G)).run s=(.error (.revert (errorData G)),s) := by
  have picked : (failingGlob G).pickFn (ReturningStatic.child cd) (input G)=some answerDecl := ReturningCall.failure_picked G cd
  rw [Source.dispatch,picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (failingGlob G) (ReturningStatic.child cd) 7 answerDecl .nil [uint])
    Source.encodeVals (ReturningStatic.child cd) 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,static_internal G _ cd]

theorem static_enter (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (failingGlob G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true "Finite" 1 mark).run s=
      (.ok (.revert (errorData G)),((Source.rollbackTo mark).run (s.1,{s.2 with heap:=mark.2.2})).2) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (failingGlob G) (ReturningStatic.child (input G)) 8 (input G))).run cleared=
      (.ok (.error (.revert (errorData G))),cleared) := by
    change (match (Source.dispatch (failingGlob G) (ReturningStatic.child (input G)) 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [static_dispatch G cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (failingGlob G) (ReturningStatic.child (input G)) 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem static_source (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next) :
    (Source.callAddr (failingGlob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 0 (input G) true).run s=
      (.ok (.revert (errorData G)),s) := by
  have back := Source.rollback_transfer s.2.ex next (src:=CallerFrameChecks.owner) (dst:=CallerFrameChecks.receiver)
    (by decide) 0 transfer CallerFrameChecks.receiver CallerFrameChecks.owner (input G) true
  change next.undoN (next.journal.length-s.2.ex.journal.length)=s.2.ex at back
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,selected G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,ReturningCall.run_modSt,Bool.not_true,Bool.true_or]
  rw [static_enter]
  change ((Except.ok (.revert (errorData G)) : Except Halt Outcome),
    (s.1,{s.2 with ex:=next.undoN (next.journal.length-s.2.ex.journal.length),logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  rw [back]
  simp only [Nat.sub_self,List.drop_zero]

def staticInvoke (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .staticcall =>
      if decide (target=CallerFrameChecks.receiver) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
        decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
        decide (frame.source.value.val=0) && frame.source.static &&
        decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        some (ReturningCall.pack c ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10 target 0 bytes true).run c.1.1))
      else none
    | .call | .delegatecall => none



theorem static_invoke_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    staticInvoke G o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) := by
  unfold staticInvoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s))=_
  rw [static_source G s next code transfer]
  simp only [ReturningCall.pack,List.drop_length,List.map_nil]

theorem static_invoke_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (staticInvoke G) o
      (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (staticInvoke G) o
    (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert (errorData G)))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] (static_invoke_empty G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

theorem static_finish (G : Glob env) {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    finish s b o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      ⟨⟨s,r⟩,b⟩ [] (.revert (errorData G))=result G s r b o := by
  have clean := finish_runs_revert s r b o [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true [] (errorData G)
  simpa only [Source.ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using clean

theorem static_call (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (staticInvoke G)) s r b o shared m (ReturningCall.parent s)
      .staticcall CallerFrameChecks.receiver gas 0 offset size=some (.ok (.revert (errorData G)),result G s r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (static_invoke_actual G s next code transfer r b o gas),static_finish]

theorem size_exact (G : Glob env) {Γ} (s : EMState env Γ) r b o :
    returndataSize (result G s r b o).2.effects=some 36 := by
  have bytes := checkedReturnSize_exact (errorData G) (by rw [ReturningCall.error_length]; decide)
  simpa only [ReturningCall.error_length] using bytes

theorem nonempty (G : Glob env) : errorData G≠[] := by
  intro same
  have bad : (36 : Nat)=0 := (ReturningCall.error_length G).symm.trans (congrArg List.length same)
  exact (by decide : (36 : Nat)≠0) bad

theorem payload_window (G : Glob env) : returnWindow (errorData G) 4 2=some [0x11,0x22] := ReturningCall.error_window G

theorem exact_reraise (G : Glob env) {Γ} (s : EMState env Γ) r b o :
    (Source.reraise (.revert (result G s r b o).2.effects.returndata) : Source.EM env Γ Bytes).run s=
      (.error (.revert (errorData G)),s) := rfl

theorem prefix_control (G : Glob env) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeFailure G))
      (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution) CallerFrameChecks.residual CallerFrameChecks.encoding
      (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution) rfl (ReturningCall.memory G)
      (ReturningCall.parent (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution))
      .call CallerFrameChecks.receiver 10000 7 160 4=some (.ok (.revert (errorData G)),
        result G (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution)
          CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution)) :=
  call_actual G _ SourceBoundaryRules.prefixedMoved rfl rfl _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem static_prefix_control (G : Glob env) :
    call (CallerFrame.liftInvoke (staticInvoke G))
      (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution) CallerFrameChecks.residual CallerFrameChecks.encoding
      (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution) rfl (ReturningCall.memory G)
      (ReturningCall.parent (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution))
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=some (.ok (.revert (errorData G)),
        result G (GeneralReturningChecks.caller G SourceBoundaryRules.prefixedExecution)
          CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed SourceBoundaryRules.prefixedExecution)) :=
  static_call G _ GeneralReturningChecks.staticPrefixed rfl rfl _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem static_wrong_kind (G : Glob env) o frame target gas bytes c :
    staticInvoke G o frame .call target gas bytes c=none := rfl

theorem static_delegate_refused (G : Glob env) o frame target gas bytes c :
    staticInvoke G o frame .delegatecall target gas bytes c=none := rfl

theorem static_nonstatic_refused (G : Glob env) (s : EMState env []) r b o :
    staticInvoke G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none := rfl

theorem copied_payload (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    copyAfter (result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (GeneralReturningChecks.observed ex)) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 4 2=
      (result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex),
        some ((ReturningCall.copiedMemory G,withSourceHeap (GeneralReturningChecks.caller G ex) (ReturningCall.copiedHeap G)),
          (CallerFrameChecks.residual,CallerFrameChecks.encoding),
          (result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex)).2)) :=
  congrArg (fun x=>(result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex),x))
    (HeapWindow.copyCoupledWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ _ rfl _ 1 4 2
      (ReturningCall.error_window G) (by decide) (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2)

theorem wrong_truncated (G : Glob env) : (errorData G).take 35≠errorData G := by
  intro same
  have lengths:=congrArg List.length same
  rw [List.length_take,ReturningCall.error_length] at lengths
  exact (by decide : ¬(min 35 36=36)) lengths

theorem static_wrong_sender (G : Glob env) (s : EMState env []) r b o :
    let f:=enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G)
    staticInvoke G o {f with source:={f.source with caller:=CallerFrameChecks.receiver}}
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none := rfl

theorem static_wrong_value (G : Glob env) (s : EMState env []) r b o :
    let f:=enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G)
    staticInvoke G o {f with source:={f.source with value:=7}}
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none := rfl

theorem static_unregistered (G : Glob env) (s : EMState env []) r b o
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=none) :
    staticInvoke G o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=none := by
  unfold staticInvoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (failingGlob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s)) else none)=_
  rw [code]
  rfl

theorem source_zero_horizon (G : Glob env) (s : EMState env []) :
    (Source.callAddr (failingGlob G) ReturningCall.parentFrame 0 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.error .timeout,s) := rfl

theorem invalid_zero_copy (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    copyAfter (result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (GeneralReturningChecks.observed ex)) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 37 0=
      (result G (GeneralReturningChecks.caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (GeneralReturningChecks.observed ex),none) :=
  copyAfter_bad_source _ rfl _ 1 false ReturningCall.old rfl _ 1 37 0
    (by change (errorData G).length<37+0; rw [ReturningCall.error_length]; decide)

theorem exact_end_window (G : Glob env) : returnWindow (errorData G) 36 0=some [] := by
  unfold returnWindow
  simp only [ReturningCall.error_length,show 36+0≤36 from by decide,if_pos,List.take_zero]

end Solidity.Yul.World.GeneralFailure
