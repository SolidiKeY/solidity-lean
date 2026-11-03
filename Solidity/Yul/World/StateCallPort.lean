import Solidity.Yul.World.StateCallPhysical

/-! Selected actual state-changing Source call and full physical completion.
No arbitrary callee, supplied outcome, source-run certificate or ABI clone. -/
namespace Solidity.Yul.World.StateCallPort
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical

def parent {Γ} (s : EMState env Γ) := s.2.ex.enter CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false

def invoke (failed : Bool) (G : Glob env) : Invoke env [] :=
  fun o frame kind target _ bytes c=>match kind with
  | .call =>
    if decide (target=CallerFrameChecks.receiver) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
      decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
      decide (frame.source.value.val=7) && !frame.source.static &&
      decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
      if c.1.2.cells (complementKey false CallerFrameChecks.receiver 7)=(0xaabbcc00 : Word) then do
        let p ← prepareRepresentedSlot (E:=env) registry registry request c.2
        let next ← c.1.1.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7
        let moved := transferred c.1.1 next
        let shared : ObservedEffects env.layout env.lay env.lay := {o with effects:={o.effects with execution:=next}}
        let physical := PhysicalSlotPort.step registry registry request c.2 ReturningCall.child p moved c.1.2 shared rfl rfl
        let actual := (Source.callAddr (glob failed G) ReturningCall.parentFrame 10 target frame.source.value bytes false).run c.1.1
        let banks := match actual.1 with
          | .ok (.success _) => (physical.1.1.2,physical.1.2)
          | .ok (.revert _) => (residualRollback c.1.2.journal.length physical.1.1.2,boolEncodingRollback c.2.journal.length physical.1.2)
          | .error _ => (c.1.2,c.2)
        pure ((actual.1,(⟨⟨actual.2,banks.1⟩,banks.2⟩ : Carrier env [])),
          (actual.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    else none
  | .staticcall | .delegatecall => none

def sourceCarrier {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) : Carrier env Γ :=
  ⟨⟨changed (transferred s next) CallerFrameChecks.receiver,residualWrite r plan.packed.residualUpdate⟩,
    requestEncoding (E:=env) registry registry request encodingPrefix⟩

theorem invoke_success_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    invoke false G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩=
      some ((.ok (.success ReturningCall.output),sourceCarrier s next r),[]) := by
  unfold invoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then _ else none)=_
  rw [code]
  have prep : prepareRepresentedSlot (E:=env) registry registry request encodingPrefix=some plan :=
    (Option.some_get ready).symm
  simp only [decide_true,if_true,prep,transfer,bind,Option.bind_some,if_pos padding]
  rw [show (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G)).source.value=(7 : Word) from rfl]
  rw [StateCall.source_success G s next code transfer]
  have step:=step_exact (transferred s next) r
    ({o with effects:={o.effects with execution:=next}} : ObservedEffects env.layout env.lay env.lay) rfl
  rw [step]
  simp only [changed,transferred,List.drop_length,List.map_nil]
  rfl

theorem invoke_revert_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    invoke true G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,encodingPrefix⟩),[]) := by
  unfold invoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then _ else none)=_
  rw [code]
  have prep : prepareRepresentedSlot (E:=env) registry registry request encodingPrefix=some plan :=
    (Option.some_get ready).symm
  simp only [decide_true,if_true,prep,transfer,bind,Option.bind_some,if_pos padding]
  rw [show (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G)).source.value=(7 : Word) from rfl]
  rw [StateCall.source_revert G s next code transfer]
  have step:=step_exact (transferred s next) r
    ({o with effects:={o.effects with execution:=next}} : ObservedEffects env.layout env.lay env.lay) rfl
  rw [step]
  have res:=residualRollback_run r [plan.packed.residualUpdate]
  have enc:=boolEncodingRollback_run encodingPrefix
    (encodingWrites (selectedSlotPaths (registry request.address) request.slot) false request.address (fun _=>request.raw) encodingPrefix)
  simp only [residualRun] at res
  change boolEncodingRollback encodingPrefix.journal.length (requestEncoding (E:=env) registry registry request encodingPrefix)=encodingPrefix at enc
  simp only [res,enc,List.drop_length,List.map_nil]
  rfl

def successResult {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (sourceCarrier s next r,⟨⟨(sourceCarrier s next r).1.1.2.ex,committedLogs o.trace,ReturningCall.output⟩,o.trace,rfl⟩)
def revertResult {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨s,r⟩,encodingPrefix⟩,⟨⟨s.2.ex,committedLogs o.trace,errorData G⟩,o.trace,rfl⟩)

theorem invoke_success_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (invoke false G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩=
      some ((.ok (.success ReturningCall.output),sourceCarrier s next r),[]) :=
  CallerFrame.liftInvoke_exact (invoke false G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩ (.ok (.success ReturningCall.output))
    (sourceCarrier ⟨Source.L0 env,s.2⟩ next r) [] (invoke_success_empty G ⟨Source.L0 env,s.2⟩ next code transfer r padding o gas)

theorem invoke_revert_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (invoke true G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,encodingPrefix⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke true G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,encodingPrefix⟩ (.ok (.revert (errorData G)))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,encodingPrefix⟩ [] (invoke_revert_empty G ⟨Source.L0 env,s.2⟩ next code transfer r padding o gas)

theorem call_success (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke false G)) s r encodingPrefix o shared m (parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=some (.ok (.success ReturningCall.output),successResult s next r o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (invoke_success_actual G s next code transfer r padding o gas),finish_success]
  simp only [List.append_nil]
  rfl

theorem call_revert (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00) (o : ObservedEffects env.layout env.lay env.lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke true G)) s r encodingPrefix o shared m (parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=some (.ok (.revert (errorData G)),revertResult G s r o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (invoke_revert_actual G s next code transfer r padding o gas)]
  have clean:=finish_runs_revert s r encodingPrefix o [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] (errorData G)
  simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using
    congrArg (fun x=>some ((Except.ok (.revert (errorData G)) : Except Source.Halt Outcome),x)) clean

theorem outer_revert {Γ} (G : Glob env) (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay) (bytes : Bytes) :
    finish s encodingPrefix o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      (successResult s next r o).1 [] (.revert bytes)=
      (⟨⟨s,r⟩,encodingPrefix⟩,⟨⟨s.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) := by
  have res:=residualRollback_run r [plan.packed.residualUpdate]
  simp only [residualRun] at res
  have enc:=boolEncodingRollback_run encodingPrefix
    (encodingWrites (selectedSlotPaths (registry request.address) request.slot) false request.address (fun _=>request.raw) encodingPrefix)
  change boolEncodingRollback encodingPrefix.journal.length (requestEncoding (E:=env) registry registry request encodingPrefix)=encodingPrefix at enc
  have comp : companionRollback (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      (⟨(next.apply (writeOp CallerFrameChecks.receiver)),residualWrite r plan.packed.residualUpdate⟩ : ResidualCompanion env.layout env.lay env.lay complementCarrierOwnership)=⟨s.2.ex,r⟩ := by
    change (⟨(next.apply (writeOp CallerFrameChecks.receiver)).undoN
      ((next.apply (writeOp CallerFrameChecks.receiver)).journal.length-s.2.ex.journal.length),
      residualRollback r.journal.length (residualWrite r plan.packed.residualUpdate)⟩ : ResidualCompanion env.layout env.lay env.lay complementCarrierOwnership)=_
    rw [rollback_write_transfer s.2.ex next transfer,res]
  have src : (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (changed (transferred s next) CallerFrameChecks.receiver)=(.ok (),s) := by
    change ((Except.ok () : Except Source.Halt Unit),(s.1,{s.2 with
      ex:=(next.apply (writeOp CallerFrameChecks.receiver)).undoN ((next.apply (writeOp CallerFrameChecks.receiver)).journal.length-s.2.ex.journal.length)
      logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
    rw [rollback_write_transfer s.2.ex next transfer]
    simp only [Nat.sub_self,List.drop_zero]
  change finish s encodingPrefix o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
    (sourceCarrier s next r) [] (.revert bytes)=_
  have marker : (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G)).source.mark=s.2.ex.journal.length := rfl
  have current : (changed (transferred s next) CallerFrameChecks.receiver).2.ex=next.apply (writeOp CallerFrameChecks.receiver) := rfl
  simp only [finish,sourceCarrier,marker,current,comp,enc,src,rollbackTrace,discardLogs,List.append_nil,returnData]

end Solidity.Yul.World.StateCallPort
