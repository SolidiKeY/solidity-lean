import Solidity.Yul.World.StateCallChecks
import Solidity.Yul.World.StateCallHalts

namespace Solidity.Yul.World.StateCallExtra
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical
open Solidity.Yul.World.StateCallPort

/-- Actual shorter Source horizon, proved below to stop before assignment. -/
def lowInvoke (failed : Bool) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
  | .call =>
    if decide (target=CallerFrameChecks.receiver) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
      decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
      decide (frame.source.value.val=7) && !frame.source.static &&
      decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
      some (staticPack c ((Source.callAddr (glob failed G) ReturningCall.parentFrame 6 target 7 bytes false).run c.1.1))
    else none
  | .staticcall | .delegatecall => none

theorem low_empty (failed : Bool) (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    lowInvoke failed G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.error .timeout,⟨⟨transferred s next,r⟩,b⟩),[]) := by
  unfold lowInvoke
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (staticPack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob failed G) ReturningCall.parentFrame 6
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [code]
  change some (staticPack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob failed G) ReturningCall.parentFrame 6
      CallerFrameChecks.receiver 7 (input G) false).run s))=_
  rw [StateCall.source_timeout failed G s next code transfer]
  simp only [staticPack,transferred,List.drop_length,List.map_nil]

theorem low_actual (failed : Bool) (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (lowInvoke failed G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.error .timeout,⟨⟨transferred s next,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (lowInvoke failed G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.error .timeout)
    ⟨⟨transferred (⟨Source.L0 env,s.2⟩ : EMState env []) next,r⟩,b⟩ [] (low_empty failed G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

theorem low_call (failed : Bool) (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (lowInvoke failed G)) s r b o shared m (parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=
      some (.error .timeout,pending o ⟨⟨transferred s next,r⟩,b⟩ []) :=
  call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (low_actual failed G s next code transfer r b o gas)

theorem low_witness (failed : Bool) (G : Glob env) :
    call (CallerFrame.liftInvoke (lowInvoke failed G)) (StateCallChecks.caller G) StateCallChecks.residual encodingPrefix StateCallChecks.observed rfl
      (StateCallChecks.memory G) (parent (StateCallChecks.caller G)) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending StateCallChecks.observed
        ⟨⟨transferred (StateCallChecks.caller G) StateCallChecks.moved,StateCallChecks.residual⟩,encodingPrefix⟩ []) :=
  low_call failed G _ StateCallChecks.moved rfl rfl _ _ _ rfl _ 10000 160 4 (StateCallChecks.loaded G)

theorem error_length (G : Glob env) : (StateCall.errorData G).length=36 := by
  simp only [StateCall.errorData,List.length_append,Glob.selector,List.length_take,wordBytes_length,ReturningCall.output_length]
  rfl

theorem error_window (G : Glob env) : returnWindow (StateCall.errorData G) 4 2=some [0x11,0x22] := by
  have len : (G.selector (sigOf env.layout "Denied" [ReturningCall.uint])).length=4 := by
    simp only [Glob.selector,List.length_take,wordBytes_length]; rfl
  have actual:=ReturningCall.window_after_prefix (G.selector (sigOf env.layout "Denied" [ReturningCall.uint])) ReturningCall.output 2
    (by rw [ReturningCall.output_length]; decide)
  simpa only [len,ReturningCall.output_prefix] using actual

theorem source_prefix_journals (G : Glob env) :
    let out:=successResult (StateCallChecks.caller G) StateCallChecks.moved StateCallChecks.residual StateCallChecks.observed
    out.1.1.1.2.ex.journal.drop 3=StateCallChecks.entry.journal ∧
    out.1.1.2.journal.drop 1=StateCallChecks.residual.journal ∧ out.1.2.journal.drop 1=encodingPrefix.journal := ⟨rfl,rfl,rfl⟩

theorem success_full_word (G : Glob env) :
    let out:=successResult (StateCallChecks.caller G) StateCallChecks.moved StateCallChecks.residual StateCallChecks.observed
    reencodePersistentSlot (representedBanks (E:=env) registry false out.1.2)
      ⟨out.2.effects.execution,out.1.1.2⟩ CallerFrameChecks.receiver 7=some request.raw :=
  source_reencode (transferred (StateCallChecks.caller G) StateCallChecks.moved) StateCallChecks.residual
    {StateCallChecks.observed with effects:={StateCallChecks.observed.effects with execution:=StateCallChecks.moved}} rfl

def trueEntry := StateCallChecks.entry.apply (writeOp CallerFrameChecks.receiver)
def trueMoved := (trueEntry.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def trueCaller (G : Glob env) : EMState env [.bytes .memory] := ⟨(StateCallChecks.caller G).1,{(StateCallChecks.caller G).2 with ex:=trueEntry}⟩
def trueObserved : ObservedEffects env.layout env.lay env.lay := {StateCallChecks.observed with effects:={StateCallChecks.observed.effects with execution:=trueEntry}}

theorem dirty_true_input : reencodePersistentSlot (representedBanks (E:=env) registry false encodingPrefix)
    ⟨trueEntry,StateCallChecks.residual⟩ CallerFrameChecks.receiver 7=some 0xaabbcc02 := rfl

theorem dirty_true_success (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke false G)) (trueCaller G) StateCallChecks.residual encodingPrefix trueObserved rfl
      (StateCallChecks.memory G) (parent (trueCaller G)) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.ok (.success ReturningCall.output),successResult (trueCaller G) trueMoved StateCallChecks.residual trueObserved) :=
  call_success G _ trueMoved rfl rfl _ rfl _ rfl _ 10000 160 4 (StateCallChecks.loaded G)

theorem dirty_true_output (G : Glob env) :
    let out:=successResult (trueCaller G) trueMoved StateCallChecks.residual trueObserved
    reencodePersistentSlot (representedBanks (E:=env) registry false out.1.2)
      ⟨out.2.effects.execution,out.1.1.2⟩ CallerFrameChecks.receiver 7=some 0xaabbcc01 :=
  source_reencode (transferred (trueCaller G) trueMoved) StateCallChecks.residual
    {trueObserved with effects:={trueObserved.effects with execution:=trueMoved}} rfl

theorem pending_controls (G : Glob env) :
    let out:=pending StateCallChecks.observed
      (⟨⟨transferred (StateCallChecks.caller G) StateCallChecks.moved,StateCallChecks.residual⟩,encodingPrefix⟩ : Carrier env [.bytes .memory]) []
    out.1.1.1.2.ex.journal.length=6 ∧ out.1.1.2.journal.length=1 ∧ out.1.2.journal.length=1 ∧
      out.2.trace=GeneralReturningChecks.tracePrefix ∧ out.2.effects.returndata=[9,8,7,6] ∧
      (out.1.1.1.2.ex.world.accounts CallerFrameChecks.receiver).storage.read flagPath=some (.bool false) ∧
      out.1.1.1.2.heap=StateCallChecks.heap G ∧ out.1.1.1.2.fnLocals=(StateCallChecks.caller G).2.fnLocals :=
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem success_size (G : Glob env) : returndataSize (successResult (StateCallChecks.caller G) StateCallChecks.moved StateCallChecks.residual StateCallChecks.observed).2.effects=some 32 := by
  have actual:=checkedReturnSize_exact ReturningCall.output (by rw [ReturningCall.output_length]; decide)
  simpa only [ReturningCall.output_length] using actual

theorem revert_size (G : Glob env) : returndataSize (revertResult G (StateCallChecks.caller G) StateCallChecks.residual StateCallChecks.observed).2.effects=some 36 := by
  have actual:=checkedReturnSize_exact (StateCall.errorData G) (by rw [error_length]; decide)
  simpa only [error_length] using actual

end Solidity.Yul.World.StateCallExtra
