import Solidity.Yul.World.GeneralReturningOutput

/-! Controls instantiate the general adapter, not requested source outcomes.
The main adapter theorems quantify arbitrary caller states, heaps, contexts,
journals and traces; numeric instances here are additional controls only. -/
namespace Solidity.Yul.World.GeneralReturningChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output)
open Solidity.Yul.World.GeneralReturning

def extraLog : Log := ⟨CallerFrameChecks.receiver,⟨2,by decide⟩,#v[41,42],[0x80,0x81]⟩
def tracePrefix : List Observation := CallerFrameChecks.callerTrace++[.event (.credit CallerFrameChecks.owner 5),.log extraLog]

def caller (G : Glob env) (ex : ExecState env.layout env.lay env.lay) : EMState env [.bytes .memory,.bytes .memory] :=
  ⟨ReturningCall.locals,{(ReturningCall.caller G).2 with ex:=ex,events:=interactionEvents tracePrefix}⟩
def observed (ex : ExecState env.layout env.lay env.lay) : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨ex,committedLogs tracePrefix,[9,8,7,6]⟩,tracePrefix,rfl⟩
def result (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :=
  successResult (caller G ex) next CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)

def run (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :=
  call (CallerFrame.liftInvoke (ReturningCall.invoke G)) (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
    (observed ex) rfl (ReturningCall.memory G) (ReturningCall.parent (caller G ex))
    .call CallerFrameChecks.receiver 10000 7 160 4

/-- Arbitrary execution state, real two-object source heap. The actual encoder
and placement discharge the input coupling; no fixed entryExecution premise. -/
theorem encoded_call (G : Glob env) (ex next : ExecState env.layout env.lay env.lay)
    (code : (ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    run G ex=some (.ok (.success output),result G ex next) :=
  call_actual G (caller G ex) next code transfer CallerFrameChecks.residual CallerFrameChecks.encoding
    (observed ex) rfl (ReturningCall.memory G) 10000 160 4 (ReturningCall.input_load G)

/-- The encoded view used above is about this caller's actual heap, unchanged
by the arbitrary execution prefix. Header and exact payload are constructive. -/
theorem input_coupling (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    (ReturningCall.inputEntry G).Reads (ReturningCall.placement G) (ReturningCall.memory G) ∧
    (caller G ex).2.heap=(ReturningCall.heap G) := ⟨ReturningCall.input_reads G,rfl⟩

theorem caller_memOK (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    Source.MemOK env (ReturningCall.heap G).ty (caller G ex) := by
  have ok := ReturningCall.owner_memOK G
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2⟩

def copiedState (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :=
  withSourceHeap (after (caller G ex) next) (ReturningCall.copiedHeap G)

theorem copy_output (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    copyOutput (result G ex next) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 2=
      (result G ex next,some ((ReturningCall.copiedMemory G,copiedState G ex next),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G ex next).2)) := by
  have actual := output_encoded (caller G ex) next CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)
    (ReturningCall.placement G) (ReturningCall.entries G) (ReturningCall.distinct G) (ReturningCall.outputEntry G)
    (List.mem_cons_of_mem _ List.mem_cons_self) ReturningCall.reserved 1 2
    (by change 1+min 2 output.length≤ReturningCall.old.length; rw [ReturningCall.output_length]; decide)
  simpa only [ReturningCall.outputEntry,ReturningCall.output_prefix] using actual

theorem copy_state (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    HeapWindow.copyStateWindow (result G ex next).2.effects (after (caller G ex) next)
      (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 0 2=
      some (ReturningCall.copiedMemory G,copiedState G ex next) :=
  HeapWindow.copyStateWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ 1 0 2
    (by change returnWindow output 0 2=some [0x11,0x22]; rw [ReturningCall.output_exact]; decide)
    (by decide) (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2

theorem copy_memOK (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    Source.MemOK env (ReturningCall.heap G).ty (copiedState G ex next) :=
  output_memOK _ (caller G ex) next CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)
    _ 1 false ReturningCall.old rfl _ _ 1 0 2 _ (copy_state G ex next) (caller_memOK G ex)

theorem copied_aliases (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G ex next).1.get .here))).run (copiedState G ex next)=
      (.ok ReturningCall.copiedBytes,copiedState G ex next) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G ex next).2.fnLocals.2.get .here))).run (copiedState G ex next)=
      (.ok ReturningCall.copiedBytes,copiedState G ex next) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G ex next).1.get (.there .here)))).run (copiedState G ex next)=
      (.ok (input G),copiedState G ex next) := ⟨rfl,rfl,rfl⟩

theorem complete_trace (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    (result G ex next).2.trace=[.event (.credit CallerFrameChecks.receiver 2),.log CallerFrameChecks.log,
      .event (.credit CallerFrameChecks.owner 5),.log extraLog] ∧
    (copiedState G ex next).2.events=interactionEvents tracePrefix ∧
    (copiedState G ex next).2.logs=(ReturningCall.caller G).2.logs ∧
    (result G ex next).1.1.2=CallerFrameChecks.residual ∧ (result G ex next).1.2=CallerFrameChecks.encoding :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem raw_copy_frame (G : Glob env) :
    readBytes (ReturningCall.copiedMemory G) 288 6=ReturningCall.copiedBytes ∧
    (mload (ReturningCall.copiedMemory G) 256).val=6 ∧
    ReturningCall.copiedBytes.drop 3=ReturningCall.old.drop 3 ∧
    (ReturningCall.inputEntry G).Reads (ReturningCall.placement G) (ReturningCall.copiedMemory G) :=
  ⟨ReturningCall.copied_payload G,ReturningCall.copied_header G,ReturningCall.exact_untouched_suffix.1,
    ReturningCall.input_entry_after_copy G⟩

theorem prefixed_call (G : Glob env) :
    run G SourceBoundaryRules.prefixedExecution=some (.ok (.success output),
      result G SourceBoundaryRules.prefixedExecution SourceBoundaryRules.prefixedMoved) :=
  encoded_call G _ _ rfl rfl

theorem nonempty_prefixes : SourceBoundaryRules.prefixedExecution.journal.length=4 ∧
    SourceBoundaryRules.prefixedMoved.journal.length=6 ∧ CallerFrameChecks.residual.journal.length=1 ∧
    CallerFrameChecks.encoding.journal.length=1 ∧ tracePrefix.length=4 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem refused_call (G : Glob env) (ex : ExecState env.layout env.lay env.lay)
    (code : (ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none) :
    run G ex=some (.ok (.revert []),refusedResult (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)) :=
  call_refused G (caller G ex) code transfer _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem insufficient_call (G : Glob env) :
    run G SourceBoundaryRules.insufficientExecution=some (.ok (.revert []),
      refusedResult (caller G SourceBoundaryRules.insufficientExecution) CallerFrameChecks.residual CallerFrameChecks.encoding
        (observed SourceBoundaryRules.insufficientExecution)) := refused_call G _ rfl rfl

theorem overflow_call (G : Glob env) :
    run G SourceBoundaryRules.overflowExecution=some (.ok (.revert []),
      refusedResult (caller G SourceBoundaryRules.overflowExecution) CallerFrameChecks.residual CallerFrameChecks.encoding
        (observed SourceBoundaryRules.overflowExecution)) := refused_call G _ rfl rfl

theorem refused_copy (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    copyOutput (refusedResult (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)) rfl
      (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 2=
      (refusedResult (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex),
        some ((ReturningCall.memory G,caller G ex),(CallerFrameChecks.residual,CallerFrameChecks.encoding),
          (refusedResult (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding (observed ex)).2)) :=
  refused_output _ _ _ _ _ 1 false ReturningCall.old rfl _ 1 2 (by decide)
    (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2

theorem timeout_call (G : Glob env) (ex next : ExecState env.layout env.lay env.lay)
    (code : (ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeAt 6 G)) (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed ex) rfl (ReturningCall.memory G) (ReturningCall.parent (caller G ex))
      .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending (observed ex) ⟨⟨after (caller G ex) next,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []) :=
  call_timeout G (caller G ex) next code transfer _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

theorem prefixed_timeout (G : Glob env) :
    call (CallerFrame.liftInvoke (ReturningCall.invokeAt 6 G)) (caller G SourceBoundaryRules.prefixedExecution)
      CallerFrameChecks.residual CallerFrameChecks.encoding (observed SourceBoundaryRules.prefixedExecution) rfl
      (ReturningCall.memory G) (ReturningCall.parent (caller G SourceBoundaryRules.prefixedExecution))
      .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending (observed SourceBoundaryRules.prefixedExecution)
        ⟨⟨after (caller G SourceBoundaryRules.prefixedExecution) SourceBoundaryRules.prefixedMoved,CallerFrameChecks.residual⟩,
          CallerFrameChecks.encoding⟩ []) := timeout_call G _ _ rfl rfl

theorem timeout_prefix_buffer (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    (pending (observed ex) ⟨⟨after (caller G ex) next,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []).2.trace=tracePrefix ∧
    (pending (observed ex) ⟨⟨after (caller G ex) next,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []).2.effects.returndata=[9,8,7,6] ∧
    (pending (observed ex) ⟨⟨after (caller G ex) next,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []).1.1.1.2.ex=next := ⟨rfl,rfl,rfl⟩

theorem no_stale_buffer (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    (result G ex next).2.effects.returndata≠[9,8,7,6] := by
  intro same
  have bad : (32 : Nat)=4 := ReturningCall.output_length.symm.trans (congrArg List.length same)
  exact (by decide : (32 : Nat)≠4) bad

theorem wrong_extent (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    copyOutput (result G ex next) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 5 2=
      (result G ex next,none) := copyOutput_refusal _ rfl _ 1 false ReturningCall.old rfl _ 5 2
        (by change ¬(5+min 2 output.length≤ReturningCall.old.length); rw [ReturningCall.output_length]; decide)

theorem invalid_zero (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    copyAfter (result G ex next) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 33 0=
      (result G ex next,none) := GeneralReturning.invalid_zero _ _ _ _ _ _ 1 false ReturningCall.old rfl _ 1

theorem wrong_owner (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (ReturningCall.invoke G) (observed ex)
      (enter (caller G ex) CallerFrameChecks.residual {ReturningCall.parent (caller G ex) with this:=CallerFrameChecks.target}
        .call CallerFrameChecks.receiver 7 (input G)) .call CallerFrameChecks.receiver 10000 (input G)
      ⟨⟨caller G ex,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem static_call_general (G : Glob env) (ex next : ExecState env.layout env.lay env.lay)
    (code : (ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next) :
    call (CallerFrame.liftInvoke (ReturningStatic.invoke G)) (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed ex) rfl (ReturningCall.memory G) (ReturningCall.parent (caller G ex))
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=some (.ok (.success output),result G ex next) :=
  static_call G (caller G ex) next code transfer _ _ _ rfl _ 10000 160 4 (ReturningCall.input_load G)

def staticPrefixed := (SourceBoundaryRules.prefixedExecution.apply
  (.account CallerFrameChecks.owner (fun a=>a.withBalance 11))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 23))

theorem static_prefixed_call (G : Glob env) :
    call (CallerFrame.liftInvoke (ReturningStatic.invoke G)) (caller G SourceBoundaryRules.prefixedExecution)
      CallerFrameChecks.residual CallerFrameChecks.encoding (observed SourceBoundaryRules.prefixedExecution) rfl
      (ReturningCall.memory G) (ReturningCall.parent (caller G SourceBoundaryRules.prefixedExecution))
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=
      some (.ok (.success output),result G SourceBoundaryRules.prefixedExecution staticPrefixed) :=
  static_call_general G _ _ rfl rfl

theorem static_journal_prefix : staticPrefixed.journal.drop 2=SourceBoundaryRules.prefixedExecution.journal ∧
    staticPrefixed.journal.length=6 ∧ (staticPrefixed.world.accounts CallerFrameChecks.owner).balance.val=11 ∧
    (staticPrefixed.world.accounts CallerFrameChecks.receiver).balance.val=23 := ⟨rfl,rfl,rfl,rfl⟩

theorem prefixed_enclosing_revert (G : Glob env) :
    finish (caller G SourceBoundaryRules.prefixedExecution) CallerFrameChecks.encoding (observed SourceBoundaryRules.prefixedExecution)
      (enter (caller G SourceBoundaryRules.prefixedExecution) CallerFrameChecks.residual
        (ReturningCall.parent (caller G SourceBoundaryRules.prefixedExecution)) .call CallerFrameChecks.receiver 7 (input G))
      (result G SourceBoundaryRules.prefixedExecution SourceBoundaryRules.prefixedMoved).1 [] (.revert [0xee])=
      (⟨⟨caller G SourceBoundaryRules.prefixedExecution,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨SourceBoundaryRules.prefixedExecution,committedLogs tracePrefix,[0xee]⟩,tracePrefix,rfl⟩) :=
  enclosing_revert G (caller G SourceBoundaryRules.prefixedExecution) SourceBoundaryRules.prefixedMoved rfl _ _ _ [0xee]

theorem end_zero_copy (G : Glob env) (ex next : ExecState env.layout env.lay env.lay) :
    copyAfter (result G ex next) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 6 32 0=
      (result G ex next,some ((ReturningCall.memory G,after (caller G ex) next),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G ex next).2)) :=
  end_zero _ _ _ _ _ _ 1 false ReturningCall.old rfl _ 6 (by decide)
    (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2

theorem static_value_refused (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed ex) rfl (ReturningCall.memory G) {ReturningCall.parent (caller G ex) with static:=true}
      .call CallerFrameChecks.receiver 10000 7 160 4=none :=
  call_static_value_refusal _ _ _ _ _ rfl _ _ _ _ _ _ _ rfl (by decide)

theorem input_bounds_refused (G : Glob env) (ex : ExecState env.layout env.lay env.lay) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) (caller G ex) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed ex) rfl (ReturningCall.memory G) (ReturningCall.parent (caller G ex))
      .call CallerFrameChecks.receiver 10000 7 ⟨2^256-1,by decide⟩ 2=none := by
  apply input_refused G (caller G ex) _ _ _ rfl
  simp only [PhysicalHeapPort.port,TargetMemory.port,show (2 : Word).val=2 from rfl,
    show ¬((2^256-1)+2≤2^256) from by decide,if_false]

end Solidity.Yul.World.GeneralReturningChecks
