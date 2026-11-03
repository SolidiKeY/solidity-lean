import Solidity.Yul.World.KnownStatic

/-! Actual selected CALL then STATICCALL, followed by a separately stated
journal/frame rollback. No outer source-statement reachability is assumed. -/
namespace Solidity.Yul.World.KnownSequence
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.KnownCall (glob parentFrame input caller observed parent moved entryExecution)
open Solidity.Yul.World.CallbackSuccess (env)

def afterBoth := (moved.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def state : Source.EMState env [.bytes .memory] := ⟨caller.1,{caller.2 with ex:=afterBoth}⟩
def callObserved := (KnownCall.result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed).2

theorem second_source (G : Glob env) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 input true).run
      (Source.L0 env,(KnownCall.after caller).2)=(.ok (.success []),(Source.L0 env,state.2)) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem second_invoke (G : Glob env) :
    CallerFrame.liftInvoke (KnownStatic.invoke G) callObserved
      (enter (KnownCall.after caller) CallerFrameChecks.residual (parent (KnownCall.after caller)) .staticcall CallerFrameChecks.receiver 0 input)
      .staticcall CallerFrameChecks.receiver 10000 input
      ⟨⟨KnownCall.after caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=
      some ((.ok (.success []),⟨⟨state,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),[]) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

def result : Result env [.bytes .memory] :=
  (⟨⟨state,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨afterBoth,committedLogs observed.trace,[]⟩,observed.trace,rfl⟩)

theorem second_call (G : Glob env) :
    call (CallerFrame.liftInvoke (KnownStatic.invoke G)) (KnownCall.after caller)
      CallerFrameChecks.residual CallerFrameChecks.encoding callObserved rfl
      PhysicalCompletionChecks.memory (parent (KnownCall.after caller)) .staticcall CallerFrameChecks.receiver 10000 0 160 4=
      some (.ok (.success []),result) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some input := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (second_invoke G)]
  simp only [finish_success,List.append_nil,result,callObserved,KnownCall.result,state]

/-- Concrete intermediate state supplies the real shared-world equality;
no coherence proof is invented for an arbitrary unindexed Result. -/
theorem sequence (G : Glob env) :
    call (CallerFrame.liftInvoke (KnownCall.invoke G)) caller CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl
      PhysicalCompletionChecks.memory (parent caller) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.ok (.success []),KnownCall.result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed) ∧
    call (CallerFrame.liftInvoke (KnownStatic.invoke G)) (KnownCall.after caller)
      CallerFrameChecks.residual CallerFrameChecks.encoding callObserved rfl
      PhysicalCompletionChecks.memory (parent (KnownCall.after caller)) .staticcall CallerFrameChecks.receiver 10000 0 160 4=
      some (.ok (.success []),result) := ⟨KnownCall.concrete G,second_call G⟩

theorem source_sequence (G : Glob env) :
    ((do
      let first ← Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false
      let second ← Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 input true
      pure (first,second)).run (Source.L0 env,caller.2))=
      (.ok (.success [],.success []),(Source.L0 env,state.2)) := by
  rw [Source.Hoare.run_bind,KnownCall.source_run G _ rfl]
  change ((do
    let second ← Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 input true
    pure (Outcome.success [],second)).run (Source.L0 env,(KnownCall.after caller).2))=_
  rw [Source.Hoare.run_bind,second_source]
  rfl

theorem enclosing_revert : finish caller CallerFrameChecks.encoding observed
    (enter caller CallerFrameChecks.residual (parent caller) .call CallerFrameChecks.receiver 7 input)
    ⟨⟨state,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] (.revert [0xee])=
      (⟨⟨caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨entryExecution,committedLogs observed.trace,[0xee]⟩,observed.trace,rfl⟩) := by
  have undo := finish_runs_revert caller CallerFrameChecks.residual CallerFrameChecks.encoding observed
    [.account CallerFrameChecks.owner (fun a=>a.withBalance 4),.account CallerFrameChecks.receiver (fun a=>a.withBalance 30),
     .account CallerFrameChecks.owner (fun a=>a.withBalance 4),.account CallerFrameChecks.receiver (fun a=>a.withBalance 30)]
    [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 input false [] [0xee]
  simpa only [rollbackTrace,discardLogs,List.append_nil] using undo

theorem complete_prefix : result.1.1.1.1=caller.1 ∧ result.1.1.1.2.heap=caller.2.heap ∧
    result.1.1.1.2.fnLocals=caller.2.fnLocals ∧ result.1.1.1.2.events=caller.2.events ∧
    result.1.1.1.2.logs=caller.2.logs ∧ result.1.1.2=CallerFrameChecks.residual ∧ result.1.2=CallerFrameChecks.encoding ∧
    result.2.trace=observed.trace ∧ result.2.effects.returndata=[] ∧ afterBoth.journal.length=7 ∧
    (afterBoth.world.accounts CallerFrameChecks.owner).balance=4 ∧
    (afterBoth.world.accounts CallerFrameChecks.receiver).balance=30 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.World.KnownSequence
