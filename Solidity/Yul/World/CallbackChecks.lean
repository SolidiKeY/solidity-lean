import Solidity.Yul.World.Callback

namespace Solidity.Yul.World.CallbackChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.PhysicalCompletion

def suffix (out : Outcome) : List Observation :=
  [.event (.call CallerFrameChecks.target 0 [17,34,51,68] false),
   .event (.reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false),
   .event (.reentered (.revert [])),.event (.answer out none)]
def events (out : Outcome) : List Roadmap.Event := CallerFrameChecks.caller.2.events++
  [.call CallerFrameChecks.target 0 [17,34,51,68] false,
   .reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false,.reentered (.revert []),.answer out none]
def after (out : Outcome) : Source.EMState packedTypedEnv [.bytes .memory] :=
  ⟨CallerFrameChecks.locals,{CallerFrameChecks.caller.2 with events:=events out}⟩
def result (out : Outcome) : Result packedTypedEnv [.bytes .memory] :=
  (⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨CallerFrameChecks.caller.2.ex,committedLogs (CallerFrameChecks.callerTrace++suffix out),returnData out⟩,
      CallerFrameChecks.callerTrace++suffix out,rfl⟩)

theorem actual_callback_dispatch (G : Glob packedTypedEnv) out :
    (Source.dispatch (Callback.callbackGlob G out)
      ⟨CallerFrameChecks.receiver,CallerFrameChecks.target,7,false,"Finite",true,2⟩ 1 []).run
      (Source.L0 packedTypedEnv,{CallerFrameChecks.caller.2 with ex:=CallerFrameChecks.credited,heap:=Source.Heap.empty}) =
      (.error (.revert []),(Source.L0 packedTypedEnv,
        {CallerFrameChecks.caller.2 with ex:=CallerFrameChecks.credited,heap:=Source.Heap.empty})) := rfl

theorem actual_source_run (G : Glob packedTypedEnv) (out : Outcome) :
    (Source.callAddr (Callback.callbackGlob G out)
      ⟨CallerFrameChecks.owner,CallerFrameChecks.owner,0,false,"EnvironmentCallback",true,0⟩ 4
      CallerFrameChecks.target 0 [17,34,51,68] false).run (Source.L0 packedTypedEnv,CallerFrameChecks.caller.2) =
      (.ok out,(Source.L0 packedTypedEnv,(after out).2)) := by
  cases out with
  | success data =>
    change ((Except.ok (Outcome.success data) : Except Halt Outcome),(Source.L0 packedTypedEnv,
      {CallerFrameChecks.caller.2 with ex:=CallerFrameChecks.credited.undo,events:=events (.success data)})) = _
    rw [show CallerFrameChecks.credited.undo=CallerFrameChecks.caller.2.ex from Source.ExecState.undo_apply _ _]
    rfl
  | revert data =>
    change ((Except.ok (Outcome.revert data) : Except Halt Outcome),(Source.L0 packedTypedEnv,
      {CallerFrameChecks.caller.2 with
        ex:=CallerFrameChecks.credited.undo.undoN (CallerFrameChecks.credited.undo.journal.length-CallerFrameChecks.caller.2.ex.journal.length),
        events:=events (.revert data)})) = _
    rw [show CallerFrameChecks.credited.undo=CallerFrameChecks.caller.2.ex from Source.ExecState.undo_apply _ _]
    rfl

theorem invoke_actual (G : Glob packedTypedEnv) out :
    Callback.callerInvoke G out CallerFrameChecks.observed
      (enter CallerFrameChecks.caller CallerFrameChecks.residual CallerFrameChecks.parent .call CallerFrameChecks.target 0 [17,34,51,68])
      .call CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨CallerFrameChecks.caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ =
      some ((.ok out,⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),suffix out) := by
  have ran : Callback.invoke G out CallerFrameChecks.observed
      (enter CallerFrameChecks.caller CallerFrameChecks.residual CallerFrameChecks.parent .call CallerFrameChecks.target 0 [17,34,51,68])
      .call CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨⟨Source.L0 packedTypedEnv,CallerFrameChecks.caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ =
      some ((.ok out,⟨⟨⟨Source.L0 packedTypedEnv,(after out).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),suffix out) := by
    let src := (Source.callAddr (Callback.callbackGlob G out)
      ⟨CallerFrameChecks.owner,CallerFrameChecks.owner,0,false,"EnvironmentCallback",true,0⟩ 4 CallerFrameChecks.target 0 [17,34,51,68] false).run
        (Source.L0 packedTypedEnv,CallerFrameChecks.caller.2)
    change some ((src.1,(⟨⟨src.2,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ : Carrier packedTypedEnv [])),
      (src.2.2.events.drop CallerFrameChecks.caller.2.events.length).map Observation.event) = _
    have actual : src=(.ok out,(Source.L0 packedTypedEnv,(after out).2)) := actual_source_run G out
    rw [actual]
    rfl
  exact CallerFrame.liftInvoke_exact (Callback.invoke G out) CallerFrameChecks.observed
    (enter CallerFrameChecks.caller CallerFrameChecks.residual CallerFrameChecks.parent .call CallerFrameChecks.target 0 [17,34,51,68])
    .call CallerFrameChecks.target 10000 [17,34,51,68]
    ⟨⟨CallerFrameChecks.caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (.ok out)
    ⟨⟨⟨Source.L0 packedTypedEnv,(after out).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (suffix out) ran

theorem completion_actual (out : Outcome) :
    finish CallerFrameChecks.caller CallerFrameChecks.encoding CallerFrameChecks.observed
      (enter CallerFrameChecks.caller CallerFrameChecks.residual CallerFrameChecks.parent .call CallerFrameChecks.target 0 [17,34,51,68])
      ⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (suffix out) out = result out := by
  cases out <;> rfl

theorem call_actual (G : Glob packedTypedEnv) (out : Outcome) :
    call (Callback.callerInvoke G out) CallerFrameChecks.caller CallerFrameChecks.residual CallerFrameChecks.encoding
      CallerFrameChecks.observed rfl PhysicalCompletionChecks.memory CallerFrameChecks.parent .call CallerFrameChecks.target 10000 0 160 4 =
      some (.ok out,result out) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some [17,34,51,68] := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (invoke_actual G out),completion_actual]

theorem frame_and_trace (out : Outcome) :
    (result out).1.1.1.1=CallerFrameChecks.caller.1 ∧ (result out).1.1.1.2.heap=CallerFrameChecks.caller.2.heap ∧
    (result out).1.1.1.2.fnLocals=CallerFrameChecks.caller.2.fnLocals ∧
    (result out).1.1.1.2.logs=CallerFrameChecks.caller.2.logs ∧ (result out).1.1.1.2.ex=CallerFrameChecks.caller.2.ex ∧
    (result out).1.1.1.2.events=events out ∧ (result out).1.1.2=CallerFrameChecks.residual ∧
    (result out).1.2=CallerFrameChecks.encoding ∧ (result out).2.trace=CallerFrameChecks.callerTrace++suffix out ∧
    (result out).2.effects.returndata=returnData out := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.World.CallbackChecks
