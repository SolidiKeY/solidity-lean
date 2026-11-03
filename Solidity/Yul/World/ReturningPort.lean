import Solidity.Yul.World.ReturningMemory
import Solidity.Yul.World.ReturningFailure

namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def locals : Source.Locals env.layout [.bytes .memory,.bytes .memory] :=
  .cons (.memRef rfl 1) (.cons (.memRef rfl 0) .nil)
def caller (G : Glob env) : Source.EMState env [.bytes .memory,.bytes .memory] :=
  ⟨locals,⟨entryExecution,heap G,[.credit CallerFrameChecks.receiver 2],[(CallerFrameChecks.owner,[0x70])],
    ⟨[.bytes .memory,.bytes .memory],locals⟩⟩⟩
def observed (_G : Glob env) : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨entryExecution,committedLogs CallerFrameChecks.callerTrace,[9,8,7,6]⟩,CallerFrameChecks.callerTrace,rfl⟩
def parent {Γ} (s : Source.EMState env Γ) := s.2.ex.enter CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false

/-- Packing alone is not an observation-adequacy theorem. All Source state
(including legacy logs) is retained; the event suffix is adequate here only for
the two selected templates whose actual proofs preserve logs and physical banks. -/
def pack (c : Carrier env []) (run : Except Halt Outcome × Source.EMState env []) :=
  ((run.1,(⟨⟨run.2,c.1.2⟩,c.2⟩ : Carrier env [])),
    (run.2.2.events.drop c.1.1.2.events.length).map Observation.event)

def template (failed : Bool) (G : Glob env) : Glob env := if failed then failingGlob G else glob G

/-- Restricted to the proved returning/custom-error programs, never an adapter
for an arbitrary log-emitting or represented-storage-writing source body. -/
def invokeTemplateAt (horizon : Nat) (failed : Bool) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .call =>
      if decide (target=CallerFrameChecks.receiver) &&
          !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
          decide (frame.source.value.val=7) && !frame.source.static &&
          decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        some (pack c ((Source.callAddr (template failed G) parentFrame horizon target frame.source.value bytes false).run c.1.1))
      else none
    | .staticcall | .delegatecall => none

def invokeAt (horizon : Nat) (G : Glob env) : Invoke env [] := invokeTemplateAt horizon false G
def invoke (G : Glob env) : Invoke env [] := invokeAt 10 G

theorem invoke_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  have ran := source_run G (⟨l,⟨entryExecution,h,events,logs,fn⟩⟩ : Source.EMState env []) rfl
  unfold invoke invokeAt invokeTemplateAt template
  change some (pack ⟨⟨(l,⟨entryExecution,h,events,logs,fn⟩),r⟩,b⟩
    ((Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run
      (l,⟨entryExecution,h,events,logs,fn⟩)))=_
  rw [ran]
  simp only [pack,after,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩ (.ok (.success output))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : Source.EMState env []),r⟩,b⟩ [] (invoke_empty G ⟨Source.L0 env,s.2⟩ entry r b o)

def result (G : Glob env) : Result env [.bytes .memory,.bytes .memory] :=
  (⟨⟨after (caller G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨moved,committedLogs (observed G).trace,output⟩,(observed G).trace,rfl⟩)

theorem call_actual (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke G)) (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed G) rfl (memory G) (parent (caller G)) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.ok (.success output),result G) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (input_load G)
    (invoke_actual G (caller G) rfl _ _ (observed G))]
  simp only [finish_success,List.append_nil,result,after]

theorem full_frame (G : Glob env) :
    (result G).1.1.1.1=(caller G).1 ∧ (result G).1.1.1.2.heap=(caller G).2.heap ∧
    (result G).1.1.1.2.fnLocals=(caller G).2.fnLocals ∧ (result G).1.1.1.2.events=(caller G).2.events ∧
    (result G).1.1.1.2.logs=(caller G).2.logs ∧ (result G).1.1.2=CallerFrameChecks.residual ∧
    (result G).1.2=CallerFrameChecks.encoding ∧ (result G).2.trace=(observed G).trace ∧
    (result G).2.effects.returndata=output := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.World.ReturningCall
