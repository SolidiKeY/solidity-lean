import Solidity.Yul.World.ReturningCopy
import Solidity.Yul.World.ReturningFailure

namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Outcome Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def invokeFailure (G : Glob env) : Invoke env [] := invokeTemplateAt 10 true G

theorem failure_invoke_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invokeFailure G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  have ran := failure_source G (⟨l,⟨entryExecution,h,events,logs,fn⟩⟩ : Source.EMState env []) rfl
  unfold invokeFailure invokeTemplateAt template
  change some (pack ⟨⟨(l,⟨entryExecution,h,events,logs,fn⟩),r⟩,b⟩
    ((Source.callAddr (failingGlob G) parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run
      (l,⟨entryExecution,h,events,logs,fn⟩)))=_
  rw [ran]
  simp only [pack,List.drop_length,List.map_nil]

theorem failure_invoke_actual (G : Glob env) :
    CallerFrame.liftInvoke (invokeFailure G) (observed G)
      (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=
      some ((.ok (.revert (errorData G)),⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),[]) :=
  CallerFrame.liftInvoke_exact (invokeFailure G) (observed G)
    (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
    (.ok (.revert (errorData G))) ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []
    (failure_invoke_empty G ⟨Source.L0 env,(caller G).2⟩ rfl _ _ (observed G))

def failureResult (G : Glob env) : Result env [.bytes .memory,.bytes .memory] :=
  (⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨entryExecution,committedLogs (observed G).trace,errorData G⟩,(observed G).trace,rfl⟩)

theorem failure_finish (G : Glob env) :
    finish (caller G) CallerFrameChecks.encoding (observed G)
      (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      ⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] (.revert (errorData G))=failureResult G := by
  have clean := finish_runs_revert (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding (observed G)
    [] [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] (errorData G)
  simpa only [Source.ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using clean

theorem failure_call (G : Glob env) :
    call (CallerFrame.liftInvoke (invokeFailure G)) (caller G) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed G) rfl (memory G) (parent (caller G)) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.ok (.revert (errorData G)),failureResult G) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (input_load G) (failure_invoke_actual G),failure_finish]

theorem error_length (G : Glob env) : (errorData G).length=36 := by
  simp only [errorData,List.length_append,Glob.selector,List.length_take,wordBytes_length,output_length]
  rfl

theorem window_after_prefix (leading trailing : Bytes) (n : Nat) (bound : n≤trailing.length) :
    returnWindow (leading++trailing) leading.length n=some (trailing.take n) := by
  simp only [returnWindow,List.length_append,Nat.add_le_add_iff_left,bound,if_true,List.drop_left]

theorem error_window (G : Glob env) : returnWindow (errorData G) 4 2=some [0x11,0x22] := by
  have len : ((glob G).selector (sigOf env.layout "Denied" [uint])).length=4 := by
    simp only [Glob.selector,List.length_take,wordBytes_length]; rfl
  have actual : returnWindow (errorData G) 4 2=some (callOutput output 2) := by
    simpa only [len] using window_after_prefix ((glob G).selector (sigOf env.layout "Denied" [uint])) output 2
      (by rw [output_length]; decide)
  exact actual.trans (congrArg some output_prefix)

theorem failure_copy (G : Glob env) :
    copyAfter (failureResult G) rfl (placement G) 1 false old rfl (memory G) 1 4 2=
      (failureResult G,some ((copiedMemory G,withSourceHeap (caller G) (copiedHeap G)),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(failureResult G).2)) :=
  congrArg (fun x=>(failureResult G,x))
    (HeapWindow.copyCoupledWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ _ rfl _ 1 4 2
      (error_window G) (by decide) (output_reads G).1 (output_reads G).2)

end Solidity.Yul.World.ReturningCall
