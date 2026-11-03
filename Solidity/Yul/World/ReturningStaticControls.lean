import Solidity.Yul.World.ReturningStatic
import Solidity.Yul.World.ReturningCopy

/-! Full-carrier and bounded-output controls for the selected source STATICCALL.
No generic source/world or gas adequacy is asserted. -/
namespace Solidity.Yul.World.ReturningStatic
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output entryExecution)
theorem world_unchanged : zeroMoved.world=entryExecution.world := by
  apply congrArg Source.World.mk
  funext a
  by_cases receiver : a=CallerFrameChecks.receiver
  · subst a; rfl
  by_cases owner : a=CallerFrameChecks.owner
  · subst a; rfl
  change ((entryExecution.world.set CallerFrameChecks.owner
    ((entryExecution.world.accounts CallerFrameChecks.owner).withBalance 11)).set CallerFrameChecks.receiver
    (((entryExecution.world.set CallerFrameChecks.owner
      ((entryExecution.world.accounts CallerFrameChecks.owner).withBalance 11)).accounts CallerFrameChecks.receiver).withBalance 23)).accounts a=
    entryExecution.world.accounts a
  rw [Source.World.set_other _ receiver,Source.World.set_other _ owner]

theorem journal_not_unchanged : zeroMoved.journal.length=5 ∧ entryExecution.journal.length=3 ∧
    zeroMoved.journal≠entryExecution.journal := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have impossible : (5 : Nat)=3 := congrArg List.length same
  contradiction


theorem full_frame (G : Glob env) :
    (result G).1.1.1.1=(ReturningCall.caller G).1 ∧
    (result G).1.1.1.2.heap=(ReturningCall.caller G).2.heap ∧
    (result G).1.1.1.2.fnLocals=(ReturningCall.caller G).2.fnLocals ∧
    (result G).1.1.1.2.events=(ReturningCall.caller G).2.events ∧
    (result G).1.1.1.2.logs=(ReturningCall.caller G).2.logs ∧
    (result G).1.1.2=CallerFrameChecks.residual ∧ (result G).1.2=CallerFrameChecks.encoding ∧
    (result G).2.trace=(ReturningCall.observed G).trace ∧ (result G).2.effects.returndata=output :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Generic typed frame projection avoids unfolding the concrete caller heap. -/
theorem child_context_at {Γ} (s : Source.EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (bytes : Roadmap.Bytes) :
    PhysicalSlotPort.sourceFrame (enter s r (ReturningCall.parent s) .staticcall
      CallerFrameChecks.receiver 0 bytes).source "Finite" true 1 = child bytes := rfl

theorem child_context (G : Glob env) :
    PhysicalSlotPort.sourceFrame (enter (ReturningCall.caller G) CallerFrameChecks.residual
      (ReturningCall.parent (ReturningCall.caller G)) .staticcall CallerFrameChecks.receiver 0 (input G)).source "Finite" true 1=child (input G) :=
  child_context_at (ReturningCall.caller G) CallerFrameChecks.residual (input G)

def copiedState (G : Glob env) := withSourceHeap (after (ReturningCall.caller G)) (ReturningCall.copiedHeap G)

theorem copy_output (G : Glob env) :
    copyOutput (result G) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 2=
      (result G,some ((ReturningCall.copiedMemory G,copiedState G),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G).2)) := by
  have actual := copyOutput_exact (result G) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 2
    (by change 1+min 2 output.length≤ReturningCall.old.length; rw [ReturningCall.output_length]; decide)
    (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2
  simpa only [ReturningCall.output_prefix] using actual

theorem copied_full_frame (G : Glob env) :
    (copiedState G).1=(ReturningCall.caller G).1 ∧
    (copiedState G).2.fnLocals=(ReturningCall.caller G).2.fnLocals ∧
    (copiedState G).2.ex=zeroMoved ∧
    (copiedState G).2.events=(ReturningCall.caller G).2.events ∧
    (copiedState G).2.logs=(ReturningCall.caller G).2.logs ∧
    (result G).2.effects.returndata.length=32 :=
  ⟨rfl,rfl,rfl,rfl,rfl,ReturningCall.output_length⟩

theorem copied_aliases (G : Glob env) :
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G).1.get .here))).run (copiedState G)=
      (.ok ReturningCall.copiedBytes,copiedState G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G).2.fnLocals.2.get .here))).run (copiedState G)=
      (.ok ReturningCall.copiedBytes,copiedState G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((copiedState G).1.get (.there .here)))).run (copiedState G)=
      (.ok (input G),copiedState G) := ⟨rfl,rfl,rfl⟩

theorem wrong_extent (G : Glob env) :
    copyOutput (result G) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 5 2=
      (result G,none) := copyOutput_refusal _ rfl _ 1 false ReturningCall.old rfl _ 5 2
        (by change ¬(5+min 2 output.length≤ReturningCall.old.length); rw [ReturningCall.output_length]; decide)

theorem invalid_zero (G : Glob env) :
    copyAfter (result G) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 33 0=
      (result G,none) := copyAfter_bad_source _ rfl _ 1 false ReturningCall.old rfl _ 1 33 0
        (by change output.length<33+0; rw [ReturningCall.output_length]; decide)

theorem nonstatic_frame_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G)) .call CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(ReturningCall.caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl



theorem owner_memOK (G : Glob env) : Source.MemOK env (ReturningCall.heap G).ty (after (ReturningCall.caller G)) := by
  have first : HeapOK (E:=env) (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes (input G)⟩).1 :=
    HeapOK.alloc HeapOK.empty (.bytes (input G))
  have ok : HeapOK (E:=env) (ReturningCall.heap G) := HeapOK.alloc first (.bytes ReturningCall.old)
  have top : HeapShaped (E:=env) (ReturningCall.heap G) := HeapShaped.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes ReturningCall.old⟩)
    (HeapShaped.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapShaped.empty trivial) trivial
  have inner : HeapInner (E:=env) (ReturningCall.heap G) := HeapInner.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes ReturningCall.old⟩)
    (HeapInner.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapInner.empty trivial) trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩,top,inner⟩


theorem copy_state (G : Glob env) :
    HeapWindow.copyStateWindow (result G).2.effects (after (ReturningCall.caller G))
      (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 1 0 2=
      some (ReturningCall.copiedMemory G,copiedState G) :=
  HeapWindow.copyStateWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ 1 0 2
    (by change returnWindow output 0 2=some [0x11,0x22]; rw [ReturningCall.output_exact]; decide)
    (by decide) (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2

theorem copied_memOK (G : Glob env) : Source.MemOK env (ReturningCall.heap G).ty (copiedState G) :=
  HeapWindow.copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ (copy_state G) (owner_memOK G)

theorem no_stale_buffer (G : Glob env) : (result G).2.effects.returndata≠[9,8,7,6] := by
  intro stale
  have length : (32 : Nat)=4 := ReturningCall.output_length.symm.trans (congrArg List.length stale)
  exact (by decide : (32 : Nat)≠4) length

theorem end_zero_copy (G : Glob env) :
    copyAfter (result G) rfl (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 6 32 0=
      (result G,some ((ReturningCall.memory G,after (ReturningCall.caller G)),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G).2)) := by
  have zero : HeapWindow.copyHeapWindow (result G).2.effects (result G).1.1.1.2.heap
      (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 6 32 0=
      some (ReturningCall.memory G,(result G).1.1.1.2.heap) :=
    HeapWindow.copyHeapWindow_zero (result G).2.effects (result G).1.1.1.2.heap
      (ReturningCall.placement G) 1 false ReturningCall.old rfl (ReturningCall.memory G) 6 32
      (by change 32≤output.length; rw [ReturningCall.output_length]; exact Nat.le_refl _)
      (by decide) (ReturningCall.output_reads G).1 (ReturningCall.output_reads G).2
  unfold copyAfter HeapWindow.copyCoupledWindow
  rw [HeapWindow.copyStateWindow_heap,zero]
  simp only [Option.map_some,withSourceHeap_unchanged]
  rfl

theorem wrong_context_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (enter (ReturningCall.caller G) CallerFrameChecks.residual {ReturningCall.parent (ReturningCall.caller G) with this:=CallerFrameChecks.target} .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(ReturningCall.caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem wrong_value_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (let f := enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G)) .staticcall CallerFrameChecks.receiver 0 (input G);
      {f with source := {f.source with value:=1}})
    .staticcall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(ReturningCall.caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem wrong_kind_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G)) .staticcall CallerFrameChecks.receiver 0 (input G))
    .delegatecall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(ReturningCall.caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem precompile_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G)) .staticcall (⟨2,by decide⟩ : Solidity.Roadmap.Address) 0 (input G))
    .staticcall (⟨2,by decide⟩ : Solidity.Roadmap.Address) 10000 (input G)
    ⟨⟨⟨Source.L0 env,(ReturningCall.caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem unregistered_refusal (G : Glob env) : invoke G (ReturningCall.observed G)
    (enter (ReturningCall.unregistered G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.unregistered G))
      .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨(ReturningCall.unregistered G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

/-- STATICCALL entry fixes value to zero; supplying another nominal value to
`enter` does not construct a nonzero child. The malformed-frame test above
therefore changes the actual frame field explicitly. -/
theorem static_entry_zero (G : Glob env) :
    (enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G))
      .staticcall CallerFrameChecks.receiver 1 (input G)).source.value=0 := rfl

/-- Actual source no-op transfer journal is undone at an enclosing boundary;
the caller output heap is retained by the existing rollbackTo policy. This
is a frame boundary, not a claim of an executed outer Yul revert statement. -/
theorem enclosing_revert (G : Glob env) :
    finish (ReturningCall.caller G) CallerFrameChecks.encoding (ReturningCall.observed G)
      (enter (ReturningCall.caller G) CallerFrameChecks.residual (ReturningCall.parent (ReturningCall.caller G))
        .staticcall CallerFrameChecks.receiver 0 (input G))
      ⟨⟨copiedState G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] (.revert [0xee])=
      (⟨⟨withSourceHeap (ReturningCall.caller G) (ReturningCall.copiedHeap G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨entryExecution,committedLogs (ReturningCall.observed G).trace,[0xee]⟩,(ReturningCall.observed G).trace,rfl⟩) := by
  have rollback := finish_runs_revert (withSourceHeap (ReturningCall.caller G) (ReturningCall.copiedHeap G)) CallerFrameChecks.residual
    CallerFrameChecks.encoding (ReturningCall.observed G)
    [.account CallerFrameChecks.owner (fun a=>a.withBalance 11),.account CallerFrameChecks.receiver (fun a=>a.withBalance 23)]
    [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 0 (input G) true [] [0xee]
  simpa only [Source.ExecState.run,rollbackTrace,discardLogs,List.append_nil] using rollback

end Solidity.Yul.World.ReturningStatic
