import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarLoop

/-! One populated target image performs allocating descent and scalar return.
The saved history is obtained from the actual descent, not supplied as an
independent return premise. This is not general recursive compiler selection
or source/target adequacy. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedExecution
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open ScalarAllocatingDescent

def image : List Instr := ScalarAllocatingDescent.Controls.setupCode ++ ScalarAllocatingDescent.Controls.loopCode ++ FullScalarLoop.code (C:=C) 2 8 7 F

theorem complete :
 ∃ (τ : State C (Frame A)) (e : ScalarAllocatingDescent.Controls.σ.H <+: τ.H) (down last : Machine) (addresses : Nat → Fin W),
 run image AllocatorReturn.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F (FullScalarLoop.returned τ 0 2 (by decide)) addresses last ∧
 Heap.Keeps e ScalarAllocatingDescent.Controls.σ.heap τ.heap ∧
 StructAllocatorRepr (FullScalarLoop.returned τ 0 2 (by decide)).heap addresses 16
   (⟨30,by decide⟩ : Fin W) last ∧
 loopIterN (run (FullScalarLoop.condition 8 7)) (run (FullScalarUnwind.code (C:=C) 2 8 F)) 2 down=.inl last ∧
 loopIterN (run (FullScalarLoop.condition 8 7)) (run (FullScalarUnwind.code (C:=C) 2 8 F)) 3 down=.inr (.ok last 0) ∧
 last.stack=[w[77]] ∧ last.mem 0=w[30] ∧ last.mem 8=w[10] ∧ last.mem 2=w[16] ∧
 last.mem 7=w[10] ∧ last.mem 9=w[99] ∧
 last.mem 11=w[2] ∧ last.mem 14=w[1] ∧ last.mem 4=w[2] ∧
 last.mem 0≠w[34] ∧ last.mem 8≠w[16] ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) (FullScalarLoop.returned τ 0 2 (by decide)).env=countValue 2 (by decide) := by
 obtain ⟨τ,e,down,addresses,setup,running,repr,environment,size,kept,owner,extended,history,obs⟩ := ScalarAllocatingDescent.Controls.available 2 (by decide)
 have result : TEnv.get (.here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [environment];rfl
 have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [environment];rfl
 have stopped := GuardedPrefixes.finish_prefix _ _ 2 ScalarAllocatingDescent.Controls.input down (.ok down 0) running
   (zero_turn τ counter addresses down repr 8)
 have descend : run ScalarAllocatingDescent.Controls.loopCode ScalarAllocatingDescent.Controls.input=.ok down 0 :=
   GuardedRecursion.successful_loop guardCompiled.code (AllocatingScalarTurn.code 8) ScalarAllocatingDescent.Controls.input down 3 stopped
 have position : down.mem 8=w[16] := congrArg (fun t : List Word × List Word => t.2[5]!) obs
 have bottom : down.mem 7=w[10] := congrArg (fun t : List Word × List Word => t.2[4]!) obs
 have reference : down.mem 2=w[16] := congrArg (fun t : List Word × List Word => t.2[1]!) obs
 have saved : ∀ j,j<2 → down.mem (10+3*j)=down.mem 2 ∧ down.mem (10+3*j+1)=.val (wmod (0+2-j)) := by
   intro j small
   exact ⟨(history j small).1.trans reference.symm,(history j small).2.1⟩
 obtain ⟨last,returns,done,lastRepr,growth,stack,pointer,refWord,outside⟩ :=
   FullScalarLoop.iter 2 0 τ addresses down repr (by decide) result 8 8 7 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) position bottom saved
 have returnRun := FullScalarLoop.run_of_stopped done
 have prefixRun : run (ScalarAllocatingDescent.Controls.setupCode ++ ScalarAllocatingDescent.Controls.loopCode) AllocatorReturn.Checks.input=.ok down 0 :=
   (run_append_ok setup).trans descend
 have actual : run image AllocatorReturn.Checks.input=.ok last 0 :=
   (run_append_ok prefixRun).trans returnRun
 have lastOwner := growth (⟨30,by decide⟩ : Fin W) (by decide) owner (by decide)
 have stack0 : down.stack=[w[77]] := congrArg (fun t : List Word × List Word => t.1) obs
 have cursor : down.mem 0=w[30] := congrArg (fun t : List Word × List Word => t.2[0]!) obs
 have sentinel : down.mem 9=w[99] := congrArg (fun t : List Word × List Word => t.2[6]!) obs
 refine ⟨τ,e,down,last,addresses,actual,lastRepr,kept,lastOwner,returns,done,
   stack.trans stack0,?_,pointer,refWord.trans reference,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (outside 0 (by decide) (by decide) (by decide) (by decide)).trans cursor
 · exact (outside 7 (by decide) (by decide) (by decide) (by decide)).trans bottom
 · exact (outside 9 (by decide) (by decide) (by decide) (by decide)).trans sentinel
 · exact (outside 11 (by decide) (by decide) (by decide) (by decide)).trans (history 0 (by decide)).2.1
 · exact (outside 14 (by decide) (by decide) (by decide) (by decide)).trans (history 1 (by decide)).2.1
 · exact Restore.uint_unique (lastRepr.core.vals (.here : Idx (Frame A) (.val .uint))) (ReprV.uint_of rfl)
 · rw [(outside 0 (by decide) (by decide) (by decide) (by decide)).trans cursor];decide
 · rw [pointer];decide
 · rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedExecution

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedExecution.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedExecution.complete
