import Solidity.Backend.InternalFlow.RuntimeFrameV3OuterScalarRestore
import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeReturnRepresentation
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn

/-! An inhabited outer call: actual arguments, full caller capture, checked
entry, allocating native body and scalar return. This explicit image is not
claimed as public general recursive compiler selection or profile closure. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OuterAllocatingCall
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev σ := ScalarAllocatingDescent.Controls.σ
abbrev input := ScalarAllocatingDescent.Controls.input

def image : List Instr :=
 (((Restore.saveCells 8 (Restore.contextCells 2 (Frame A)) ++ AllocatingScalarEntry.code (C:=C) 2 F) ++
 [.mload 8,.mstore 7]) ++ ScalarPairedTransport.image guardCompiled 8 7) ++ OuterScalarRestore.code (R:=A) 2 8

def source : Stmt C (Frame A) (Frame A) :=
 InterfaceV1.recursiveSource "outerAllocating" (next A (by rfl)) (result A) (AllocatingScalarSource.step A (by rfl)) 2

theorem complete : ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 source.run σ=.ok out ∧ run image input=.ok last 0 ∧ StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8,last.mem 9])=
 ([w[77]],[w[26],w[16],w[2],w[1],w[10],w[99]]) ∧
 last.mem 4≠w[2] ∧ run image input≠.revert := by
 have repr : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr σ.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨saved,savedRun,captured,savedRepr,captureGrowth⟩ :=
   Context.capture_context (σ:=σ) (F:=F) (base:=CountdownWitness.P.base) input 8 8 10 repr
     (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) rfl
 have entry := AllocatingScalarEntry.entry (by rfl) σ 1 (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base saved savedRepr
 let child := entered σ 1 (by decide) CountdownWitness.P.r0
 let active := AllocatingScalarEntry.childMachine (R:=A) 2 saved 1 (by decide)
 let prepared := writeMachine active 7 w[13]
 have savedPointer : saved.mem 8=w[13] := captured.cursor
 have activePointer : active.mem 8=w[13] := by
   change saved.mem 8=w[13]
   exact savedPointer
 have preparedRun : run [.mload 8,.mstore 7] active=.ok prepared 0 := by
   change Out.ok (writeMachine active 7 (active.mem 8)) 0=_
   rw [activePointer]
 have preparedRepr : StateRepr 1 2 16 F child CountdownWitness.P.base prepared :=
   reserved_write entry.2.1 7 (by decide) (by decide) w[13]
 have savedOwner := captureGrowth (⟨22,by decide⟩ : Fin W) (by decide) owned (by decide)
 have activeOwner : StructAllocatorRepr child.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) active :=
   (savedOwner.localWrite 3 (by decide) (by decide) w[1]).localWrite 4 (by decide) (by decide) w[0]
 have preparedOwner : StructAllocatorRepr child.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) prepared :=
   activeOwner.localWrite 7 (by decide) (by decide) w[13]
 have preparedPointer : prepared.mem 8=w[13] := by
   change active.mem 8=w[13]
   exact activePointer
 obtain ⟨bodyOut,after,addresses,bodySource,bodyRun,bodyRepr,bodyKept,extended,bodyGrowth,bodyOwner,bodyStack,bodyPointer,bodyRef,inventory,bodyWords⟩ :=
   NativeReturnRepresentation.endpoint 2 1 child (by decide) CountdownWitness.P.r0 rfl rfl rfl
     CountdownWitness.P.base prepared preparedRepr (⟨22,by decide⟩ : Fin W) preparedOwner (by decide)
     8 8 7 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     preparedPointer (by decide) (by decide) (by decide) rfl (by decide)
 have savedRef : saved.mem 10=w[16] := by
   simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 0 (by decide)
 have savedCount : saved.mem 11=w[2] := by
   simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 1 (by decide)
 have payloadRef : after.mem 10=w[16] :=
   (bodyWords 10 (by decide) (by decide) (by decide) (.inl (by decide))).trans (show prepared.mem 10=saved.mem 10 from rfl) |>.trans savedRef
 have payloadCount : after.mem 11=w[2] :=
   (bodyWords 11 (by decide) (by decide) (by decide) (.inl (by decide))).trans (show prepared.mem 11=saved.mem 11 from rfl) |>.trans savedCount
 obtain ⟨last,restoreRun,restored,lastStack,lastPointer,lastRef,lastCount,lastResult,restoreGrowth,outside⟩ :=
   OuterScalarRestore.step bodyOut.st addresses after bodyRepr 2 (by decide) 8 8 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) bodyPointer
     (payloadRef.trans bodyRef.symm) payloadCount
 let arguments : TEnv C σ.H (Parameters A) := (countValue 1 (by decide),(some CountdownWitness.P.r0,()))
 let out := exported (result A) Ext.refl σ arguments bodyOut
 have native : source.run σ=.ok out := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) 2).ext
     (AllocatingScalarSource.body A (by rfl) 2).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) 2).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   exact call_return (next A (by rfl)) (result A) .refl _ σ arguments entry.2.2.1 bodyOut bodySource
 have exactBody := AllocatingScalarSource.one_return (C:=C) (R:=A) (by rfl) child 0 CountdownWitness.P.r0 rfl rfl
 have bodyEq := Except.ok.inj (bodySource.symm.trans exactBody)
 have stateEq : bodyOut.st.setLocal (.there .here) (countValue 2 (by decide))=out.st := by
   change bodyOut.st.setLocal (.there .here) (countValue 2 (by decide))=(exported (result A) .refl σ arguments bodyOut).st
   rw [bodyEq]
   rfl
 rw [stateEq] at restored restoreGrowth
 have actual : run image input=.ok last 0 :=
   (run_append_ok ((run_append_ok ((run_append_ok savedRun).trans entry.1)).trans preparedRun)).trans
     ((run_append_ok bodyRun).trans restoreRun)
 have finalOwner := restoreGrowth (⟨26,by decide⟩ : Fin W) (by decide) bodyOwner (by decide)
 have cursor : last.mem 0=w[26] := finalOwner.arrays.free.cell
 have scalar : after.mem 4=w[1] := by
   have represented := bodyRepr.core.vals (.here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) bodyOut.st.env) (after.mem 4) at represented
   rw [bodyEq] at represented
   exact Restore.uint_unique represented (ReprV.uint_of rfl)
 have savedSentinel : saved.mem 9=w[99] := captured.exterior 9 (by decide) (.inl (by decide))
 have sentinel : last.mem 9=w[99] := (outside 9 (by decide) (by decide) (by decide)).trans
   ((bodyWords 9 (by decide) (by decide) (by decide) (.inl (by decide))).trans
     ((show prepared.mem 9=saved.mem 9 from rfl).trans savedSentinel))
 have preparedStack : prepared.stack=saved.stack := rfl
 refine ⟨out,last,addresses,native,actual,restored,?_,?_,?_⟩
 · rw [lastStack,bodyStack,preparedStack,captured.stack,cursor,lastRef,bodyRef,lastCount,lastResult,scalar,lastPointer,sentinel]
   rfl
 · rw [lastResult,scalar]
   intro bad
   have impossible : (1:Nat)=2 := congrArg Fin.val (Word.val.inj bad)
   omega
 · rw [actual];intro bad;cases bad

end Solidity.Backend.InternalFlow.RuntimeFrame.OuterAllocatingCall
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OuterAllocatingCall.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OuterAllocatingCall.complete
