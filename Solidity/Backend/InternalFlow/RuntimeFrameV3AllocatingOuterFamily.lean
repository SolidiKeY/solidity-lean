import Solidity.Backend.InternalFlow.RuntimeFrameV3OuterAllocatingCall
import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeReturnRepresentation
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn

/-! One explicit outer-call image over arbitrary admitted count and quotation
index. Caller representation, full capture, the checked decrement argument,
actual native recursive body, and scalar restoration produce the actual
exported caller output and allocation cursor. Capacity is required for each
count; no public general recursive compiler or approved profile is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
def image : List Instr := OuterAllocatingCall.image

def source (depth : Nat) : Stmt C (Frame A) (Frame A) :=
 InterfaceV1.recursiveSource "outerAllocating" (next A (by rfl)) (result A) (AllocatingScalarSource.step A (by rfl)) depth

theorem endpoint {L frame : Nat} (depth n : Nat) (σ : State C (Frame A))
 (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (room : 13+3*n≤frame) (space : cursor.val+4*n<W)
 (payloadFit : 13+3*n<W) (current : before.mem 8=w[10]) (enough : n<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run σ=.ok out ∧ run image before=.ok last 0 ∧
 StateRepr L 2 frame F out.st addresses last ∧
 last.stack=before.stack ∧ last.mem 8=w[10] ∧ last.mem 2=.val (base ref.id) ∧
 last.mem 3=.val (wmod (n+1)) ∧ last.mem 4=.val (wmod n) ∧
 StructAllocatorRepr out.st.heap addresses frame (⟨cursor.val+4*n,space⟩ : Fin W) last := by
 obtain ⟨saved,savedRun,captured,savedRepr,captureGrowth⟩ :=
   Context.capture_context (σ:=σ) (F:=F) (base:=base) before 8 8 10 repr
     (by decide) (by decide) (by omega) (by decide) (by change 13≤frame;omega) (.inl (by decide)) (by decide) current
 have entry := AllocatingScalarEntry.entry (by rfl) σ n fit ref counter alias base saved savedRepr
 let child := entered σ n (by omega) ref
 let active := AllocatingScalarEntry.childMachine (R:=A) 2 saved n (by omega)
 let prepared := writeMachine active 7 w[13]
 have savedPointer : saved.mem 8=w[13] := captured.cursor
 have activePointer : active.mem 8=w[13] := savedPointer
 have preparedRun : run [.mload 8,.mstore 7] active=.ok prepared 0 := by
   change Out.ok (writeMachine active 7 (active.mem 8)) 0=_
   rw [activePointer]
 have preparedRepr : StateRepr L 2 frame F child base prepared :=
   reserved_write entry.2.1 7 (by decide) (by omega) w[13]
 have savedOwner := captureGrowth cursor (by omega) owned (by omega)
 have activeOwner : StructAllocatorRepr child.heap base frame cursor active :=
   (savedOwner.localWrite 3 (by decide) (by omega) (.val ⟨n,by omega⟩)).localWrite 4 (by decide) (by omega) w[0]
 have preparedOwner : StructAllocatorRepr child.heap base frame cursor prepared :=
   activeOwner.localWrite 7 (by decide) (by omega) w[13]
 obtain ⟨bodyOut,after,addresses,bodySource,bodyRun,bodyRepr,bodyKept,extended,bodyGrowth,bodyOwner,bodyStack,bodyPointer,bodyRef,inventory,bodyWords⟩ :=
   NativeReturnRepresentation.endpoint depth n child (by omega) ref rfl rfl rfl base prepared preparedRepr cursor preparedOwner space
     8 8 7 13 (by decide) (by decide) (by omega) (by decide) room (by decide) payloadFit
     (show prepared.mem 8=w[13] from activePointer) (by decide) (by decide) (by decide) rfl enough
 have savedRef : saved.mem 10=.val (base ref.id) := by
   have observed := repr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
   obtain ⟨r,binding,word⟩ := observed
   have same : r=ref := Option.some.inj (binding.symm.trans alias)
   subst r
   have savedWord : saved.mem 10=before.mem 2 := by
     simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 0 (by decide)
   exact savedWord.trans word
 have savedCount : saved.mem 11=.val (wmod (n+1)) := by
   have word := repr.core.vals (.there .here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env) (before.mem 3) at word
   rw [counter] at word
   have actual := Restore.uint_unique word (ReprV.uint_of rfl)
   have savedWord : saved.mem 11=before.mem 3 := by
     simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 1 (by decide)
   exact savedWord.trans
     (actual.trans (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt fit).symm)))
 have payloadRef : after.mem 10=.val (base ref.id) :=
   (bodyWords 10 (by decide) (by omega) (by decide) (.inl (by decide))).trans (show prepared.mem 10=saved.mem 10 from rfl) |>.trans savedRef
 have payloadCount : after.mem 11=.val (wmod (n+1)) :=
   (bodyWords 11 (by decide) (by omega) (by decide) (.inl (by decide))).trans (show prepared.mem 11=saved.mem 11 from rfl) |>.trans savedCount
 obtain ⟨last,restoreRun,restored,lastStack,lastPointer,lastRef,lastCount,lastResult,restoreGrowth,outside⟩ :=
   OuterScalarRestore.step bodyOut.st addresses after bodyRepr (n+1) fit 8 8 10
     (by decide) (by decide) (by omega) (by decide) (by decide) (by decide) bodyPointer
     (payloadRef.trans bodyRef.symm) payloadCount
 let arguments : TEnv C σ.H (Parameters A) := (countValue n (by omega),(some ref,()))
 let out := exported (result A) Ext.refl σ arguments bodyOut
 have native : (source depth).run σ=.ok out := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) depth).ext
     (AllocatingScalarSource.body A (by rfl) depth).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) depth).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   exact call_return (next A (by rfl)) (result A) .refl _ σ arguments entry.2.2.1 bodyOut bodySource
 obtain ⟨seen,seenRun,_,locals,_⟩ := AllocatingScalarSource.success (by rfl) depth child n (by omega) ref rfl rfl enough
 have sameOut : seen=bodyOut := Except.ok.inj (seenRun.symm.trans bodySource)
 subst seen
 have callerEnv : σ.env=(σ.env.1,(countValue (n+1) fit,(some ref,()))) :=
   Prod.ext rfl (Prod.ext counter (Prod.ext alias (by cases σ.env.2.2.2;rfl)))
 have stateEq : bodyOut.st.setLocal (.there .here) (countValue (n+1) fit)=out.st := by
   change bodyOut.st.withEnv (TEnv.set (.there .here) (countValue (n+1) fit) bodyOut.st.env)=_
   rw [locals]
   simp only [out,exported,result,CallRet.leaveT,CallRet.enterT,TEnv.drop,TEnv.take]
   rw [callerEnv,locals]
   rfl
 rw [stateEq] at restored restoreGrowth
 have actual : run image before=.ok last 0 :=
   (run_append_ok ((run_append_ok ((run_append_ok savedRun).trans entry.1)).trans preparedRun)).trans
     ((run_append_ok bodyRun).trans restoreRun)
 have finalOwner := restoreGrowth (⟨cursor.val+4*n,space⟩ : Fin W) (by omega) bodyOwner (by omega)
 have scalar : after.mem 4=.val (wmod n) := by
   have represented := bodyRepr.core.vals (.here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) bodyOut.st.env) (after.mem 4) at represented
   rw [locals] at represented
   exact (Restore.uint_unique represented (ReprV.uint_of rfl)).trans
     (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt (by omega : n<W)).symm))
 exact ⟨out,last,addresses,native,actual,restored,lastStack.trans (bodyStack.trans captured.stack),lastPointer,
   lastRef.trans bodyRef,lastCount,lastResult.trans scalar,finalOwner⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.endpoint
