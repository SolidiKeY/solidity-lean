import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarEntry

/-! A real allocating recursive-entry turn at the existing scalar frame layout.
The public allocation image and value compiler are reused. No recursive body
compiler, arbitrary target relation or approved-domain instance is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTurn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingScalarEntry
abbrev F := AllocatingScalarTarget.F
abbrev C := CountdownWitness.P.C
abbrev A := CountdownWitness.A

def code (pointer : Nat) : List Instr := AllocatingScalarTarget.selected.code ++
 (Restore.saveCells pointer (Restore.contextCells 2 (Frame A)) ++ AllocatingScalarEntry.code (C:=C) 2 F)

theorem turn {L frame : Nat} (σ : State C (Frame A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (space : cursor.val+4<W) (lo pointer start : Nat)
 (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (payloadBelow : start+3≤frame)
 (separate : pointer<start) (fits : start+3<W)
 (current : before.mem pointer=.val (wmod start)) :
 let allocated := AllocatingScalarSource.allocated σ
 let extension := AllocatingScalarSource.extension σ
 let addresses := upd base σ.H.length cursor
 let child := entered allocated n (by omega) (ref.wk extension)
 ∃ target,
 AllocatingScalarSource.allocate.run σ=.ok ⟨allocated,extension⟩ ∧
 run (code pointer) before=.ok target 0 ∧ StateRepr L 2 frame F child addresses target ∧
 StructAllocatorRepr child.heap addresses frame (⟨cursor.val+4,space⟩ : Fin W) target ∧
 BaseExtends σ.H base addresses ∧ target.stack=before.stack ∧
 target.mem pointer=.val (wmod (start+3)) ∧
 target.mem 0=.val (wmod (cursor.val+4)) ∧ target.mem 3=.val (⟨n,by omega⟩ : Fin W) ∧
 target.mem 4=w[0] ∧ target.mem 5=.val cursor ∧
 (∀ i,i<3 → target.mem (start+i)=before.mem (2+i)) ∧
 (∀ x,x≠0 → x≠3 → x≠4 → x≠5 → x≠pointer → x≠cursor.val →
   (x<start ∨ start+3≤x) → target.mem x=before.mem x) := by
 let allocated := AllocatingScalarSource.allocated σ
 let extension := AllocatingScalarSource.extension σ
 let addresses := upd base σ.H.length cursor
 let m := writeMachine (allocateMachine before cursor AllocatingScalarSource.size) 5 (.val cursor)
 obtain ⟨source,allocatedRun,allocatedRepr,allocatedOwner,allocatedStack,allocatedWords⟩ :=
   Footprint.declare (σ:=σ) repr owned (by decide) .bool
     (AllocatingScalarSource.lengthExpr (C:=C) (R:=A)) rfl AllocatingScalarSource.size rfl space
     (lo:=lo) privateBelow (by change 2+(3+1)≤frame;omega)
 have parentRepr : StateRepr L 2 frame F allocated addresses m := allocatedRepr.drop (.push .refl)
 have parameters := AllocatingScalarSource.allocated_parameters σ n fit ref counter alias
 obtain ⟨saved,captureRun,captured,savedRepr,captureGrowth⟩ :=
   Context.capture_context (σ:=allocated) (F:=F) (base:=addresses) m lo pointer start parentRepr
     (by change 2+3≤lo;omega) pointerAbove pointerBelow payloadAbove payloadBelow (.inl separate) fits
     ((allocatedWords pointer pointerAbove pointerBelow).trans current)
 have facts := AllocatingScalarEntry.entry rfl allocated n fit (ref.wk extension) parameters.1 parameters.2
   addresses saved savedRepr
 let target := childMachine (R:=A) 2 saved n (by omega)
 have owner := captureGrowth (⟨cursor.val+4,space⟩ : Fin W) (by decide) allocatedOwner (by omega)
 have targetOwner : StructAllocatorRepr (entered allocated n (by omega) (ref.wk extension)).heap addresses frame
   (⟨cursor.val+4,space⟩ : Fin W) target :=
   (owner.localWrite 3 (by decide) (by omega) (.val ⟨n,by omega⟩)).localWrite 4 (by decide) (by omega) w[0]
 have entryOutside (x : Nat) (h3 : x≠3) (h4 : x≠4) : target.mem x=saved.mem x :=
   (upd_other _ _ h4).trans (upd_other _ _ h3)
 have allocationOutside (x : Nat) (h0 : x≠0) (h5 : x≠5) (hc : x≠cursor.val) : m.mem x=before.mem x :=
   (upd_other _ _ h5).trans ((upd_other _ _ h0).trans (upd_other _ _ hc))
 have payload (i : Nat) (small : i<3) : target.mem (start+i)=before.mem (2+i) := by
   rw [entryOutside (start+i) (by omega) (by omega)]
   have savedWord : saved.mem (start+i)=m.mem (2+i) := by
     simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload i small
   exact savedWord.trans (allocationOutside (2+i) (by omega) (by omega)
     (by have above:=owned.arrays.free.above;omega))
 have privateWord : target.mem 5=.val cursor := by
   rw [entryOutside 5 (by decide) (by decide),captured.locals 5 privateBelow]
   rfl
 have allocatorWord : target.mem 0=.val (wmod (cursor.val+4)) := by
   rw [entryOutside 0 (by decide) (by decide),captured.locals 0 (by omega)]
   change Word.val (wmod (cursor.val+3+1))=Word.val (wmod (cursor.val+4))
   rw [show cursor.val+3+1=cursor.val+4 from by omega]
 refine ⟨target,AllocatingScalarSource.scoped_allocation σ,?_,facts.2.1,targetOwner,
   (fun r => allocationBase_old base cursor r),?_,?_,allocatorWord,rfl,rfl,privateWord,payload,?_⟩
 · have allocatedRun' : run AllocatingScalarTarget.selected.code before=.ok m 0 := by
     simpa only [AllocatingScalarTarget.selected,List.append_nil] using allocatedRun
   exact (run_append_ok allocatedRun').trans ((run_append_ok captureRun).trans facts.1)
 · exact captured.stack.trans allocatedStack
 · exact (entryOutside pointer (by omega) (by omega)).trans captured.cursor
 · intro x h0 h3 h4 h5 hp hc outside
   exact (entryOutside x h3 h4).trans ((captured.exterior x hp outside).trans (allocationOutside x h0 h5 hc))

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTurn

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTurn.turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTurn.turn
