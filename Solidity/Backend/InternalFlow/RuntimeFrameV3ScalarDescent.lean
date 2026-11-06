import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarStop
import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveHistory

/-! Actual arbitrary-count descent supplies the scalar child and saved parent
history for one runtime return image. No desired midpoint is a premise; the
same initial frame, current pointer and existing capacity bounds are used. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDescent
open Evm Evm.Memory RecursiveSource RecursiveActivation ScalarRecursiveSource

def image {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer bottom : Nat) : List Instr :=
 [.mload pointer,.mstore bottom] ++ (descentCode (C:=C) b F pointer ++ [.push w[0],.mstore (b+2)])

/-- The zero scalar frame and every saved pair are derived from checked
capture/decrement execution, including count zero. No source or target run is
supplied as an input. -/
theorem reached {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Frame R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine)
 (repr : StateRepr L b frame (F.push (.val .uint) .ok) σ base before)
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (above : lo≤pointer)
 (below : pointer<frame) (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+3≤bottom) (bottomBelow : bottom<frame) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ after addresses,
 run (image (C:=C) b F pointer bottom) before=.ok after 0 ∧
 StateRepr L b frame (F.push (.val .uint) .ok) (ScalarPrefixes.sourceAt σ 0 W_pos) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem pointer=.val (wmod (start+2*count)) ∧ after.mem bottom=.val (wmod start) ∧
 after.mem b=before.mem b ∧
 (∀ j,j<count → after.mem (start+2*j)=after.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 GrowsAllocator b frame 0 σ base before (ScalarPrefixes.sourceAt σ 0 W_pos) addresses after ∧
 (∀ x,x≠pointer → x≠bottom → x≠b+1 → x≠b+2 →
   (x<start ∨ start+2*count≤x) → after.mem x=before.mem x) := by
 let setup := writeMachine before bottom (.val (wmod start))
 have setupRun : run [.mload pointer,.mstore bottom] before=.ok setup 0 := by
   change (.ok (writeMachine before bottom (before.mem pointer)) 0 : Evm.Out)=_
   rw [current]
 have setupRepr := reserved_write repr bottom bottomAbove bottomBelow (.val (wmod start))
 let params : State C (Parameters R) := σ.drop (.push .refl)
 have paramsRepr : StateRepr L b frame F params base setup := setupRepr.drop (.push .refl)
 have position : setup.mem pointer=.val (wmod start) :=
   (upd_other before.mem (.val (wmod start)) bottomSeparate.symm).trans current
 obtain ⟨down,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete hm count bound params ref counter alias base setup paramsRepr
     lo pointer start (by omega) above below payload separate capacity fits position
 obtain ⟨saved,outside⟩ := RecursiveHistory.saved_history hm count bound params ref counter alias
   base setup down paramsRepr lo pointer start (by omega) above below payload separate capacity fits position running
 let after := writeMachine down (b+2) w[0]
 have sourceTail : σ.env.2.2=(some ref,()) := Prod.ext alias (by cases σ.env.2.2.2;rfl)
 have zeroRepr : StateRepr L b frame (F.push (.val .uint) .ok)
     (ScalarPrefixes.sourceAt σ 0 W_pos) addresses after := by
   have zero := represented.consVal (PrimTy.dflt .uint) w[0] (ReprV.dflt_zero .uint) repr.locals
   have source : (params.withEnv (Δ:=Parameters R) (countValue 0 W_pos,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)=
       ScalarPrefixes.sourceAt σ 0 W_pos := by
     change σ.withEnv (Δ:=Frame R) (countValue 0 W_pos,(countValue 0 W_pos,(some ref,())))=
       σ.withEnv (Δ:=Frame R) (countValue 0 W_pos,(countValue 0 W_pos,σ.env.2.2))
     rw [sourceTail]
   rw [source] at zero
   exact zero
 have refWord : after.mem b=before.mem b :=
   (upd_other down.mem w[0] (by omega)).trans
     ((outside b (by omega) (by omega) (.inl (by omega))).trans
       (upd_other before.mem (.val (wmod start)) (by omega)))
 refine ⟨after,addresses,?_,zeroRepr,stack,extended,?_,?_,refWord,?_,?_,?_⟩
 · unfold image
   rw [run_append_ok setupRun,run_append_ok (RecursiveDescent.run_of_stopped stopped)]
   rfl
 · exact (upd_other down.mem w[0] (by omega)).trans cursor
 · exact (upd_other down.mem w[0] (by omega)).trans
     ((outside bottom bottomSeparate (by omega) (.inl bottomBefore)).trans (upd_same _ _ _))
 · intro j small
   have oldRef : setup.mem b=before.mem b := upd_other before.mem (.val (wmod start)) (by omega)
   exact ⟨(upd_other down.mem w[0] (by omega)).trans
       (((saved j small).1.trans oldRef).trans refWord.symm),
     (upd_other down.mem w[0] (by omega)).trans (saved j small).2⟩
 · intro allocation positive initial space
   have setupOwner := initial.localWrite bottom (by omega) bottomBelow (.val (wmod start))
   have downOwner := growth allocation positive setupOwner space
   simpa only [Nat.add_zero] using downOwner.localWrite (b+2) (by omega)
     (by have h:=repr.locals;change b+3≤frame at h;omega) w[0]
 · intro x hp hb hc hv region
   exact (upd_other down.mem w[0] hv).trans
     ((outside x hp hc region).trans (upd_other before.mem (.val (wmod start)) hb))

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDescent
