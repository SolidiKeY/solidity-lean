import Solidity.Backend.InternalFlow.RuntimeFrameV3PairedUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation

/-! Descent followed by paired unwind for the effect-free countdown family: a
hand-written image, not compiler output. `endpoint` relates the final machine to
the original source `StateRepr` (the source returns its state unchanged); it is
an endpoint correspondence, with no per-parent representation during unwind.
No `PendingRecursiveReturns` inhabitant is built. -/

namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveReturn
open Evm Evm.Memory RecursiveSource RecursiveActivation

def code {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer bottom : Nat) : List Instr :=
 descentCode (C:=C) b F pointer ++ PairedUnwind.code b pointer bottom R

theorem activation_fields {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (σ : State C (Parameters R))
 (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before after : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (payloadBelow : start+2≤frame)
 (pointerBefore : pointer<start) (fits : start+2<W)
 (current : before.mem pointer=.val (wmod start))
 (actual : run (activationCode (C:=C) b F pointer) before=.ok after 0) :
 {after with mem:=before.mem,stack:=before.stack}=before := by
 obtain ⟨saved,captureRun,captured,captureRepr,growth⟩ :=
   Context.capture_context before lo pointer start repr localBound pointerAbove pointerBelow
     payloadAbove payloadBelow (.inl pointerBefore) fits current
 have update := decrement_run hm σ n bound ref counter alias base saved captureRepr
 have combined := (Evm.run_append_ok captureRun).trans update
 have same := (Evm.Out.ok.inj (actual.symm.trans combined)).1
 rw [same]
 exact captured.fields

theorem descent_fields {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before after : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start))
 (actual : loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (activationCode (C:=C) b F pointer)) count before=.inl after) :
 {after with mem:=before.mem,stack:=before.stack}=before := by
 induction count generalizing σ base before start with
 | zero =>
   have same : before=after := Sum.inl.inj actual
   subst after;rfl
 | succ count ih =>
   let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
   obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
     activation hm σ count bound ref counter alias base before repr lo pointer start localBound
       pointerAbove pointerBelow payloadAbove (by omega) (.inl pointerBefore) (by omega) current
   have first := activation_fields hm σ count bound ref counter alias base before next repr
     lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega) pointerBefore (by omega) current executed
   have turn := positive_turn σ count bound counter base before next repr pointer executed
   have rest : loopIterN (run (guardCompiled (C:=C) b F).code)
       (run (activationCode (C:=C) b F pointer)) count next=.inl after := by
     simpa only [loopIterN,turn] using actual
   have tail := ih (by omega) child ref rfl rfl addresses next represented
     (start+2) (by omega) (by omega) (by omega) (by omega) cursor rest
   have changed := congrArg (fun m : Machine => {m with mem:=before.mem,stack:=before.stack}) tail
   change {after with mem:=before.mem,stack:=before.stack}={next with mem:=before.mem,stack:=before.stack} at changed
   exact changed.trans first

theorem endpoint {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame)
 (bottomAbove : b+2≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start))
 (bottomValue : before.mem bottom=.val (wmod start)) :
 ∃ last,
 (∀ depth, count<depth → (body R hm depth).run σ=.ok ⟨σ,List.prefix_refl _⟩) ∧
 run (code (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F σ base last ∧ last.stack=before.stack ∧
 last.mem pointer=.val (wmod start) ∧
 (∀ x, x<start → last.mem x=before.mem x) ∧
 (∀ x, frame≤x → last.mem x=before.mem x) ∧
 (∀ j, j<count → last.mem (start+2*j)=before.mem b ∧
   last.mem (start+2*j+1)=.val (wmod (count-j))) := by
 obtain ⟨after,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete hm count bound σ ref counter alias base before repr lo pointer start
     localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 obtain ⟨saved,descExterior⟩ := RecursiveHistory.saved_history hm count bound σ ref counter alias base before after repr
   lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current running
 have afterBottom : after.mem bottom=.val (wmod start) :=
   (descExterior bottom bottomSeparate (by omega) (.inl bottomBefore)).trans bottomValue
 obtain ⟨last,returned,returnStack,returnCursor,reference,scalar,returnExterior,returnFields⟩ :=
   PairedUnwind.iter count count (Nat.le_refl _) R before after b lo pointer bottom start localBound
     pointerAbove payloadAbove pointerBefore bottomAbove bottomSeparate fits cursor afterBottom saved
 have fields := descent_fields hm count bound σ ref counter alias base before after repr
   lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current running
 have sameStack : last.stack=before.stack := returnStack.trans stack
 have originalRef : last.mem b=before.mem b := by
   by_cases zero : count=0
   · have empty : before=after := Sum.inl.inj (by simpa only [zero,loopIterN] using running)
     simpa only [zero,if_true,←empty] using reference
   · simpa only [zero,if_false] using reference
 have originalCounter : last.mem (b+1)=before.mem (b+1) := by
   by_cases zero : count=0
   · have empty : before=after := Sum.inl.inj (by simpa only [zero,loopIterN] using running)
     simpa only [zero,if_true,←empty] using scalar
   · rw [RecursiveHistory.counter_word σ count bound counter base before repr]
     simpa only [zero,if_false] using scalar
 have low : ∀ x, x<start → last.mem x=before.mem x := by
   intro x below
   by_cases atPointer : x=pointer
   · subst x;exact returnCursor.trans current.symm
   by_cases atRef : x=b
   · subst x;exact originalRef
   by_cases atCounter : x=b+1
   · subst x;exact originalCounter
   exact (returnExterior x atPointer atRef atCounter).trans
     (descExterior x (by omega) atCounter (.inl (by omega)))
 have high : ∀ x, frame≤x → last.mem x=before.mem x := by
   intro x above
   exact (returnExterior x (by omega) (by omega) (by omega)).trans
     (descExterior x (by omega) (by omega) (.inr (by omega)))
 have allFields := congrArg (fun m : Machine => {m with mem:=before.mem,stack:=before.stack}) returnFields
 change {last with mem:=before.mem,stack:=before.stack}={after with mem:=before.mem,stack:=before.stack} at allFields
 have reset := congrArg (fun m : Machine => {m with mem:=last.mem,stack:=last.stack}) (allFields.trans fields)
 change last={before with mem:=last.mem,stack:=last.stack} at reset
 rw [sameStack] at reset
 have locals : ∀ {t : LTy} (index : Idx (Parameters R) t), Restored.Observed F index →
     last.mem (cellOf b index)=before.mem (cellOf b index) := by
   intro t index observed
   apply low
   have small := lvl_lt b index
   change cellOf b index<b+(Parameters R).length at small
   have len : (Parameters R).length=2 := rfl
   rw [len] at small
   omega
 have finalRepr := Restored.memory_transport repr last.mem locals high
 rw [←reset] at finalRepr
 refine ⟨last,?_,?_,finalRepr,sameStack,returnCursor,low,high,?_⟩
 · intro depth enough
   simpa only [if_pos enough] using all_horizons hm depth σ count bound ref counter alias
 · rw [code,Evm.run_append_ok (RecursiveDescent.run_of_stopped stopped)]
   exact PairedUnwind.run_of_stopped returned
 · intro j small
   exact ⟨(returnExterior _ (by omega) (by omega) (by omega)).trans (saved j small).1,
     (returnExterior _ (by omega) (by omega) (by omega)).trans (saved j small).2⟩

/-- Copy the actual runtime entry cursor to a private bottom cell. -/
def initializeCode (pointer bottom : Nat) : List Instr := [.mload pointer,.mstore bottom]
def entryCode {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer bottom : Nat) : List Instr :=
 initializeCode pointer bottom ++ code (C:=C) b F pointer bottom

theorem initialize_run (before : Machine) (pointer bottom : Nat) :
 run (initializeCode pointer bottom) before=.ok (writeMachine before bottom (before.mem pointer)) 0 := by
 rfl

theorem initialize_repr {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (repr : StateRepr L b frame F σ base before) (pointer bottom : Nat)
 (above : b+Γ.length≤bottom) (below : bottom<frame) :
 StateRepr L b frame F σ base (writeMachine before bottom (before.mem pointer)) := by
 apply Restored.memory_transport repr
 · intro t index observed
   have small := lvl_lt b index
   change cellOf b index<b+Γ.length at small
   exact upd_other _ _ (by omega)
 · intro x high
   exact upd_other _ _ (by omega)

/-- A single image including real runtime-header initialization. Neither the
source counter, unrolling depth nor starting cursor occurs in the code. -/
theorem initialized_endpoint {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame)
 (bottomAbove : b+2≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ last,
 (∀ depth, count<depth → (body R hm depth).run σ=.ok ⟨σ,List.prefix_refl _⟩) ∧
 run (entryCode (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F σ base last ∧ last.stack=before.stack ∧
 last.mem pointer=.val (wmod start) ∧
 (∀ x, x<start → x≠bottom → last.mem x=before.mem x) ∧
 (∀ x, frame≤x → last.mem x=before.mem x) ∧
 (∀ j, j<count → last.mem (start+2*j)=before.mem b ∧
   last.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 last.mem bottom=.val (wmod start) := by
 let initial := writeMachine before bottom (before.mem pointer)
 have ready : StateRepr L b frame F σ base initial :=
   initialize_repr repr pointer bottom bottomAbove (by omega)
 have initialCursor : initial.mem pointer=.val (wmod start) :=
   (upd_other _ _ (Ne.symm bottomSeparate)).trans current
 have initialBottom : initial.mem bottom=.val (wmod start) := (upd_same _ _ _).trans current
 obtain ⟨last,source,executed,represented,stack,cursor,low,high,saved⟩ := endpoint hm count bound σ ref counter alias base initial ready
   lo pointer bottom start localBound pointerAbove pointerBelow bottomAbove bottomBefore bottomSeparate
   payloadAbove pointerBefore capacity fits initialCursor initialBottom
 refine ⟨last,source,?_,represented,stack,cursor,?_,?_,?_,?_⟩
 · rw [entryCode,Evm.run_append_ok (initialize_run before pointer bottom)]
   exact executed
 · intro x below different
   exact (low x below).trans (upd_other _ _ different)
 · intro x above
   exact (high x above).trans (upd_other _ _ (by omega))
 · intro j small
   exact ⟨(saved j small).1.trans (upd_other _ _ (by omega)),(saved j small).2⟩
 · exact (low bottom bottomBefore).trans initialBottom

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveReturn
