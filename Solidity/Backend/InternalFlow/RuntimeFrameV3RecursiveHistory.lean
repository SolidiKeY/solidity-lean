import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveDescent

/-! Saved parent payload history along the countdown descent, and a
nearest-parent pop with the existing `Restore.restoreCells`. -/

namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveHistory
open Evm Evm.Memory RecursiveSource RecursiveActivation

/-- Actual activation writes only its counter, cursor and new payload.
The execution premise is supplied by the checked activation theorem. -/
theorem activation_exterior {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
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
 ∀ x, x≠pointer → x≠b+1 → (x<start ∨ start+2≤x) → after.mem x=before.mem x := by
 obtain ⟨saved,captureRun,captured,captureRepr,growth⟩ :=
   Context.capture_context before lo pointer start repr localBound pointerAbove pointerBelow
     payloadAbove payloadBelow (.inl pointerBefore) fits current
 have update := decrement_run hm σ n bound ref counter alias base saved captureRepr
 have combined := (Evm.run_append_ok captureRun).trans update
 have same := (Evm.Out.ok.inj (actual.symm.trans combined)).1
 rw [same]
 intro x notPointer notCounter outside
 have destination : cellOf b (.here : Idx (Parameters R) (.val .uint))=b+1 := rfl
 change upd saved.mem (cellOf b (.here : Idx (Parameters R) (.val .uint))) _ x=_
 rw [destination]
 simp only [upd,if_neg notCounter]
 apply captured.exterior x notPointer
 simpa only [Restore.contextCells,List.length_map,List.length_range,Parameters,
   List.length_cons,List.length_nil] using outside

/-- Exact counter word follows from the actual primitive representation. -/
theorem counter_word {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (count : Nat) (bound : count<W)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L b frame F σ base m) :
 m.mem (b+1)=.val (wmod count) := by
 have represented := repr.core.vals (.here : Idx (Parameters R) (.val .uint))
 change ReprV .uint (TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env) (m.mem (b+1)) at represented
 rw [counter] at represented
 have word : m.mem (b+1)=.val ⟨count,bound⟩ := Restore.uint_unique represented (ReprV.uint_of rfl)
 rw [word]
 congr 1
 exact Fin.ext (Nat.mod_eq_of_lt bound).symm


/-- The saved frames are the ACTUAL parent contexts in source call order.
Their contents and all exterior words follow from the executed native
activations. They are not supplied as a frame-history or simulation premise. -/
theorem saved_history {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
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
 (∀ j, j<count → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x, x≠pointer → x≠b+1 → (x<start ∨ start+2*count≤x) → after.mem x=before.mem x) := by
 induction count generalizing σ base before start with
 | zero =>
   have same : before=after := Sum.inl.inj actual
   subst after
   constructor
   · intro j small;omega
   · intro x notPointer notCounter outside;rfl
 | succ count ih =>
   let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
   obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
     activation hm σ count bound ref counter alias base before repr lo pointer start localBound
       pointerAbove pointerBelow payloadAbove (by omega) (.inl pointerBefore) (by omega) current
   have firstExterior := activation_exterior hm σ count bound ref counter alias base before next repr
     lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega) pointerBefore (by omega) current executed
   have turn := positive_turn σ count bound counter base before next repr pointer executed
   have rest : loopIterN (run (guardCompiled (C:=C) b F).code)
       (run (activationCode (C:=C) b F pointer)) count next=.inl after := by
     simpa only [loopIterN,turn] using actual
   obtain ⟨history,exterior⟩ := ih (by omega) child ref rfl rfl addresses next represented
     (start+2) (by omega) (by omega) (by omega) (by omega) cursor rest
   constructor
   · intro j small
     cases j with
     | zero =>
       have savedRef := payload 0 (by decide)
       have savedCounter := payload 1 (by decide)
       have refAfter := exterior start (by omega) (by omega) (.inl (by omega))
       have counterAfter := exterior (start+1) (by omega) (by omega) (.inl (by omega))
       have word := counter_word σ (count+1) bound counter base before repr
       constructor
       · simpa only [Nat.mul_zero,Nat.add_zero] using refAfter.trans savedRef
       · simpa only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using counterAfter.trans (savedCounter.trans word)
     | succ j =>
       have words := history j (by omega)
       have offset : start+2*(j+1)=start+2+2*j := by omega
       constructor
       · rw [offset]
         exact words.1.trans (firstExterior b (by omega) (by omega) (.inl (by omega)))
       · rw [offset]
         simpa only [Nat.add_sub_add_right] using words.2
   · intro x notPointer notCounter outside
     exact (exterior x notPointer notCounter (by omega)).trans
       (firstExterior x notPointer notCounter (by omega))


/-- Execute the real descent and first return pop. Its parent payload is
DERIVED from the same descent, never a supplied saved-context oracle. This
restores the nearest native parent (counter1), not all recursive callers. -/
theorem descend_then_pop {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count+1<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (count+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*(count+1)≤frame) (fits : start+2*(count+1)<W)
 (current : before.mem pointer=.val (wmod start)) :
 let child : State C (Parameters R) := σ.withEnv (countValue 0 W_pos,(some ref,()))
 let parentSnapshot := writeMachine before (b+1) (.val (wmod 1))
 ∃ after last addresses,
 run (descentCode (C:=C) b F pointer) before=.ok after 0 ∧
 StateRepr L b frame F child addresses after ∧
 run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) after=.ok last 0 ∧
 Context.Recovered parentSnapshot after last (Restore.contextCells b (Parameters R)) lo pointer (start+2*count) ∧
 last.stack=before.stack ∧ last.mem pointer=.val (wmod (start+2*count)) ∧
 last.mem b=before.mem b ∧ last.mem (b+1)=.val (wmod 1) := by
 obtain ⟨after,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete hm (count+1) bound σ ref counter alias base before repr lo pointer start
     localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 obtain ⟨history,exterior⟩ := saved_history hm (count+1) bound σ ref counter alias base before after repr
   lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current running
 let snapshot := writeMachine before (b+1) (.val (wmod 1))
 have parentWords := history count (by omega)
 have payload : ∀ i, i<(Parameters R).length → after.mem (start+2*count+i)=snapshot.mem (b+i) := by
   intro i small
   have len : (Parameters R).length=2 := rfl
   rw [len] at small
   have snapshotRef : snapshot.mem b=before.mem b := by
     simp only [snapshot,writeMachine,upd,if_neg (show b≠b+1 by omega)]
   have snapshotCounter : snapshot.mem (b+1)=.val (wmod 1) := upd_same _ _ _
   have one : count+1-count=1 := by omega
   rcases (by omega : i=0 ∨ i=1) with rfl | rfl
   · simpa only [Nat.add_zero,snapshotRef] using parentWords.1
   · simpa only [one,snapshotCounter] using parentWords.2
 have position : start+2*count+2=start+2*(count+1) := by omega
 obtain ⟨last,pop,recovered,locals⟩ := Context.restore_context b (Parameters R) snapshot after lo pointer (start+2*count)
   localBound pointerAbove (by omega) (.inl (by omega)) (by simpa only [show (Parameters R).length=2 from rfl,position] using fits)
   (by simpa only [show (Parameters R).length=2 from rfl,position] using cursor) payload
 have reference := locals (.there .here : Idx (Parameters R) (.mem R))
 have countWord := locals (.here : Idx (Parameters R) (.val .uint))
 have finalRef : last.mem b=before.mem b := by
   change last.mem b=snapshot.mem b at reference
   simpa only [snapshot,writeMachine,upd,if_neg (show b≠b+1 by omega)] using reference
 have finalCounter : last.mem (b+1)=.val (wmod 1) := by
   change last.mem (b+1)=snapshot.mem (b+1) at countWord
   simpa only [snapshot,writeMachine,upd,if_true] using countWord
 exact ⟨after,last,addresses,RecursiveDescent.run_of_stopped stopped,represented,pop,recovered,
   recovered.stack.trans stack,recovered.cursor,finalRef,finalCounter⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveHistory
