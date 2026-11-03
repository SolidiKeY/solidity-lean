import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveHistory
import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveUnwind

/-! Paired all-parent unwind for the hand-written countdown descent image
(`RecursiveSource` family): word-level restoration of the saved reference and
counter for every frame count, given a saved history. Per-parent `StateRepr`
during the unwind and general recursive bodies are open. -/

namespace Solidity.Backend.InternalFlow.RuntimeFrame.PairedUnwind
open Evm Evm.Memory RecursiveSource

abbrev condition := RecursiveUnwind.condition
def code (b pointer bottom : Nat) (R : RefTy) : List Instr :=
 [.loop (condition pointer bottom) (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))]

theorem turn_more (m next : Machine) (b pointer bottom start frames : Nat) (R : RefTy)
 (current : m.mem pointer=.val (wmod (start+2*(frames+1))))
 (bottomValue : m.mem bottom=.val (wmod start)) (fits : start+2*(frames+1)<W)
 (body : run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) m=.ok next 0) :
 loopTurn (run (condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) m=.inl next := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod (start+2*(frames+1))) (wmod start) current bottomValue
 have different : (wmod (start+2*(frames+1))).val≠(wmod start).val := by
   change (start+2*(frames+1))%W≠start%W
   rw [Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt (show start<W by omega)]
   omega
 simp only [loopTurn,guard,decide_eq_true different,Machine.push,bword,if_true,if_false,Nat.one_ne_zero,body]

theorem turn_done (m : Machine) (b pointer bottom start : Nat) (R : RefTy)
 (current : m.mem pointer=.val (wmod start)) (bottomValue : m.mem bottom=.val (wmod start)) :
 loopTurn (run (condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) m=.inr (.ok m 0) := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod start) (wmod start) current bottomValue
 simp only [loopTurn,guard,ne_eq,not_true_eq_false,decide_false,Machine.push,bword,
   Bool.false_eq_true,if_false,if_true]

/-- Consume any number of genuine saved parent contexts with one runtime
code image. Payload may be supplied by RecursiveHistory.saved_history; this
is a word-level return law, not an assumed recursive simulation. -/
theorem iter (frames total : Nat) (enough : frames≤total) (R : RefTy)
 (before after : Machine) (b lo pointer bottom start : Nat)
 (localBound : b+2≤lo) (pointerAbove : lo≤pointer) (_payloadAbove : lo≤start)
 (pointerBefore : pointer<start)
 (bottomAbove : b+2≤bottom) (bottomSeparate : bottom≠pointer) (fits : start+2*frames<W)
 (current : after.mem pointer=.val (wmod (start+2*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j, j<frames → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (total-j))) :
 ∃ last,
 loopIterN (run (condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) (frames+1) after=.inr (.ok last 0) ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=(if frames=0 then after.mem b else before.mem b) ∧
 last.mem (b+1)=(if frames=0 then after.mem (b+1) else .val (wmod total)) ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x) ∧
 {last with mem:=after.mem,stack:=after.stack}=after := by
 induction frames generalizing after with
 | zero =>
   have position : after.mem pointer=.val (wmod start) := by simpa only [Nat.mul_zero,Nat.add_zero] using current
   have stopped := turn_done after b pointer bottom start R position bottomValue
   refine ⟨after,?_,rfl,position,rfl,rfl,?_,rfl⟩
   · simp only [loopIterN,stopped]
   · intro x notPointer notRef notCounter;rfl
 | succ frames ih =>
   let snapshot := writeMachine before (b+1) (.val (wmod (total-frames)))
   have payload : ∀ i, i<(Parameters R).length → after.mem (start+2*frames+i)=snapshot.mem (b+i) := by
     intro i small
     have len : (Parameters R).length=2 := rfl
     rw [len] at small
     have words := saved frames (by omega)
     rcases (by omega : i=0 ∨ i=1) with rfl | rfl
     · simpa only [Nat.add_zero,snapshot,writeMachine,upd,if_neg (show b≠b+1 by omega)] using words.1
     · simpa only [snapshot,writeMachine,upd,if_true] using words.2
   have position : start+2*frames+2=start+2*(frames+1) := by omega
   obtain ⟨mid,body,recovered,locals⟩ := Context.restore_context b (Parameters R) snapshot after lo pointer (start+2*frames)
     localBound pointerAbove (by omega) (.inl (by omega))
     (by simpa only [show (Parameters R).length=2 from rfl,position] using fits)
     (by simpa only [show (Parameters R).length=2 from rfl,position] using current) payload
   have turn := turn_more after mid b pointer bottom start frames R current bottomValue fits body
   have tailSaved : ∀ j, j<frames → mid.mem (start+2*j)=before.mem b ∧
       mid.mem (start+2*j+1)=.val (wmod (total-j)) := by
     intro j small
     exact ⟨(recovered.exterior _ (by omega) (by omega)).trans (saved j (by omega)).1,
       (recovered.exterior _ (by omega) (by omega)).trans (saved j (by omega)).2⟩
   have bodyExterior : ∀ x, x≠pointer → x≠b → x≠b+1 → mid.mem x=after.mem x := by
     intro x notPointer notRef notCounter
     by_cases below : x<lo
     · have absent : x∉Restore.contextCells b (Parameters R) := by
         change x∉[b,b+1]
         simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
         exact ⟨notRef,notCounter⟩
       simpa only [if_neg absent] using recovered.locals x below
     · exact recovered.exterior x (by omega) notPointer
   have nextBottom : mid.mem bottom=.val (wmod start) :=
     (bodyExterior bottom bottomSeparate (by omega) (by omega)).trans bottomValue
   obtain ⟨last,stopped,stack,cursor,reference,counter,exterior,fields⟩ :=
     ih (by omega) mid (by omega) recovered.cursor nextBottom tailSaved
   have bodyRef := locals (.there .here : Idx (Parameters R) (.mem R))
   have bodyCounter := locals (.here : Idx (Parameters R) (.val .uint))
   change mid.mem b=snapshot.mem b at bodyRef
   change mid.mem (b+1)=snapshot.mem (b+1) at bodyCounter
   have refWord : mid.mem b=before.mem b := by
     simpa only [snapshot,writeMachine,upd,if_neg (show b≠b+1 by omega)] using bodyRef
   have counterWord : mid.mem (b+1)=.val (wmod (total-frames)) := by
     simpa only [snapshot,writeMachine,upd,if_true] using bodyCounter
   refine ⟨last,?_,stack.trans recovered.stack,cursor,?_,?_,?_,?_⟩
   · simpa only [loopIterN,turn] using stopped
   · by_cases empty : frames=0
     · simpa only [empty,if_true,if_false,Nat.add_one_ne_zero] using reference.trans (by simpa only [empty,if_true] using refWord)
     · simpa only [empty,if_false,Nat.add_one_ne_zero] using reference
   · by_cases empty : frames=0
     · have currentWord : mid.mem (b+1)=.val (wmod total) := by simpa only [empty,Nat.sub_zero] using counterWord
       have initialWord : last.mem (b+1)=mid.mem (b+1) := by simpa only [empty,if_true] using counter
       simpa only [if_false,Nat.add_one_ne_zero] using initialWord.trans currentWord
     · simpa only [empty,if_false,Nat.add_one_ne_zero] using counter
   · intro x notPointer notRef notCounter
     exact (exterior x notPointer notRef notCounter).trans (bodyExterior x notPointer notRef notCounter)
   · have changed := congrArg (fun m : Machine => {m with mem:=after.mem,stack:=after.stack}) fields
     change {last with mem:=after.mem,stack:=after.stack}={mid with mem:=after.mem,stack:=after.stack} at changed
     exact changed.trans recovered.fields

theorem run_of_stopped {b pointer bottom horizon : Nat} {R : RefTy} {before after : Machine}
 (stopped : loopIterN (run (condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) horizon before=.inr (.ok after 0)) :
 run (code b pointer bottom R) before=.ok after 0 := by
 have done := loopRun_of_iterN stopped
 change loopRun (fun m => exec (condition pointer bottom) 0 m)
   (fun m => exec (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) 0 m) before=.ok after 0 at done
 simp only [code,run,exec_cons_zero,Instr.step,done,Out.ok_bind,exec_nil]

end Solidity.Backend.InternalFlow.RuntimeFrame.PairedUnwind
