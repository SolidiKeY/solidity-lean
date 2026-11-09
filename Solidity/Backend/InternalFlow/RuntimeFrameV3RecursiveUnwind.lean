import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveProducer
import Solidity.Backend.InternalFlow.RuntimeFrameRestore

/-! Runtime return-loop control over actual frame words and existing target
instructions. The code reads its bottom cursor at runtime and is independent
of the number of frames. Saved-word premises are concrete memory contents,
not execution/simulation or source approval premises. This partial component
does not yet connect source recursive calls to the target control stack. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveUnwind
open Evm Evm.Memory

def condition (pointer bottom : Nat) : List Instr :=
 [.mload bottom,.mload pointer,.eq,.iszero]
def code (destination pointer bottom : Nat) : List Instr :=
 [.loop (condition pointer bottom) (Restore.code destination pointer)]

theorem condition_run (m : Machine) (pointer bottom : Nat) (a z : Fin W)
 (hp : m.mem pointer=.val a) (hb : m.mem bottom=.val z) :
 run (condition pointer bottom) m =
 .ok (m.push (.val (bword (decide (a.val≠z.val))))) 0 := by
 by_cases equal : a.val=z.val
 all_goals simp only [condition,run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,
   exec_nil,hp,hb,Machine.push,bword,ne_eq,equal,not_true_eq_false,not_false_eq_true,
   decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,Nat.one_ne_zero]

theorem restore_same (m : Machine) (destination pointer : Nat) (address : Fin W)
 (different : destination≠pointer)
 (same : m.mem (address.val-1)=m.mem destination) :
 Restore.restored m destination pointer address =
 writeMachine m pointer (.val (wmod (address.val-1))) := by
 have memory : upd (upd m.mem pointer (.val (wmod (address.val-1)))) destination
     (m.mem destination) = upd m.mem pointer (.val (wmod (address.val-1))) := by
   funext x
   by_cases atDestination : x=destination
   · subst x
     simp only [upd,ite_eq_right different,ite_true]
   · simp only [upd,ite_eq_right atDestination]
 change {m with mem := (upd (upd m.mem pointer (.val (wmod (address.val-1)))) destination (m.mem (address.val-1)))} = _
 rw [same,memory]
 rfl

theorem turn_live (m : Machine) (destination pointer bottom : Nat) (a z : Fin W)
 (hp : m.mem pointer=.val a) (hb : m.mem bottom=.val z)
 (different : a.val≠z.val) (positive : 0<a.val)
 (separate : pointer≠a.val-1) (destinationSeparate : destination≠pointer)
 (same : m.mem (a.val-1)=m.mem destination) :
 loopTurn (run (condition pointer bottom)) (run (Restore.code destination pointer)) m =
 .inl (writeMachine m pointer (.val (wmod (a.val-1)))) := by
 have condition := condition_run m pointer bottom a z hp hb
 have restored := Restore.run m destination pointer a hp positive separate
 rw [restore_same m destination pointer a destinationSeparate same] at restored
 simp only [loopTurn,condition,ne_eq,different,not_false_eq_true,decide_true,bword,
   Machine.push,ite_true,ite_false,Nat.one_ne_zero]
 rw [restored]

theorem turn_done (m : Machine) (destination pointer bottom : Nat) (a : Fin W)
 (hp : m.mem pointer=.val a) (hb : m.mem bottom=.val a) :
 loopTurn (run (condition pointer bottom)) (run (Restore.code destination pointer)) m =
 .inr (.ok m 0) := by
 simp only [loopTurn,condition_run m pointer bottom a a hp hb,ne_eq,
   not_true_eq_false,decide_false,bword,Machine.push,Bool.false_eq_true,ite_false,ite_true]

theorem write_current (m : Machine) (pointer : Nat) :
 writeMachine m pointer (m.mem pointer)=m := by
 have memory : upd m.mem pointer (m.mem pointer)=m.mem := by
   funext x
   by_cases same : x=pointer
   · subst x;simp only [upd,ite_true]
   · simp only [upd,ite_eq_right same]
 change {m with mem := upd m.mem pointer (m.mem pointer)}=m
 rw [memory]

theorem write_overwrite (m : Machine) (pointer : Nat) (first last : Word) :
 writeMachine (writeMachine m pointer first) pointer last=writeMachine m pointer last := by
 have memory : upd (upd m.mem pointer first) pointer last=upd m.mem pointer last := by
   funext x
   by_cases same : x=pointer
   · subst x;simp only [upd,ite_true]
   · simp only [upd,ite_eq_right same]
 change {m with mem := upd (upd m.mem pointer first) pointer last}=_
 rw [memory]
 rfl

/-- Actual finite termination of one runtime-indexed return loop. Every pop
restores the saved word to the same destination; no saved payload is erased.
`n+1` counts the n restoring turns AND the final false-condition observation. -/
theorem unwind_iter (n : Nat) (m : Machine) (destination pointer bottom start : Nat)
 (hp : m.mem pointer=.val (wmod (start+n)))
 (hb : m.mem bottom=.val (wmod start))
 (destinationSeparate : destination≠pointer) (bottomSeparate : bottom≠pointer)
 (below : pointer<start) (fits : start+n<W)
 (saved : ∀ i, i<n → m.mem (start+i)=m.mem destination) :
 loopIterN (run (condition pointer bottom)) (run (Restore.code destination pointer)) (n+1) m =
 .inr (.ok (writeMachine m pointer (.val (wmod start))) 0) := by
 induction n generalizing m with
 | zero =>
   have samePointer : m.mem pointer=.val (wmod start) := by simpa only [Nat.add_zero] using hp
   have done := turn_done m destination pointer bottom (wmod start) samePointer hb
   have unchanged : writeMachine m pointer (.val (wmod start))=m := by
     rw [←samePointer,write_current]
   simp only [loopIterN,done,unchanged]
 | succ n ih =>
   have endValue : (wmod (start+(n+1))).val=start+(n+1) := Nat.mod_eq_of_lt fits
   have startValue : (wmod start).val=start := Nat.mod_eq_of_lt (by omega)
   have lastWord : m.mem ((wmod (start+(n+1))).val-1)=m.mem destination := by
     rw [endValue, show start+(n+1)-1=start+n from by omega]
     exact saved n (by omega)
   have turn := turn_live m destination pointer bottom (wmod (start+(n+1))) (wmod start)
     hp hb (by rw [endValue,startValue];omega) (by rw [endValue];omega)
     (by rw [endValue];omega) destinationSeparate lastWord
   have decrement : (wmod (start+(n+1))).val-1=start+n := by rw [endValue];omega
   rw [decrement] at turn
   let next := writeMachine m pointer (.val (wmod (start+n)))
   have nextPointer : next.mem pointer=.val (wmod (start+n)) := upd_same _ _ _
   have nextBottom : next.mem bottom=.val (wmod start) := by
     simpa only [next,writeMachine,upd,ite_eq_right bottomSeparate] using hb
   have nextSaved : ∀ i, i<n → next.mem (start+i)=next.mem destination := by
     intro i small
     simpa only [next,writeMachine,upd,ite_eq_right destinationSeparate,
       ite_eq_right (show start+i≠pointer by omega)] using saved i (by omega)
   have tail := ih next nextPointer nextBottom (by omega) nextSaved
   simp only [loopIterN,turn]
   simpa only [loopIterN,next,write_overwrite] using tail

/-- A genuine complete target run follows from the actual stopping horizon;
no target endpoint or termination oracle is an input. -/
theorem unwind_run (n : Nat) (m : Machine) (destination pointer bottom start : Nat)
 (hp : m.mem pointer=.val (wmod (start+n)))
 (hb : m.mem bottom=.val (wmod start))
 (destinationSeparate : destination≠pointer) (bottomSeparate : bottom≠pointer)
 (below : pointer<start) (fits : start+n<W)
 (saved : ∀ i, i<n → m.mem (start+i)=m.mem destination) :
 run (code destination pointer bottom) m =
 .ok (writeMachine m pointer (.val (wmod start))) 0 := by
 have terminated := loopRun_of_iterN
  (unwind_iter n m destination pointer bottom start hp hb destinationSeparate bottomSeparate below fits saved)
 change loopRun (fun x => exec (condition pointer bottom) 0 x)
   (fun x => exec (Restore.code destination pointer) 0 x) m = _ at terminated
 simp only [code,run,exec_cons_zero,Instr.step,terminated,Out.ok_bind,exec_nil]

/-- Full reached representation and exact zero heap-allocation transport come
from the checked runtime loop, not an assumed return/frame simulation. -/
theorem endpoint {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {caller : State C Γ} {base : Nat → Fin W}
 (n : Nat) (m : Machine) (destination pointer bottom start : Nat)
 (repr : StateRepr L b frame F caller base m)
 (pointerAbove : b+Γ.length≤pointer) (pointerBelow : pointer<frame)
 (hp : m.mem pointer=.val (wmod (start+n)))
 (hb : m.mem bottom=.val (wmod start))
 (destinationSeparate : destination≠pointer) (bottomSeparate : bottom≠pointer)
 (below : pointer<start) (fits : start+n<W)
 (saved : ∀ i, i<n → m.mem (start+i)=m.mem destination) :
 let target := writeMachine m pointer (.val (wmod start))
 run (code destination pointer bottom) m = .ok target 0 ∧
 StateRepr L b frame F caller base target ∧ target.stack=m.stack ∧
 GrowsAllocator b frame 0 caller base m caller base target := by
 refine ⟨unwind_run n m destination pointer bottom start hp hb destinationSeparate bottomSeparate below fits saved,
   reserved_write repr pointer pointerAbove pointerBelow _,rfl,?_⟩
 intro cursor positive alloc space
 simpa only [Nat.add_zero] using alloc.localWrite pointer (by omega) pointerBelow (.val (wmod start))

/-- A return turn consumes the actual top word, without assuming that it
matches the current caller cell or any other frame's word. -/
theorem turn_pop (m : Machine) (destination pointer bottom : Nat) (a z : Fin W)
 (hp : m.mem pointer=.val a) (hb : m.mem bottom=.val z)
 (different : a.val≠z.val) (positive : 0<a.val) (separate : pointer≠a.val-1) :
 loopTurn (run (condition pointer bottom)) (run (Restore.code destination pointer)) m =
 .inl (Restore.restored m destination pointer a) := by
 have condition := condition_run m pointer bottom a z hp hb
 have restored := Restore.run m destination pointer a hp positive separate
 simp only [loopTurn,condition,ne_eq,different,not_false_eq_true,decide_true,bword,
   Machine.push,ite_true,ite_false,Nat.one_ne_zero]
 rw [restored]

theorem restore_merge (m : Machine) (destination pointer : Nat) (upper lower : Fin W)
 (payloadPointer : lower.val-1≠pointer) (payloadDestination : lower.val-1≠destination) :
 Restore.restored (Restore.restored m destination pointer upper) destination pointer lower =
 Restore.restored m destination pointer lower := by
 have read := Restore.outside m destination pointer upper (lower.val-1) payloadPointer payloadDestination
 have memory : upd (upd (Restore.restored m destination pointer upper).mem pointer (.val (wmod (lower.val-1))))
     destination ((Restore.restored m destination pointer upper).mem (lower.val-1)) =
     upd (upd m.mem pointer (.val (wmod (lower.val-1)))) destination (m.mem (lower.val-1)) := by
   rw [read]
   funext x
   by_cases hd : x=destination
   · subst x;simp only [upd,ite_true]
   · by_cases hp : x=pointer
     · subst x;simp only [upd,ite_eq_right hd,ite_true]
     · simp only [Restore.restored,upd,ite_eq_right hd,ite_eq_right hp]
 change {m with mem := (upd (upd (Restore.restored m destination pointer upper).mem pointer (.val (wmod (lower.val-1)))) destination ((Restore.restored m destination pointer upper).mem (lower.val-1)))} = _
 rw [memory]
 rfl

/-- All positive frame counts terminate after restoring each ACTUAL saved
word in LIFO order. Intermediate values may differ and the initial destination
may be clobbered. The final word is the bottom frame's word, never guessed
from the initial current destination. No recursive source evaluation is added. -/
theorem unwind_nonempty_iter (n : Nat) (m : Machine) (destination pointer bottom start : Nat)
 (hp : m.mem pointer=.val (wmod (start+(n+1))))
 (hb : m.mem bottom=.val (wmod start))
 (bottomPointer : bottom≠pointer) (bottomDestination : bottom≠destination)
 (destinationPointer : destination≠pointer)
 (pointerBelow : pointer<start) (destinationBelow : destination<start)
 (fits : start+(n+1)<W) :
 loopIterN (run (condition pointer bottom)) (run (Restore.code destination pointer)) (n+2) m =
 .inr (.ok (Restore.restored m destination pointer (wmod (start+1))) 0) := by
 induction n generalizing m with
 | zero =>
   have endValue : (wmod (start+1)).val=start+1 := Nat.mod_eq_of_lt fits
   have startValue : (wmod start).val=start := Nat.mod_eq_of_lt (by omega)
   let next := Restore.restored m destination pointer (wmod (start+1))
   have turn := turn_pop m destination pointer bottom (wmod (start+1)) (wmod start) hp hb
     (by rw [endValue,startValue];omega) (by rw [endValue];omega) (by rw [endValue];omega)
   have nextPointer : next.mem pointer=.val (wmod start) := by
     simp only [next,Restore.restored,upd,ite_eq_right (Ne.symm destinationPointer),ite_true,endValue,Nat.add_sub_cancel]
   have nextBottom : next.mem bottom=.val (wmod start) :=
     (Restore.outside m destination pointer _ bottom bottomPointer bottomDestination).trans hb
   simp only [loopIterN,turn]
   change loopIterN (run (condition pointer bottom)) (run (Restore.code destination pointer)) 1 next = _
   rw [loopIterN,turn_done next destination pointer bottom (wmod start) nextPointer nextBottom]
 | succ n ih =>
   have endValue : (wmod (start+(n+1+1))).val=start+(n+1+1) := Nat.mod_eq_of_lt fits
   have startValue : (wmod start).val=start := Nat.mod_eq_of_lt (by omega)
   let next := Restore.restored m destination pointer (wmod (start+(n+1+1)))
   have turn := turn_pop m destination pointer bottom (wmod (start+(n+1+1))) (wmod start) hp hb
     (by rw [endValue,startValue];omega) (by rw [endValue];omega) (by rw [endValue];omega)
   have decrement : (wmod (start+(n+1+1))).val-1=start+(n+1) := by rw [endValue];omega
   have nextPointer : next.mem pointer=.val (wmod (start+(n+1))) := by
     simp only [next,Restore.restored,upd,ite_eq_right (Ne.symm destinationPointer),ite_true,decrement]
   have nextBottom : next.mem bottom=.val (wmod start) :=
     (Restore.outside m destination pointer _ bottom bottomPointer bottomDestination).trans hb
   have tail := ih next nextPointer nextBottom (by omega)
   have lowerValue : (wmod (start+1)).val-1=start := by
     rw [show (wmod (start+1)).val=start+1 from Nat.mod_eq_of_lt (by omega)];omega
   have merged := restore_merge m destination pointer (wmod (start+(n+1+1))) (wmod (start+1))
     (by rw [lowerValue];omega) (by rw [lowerValue];omega)
   simp only [loopIterN,turn]
   simpa only [loopIterN,next,merged] using tail

theorem unwind_nonempty_run (n : Nat) (m : Machine) (destination pointer bottom start : Nat)
 (hp : m.mem pointer=.val (wmod (start+(n+1))))
 (hb : m.mem bottom=.val (wmod start))
 (bottomPointer : bottom≠pointer) (bottomDestination : bottom≠destination)
 (destinationPointer : destination≠pointer)
 (pointerBelow : pointer<start) (destinationBelow : destination<start)
 (fits : start+(n+1)<W) :
 run (code destination pointer bottom) m =
 .ok (Restore.restored m destination pointer (wmod (start+1))) 0 := by
 have terminated := loopRun_of_iterN (unwind_nonempty_iter n m destination pointer bottom start
   hp hb bottomPointer bottomDestination destinationPointer pointerBelow destinationBelow fits)
 change loopRun (fun x => exec (condition pointer bottom) 0 x)
   (fun x => exec (Restore.code destination pointer) 0 x) m = _ at terminated
 simp only [code,run,exec_cons_zero,Instr.step,terminated,Out.ok_bind,exec_nil]

theorem restore_after_clobber (m : Machine) (destination pointer : Nat) (address : Fin W)
 (temporary : Word) (payloadSeparate : address.val-1≠destination) :
 Restore.restored (writeMachine m destination temporary) destination pointer address =
 Restore.restored m destination pointer address := by
 have read : (writeMachine m destination temporary).mem (address.val-1)=m.mem (address.val-1) :=
   upd_other _ _ payloadSeparate
 have memory : upd (upd (writeMachine m destination temporary).mem pointer (.val (wmod (address.val-1))))
     destination ((writeMachine m destination temporary).mem (address.val-1)) =
     upd (upd m.mem pointer (.val (wmod (address.val-1)))) destination (m.mem (address.val-1)) := by
   rw [read]
   funext x
   by_cases hd : x=destination
   · subst x;simp only [upd,ite_true]
   · by_cases hp : x=pointer
     · subst x;simp only [upd,ite_eq_right hd,ite_true]
     · simp only [writeMachine,upd,ite_eq_right hd,ite_eq_right hp]
 change {m with mem := (upd (upd (writeMachine m destination temporary).mem pointer (.val (wmod (address.val-1)))) destination ((writeMachine m destination temporary).mem (address.val-1)))} = _
 rw [memory]
 rfl

/-- Recover a genuinely clobbered caller cell from its bottom saved frame.
The represented machine is the actual caller snapshot BEFORE this physical
clobber, not a supplied desired final representation. Higher saved words may
be different. Heap/world mutations between capture and return are not covered. -/
theorem recover_clobbered {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {caller : State C Γ} {base : Nat → Fin W}
 (n : Nat) (m : Machine) (destination pointer bottom start : Nat) (temporary : Word)
 (repr : StateRepr L b frame F caller base m)
 (pointerAbove : b+Γ.length≤pointer) (pointerBelow : pointer<frame)
 (hp : m.mem pointer=.val (wmod (start+(n+1))))
 (hb : m.mem bottom=.val (wmod start))
 (bottomPointer : bottom≠pointer) (bottomDestination : bottom≠destination)
 (destinationPointer : destination≠pointer)
 (pointerLower : pointer<start) (destinationLower : destination<start)
 (fits : start+(n+1)<W) (captured : m.mem start=m.mem destination) :
 let target := writeMachine m pointer (.val (wmod start))
 run (code destination pointer bottom) (writeMachine m destination temporary)=.ok target 0 ∧
 StateRepr L b frame F caller base target ∧ target.stack=m.stack ∧
 GrowsAllocator b frame 0 caller base m caller base target := by
 have changedPointer : (writeMachine m destination temporary).mem pointer=.val (wmod (start+(n+1))) :=
   (upd_other _ _ (Ne.symm destinationPointer)).trans hp
 have changedBottom : (writeMachine m destination temporary).mem bottom=.val (wmod start) :=
   (upd_other _ _ bottomDestination).trans hb
 have actual := unwind_nonempty_run n (writeMachine m destination temporary) destination pointer bottom start
   changedPointer changedBottom bottomPointer bottomDestination destinationPointer pointerLower destinationLower fits
 have payload : (wmod (start+1)).val-1=start := by
   rw [show (wmod (start+1)).val=start+1 from Nat.mod_eq_of_lt (by omega)];omega
 rw [restore_after_clobber m destination pointer (wmod (start+1)) temporary (by rw [payload];omega)] at actual
 rw [restore_same m destination pointer (wmod (start+1)) destinationPointer (by rw [payload];exact captured),payload] at actual
 refine ⟨actual,reserved_write repr pointer pointerAbove pointerBelow _,rfl,?_⟩
 intro cursor positive alloc space
 simpa only [Nat.add_zero] using alloc.localWrite pointer (by omega) pointerBelow (.val (wmod start))

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveUnwind
