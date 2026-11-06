import Solidity.Backend.InternalFlow.RuntimeFrameSaved

/-! Runtime descent prefixes on the existing target loop and frame-word code.
This is a partial foundation for the recursive producer, not an inhabitant of
InterfaceV3.PendingRecursiveReturns. The horizon is not an admission cutoff:
every natural horizon has the theorem under its actual finite frame/no-wrap
bounds. Source recursive return, unwind and divergence agreement remain open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveProducer
open Evm Evm.Memory

/-- The same condition and body instructions are used at every horizon. -/
def condition : List Instr := [.push (.val (wmod 1))]
def descentCode (source pointer : Nat) : List Instr :=
 [.loop condition (saveCode source pointer)]

theorem condition_run (m : Machine) :
 run condition m = .ok (m.push (.val (wmod 1))) 0 := rfl

theorem descent_turn (m : Machine) (source pointer : Nat) (address : Fin W)
 (hp : m.mem pointer = .val address) (hs : pointer ≠ address.val) :
 loopTurn (run condition) (run (saveCode source pointer)) m =
 .inl (Stack.pushed m pointer address (m.mem source)) := by
 have nonzero : (wmod 1).val ≠ 0 := by decide +kernel
 have saved := save_word_run m source pointer address hp hs
 simp only [loopTurn,condition_run,Machine.push,nonzero,if_false]
 rw [saved]


/-- Every reached descent prefix retains the SAME full caller representation,
heap address map and evaluation stack. Saving frame words consumes no heap
allocation. The frame cursor advances by the actual horizon. No callee heap
noninterference or source/target recursive simulation is assumed here. -/
theorem descent_prefix {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {caller : State C Γ} {base : Nat → Fin W} (n : Nat) (m : Machine)
 (source pointer start : Nat) (repr : StateRepr L b frame F caller base m)
 (hp : m.mem pointer = .val (wmod start))
 (pointerAbove : b+Γ.length ≤ pointer) (pointerBelow : pointer < start)
 (payloadAbove : b+Γ.length ≤ start)
 (room : start+n < frame) (fits : start+n < W) :
 ∃ reached, loopIterN (run condition) (run (saveCode source pointer)) n m = .inl reached ∧
 StateRepr L b frame F caller base reached ∧ reached.stack=m.stack ∧
 reached.mem pointer=.val (wmod (start+n)) ∧
 GrowsAllocator b frame 0 caller base m caller base reached ∧
 (∀ address, address<start → address≠pointer → reached.mem address=m.mem address) := by
 induction n generalizing m start with
 | zero =>
   refine ⟨m,rfl,repr,rfl,?_,?_,?_⟩
   · simpa only [Nat.add_zero] using hp
   · intro cursor positive alloc space
     simpa only [Nat.add_zero] using alloc
   · intro address lower separate
     rfl
 | succ n ih =>
   have startFits : (wmod start).val=start := Nat.mod_eq_of_lt (by omega)
   have separate : pointer ≠ (wmod start).val := by rw [startFits];omega
   let next := Stack.pushed m pointer (wmod start) (m.mem source)
   have turn := descent_turn m source pointer (wmod start) hp separate
   have nextRepr : StateRepr L b frame F caller base next :=
     pushed_repr repr pointer (wmod start) _ pointerAbove (by omega)
       (by rw [startFits];exact payloadAbove) (by rw [startFits];omega)
   have nextPointer : next.mem pointer=.val (wmod (start+1)) := by
     simp only [next,Stack.pushed,upd_same,startFits,Nat.add_comm]
   have firstGrowth : GrowsAllocator b frame 0 caller base m caller base next :=
     pushed_allocator pointer (wmod start) _ pointerAbove (by omega)
       (by rw [startFits];exact payloadAbove) (by rw [startFits];omega)
   obtain ⟨last,runLast,lastRepr,stackLast,pointerLast,growthLast,oldLast⟩ :=
     ih next (start+1) nextRepr nextPointer (by omega) (by omega) (by omega) (by omega)
   refine ⟨last,?_,lastRepr,?_,?_,?_,?_⟩
   · simp only [loopIterN,turn]
     exact runLast
   · exact stackLast
   · simpa only [Nat.add_assoc,Nat.add_comm 1 n] using pointerLast
   · simpa only [Nat.zero_add] using firstGrowth.comp growthLast
   · intro address lower different
     rw [oldLast address (by omega) different]
     simp only [next,Stack.pushed,upd,if_neg different,startFits,if_neg (show address≠start by omega)]

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveProducer
