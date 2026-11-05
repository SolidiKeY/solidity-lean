import Solidity.Backend.InternalFlow.RuntimeFrameV3ParentRestore
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource

/-! Restore the saved counter while retaining the scalar result and the SAME
reference. The premise `after.mem start = after.mem b` requires the saved
reference word to equal the active one; this theorem does not restore a
different parent reference. Payload and reached representation are actual
inputs. Output run, representation, stack and allocator transport are derived.
No general recursive compiler or approved-domain instance is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarParentRestore
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem restore {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (parent : Nat) (bound : parent<W) (lo pointer start : Nat)
 (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+2<W)
 (current : after.mem pointer=.val (wmod (start+2)))
 (reference : after.mem start=after.mem b)
 (counter : after.mem (start+1)=.val (wmod parent)) :
 ∃ last,
 run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) after=.ok last 0 ∧
 StateRepr L b frame F (σ.setLocal (.there .here) (countValue parent bound)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=after.mem b ∧ last.mem (b+1)=.val (wmod parent) ∧
 last.mem (b+2)=after.mem (b+2) ∧
 GrowsAllocator b frame 0 σ base after (σ.setLocal (.there .here) (countValue parent bound)) base last ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x) := by
 let snapshot := writeMachine after (b+1) (.val (wmod parent))
 have model : StateRepr L b frame F (σ.setLocal (.there .here) (countValue parent bound)) base snapshot :=
   repr.setVal (.there .here) (countValue parent bound) (.val (wmod parent)) (by
     have word : wmod parent=(⟨parent,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
     rw [word]
     exact ReprV.uint_of rfl)
 have saved : ∀ i, i<(Parameters R).length → after.mem (start+i)=snapshot.mem (b+i) := by
   intro i small
   change i<2 at small
   rcases (by omega : i=0 ∨ i=1) with rfl | rfl
   · simpa only [Nat.add_zero,snapshot,writeMachine,upd,if_neg (show b≠b+1 from by omega)] using reference
   · simpa only [snapshot,writeMachine,upd,if_true] using counter
 obtain ⟨last,executed,recovered,values⟩ := Context.restore_context b (Parameters R) snapshot after
   lo pointer start (by change b+2≤lo;omega) above payload (.inl separate) fits current saved
 have exterior : ∀ x, x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x := by
   intro x hp hr hc
   by_cases low : x<lo
   · have absent : x∉Restore.contextCells b (Parameters R) := by
       change x∉[b,b+1]
       simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
       exact ⟨hr,hc⟩
     simpa only [if_neg absent] using recovered.locals x low
   · exact recovered.exterior x (by omega) hp
 have resultWord : last.mem (b+2)=after.mem (b+2) := exterior _ (by omega) (by omega) (by omega)
 have heap : ∀ x, frame≤x → last.mem x=snapshot.mem x := by
   intro x high
   exact (exterior x (by omega) (by omega) (by omega)).trans (upd_other _ _ (by omega)).symm
 have transported := (Restored.memory_transport model last.mem (by
   intro t index observed
   cases index with
   | here =>
     change last.mem (b+2)=snapshot.mem (b+2)
     exact resultWord.trans (upd_other _ _ (by omega)).symm
   | there index => simpa only [cellOf,lvl_there] using values index) heap).stack last.stack
 have reset := congrArg (fun m : Machine => {m with mem:=last.mem,stack:=last.stack}) recovered.fields
 change last={after with mem:=last.mem,stack:=last.stack} at reset
 change StateRepr L b frame F (σ.setLocal (.there .here) (countValue parent bound)) base
   {after with mem:=last.mem,stack:=last.stack} at transported
 rw [←reset] at transported
 have oldRef := values (.there .here : Idx (Parameters R) (.mem R))
 have oldCounter := values (.here : Idx (Parameters R) (.val .uint))
 change last.mem b=snapshot.mem b at oldRef
 change last.mem (b+1)=snapshot.mem (b+1) at oldCounter
 refine ⟨last,executed,transported,recovered.stack,recovered.cursor,?_,?_,resultWord,?_,exterior⟩
 · simpa only [snapshot,writeMachine,upd,if_neg (show b≠b+1 from by omega)] using oldRef
 · simpa only [snapshot,writeMachine,upd,if_true] using oldCounter
 · intro cursor positive initial space
   have ownership := recovered.allocator σ.heap base frame cursor (by
     intro x member
     change x∈[b,b+1] at member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl | rfl <;> constructor <;> omega) (by omega) below initial
   simpa only [Nat.add_zero] using ownership

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarParentRestore

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarParentRestore.restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarParentRestore.restore
