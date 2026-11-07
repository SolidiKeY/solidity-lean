import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarParentRestore
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource

/-! Restore an actual saved parent reference, which may differ from the active
callee reference, together with its counter. The typed parent reference belongs
to the reached heap. Saved payload words, frame separation and the reached
representation remain explicit inputs. This proves the real restore run and
its represented output; it does not produce a capture or recursive selection. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem restore {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (parentRef : HRef σ.H R) (parent : Nat) (bound : parent<W) (lo pointer start : Nat)
 (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+2<W)
 (current : after.mem pointer=.val (wmod (start+2)))
 (reference : after.mem start=.val (base parentRef.id))
 (counter : after.mem (start+1)=.val (wmod parent)) :
 ∃ last,
 run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) after=.ok last 0 ∧
 StateRepr L b frame F ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent bound)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=.val (base parentRef.id) ∧ last.mem (b+1)=.val (wmod parent) ∧
 last.mem (b+2)=after.mem (b+2) ∧
 GrowsAllocator b frame 0 σ base after ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent bound)) base last ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x) := by
 let rebound := writeMachine after b (.val (base parentRef.id))
 let snapshot := writeMachine rebound (b+1) (.val (wmod parent))
 have model : StateRepr L b frame F
     ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent bound)) base snapshot :=
   (repr.setMem (.there (.there .here)) parentRef).setVal (.there .here)
     (countValue parent bound) (.val (wmod parent)) (by
       have word : wmod parent=(⟨parent,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
       rw [word]
       exact ReprV.uint_of rfl)
 have snapshot_ref : snapshot.mem b=.val (base parentRef.id) := by
   simp only [snapshot,rebound,writeMachine,upd,if_neg (show b≠b+1 from by omega),if_true]
 have snapshot_counter : snapshot.mem (b+1)=.val (wmod parent) := by
   simp only [snapshot,writeMachine,upd,if_true]
 have snapshot_other : ∀ x, x≠b → x≠b+1 → snapshot.mem x=after.mem x := by
   intro x hr hc
   simp only [snapshot,rebound,writeMachine,upd,if_neg hc,if_neg hr]
 have saved : ∀ i, i<(Parameters R).length → after.mem (start+i)=snapshot.mem (b+i) := by
   intro i small
   change i<2 at small
   rcases (by omega : i=0 ∨ i=1) with rfl | rfl
   · simpa only [Nat.add_zero,snapshot_ref] using reference
   · simpa only [snapshot_counter] using counter
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
   exact (exterior x (by omega) (by omega) (by omega)).trans (snapshot_other x (by omega) (by omega)).symm
 have transported := (Restored.memory_transport model last.mem (by
   intro t index observed
   cases index with
   | here =>
     change last.mem (b+2)=snapshot.mem (b+2)
     exact resultWord.trans (snapshot_other (b+2) (by omega) (by omega)).symm
   | there index => simpa only [cellOf,lvl_there] using values index) heap).stack last.stack
 have reset := congrArg (fun m : Machine => {m with mem:=last.mem,stack:=last.stack}) recovered.fields
 change last={after with mem:=last.mem,stack:=last.stack} at reset
 change StateRepr L b frame F ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent bound)) base
   {after with mem:=last.mem,stack:=last.stack} at transported
 rw [←reset] at transported
 have oldRef := values (.there .here : Idx (Parameters R) (.mem R))
 have oldCounter := values (.here : Idx (Parameters R) (.val .uint))
 change last.mem b=snapshot.mem b at oldRef
 change last.mem (b+1)=snapshot.mem (b+1) at oldCounter
 refine ⟨last,executed,transported,recovered.stack,recovered.cursor,?_,?_,resultWord,?_,exterior⟩
 · simpa only [snapshot_ref] using oldRef
 · simpa only [snapshot_counter] using oldCounter
 · intro cursor positive initial space
   have ownership := recovered.allocator σ.heap base frame cursor (by
     intro x member
     change x∈[b,b+1] at member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl | rfl <;> constructor <;> omega) (by omega) below initial
   simpa only [Nat.add_zero] using ownership

end Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.restore
