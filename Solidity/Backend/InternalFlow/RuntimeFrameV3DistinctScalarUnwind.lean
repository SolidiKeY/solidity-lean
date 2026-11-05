import Solidity.Backend.InternalFlow.RuntimeFrameV3DistinctParentRestore
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwind

/-! Actual typed parent-reference/counter restoration followed by the existing
checked scalar increment. The saved counter and child result are independent.
No recursive compiler selection or source-history premise is invented. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open ScalarUnwind (code)

theorem step {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (parent : Nat) (parentBound : parent<W) (parentRef : HRef σ.H R)
 (n : Nat) (bound : n+1<W)
 (result : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega))
 (lo pointer start : Nat)
 (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+2<W)
 (current : after.mem pointer=.val (wmod (start+2)))
 (reference : after.mem start=.val (base parentRef.id))
 (counter : after.mem (start+1)=.val (wmod parent)) :
 ∃ last,
 run (code (C:=C) b pointer F) after=.ok last 0 ∧
 StateRepr L b frame F (finished ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent parentBound)) (n+1) bound) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=.val (base parentRef.id) ∧ last.mem (b+1)=.val (wmod parent) ∧
 last.mem (b+2)=.val (wmod (n+1)) ∧
 GrowsAllocator b frame 0 σ base after
   (finished ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent parentBound)) (n+1) bound) base last ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 obtain ⟨mid,executed,represented,stack,cursor,alias,count,live,growth,outside⟩ :=
   DistinctParentRestore.restore σ base after repr parentRef parent parentBound lo pointer start locals above below payload separate fits current reference counter
 have advanced := ScalarUnwind.advance ((σ.setLocal (.there (.there .here)) (some parentRef)).setLocal (.there .here) (countValue parent parentBound)) base mid represented n bound result
 let last := writeMachine mid (b+2) (.val (wmod (n+1)))
 have unchanged : ∀ x, x≠b+2 → last.mem x=mid.mem x := fun x different => upd_other _ _ different
 refine ⟨last,?_,advanced.2,stack,?_,?_,?_,?_,?_,?_⟩
 · unfold code
   rw [run_append_ok executed]
   exact advanced.1
 · exact (unchanged pointer (by omega)).trans cursor
 · exact (unchanged b (by omega)).trans alias
 · exact (unchanged (b+1) (by omega)).trans count
 · exact upd_same _ _ _
 · intro allocation positive initial space
   have owned := growth allocation positive initial space
   simpa only [Nat.add_zero] using owned.localWrite (b+2) (by omega) (by have h:=repr.locals;change b+3≤frame at h;omega) (.val (wmod (n+1)))
 · intro x hp hr hc hv
   exact (unchanged x hv).trans (outside x hp hr hc)

end Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.step
