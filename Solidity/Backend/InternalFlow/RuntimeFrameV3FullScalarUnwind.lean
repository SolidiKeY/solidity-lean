import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwind

/-! Return from a full three-cell scalar capture. The saved private-result
slot is skipped by an actual checked pointer decrement, retaining the child's
live result, before the existing two-parameter restore and scalar increment.
The old payload remains in memory. No general recursive compiler is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def skipCode (pointer : Nat) : List Instr := Stack.decrementCode pointer ++ [.mstore pointer]
def skipped (m : Machine) (pointer start : Nat) := writeMachine m pointer (.val (wmod (start+2)))
def code {C : Contract} {R : RefTy} (b pointer : Nat) (F : Frag (Frame R)) : List Instr :=
 skipCode pointer ++ ScalarUnwind.code (C:=C) b pointer F

theorem skip_run (m : Machine) (pointer start : Nat) (fits : start+3<W)
 (current : m.mem pointer=.val (wmod (start+3))) :
 run (skipCode pointer) m=.ok (skipped m pointer start) 0 := by
 have index : (wmod (start+3)).val=start+3 := Nat.mod_eq_of_lt fits
 have actual := Stack.decrement_run m pointer (wmod (start+3)) current (by rw [index];omega)
 unfold skipCode
 rw [run_append_ok actual]
 change Out.ok (writeMachine m pointer (.val (wmod ((wmod (start+3)).val-1)))) 0=_
 rw [index,show start+3-1=start+2 from by omega]
 rfl

theorem step {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (n : Nat) (bound : n+1<W)
 (result : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega))
 (lo pointer start : Nat)
 (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+3<W)
 (current : after.mem pointer=.val (wmod (start+3)))
 (reference : after.mem start=after.mem b)
 (counter : after.mem (start+1)=.val (wmod (n+1))) :
 ∃ last,
 run (code (C:=C) b pointer F) after=.ok last 0 ∧
 StateRepr L b frame F (finished (σ.setLocal (.there .here) (countValue (n+1) bound)) (n+1) bound) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=after.mem b ∧ last.mem (b+1)=.val (wmod (n+1)) ∧
 last.mem (b+2)=.val (wmod (n+1)) ∧
 GrowsAllocator b frame 0 σ base after
   (finished (σ.setLocal (.there .here) (countValue (n+1) bound)) (n+1) bound) base last ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 let mid := skipped after pointer start
 have shifted : StateRepr L b frame F σ base mid :=
   reserved_write repr pointer (by change b+3≤pointer;omega) below _
 have current' : mid.mem pointer=.val (wmod (start+2)) := upd_same _ _ _
 have reference' : mid.mem start=mid.mem b :=
   (upd_other _ _ (by omega)).trans (reference.trans (upd_other _ _ (by omega)).symm)
 have counter' : mid.mem (start+1)=.val (wmod (n+1)) :=
   (upd_other _ _ (by omega)).trans counter
 obtain ⟨last,executed,represented,stack,cursor,alias,count,value,growth,outside⟩ :=
   ScalarUnwind.step σ base mid shifted n bound result lo pointer start locals above below payload separate
     (by omega) current' reference' counter'
 refine ⟨last,(run_append_ok (skip_run after pointer start fits current)).trans executed,
   represented,stack,cursor,?_,count,value,?_,?_⟩
 · exact alias.trans (upd_other _ _ (by omega))
 · intro cursor positive owned space
   exact growth cursor positive (owned.localWrite pointer (by omega) below _) space
 · intro x hp hr hc hv
   exact (outside x hp hr hc hv).trans (upd_other _ _ hp)

end Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind.skip_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind.skip_run

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarUnwind.step
