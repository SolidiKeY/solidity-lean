import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarEmitter

/-! Soundness of selected scalar-family code. No target run or reached-state
witness is supplied: the checked argument and actual initial representation
feed the existing disjoint entry/descent/unwind/export proof. Runtime payload
capacity, cursor and source evaluation remain explicit. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem endpoint {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame pointer bottom : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (σ : State C Γ) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (emitted : Emission b c frame pointer bottom F count) (destination : Idx Γ (.val .uint))
 (n : Nat) (bound : n<W) (evaluated : count.evalT σ=.ok (countValue n bound))
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (start : Nat) (payload : c+3≤start) (separate : pointer<start)
 (bottomBefore : bottom<start) (capacity : start+2*n≤frame) (fits : start+2*n<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ after addresses,
 run (emitted.code reference destination) before=.ok after 0 ∧
 (∀ f depth,(DisjointScalarReturn.call hm reference count destination f depth).run σ=
   if n<depth then .ok ⟨σ.setLocal destination (countValue n bound),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr L b frame F (σ.setLocal destination (countValue n bound)) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem (cellOf b destination)=.val (wmod n) ∧ after.mem (c+2)=.val (wmod n) ∧
 after.mem (c+1)=.val (wmod n) ∧ after.mem c=before.mem (cellOf b reference) ∧
 after.mem pointer=.val (wmod start) ∧ after.mem bottom=.val (wmod start) ∧
 GrowsAllocator b frame 0 σ base before (σ.setLocal destination (countValue n bound)) addresses after ∧
 (∀ x,x≠cellOf b destination → x≠pointer → x≠bottom → x≠c → x≠c+1 → x≠c+2 →
   (x<start ∨ start+2*n≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<n → after.mem (start+2*j)=before.mem (cellOf b reference) ∧
   after.mem (start+2*j+1)=.val (wmod (n-j))) := by
 exact DisjointScalarReturn.endpoint hm σ reference count emitted.value destination n bound evaluated
   base before repr (c+3) pointer bottom start emitted.geometry.1 (Nat.le_refl _) emitted.geometry.2.1
   emitted.geometry.2.2.1 payload separate emitted.geometry.2.2.2.1 emitted.geometry.2.2.2.2.1
   bottomBefore emitted.geometry.2.2.2.2.2 capacity fits current

/-- A genuinely failing checked argument aborts selected code and every
suffix. No failed machine state is manufactured. -/
theorem argument_revert {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} (emitted : Emission b c frame pointer bottom F count)
 (hm : (Ty.ref R).mapFree=true) (σ : State C Γ) (reference : Idx Γ (.mem R))
 (destination : Idx Γ (.val .uint)) (failed : count.evalT σ=.error .revert)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (suffix : List Instr) : run (emitted.code reference destination ++ suffix) before=.revert := by
 have entry := (DisjointScalarEntry.revert hm σ reference count emitted.value failed base before repr
   emitted.geometry.1 (by have a:=emitted.geometry.2.1;have z:=emitted.geometry.2.2.1;omega)).2
 simpa only [Emission.code,DisjointScalarReturn.code,List.append_assoc] using
   entry ((ScalarReturn.image (C:=C) c (Frag.init (Parameters R)) pointer bottom ++
     [.mload (c+2),.mstore (cellOf b destination)]) ++ suffix)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter
