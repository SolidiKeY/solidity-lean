import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTurn
import Solidity.Semantics.AllocBytes

/-! Typed exact new-object inventory for the existing allocating scalar family.
This is a predicate on an actual reached heap/address map, not an evaluator. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory
open Evm Evm.Memory

def Holds {C : Contract} {Γ : Ctx} (initial count cursor : Nat)
 (σ : State C Γ) (base : Nat → Fin W) : Prop :=
 ∀ j,j<count → ∃ r : HRef σ.H (.array (.prim .bool)),
 r.id=initial+j ∧ σ.heap.get r=defaultArray .bool AllocatingScalarSource.size ∧
 (base r.id).val=cursor+4*j

/-- Every new reference belongs to the inventory; no extra heap object is hidden
between the initial prefix and the exact final heap length. -/
theorem covers {C : Contract} {Γ : Ctx} {initial count cursor : Nat}
 {σ : State C Γ} {base : Nat → Fin W}
 (inventory : Holds initial count cursor σ base) (size : σ.H.length=initial+count)
 {R : RefTy} (r : HRef σ.H R) (newObject : initial≤r.id) :
 ∃ j,j<count ∧ r.id=initial+j ∧ R=.array (.prim .bool) ∧
 HEq (σ.heap.get r) (defaultArray .bool AllocatingScalarSource.size : MObj σ.H (.array (.prim .bool))) ∧
 (base r.id).val=cursor+4*j := by
 have bound : r.id<σ.H.length := (List.getElem?_eq_some_iff.mp r.get?).1
 have small : r.id-initial<count := by omega
 obtain ⟨fresh,identity,contents,address⟩ := inventory (r.id-initial) small
 have sameId : r.id=fresh.id := by omega
 obtain ⟨sameType,sameRef⟩ := HRef.heq_of_id r fresh sameId
 cases sameType
 have same : r=fresh := eq_of_heq sameRef
 subst fresh
 exact ⟨r.id-initial,small,by omega,rfl,heq_of_eq contents,address⟩

/-- Different inventory identities have different actual physical bases. -/
theorem distinct {C : Contract} {Γ : Ctx} {initial count cursor : Nat}
 {σ : State C Γ} {base : Nat → Fin W}
 (inventory : Holds initial count cursor σ base) (i j : Nat) (hi : i<count) (hj : j<count) (different : i≠j) :
 base (initial+i)≠base (initial+j) := by
 obtain ⟨r,ri,rc,ra⟩ := inventory i hi
 obtain ⟨s,si,sc,sa⟩ := inventory j hj
 rw [ri] at ra
 rw [si] at sa
 intro same
 have values := congrArg Fin.val same
 omega

/-- Physical observations of each inventory object at the same reached heap. -/
theorem observe {C : Contract} {Γ : Ctx} {initial count cursor frame : Nat}
 {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
 (inventory : Holds initial count cursor σ base) (repr : HeapRepr σ.heap base frame m) :
 ∀ j,j<count →
 [m.mem (cursor+4*j),m.mem (cursor+4*j+1),m.mem (cursor+4*j+2),m.mem (cursor+4*j+3)]=
 [w[3],w[0],w[0],w[0]] := by
 intro j small
 obtain ⟨r,identity,contents,address⟩ := inventory j small
 have array := repr.arrays r
 have length : σ.heap.len r .dyn=3 := by
   simp only [Heap.len,MObj.elems_dyn,contents,defaultArray,List.length_replicate,AllocatingScalarSource.size]
 have header := array.length
 rw [length,address] at header
 have zero := array.elements 0 false (by rw [contents];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 have one := array.elements 1 false (by rw [contents];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 have two := array.elements 2 false (by rw [contents];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 change m.mem ((base r.id).val+1)=w[0] at zero
 change m.mem ((base r.id).val+2)=w[0] at one
 change m.mem ((base r.id).val+3)=w[0] at two
 rw [address] at zero one two
 rw [header,zero,one,two]
 rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.observe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.observe

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.covers

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.distinct
