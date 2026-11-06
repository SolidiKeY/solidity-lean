import Solidity.Backend.InternalFlow.RuntimeFrameV3TypedHeapExtensionality
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTarget

/-! Old-object preservation alone cannot determine a newly allocated object's
contents. Both heaps below are actual State.alloc constructions. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.Controls
open Evm Evm.Memory
abbrev σ := AllocatingScalarTarget.initial

def altered : MObj σ.H (.array (.prim .bool)) := ⟨[true,true,true],by decide⟩
abbrev left := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).1
abbrev right := (σ.alloc altered).1

theorem old_keeps_insufficient :
 Heap.Keeps (List.prefix_append σ.H [.array (.prim .bool)]) σ.heap left.heap ∧
 Heap.Keeps (List.prefix_append σ.H [.array (.prim .bool)]) σ.heap right.heap ∧
 left.heap≠right.heap ∧ ¬Defaults σ.H.length right.heap := by
 let fresh : HRef left.H (.array (.prim .bool)) := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).2
 have readLeft : left.heap.get fresh=MObj.wk (List.prefix_append σ.H [.array (.prim .bool)]) _ (defaultArray .bool AllocatingScalarSource.size) :=
   Heap.get_alloc_self σ.heap (defaultArray .bool AllocatingScalarSource.size)
 have readRight : right.heap.get fresh=MObj.wk (List.prefix_append σ.H [.array (.prim .bool)]) _ altered :=
   Heap.get_alloc_self σ.heap altered
 refine ⟨Heap.keeps_alloc σ.heap _,Heap.keeps_alloc σ.heap _,?_,?_⟩
 · intro same
   have objects := congrArg (fun hp : Heap left.H => hp.get fresh) same
   change left.heap.get fresh=right.heap.get fresh at objects
   rw [readLeft,readRight] at objects
   have impossible : false=true := congrArg (fun o : MObj left.H (.array (.prim .bool)) => (show List Bool from o.val)[0]!) objects
   cases impossible
 · intro profile
   have contents := eq_of_heq (profile fresh (Nat.le_refl _)).2
   rw [readRight] at contents
   have impossible : true=false := congrArg (fun o : MObj left.H (.array (.prim .bool)) => (show List Bool from o.val)[0]!) contents
   cases impossible

end Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.Controls.old_keeps_insufficient' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.Controls.old_keeps_insufficient
