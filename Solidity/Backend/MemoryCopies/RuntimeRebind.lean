import Solidity.Backend.MemoryCopies.RuntimeRebindInterface
import Solidity.Backend.MemoryCopies.RuntimeArrays

/-! Actual allocating rebind retains older objects independently of local binding. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem referenceArray_keeps {H : HTy} (heap : Heap H) (R : RefTy)
    (memory : (Ty.ref R).mapFree = true) (size : Fin W) :
    let grown := Objects.referenceArrayCopy heap R memory size
    Heap.Keeps grown.ext heap grown.heap :=
  Heap.Keeps.trans (SVec.keeps_copyStToM (SVec.replicate (SVal.dflt (.ref R)) size.val) memory heap)
    (Heap.keeps_alloc _ _)

theorem referenceArray_fresh {H : HTy} (heap : Heap H) (R : RefTy)
    (memory : (Ty.ref R).mapFree = true) (size : Fin W) {Q : RefTy} (old : HRef H Q) :
    let grown := Objects.referenceArrayCopy heap R memory size
    (old.wk grown.ext).id ≠ grown.val.id := by
  have lower : H.length ≤ (Objects.referenceArrayCopy heap R memory size).val.id := Grown.alloc_id_ge _
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le old.id_lt lower)

/-- Source and emitted runs are derived, including exact growth and all old
object framing. No existing-local alias facts or target execution are premises. -/
theorem RuntimeNestedDefault.rebind_correct {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size)
    {C : Contract} {Γ : Ctx} {L b frame : Nat} {frag : Frag Γ}
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (destination : Idx Γ (.mem (.array (.ref (nestedArrayType element dimensions)))))
    (length : Simple C Γ .uint) (simple : simpleIn length = true)
    (newable : (RefTy.array (.ref (nestedArrayType element dimensions))).newArrOk = true)
    (evaluated : length.evalT state = indexValue size)
    (fits : cursor.val + runtimeNestedCost element dimensions size < W) :
    RuntimeRebindResult compiled L b frame frag state base cursor machine destination length newable fits := by
  obtain ⟨base', target, source, execution, reached, allocated, extension, stack⟩ :=
    Objects.referenceRebind_correct represented allocator positive (nestedArrayType element dimensions)
      destination length simple newable memory compiled.child size evaluated fits
  exact ⟨base',target,source,execution,reached,allocated,extension,stack,
    referenceArray_keeps state.heap _ memory size,fun old => referenceArray_fresh state.heap _ memory size old⟩

#print axioms referenceArray_keeps
#print axioms referenceArray_fresh
#print axioms RuntimeNestedDefault.rebind_correct
end Solidity.Backend.MemoryCopies
