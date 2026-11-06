import Solidity.Backend.MemoryCopies.RuntimeArrayInterface

/-! Allocating rebind of an existing local, with retained old object identities. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

/-- Exact scoped/word execution plus retained old objects and a genuinely fresh
root. The complete runtime cost stays explicit; no size failure is assumed. -/
def RuntimeRebindResult {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size)
    {C : Contract} {Γ : Ctx} (L b frame : Nat) (frag : Frag Γ)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (nestedArrayType element dimensions)))))
    (length : Simple C Γ .uint)
    (newable : (RefTy.array (.ref (nestedArrayType element dimensions))).newArrOk = true)
    (fits : cursor.val + runtimeNestedCost element dimensions size < W) : Prop :=
  let grown := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) memory size
  ∃ base' target,
    TRun.rebindMem destination (.newArr length newable) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ ∧
    run (Objects.referenceRebindCode compiled.child.code b destination length) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag ((state.adopt grown).1.setLocal destination (some grown.val)) base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + runtimeNestedCost element dimensions size,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {Q : RefTy} (old : HRef state.H Q), (old.wk grown.ext).id ≠ grown.val.id)

end Solidity.Backend.MemoryCopies
