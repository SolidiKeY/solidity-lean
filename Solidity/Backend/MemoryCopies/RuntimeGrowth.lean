import Solidity.Backend.MemoryCopies.RuntimeGrowthInterface

/-! Existing emitted construction proofs supply the compiler's allocator-growth
relation at their actual reached states. No second allocator/compiler is added. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem allocator_cursor_unique {H : HTy} {heap : Heap H} {base : Nat → Fin W} {frame : Nat}
    {machine : Machine} {first second : Fin W}
    (left : Objects.AllocatorRepr heap base frame first machine)
    (right : Objects.AllocatorRepr heap base frame second machine) : first = second :=
  Word.val.inj (left.free.cell.symm.trans right.free.cell)

theorem growsAllocator_of_reached {C : Contract} {Γ Δ : Ctx} {b frame cost : Nat}
    {before : State C Γ} {after : State C Δ} {base base' : Nat → Fin W}
    {machine target : Machine} {cursor : Fin W}
    (initial : Objects.AllocatorRepr before.heap base frame cursor machine)
    (fits : cursor.val + cost < W)
    (reached : Objects.AllocatorRepr after.heap base' frame ⟨cursor.val + cost,fits⟩ target) :
    Objects.GrowsAllocator b frame cost before base machine after base' target := by
  intro actual positive represented room
  have same : actual = cursor := allocator_cursor_unique represented initial
  subst actual
  exact reached

def allocatorGrowth : AllocatorGrowthCertificate := ⟨allocator_cursor_unique,growsAllocator_of_reached⟩

theorem RuntimeNestedDefault.declare_growth {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size)
    {C : Contract} {Γ : Ctx} {L b frame : Nat} {frag : Frag Γ}
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (length : Simple C Γ .uint) (simple : simpleIn length = true)
    (newable : (RefTy.array (.ref (nestedArrayType element dimensions))).newArrOk = true)
    (evaluated : length.evalT state = indexValue size)
    (fits : cursor.val + runtimeNestedCost element dimensions size < W)
    (locals : b + (Γ.length + 1) ≤ frame) :
    let grown := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) memory size
    TRun.declMem (.array (.ref (nestedArrayType element dimensions)))
      (some (.newArr length newable)) (RefTy.mapFree_of_newArrOk newable) state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.ref (nestedArrayType element dimensions))))
        (some grown.val),grown.ext⟩ ∧
    RuntimeGrowthExecution L b frame (runtimeNestedCost element dimensions size)
      (frag.push (.mem (.array (.ref (nestedArrayType element dimensions)))) .ok)
      state ((state.adopt grown).1.push (t := .mem (.array (.ref (nestedArrayType element dimensions)))) (some grown.val))
      base machine (Objects.referenceDeclareCode compiled.child.code b length) := by
  obtain ⟨base',target,source,execution,reached,allocated,extension,stack⟩ :=
    compiled.declare_correct represented allocator positive length simple newable evaluated fits locals
  exact ⟨source,base',target,execution,reached,growsAllocator_of_reached allocator fits allocated,extension,stack⟩

theorem RuntimeNestedDefault.rebind_growth {element : Ty} {dimensions : List Nat}
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
    let grown := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) memory size
    TRun.rebindMem destination (.newArr length newable) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ ∧
    RuntimeGrowthExecution L b frame (runtimeNestedCost element dimensions size) frag
      state ((state.adopt grown).1.setLocal destination (some grown.val))
      base machine (Objects.referenceRebindCode compiled.child.code b destination length) := by
  obtain ⟨base',target,source,execution,reached,allocated,extension,stack,_,_⟩ :=
    compiled.rebind_correct represented allocator positive destination length simple newable evaluated fits
  exact ⟨source,base',target,execution,reached,growsAllocator_of_reached allocator fits allocated,extension,stack⟩

theorem RuntimeGrowthExecution.next_input {C : Contract} {Γ Δ : Ctx} {L b frame cost tail : Nat}
    {frag : Frag Δ} {before : State C Γ} {after : State C Δ}
    {base : Nat → Fin W} {machine : Machine} {code : List Instr}
    (execution : RuntimeGrowthExecution L b frame cost frag before after base machine code)
    (budget : Objects.AllocationInput b frame (cost + tail) before base machine) :
    ∃ base' target, run code machine = .ok target 0 ∧
      Objects.StateRepr L b frame frag after base' target ∧
      Objects.GrowsAllocator b frame cost before base machine after base' target ∧
      Objects.AllocationInput b frame tail after base' target ∧
      BaseExtends before.H base base' ∧ target.stack = machine.stack := by
  obtain ⟨base',target,ran,represented,growth,extension,stack⟩ := execution
  exact ⟨base',target,ran,represented,growth,growth.nextInput budget,extension,stack⟩

#print axioms allocator_cursor_unique
#print axioms growsAllocator_of_reached
#print axioms allocatorGrowth
#print axioms RuntimeNestedDefault.declare_growth
#print axioms RuntimeNestedDefault.rebind_growth
#print axioms RuntimeGrowthExecution.next_input
end Solidity.Backend.MemoryCopies
