import Solidity.Backend.MemoryCopies.RuntimeArrayInterface
import Solidity.Backend.MemoryCopies.NestedDefaults

/-! Complete runtime parent demand with production-selected nested defaults.
The existing reference-array loop and scoped declaration emitter are reused. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def selectedRuntimeNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) (size : Fin W)
    (feasible : V2.AllocatorWitness (runtimeNestedCost element dimensions size)) :
    RuntimeNestedDefault element dimensions memory size where
  child := (ReferenceDefaults.compileDefault (nestedArrayType element dimensions) memory).get
    (nested_selection_total element dimensions memory)
  selected := (Option.some_get (nested_selection_total element dimensions memory)).symm
  feasible := feasible

/-- Empty parents allocate one header regardless of the unused child's cost. -/
theorem runtimeNestedCost_zero (element : Ty) (dimensions : List Nat) :
    runtimeNestedCost element dimensions (wmod 0) = 1 := by
  simp only [runtimeNestedCost, show (wmod 0).val = 0 from rfl, Nat.zero_add,
    Nat.zero_mul, Nat.add_zero]

/-- No fitting-child witness is required on an empty-parent path. -/
def emptyRuntimeNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true)
    (feasible : V2.AllocatorWitness 1) : RuntimeNestedDefault element dimensions memory (wmod 0) :=
  selectedRuntimeNestedDefault element dimensions memory (wmod 0)
    (by simpa only [runtimeNestedCost_zero] using feasible)

def RuntimeNestedDefault.code {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size) : List Instr :=
  Objects.referenceArrayCode compiled.child.code

/-- The same selected child produces the same code at every runtime size. -/
theorem RuntimeNestedDefault.code_size_independent {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {left right : Fin W}
    (first : RuntimeNestedDefault element dimensions memory left)
    (second : RuntimeNestedDefault element dimensions memory right) : first.code = second.code := by
  have children : first.child = second.child := Option.some.inj (first.selected.symm.trans second.selected)
  exact congrArg (fun child => Objects.referenceArrayCode child.code) children

/-- The real loop consumes the runtime size, constructs every fresh child,
returns the old cursor and advances the exact complete-parent demand. -/
theorem RuntimeNestedDefault.execute {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine)
    (represented : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + runtimeNestedCost element dimensions size < W) :
    let grown := Objects.referenceArrayCopy heap (nestedArrayType element dimensions) memory size
    ∃ base' target, run compiled.code (machine.push (.val size)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + runtimeNestedCost element dimensions size, fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) :=
  Objects.referenceArray_correct compiled.child heap size base frame machine cursor represented fits

/-- This is the actual scoped declaration and its emitted code, not only a
resolved heap constructor. Source.EM graph/layout refinement is separate. -/
theorem RuntimeNestedDefault.declare_correct {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true} {size : Fin W}
    (compiled : RuntimeNestedDefault element dimensions memory size)
    {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame F state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (length : Simple C Γ .uint) (simple : simpleIn length = true)
    (newable : (RefTy.array (.ref (nestedArrayType element dimensions))).newArrOk = true)
    (evaluated : length.evalT state = indexValue size)
    (fits : cursor.val + runtimeNestedCost element dimensions size < W)
    (locals : b + (Γ.length + 1) ≤ frame) :
    let grown := Objects.referenceArrayCopy state.heap (nestedArrayType element dimensions) memory size
    ∃ base' target,
      TRun.declMem (.array (.ref (nestedArrayType element dimensions)))
        (some (.newArr length newable)) (RefTy.mapFree_of_newArrOk newable) state =
        .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.ref (nestedArrayType element dimensions))))
          (some grown.val), grown.ext⟩ ∧
      run (Objects.referenceDeclareCode compiled.child.code b length) machine = .ok target 0 ∧
      Objects.StateRepr L b frame (F.push (.mem (.array (.ref (nestedArrayType element dimensions)))) .ok)
        ((state.adopt grown).1.push (t := .mem (.array (.ref (nestedArrayType element dimensions))))
          (some grown.val)) base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + runtimeNestedCost element dimensions size, fits⟩ target ∧
      BaseExtends state.H base base' ∧ target.stack = machine.stack :=
  Objects.referenceDeclare_correct represented allocator positive (nestedArrayType element dimensions)
    length simple newable memory compiled.child size evaluated fits locals

#print axioms selectedRuntimeNestedDefault
#print axioms runtimeNestedCost_zero
#print axioms emptyRuntimeNestedDefault
#print axioms RuntimeNestedDefault.code_size_independent
#print axioms RuntimeNestedDefault.execute
#print axioms RuntimeNestedDefault.declare_correct
end Solidity.Backend.MemoryCopies
