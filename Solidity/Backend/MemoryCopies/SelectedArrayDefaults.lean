import Solidity.Backend.MemoryCopies.SelectedArrayDefaultInterface

/-! Lift actual production selection through fixed wrappers and reuse the existing
reference-array and scoped declaration emitters. No compiler branch is added. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory Semantics

theorem fixedDefault_mapFree (root : RefTy) : (dimensions : List Nat) →
    (Ty.ref (fixedDefaultType root dimensions)).mapFree = (Ty.ref root).mapFree
  | [] => rfl
  | _ :: rest => fixedDefault_mapFree root rest

theorem fixed_selection_total (root : RefTy) : (dimensions : List Nat) →
    (memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true) →
    (available : ∀ proof : (Ty.ref root).mapFree = true,
      (ReferenceDefaults.compileDefault root proof).isSome = true) →
    (ReferenceDefaults.compileDefault (fixedDefaultType root dimensions) memory).isSome = true
  | [], memory, available => available memory
  | count :: rest, memory, available => by
    have previous : (ReferenceDefaults.compileDefault (fixedDefaultType root rest) memory).isSome = true :=
      fixed_selection_total root rest memory available
    change ((ReferenceDefaults.compileDefault (fixedDefaultType root rest) memory).bind
      (fun child => some (Objects.DefaultBuilder.fixedReference child count))).isSome = true
    cases selected : ReferenceDefaults.compileDefault (fixedDefaultType root rest) memory with
    | none => rw [selected] at previous; cases previous
    | some child => rfl

theorem primitive_struct_selected (name : Name) (fields : primitiveMembers (structDef name) = true)
    (memory : (Ty.ref (.struct name)).mapFree = true) :
    (ReferenceDefaults.compileDefault (.struct name) memory).isSome = true := by
  change (if proof : primitiveMembers (structDef name) = true then
    some (Objects.DefaultBuilder.primitiveStruct proof memory) else none).isSome = true
  rw [dif_pos fields]
  rfl

theorem fixed_default_cost (root : RefTy) (dimensions : List Nat) :
    ReferenceDefaults.defaultCells (.ref (fixedDefaultType root dimensions)) =
      dimensions.foldr (fun count child => max 1 count + count * child)
        (ReferenceDefaults.defaultCells (.ref root)) := by
  induction dimensions with
  | nil => rfl
  | cons count rest previous =>
    rw [fixedDefaultType,ReferenceDefaults.defaultCells,previous]
    rfl

def selectedArrayDefault (root : RefTy) (dimensions : List Nat)
    (memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true) (size : Fin W)
    (available : ∀ proof : (Ty.ref root).mapFree = true,
      (ReferenceDefaults.compileDefault root proof).isSome = true)
    (feasible : V2.AllocatorWitness (selectedArrayCost root dimensions size)) :
    SelectedArrayDefault root dimensions memory size where
  child := (ReferenceDefaults.compileDefault (fixedDefaultType root dimensions) memory).get
    (fixed_selection_total root dimensions memory available)
  selected := (Option.some_get (fixed_selection_total root dimensions memory available)).symm
  feasible := feasible

theorem selectedArrayCost_zero (root : RefTy) (dimensions : List Nat) :
    selectedArrayCost root dimensions (wmod 0) = 1 := by
  simp only [selectedArrayCost,show (wmod 0).val = 0 from rfl,Nat.zero_add,Nat.zero_mul,Nat.add_zero]

def SelectedArrayDefault.code {root : RefTy} {dimensions : List Nat}
    {memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true} {size : Fin W}
    (compiled : SelectedArrayDefault root dimensions memory size) : List Instr :=
  Objects.referenceArrayCode compiled.child.code

theorem SelectedArrayDefault.code_size_independent {root : RefTy} {dimensions : List Nat}
    {memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true} {left right : Fin W}
    (first : SelectedArrayDefault root dimensions memory left)
    (second : SelectedArrayDefault root dimensions memory right) : first.code = second.code := by
  have same : first.child = second.child := Option.some.inj (first.selected.symm.trans second.selected)
  exact congrArg (fun child => Objects.referenceArrayCode child.code) same

theorem SelectedArrayDefault.execute {root : RefTy} {dimensions : List Nat}
    {memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true} {size : Fin W}
    (compiled : SelectedArrayDefault root dimensions memory size)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine)
    (represented : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + selectedArrayCost root dimensions size < W) :
    let grown := Objects.referenceArrayCopy heap (fixedDefaultType root dimensions) memory size
    ∃ base' target, run compiled.code (machine.push (.val size)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + selectedArrayCost root dimensions size,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) :=
  Objects.referenceArray_correct compiled.child heap size base frame machine cursor represented fits

theorem SelectedArrayDefault.declare_correct {root : RefTy} {dimensions : List Nat}
    {memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true} {size : Fin W}
    (compiled : SelectedArrayDefault root dimensions memory size)
    {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame F state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (length : Simple C Γ .uint) (simple : simpleIn length = true)
    (newable : (RefTy.array (.ref (fixedDefaultType root dimensions))).newArrOk = true)
    (evaluated : length.evalT state = indexValue size)
    (fits : cursor.val + selectedArrayCost root dimensions size < W)
    (locals : b + (Γ.length + 1) ≤ frame) :
    let grown := Objects.referenceArrayCopy state.heap (fixedDefaultType root dimensions) memory size
    ∃ base' target,
      TRun.declMem (.array (.ref (fixedDefaultType root dimensions)))
        (some (.newArr length newable)) (RefTy.mapFree_of_newArrOk newable) state =
        .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.ref (fixedDefaultType root dimensions))))
          (some grown.val), grown.ext⟩ ∧
      run (Objects.referenceDeclareCode compiled.child.code b length) machine = .ok target 0 ∧
      Objects.StateRepr L b frame (F.push (.mem (.array (.ref (fixedDefaultType root dimensions)))) .ok)
        ((state.adopt grown).1.push (t := .mem (.array (.ref (fixedDefaultType root dimensions))))
          (some grown.val)) base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + selectedArrayCost root dimensions size, fits⟩ target ∧
      BaseExtends state.H base base' ∧ target.stack = machine.stack :=
  Objects.referenceDeclare_correct represented allocator positive (fixedDefaultType root dimensions)
    length simple newable memory compiled.child size evaluated fits locals

#print axioms fixedDefault_mapFree
#print axioms fixed_selection_total
#print axioms primitive_struct_selected
#print axioms fixed_default_cost
#print axioms selectedArrayDefault
#print axioms selectedArrayCost_zero
#print axioms SelectedArrayDefault.code_size_independent
#print axioms SelectedArrayDefault.execute
#print axioms SelectedArrayDefault.declare_correct
end Solidity.Backend.MemoryCopies
