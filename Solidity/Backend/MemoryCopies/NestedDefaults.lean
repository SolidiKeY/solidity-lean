import Solidity.Backend.MemoryCopies.NestedDefaultInterface

/-! Total production selection for nested intrinsic array defaults. Successful
execution uses the existing builder simulation and exact represented demand;
this is not a new compiler or a Source size-failure theorem. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_mapFree (element : Ty) : (dimensions : List Nat) →
    (Ty.ref (nestedArrayType element dimensions)).mapFree = element.mapFree
  | [] => rfl
  | _ :: rest => nested_mapFree element rest

theorem nested_selection_total (element : Ty) :
    (dimensions : List Nat) →
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) →
    (ReferenceDefaults.compileDefault (nestedArrayType element dimensions) memory).isSome = true
  | [], _ => rfl
  | n :: rest, memory => by
    have previous : (ReferenceDefaults.compileDefault (nestedArrayType element rest) memory).isSome = true :=
      nested_selection_total element rest memory
    change ((ReferenceDefaults.compileDefault (nestedArrayType element rest) memory).bind
      (fun child => some (Objects.DefaultBuilder.fixedReference child n))).isSome = true
    cases selected : ReferenceDefaults.compileDefault (nestedArrayType element rest) memory with
    | none => rw [selected] at previous; cases previous
    | some child => rfl

/-- Extract only the actual production compiler result; no parallel code
construction or silently supplied target execution is used. -/
def selectedNestedDefault (element : Ty) (dimensions : List Nat)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true)
    (feasible : V2.AllocatorWitness
      (ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)))) :
    SelectedNestedDefault element dimensions memory where
  certified := ⟨(ReferenceDefaults.compileDefault (nestedArrayType element dimensions) memory).get
    (nested_selection_total element dimensions memory), feasible⟩
  selected := (Option.some_get (nested_selection_total element dimensions memory)).symm

/-- Exact word-cell demand includes each parent reservation and every child. -/
theorem nested_default_cost (element : Ty) (dimensions : List Nat) :
    ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) =
      dimensions.foldr (fun n child => max 1 n + n * child) 1 := by
  induction dimensions with
  | nil => rfl
  | cons n rest previous =>
    rw [nestedArrayType, ReferenceDefaults.defaultCells, previous]
    rfl

theorem SelectedNestedDefault.code_ne_nil {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true}
    (selected : SelectedNestedDefault element dimensions memory) :
    selected.certified.builder.code ≠ [] := selected.certified.code_ne_nil

/-- The production-selected code actually grows the represented allocator,
returns the old cursor, and preserves old bases, lower cells and gaps. -/
theorem SelectedNestedDefault.execute {element : Ty} {dimensions : List Nat}
    {memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true}
    (selected : SelectedNestedDefault element dimensions memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine)
    (represented : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + ReferenceDefaults.defaultCells
      (.ref (nestedArrayType element dimensions)) < W) :
    Objects.DefaultBuildResult heap (nestedArrayType element dimensions) memory
      selected.certified.builder.code (ReferenceDefaults.defaultCells
        (.ref (nestedArrayType element dimensions))) base frame cursor machine fits :=
  selected.certified.builder.correct heap base frame cursor machine represented fits

#print axioms nested_mapFree
#print axioms nested_selection_total
#print axioms selectedNestedDefault
#print axioms nested_default_cost
#print axioms SelectedNestedDefault.code_ne_nil
#print axioms SelectedNestedDefault.execute
end Solidity.Backend.MemoryCopies
