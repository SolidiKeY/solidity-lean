import Solidity.Semantics.Heap

/-!
# Runtime sorts of typed values

The KeY sort of a value the interpreter holds — the runtime side of
`Ty.keySort`, which is the static side.  The two do not always agree, and
that is the point of having both: a storage array or mapping is a `Struct`
node at runtime (`structRules.key` builds it from `mtSt` with `at(i)`
fields, and the copy taclets read it `find<[Struct]>`), while its static
type's sort is `T[]` / `mapping(K => V)`, a sibling of `Struct` below
`StValue`.  `Counterexamples/StaticRuntimeSort.lean` exhibits the gap;
`SortCheck/Faithfulness.lean` reads the runtime sort of what a taclet's
read finds.  A typed value's sort is its type's: a word's by its primitive
type, a storage node `Struct`, a memory reference `Identity`.
-/

namespace Solidity

/-- A numeric word type. -/
def isNumericTy : Ty → Bool
  | .prim p => p.isNumeric
  | _ => false

/-- The sort of a storage value: `Prim` subsorts for the primitives,
`Struct` for every tree node. -/
def SVal.keySort {T : Ty} : SVal T → KeySort
  | .prim (p := .bool) _ => .bool
  | .prim (p := .uint) _ => .int
  | .prim (p := .int) _ => .int
  | .struct _ => .struct
  | .array .. => .struct
  | .fixed _ => .struct
  | .map .. => .struct

/-- The sort of a memory slot: `Prim` subsorts inline, `Identity` for a
reference. -/
def MVal.keySort {H : HTy} : (T : Ty) → MVal H T → KeySort
  | .prim .bool, _ => .bool
  | .prim .uint, _ => .int
  | .prim .int, _ => .int
  | .ref _, _ => .identity

/-- Every storage value is an `StValue`: why a `find<[StValue]>` read claims
nothing. -/
theorem SVal.keySort_le_stValue {T : Ty} (v : SVal T) : v.keySort.le .stValue = true := by
  cases v with
  | prim x => rename_i p; cases p <;> rfl
  | _ => rfl

/-- Every memory value is a `MemValue`. -/
theorem MVal.keySort_le_memValue {H : HTy} : (T : Ty) → (m : MVal H T) →
    (MVal.keySort T m).le .memValue = true
  | .prim .bool, _ | .prim .uint, _ | .prim .int, _ | .ref _, _ => rfl

/-- A value at a numeric type is an `int`. -/
theorem SVal.keySort_numeric {T : Ty} (hT : isNumericTy T = true) (v : SVal T) :
    v.keySort = .int := by
  cases v with
  | prim x => rename_i p; cases p <;> first | rfl | exact absurd hT (by decide)
  | _ => exact absurd hT (by simp only [isNumericTy, Bool.false_eq_true, not_false_eq_true])

/-- A value at a reference type is a `Struct` node. -/
theorem SVal.keySort_ref {T : Ty} (hT : T.isReference = true) (v : SVal T) :
    v.keySort = .struct := by
  cases v with
  | prim x => exact absurd hT (by simp only [Ty.isReference, Ty.isPrimitive, Bool.not_true,
      Bool.false_eq_true, not_false_eq_true])
  | _ => rfl

theorem MVal.keySort_numeric {H : HTy} {T : Ty} (hT : isNumericTy T = true) (m : MVal H T) :
    MVal.keySort T m = .int := by
  cases T with
  | prim p => cases p <;> first | rfl | exact absurd hT (by decide)
  | ref _ => exact absurd hT (by simp only [isNumericTy, Bool.false_eq_true, not_false_eq_true])

theorem MVal.keySort_ref {H : HTy} {T : Ty} (hT : T.isReference = true) (m : MVal H T) :
    MVal.keySort T m = .identity := by
  cases T with
  | prim p => exact absurd hT (by simp only [Ty.isReference, Ty.isPrimitive, Bool.not_true,
      Bool.false_eq_true, not_false_eq_true])
  | ref _ => rfl

/-- On primitive types the static and runtime sorts agree: an `int`/`uint`
cell holds an `int`, a `bool` cell a `bool`. -/
theorem SVal.keySort_of_primitive {T : Ty} (hprim : T.isPrimitive = true) (v : SVal T) :
    v.keySort = T.keySort false := by
  cases v with
  | prim x => rename_i p; cases p <;> rfl
  | _ => exact absurd hprim (by simp only [Ty.isPrimitive, Bool.false_eq_true, not_false_eq_true])

end Solidity
