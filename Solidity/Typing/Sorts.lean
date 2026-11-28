import Solidity.Semantics.Heap


namespace Solidity

def isNumericTy : Ty → Bool
  | .prim p => p.isNumeric
  | _ => false

def SVal.keySort {T : Ty} : SVal T → KeySort
  | .prim (p := .bool) _ => .bool
  | .prim (p := .uint) _ => .int
  | .prim (p := .int) _ => .int
  | .struct _ => .struct
  | .array .. => .struct
  | .fixed _ => .struct
  | .map .. => .struct

def MVal.keySort {H : HTy} : (T : Ty) → MVal H T → KeySort
  | .prim .bool, _ => .bool
  | .prim .uint, _ => .int
  | .prim .int, _ => .int
  | .ref _, _ => .identity

theorem SVal.keySort_le_stValue {T : Ty} (v : SVal T) : v.keySort.le .stValue = true := by
  cases v with
  | prim x => rename_i p; cases p <;> rfl
  | _ => rfl

theorem MVal.keySort_le_memValue {H : HTy} : (T : Ty) → (m : MVal H T) →
    (MVal.keySort T m).le .memValue = true
  | .prim .bool, _ | .prim .uint, _ | .prim .int, _ | .ref _, _ => rfl

theorem SVal.keySort_numeric {T : Ty} (hT : isNumericTy T = true) (v : SVal T) :
    v.keySort = .int := by
  cases v with
  | prim x => rename_i p; cases p <;> first | rfl | exact absurd hT (by decide)
  | _ => exact absurd hT (by simp only [isNumericTy, Bool.false_eq_true, not_false_eq_true])

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

theorem SVal.keySort_of_primitive {T : Ty} (hprim : T.isPrimitive = true) (v : SVal T) :
    v.keySort = T.keySort false := by
  cases v with
  | prim x => rename_i p; cases p <;> rfl
  | _ => exact absurd hprim (by simp only [Ty.isPrimitive, Bool.false_eq_true, not_false_eq_true])

end Solidity
