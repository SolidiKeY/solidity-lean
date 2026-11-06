import Solidity.Source.Agreement.NormalBoolAssign

/-! Existing intrinsic Source/model positions for a boolean beneath an arbitrary
primitive pre. No new index representation or evaluator is introduced. -/
namespace Solidity.Source.Agreement

/-- Existing Source index at the exact end of the primitive pre. -/
def sourceBoolSlot (tail : List PrimTy) : (pre : List PrimTy) →
    Source.Idx (sourceContext (pre ++ .bool::tail)) .bool
  | [] => .here
  | _::ps => .there (sourceBoolSlot tail ps)

/-- Existing model index at the same exact physical local position. -/
def modelBoolSlot (tail : List PrimTy) : (pre : List PrimTy) →
    Solidity.Idx (modelContext (pre ++ .bool::tail)) (.val .bool)
  | [] => .here
  | _::ps => .there (modelBoolSlot tail ps)

/-- Both indices count the same arbitrary pre; no unrelated index is chosen. -/
theorem bool_slot_position (pre tail : List PrimTy) :
    (sourceBoolSlot tail pre).toNat = (modelBoolSlot tail pre).toNat := by
  induction pre with
  | nil => rfl
  | cons p ps ih => exact congrArg Nat.succ ih

/-- Actual existing local-set operations preserve correspondence at that slot.
Every pre value and suffix value is retained; only the selected boolean changes. -/
theorem bool_slot_set_related (D : Layout) (C : Contract) (H : HTy)
    (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail)))
    (ws : TEnv C H (modelContext (pre ++ .bool::tail))) (b : Bool)
    (related : LocalsRel D C H (pre ++ .bool::tail) ls ws) :
    LocalsRel D C H (pre ++ .bool::tail)
      (ls.set (sourceBoolSlot tail pre) (.bool b))
      (TEnv.set (modelBoolSlot tail pre) b ws) := by
  induction pre with
  | nil =>
    obtain ⟨rest, he, hr⟩ := bool_locals_shape D C H tail ls ws.1 ws.2 related
    subst ls
    exact LocalsRel.cons (PrimitiveRel.bool b) hr
  | cons p ps ih =>
    cases related with
    | cons head rest => exact LocalsRel.cons head (ih _ _ rest)

end Solidity.Source.Agreement
