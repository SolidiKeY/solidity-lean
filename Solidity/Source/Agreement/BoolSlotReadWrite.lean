import Solidity.Source.Agreement.BoolSlot

/-! Paired-index laws for the existing Source/model local operations. Recursion
is on the ordinary primitive prefix; no index representation is changed. -/
namespace Solidity.Source.Agreement

/-- Reading the actual selected Source write returns that write. -/
theorem bool_slot_source_get_set (D : Layout) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail))) (b : Bool) :
    (ls.set (sourceBoolSlot tail pre) (.bool b)).get (sourceBoolSlot tail pre) = .bool b := by
  induction pre with
  | nil => cases ls <;> rfl
  | cons p ps ih => cases ls with | cons head rest => exact ih rest

/-- Reading the actual selected model write returns the same boolean. -/
theorem bool_slot_model_get_set (C : Contract) (H : HTy) (pre tail : List PrimTy)
    (ws : TEnv C H (modelContext (pre ++ .bool::tail))) (b : Bool) :
    TEnv.get (modelBoolSlot tail pre) (TEnv.set (modelBoolSlot tail pre) b ws) = b := by
  induction pre with
  | nil => rfl
  | cons p ps ih => exact ih ws.2

/-- Rewriting a Source slot with its actual current value preserves all locals. -/
theorem bool_slot_source_set_get (D : Layout) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail))) :
    ls.set (sourceBoolSlot tail pre) (ls.get (sourceBoolSlot tail pre)) = ls := by
  induction pre with
  | nil => cases ls <;> rfl
  | cons p ps ih =>
    cases ls with
    | cons head rest => exact congrArg (Locals.cons head) (ih rest)

/-- Rewriting a model slot with its actual current value preserves its environment. -/
theorem bool_slot_model_set_get (C : Contract) (H : HTy) (pre tail : List PrimTy)
    (ws : TEnv C H (modelContext (pre ++ .bool::tail))) :
    TEnv.set (modelBoolSlot tail pre) (TEnv.get (modelBoolSlot tail pre) ws) ws = ws := by
  induction pre with
  | nil => cases ws <;> rfl
  | cons p ps ih =>
    cases ws with
    | mk head rest => exact congrArg (fun rest' => (head, rest')) (ih rest)

/-- The last selected Source write wins, retaining all surrounding locals. -/
theorem bool_slot_source_set_set (D : Layout) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail))) (a b : Bool) :
    (ls.set (sourceBoolSlot tail pre) (.bool a)).set (sourceBoolSlot tail pre) (.bool b) =
      ls.set (sourceBoolSlot tail pre) (.bool b) := by
  induction pre with
  | nil => cases ls <;> rfl
  | cons p ps ih =>
    cases ls with
    | cons head rest => exact congrArg (Locals.cons head) (ih rest)

/-- The last selected model write wins at that same physical local position. -/
theorem bool_slot_model_set_set (C : Contract) (H : HTy) (pre tail : List PrimTy)
    (ws : TEnv C H (modelContext (pre ++ .bool::tail))) (a b : Bool) :
    TEnv.set (modelBoolSlot tail pre) b (TEnv.set (modelBoolSlot tail pre) a ws) =
      TEnv.set (modelBoolSlot tail pre) b ws := by
  induction pre with
  | nil => rfl
  | cons p ps ih =>
    cases ws with
    | mk head rest => exact congrArg (fun rest' => (head, rest')) (ih rest)

/-- Two computed negations restore Source locals only when both use the same
actual slot; the initial lookup is retained as an operational premise. -/
theorem bool_slot_source_double_not (D : Layout) (pre tail : List PrimTy)
    (ls : Locals D (sourceContext (pre ++ .bool::tail))) (b : Bool)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (ls.set (sourceBoolSlot tail pre) (.bool (!b))).set
      (sourceBoolSlot tail pre) (.bool (!(!b))) = ls := by
  rw [Bool.not_not, bool_slot_source_set_set, ← read]
  exact bool_slot_source_set_get D pre tail ls

/-- The second model read observes the first write, not the stale input. -/
theorem bool_slot_model_double_not (C : Contract) (H : HTy) (pre tail : List PrimTy)
    (ws : TEnv C H (modelContext (pre ++ .bool::tail))) :
    TEnv.set (modelBoolSlot tail pre)
      (!(TEnv.get (modelBoolSlot tail pre)
        (TEnv.set (modelBoolSlot tail pre) (!(TEnv.get (modelBoolSlot tail pre) ws)) ws)))
      (TEnv.set (modelBoolSlot tail pre) (!(TEnv.get (modelBoolSlot tail pre) ws)) ws) = ws := by
  rw [bool_slot_model_get_set, Bool.not_not, bool_slot_model_set_set]
  exact bool_slot_model_set_get C H pre tail ws

end Solidity.Source.Agreement
