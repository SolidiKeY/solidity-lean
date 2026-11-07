import Solidity.Source.Agreement.BoolSlotAssign

/-! Actual middle-slot controls, without source/compiler/native fixture claims. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- A selected middle write retains both surrounding values in the actual run. -/
theorem bool_middle_source (a b c v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourceBoolSlot [.bool] [.bool])) (.bool v)) :
        RStmt E R M k (sourceContext [.bool,.bool,.bool])
          (sourceContext [.bool,.bool,.bool]))
      (.cons (.bool a) (.cons (.bool b) (.cons (.bool c) .nil)))).run (.nil, st) =
      (.ok (.normal (.cons (.bool a) (.cons (.bool v) (.cons (.bool c) .nil)))),
        (.nil, st)) := by
  rfl

/-- The actual model middle write retains neighbors and exposes the new value. -/
theorem bool_middle_model (v : Bool)
    (model : Solidity.State C (modelContext [.bool,.bool,.bool])) :
    (model.setLocal (modelBoolSlot [.bool] [.bool]) v).env =
      (model.env.1, v, model.env.2.2) := by
  rfl

/-- Choosing the head instead of the middle is observably incompatible even
for the smallest two-slot control; slot association is substantive. -/
theorem bool_wrong_slot_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      ((Locals.cons (.bool false) (.cons (.bool false) .nil)).set
        (sourceBoolSlot [] [.bool]) (.bool true))
      (TEnv.set (modelBoolSlot [.bool] []) true (false,false,())) := by
  intro related
  cases related with
  | cons head tail => exact false_not_true D head

end Solidity.Source.Agreement
