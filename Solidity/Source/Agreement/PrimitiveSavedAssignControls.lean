import Solidity.Source.Agreement.PrimitiveSavedAssign

/-! Concrete saved-copy liveness and physical-slot controls in the independent
interpreters, without source installation or compiler/native claims. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Saving shifts the original head and target; the actual code retains both
copies and both neighboring booleans while replacing the old target. -/
theorem primitive_saved_assign_middle (p : PrimTy)
    (v old : Source.Val E.layout (sourceTy p)) (a b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.local .here) (primitive_source_implicit E p))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p [.bool] [p,p,.bool]))
          (.local .here))) .nil) : RItems E R M k
            (sourceContext [p,.bool,p,.bool]) (sourceContext [p,p,.bool,p,.bool]))
      (.cons v (.cons (.bool a) (.cons old (.cons (.bool b) .nil))))).run (.nil, st) =
      (.ok (.normal (.cons v (.cons v (.cons (.bool a) (.cons v (.cons (.bool b) .nil)))))),
        (.nil, st)) := by
  cases p <;> rfl

/-- The actual model poststate retains the saved head and shifted original. -/
theorem primitive_saved_assign_heads (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    let out := (model.push model.env.1).setLocal
      (modelPrimitiveSlot p tail (p::p::pre)) model.env.1
    (out.env.1, out.env.2.1) = (model.env.1, model.env.1) := by
  rfl

/-- A real false saved value remains false even when the old target was true. -/
theorem primitive_saved_assign_false (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.local .here) (primitive_source_implicit E .bool))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot .bool [] [.bool,.bool]))
          (.local .here))) .nil) : RItems E R M k
            (sourceContext [.bool,.bool]) (sourceContext [.bool,.bool,.bool]))
      (.cons (.bool false) (.cons (.bool true) .nil))).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool false) (.cons (.bool false) .nil)))),
        (.nil, st)) := by
  rfl

/-- Replacing the saved value by the overwritten target breaks correspondence. -/
theorem primitive_saved_assign_old_target_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool,.bool]
      (.cons (.bool false) (.cons (.bool false) (.cons (.bool false) .nil)))
      (true,false,false,()) := by
  intro related
  cases related with
  | cons head rest => exact false_not_true D head

end Solidity.Source.Agreement
