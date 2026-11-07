import Solidity.Source.Agreement.PrimitiveSlotReverse

/-! Direction and retained-source controls for actual primitive-local copying.
No installed-source, compiler or native execution is inferred. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Writing the head retains the original deeper value and both bool neighbors. -/
theorem primitive_reverse_middle (p : PrimTy)
    (head old : Source.Val E.layout (sourceTy p)) (a b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p [.bool] [p,.bool]))) :
        RStmt E R M k (sourceContext [p,.bool,p,.bool])
          (sourceContext [p,.bool,p,.bool]))
      (.cons head (.cons (.bool a) (.cons old (.cons (.bool b) .nil))))).run (.nil, st) =
      (.ok (.normal (.cons old (.cons (.bool a) (.cons old (.cons (.bool b) .nil))))),
        (.nil, st)) := by
  cases p <;> rfl

/-- The model head update retains the entire original tail environment. -/
theorem primitive_reverse_tail (p : PrimTy) (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (p::pre ++ p::tail))) :
    (model.setLocal .here (TEnv.get (modelPrimitiveSlot p tail (p::pre)) model.env)).env.2 =
      model.env.2 := by
  rfl

/-- A real true head and false deeper input yield false in both slots. -/
theorem primitive_reverse_false_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot .bool [] [.bool]))) :
        RStmt E R M k (sourceContext [.bool,.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool true) (.cons (.bool false) .nil))).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool false) .nil))), (.nil, st)) := by
  rfl

/-- The result of copying the head the other way cannot represent this result. -/
theorem primitive_reverse_direction_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool false) .nil)) (true,true,()) := by
  intro related
  cases related with
  | cons head rest => exact false_not_true D head

end Solidity.Source.Agreement
