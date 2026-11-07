import Solidity.Source.Agreement.PrimitiveSlotAssign

/-! Actual local-copy controls. These are raw interpreter controls, not
source-installed, compiler or native execution witnesses. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The actual deeper write retains both differently typed neighboring values. -/
theorem primitive_head_assign_middle (p : PrimTy)
    (v old : Source.Val E.layout (sourceTy p)) (a b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot p [.bool] [p,.bool])) (.local .here)) :
        RStmt E R M k (sourceContext [p,.bool,p,.bool])
          (sourceContext [p,.bool,p,.bool]))
      (.cons v (.cons (.bool a) (.cons old (.cons (.bool b) .nil))))).run (.nil, st) =
      (.ok (.normal (.cons v (.cons (.bool a) (.cons v (.cons (.bool b) .nil))))),
        (.nil, st)) := by
  cases p <;> rfl

/-- The model also retains the head and both neighbors, using its old head. -/
theorem primitive_head_assign_middle_model (p : PrimTy)
    (model : Solidity.State C (modelContext [p,.bool,p,.bool])) :
    (model.setLocal (modelPrimitiveSlot p [.bool] [p,.bool]) model.env.1).env =
      (model.env.1, model.env.2.1, model.env.1, model.env.2.2.2) := by
  rfl

/-- Every unsigned value, including its intrinsic bound, is really copied. -/
theorem primitive_head_assign_uint (v old : PrimTy.uint.Denote)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot .uint [] [.uint])) (.local .here)) :
        RStmt E R M k (sourceContext [.uint,.uint]) (sourceContext [.uint,.uint]))
      (.cons (ofModel E.layout .uint v) (.cons (ofModel E.layout .uint old) .nil))).run
      (.nil, st) = (.ok (.normal (.cons (ofModel E.layout .uint v)
        (.cons (ofModel E.layout .uint v) .nil))), (.nil, st)) := by
  rfl

/-- Signed copying keeps the actual negative or positive integer and its bound. -/
theorem primitive_head_assign_int (v old : PrimTy.int.Denote)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local (sourcePrimitiveSlot .int [] [.int])) (.local .here)) :
        RStmt E R M k (sourceContext [.int,.int]) (sourceContext [.int,.int]))
      (.cons (ofModel E.layout .int v) (.cons (ofModel E.layout .int old) .nil))).run
      (.nil, st) = (.ok (.normal (.cons (ofModel E.layout .int v)
        (.cons (ofModel E.layout .int v) .nil))), (.nil, st)) := by
  rfl

/-- Reversing the copy direction is observably different in the existing model. -/
theorem primitive_copy_reverse_model
    (model : Solidity.State C (modelContext [.bool,.bool])) :
    Solidity.Stmt.runC (.assignLocal .here (.simple (.local (.there .here))))
      ((model.setLocal .here true).setLocal (.there .here) false) =
      .ok ⟨(((model.setLocal .here true).setLocal (.there .here) false).setLocal .here false),
        List.prefix_refl _⟩ := by
  rfl

/-- The reversed result cannot relate to the actual forward copy from true. -/
theorem primitive_copy_reverse_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool true) (.cons (.bool true) .nil)) (false,false,()) := by
  intro related
  cases related with
  | cons head rest => cases head

end Solidity.Source.Agreement
