import Solidity.Source.Agreement.PrimitiveCopySequence

/-! Actual copy-order controls for all intrinsically typed primitive values.
These runs are independent interpreter controls, not native/source fixtures. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Copying head outward and then back retains the original head in both slots. -/
theorem primitive_copy_sequence_head_survives (p : PrimTy)
    (head old : Source.Val E.layout (sourceTy p))
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p [] [p])) (.local .here)))
        (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p [] [p])))) .nil) :
          RItems E R M k (sourceContext [p,p]) (sourceContext [p,p]))
      (.cons head (.cons old .nil))).run (.nil, st) =
      (.ok (.normal (.cons head (.cons head .nil))), (.nil, st)) := by
  cases p <;> rfl

/-- Reversing the order actually retains the original deeper value instead. -/
theorem primitive_copy_sequence_deep_survives (p : PrimTy)
    (head old : Source.Val E.layout (sourceTy p))
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.expr (.assign (.local .here) (.local (sourcePrimitiveSlot p [] [p]))))
        (.stmt (.expr (.assign (.local (sourcePrimitiveSlot p [] [p])) (.local .here))) .nil) :
          RItems E R M k (sourceContext [p,p]) (sourceContext [p,p]))
      (.cons head (.cons old .nil))).run (.nil, st) =
      (.ok (.normal (.cons old (.cons old .nil))), (.nil, st)) := by
  cases p <;> rfl

/-- The actual target model also retains the original head, not a swapped pair. -/
theorem primitive_copy_sequence_model_heads (p : PrimTy)
    (model : Solidity.State C (modelContext [p,p])) :
    let mid := model.setLocal (modelPrimitiveSlot p [] [p]) model.env.1
    (mid.setLocal .here (TEnv.get (modelPrimitiveSlot p [] [p]) mid.env)).env =
      (model.env.1, model.env.1, ()) := by
  rfl

/-- For unequal bool inputs the outward-first result is incompatible with a swap. -/
theorem primitive_copy_sequence_not_swap (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool false) .nil)) (true,false,()) := by
  intro related
  cases related with
  | cons head rest => exact false_not_true D head

/-- Inward-first model execution retains the original deeper value in both slots. -/
theorem primitive_copy_inward_model_deep (p : PrimTy)
    (model : Solidity.State C (modelContext [p,p])) :
    let mid := model.setLocal .here (TEnv.get (modelPrimitiveSlot p [] [p]) model.env)
    (mid.setLocal (modelPrimitiveSlot p [] [p]) mid.env.1).env =
      (model.env.2.1, model.env.2.1, ()) := by
  rfl

/-- Actual bool computations from the same initial model state do not commute. -/
theorem primitive_copy_orders_not_commute
    (model : Solidity.State C (modelContext [.bool,.bool])) :
    let initial := (model.setLocal .here true).setLocal (.there .here) false
    let inward := initial.setLocal .here (TEnv.get (.there .here) initial.env)
    let outward := initial.setLocal (.there .here) initial.env.1
    (inward.setLocal (.there .here) inward.env.1).env ≠
      (outward.setLocal .here (TEnv.get (.there .here) outward.env)).env := by
  dsimp only
  intro same
  have impossible : false = true := congrArg Prod.fst same
  cases impossible

end Solidity.Source.Agreement
