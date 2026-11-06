import Solidity.Source.Agreement.BoolSlotNot

/-! Existing unary-not interpreter controls; no generic source or compiler claim. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The actual read and Source run are derived internally from total initial
locals. No desired operand, normal-result or final-state premise is supplied. -/
theorem bool_not_init_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons (.bool (!(TEnv.get (modelBoolSlot tail pre) model.env)))
        (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env))
      (model.push (!(TEnv.get (modelBoolSlot tail pre) model.env))) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_not_init_step (R := R) (M := M) (k := k) pre tail name G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (bool_not_init_source (R := R) (M := M) (k := k) pre tail _ G F 0 nps ph _ st read)
  have he : out = ⟨model.push (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_not_init_model pre tail name model).symm.trans ran)).symm
  subst out
  exact related

/-- The additional unary evaluation keeps its real Source horizon. -/
theorem bool_not_init_two_timeout (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.declInit (.unary .not (.local (sourceBoolSlot tail pre))) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
      ls).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- Actual true input produces false, retaining the original true local. -/
theorem bool_not_true_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.declInit (.unary .not (.local (sourceBoolSlot [] []))) rfl : RStmt E R M k
        (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool true) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool true) .nil))), (.nil, st)) := by
  rfl

/-- Actual false input produces true; the operator is not a constant function. -/
theorem bool_not_false_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.declInit (.unary .not (.local (sourceBoolSlot [] []))) rfl : RStmt E R M k
        (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool false) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool false) .nil))), (.nil, st)) := by
  rfl

/-- Omitting negation is incompatible with the actual true-input result. -/
theorem bool_not_identity_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool true) .nil)) (true,true,()) := by
  intro related
  cases related with
  | cons head tail => exact false_not_true D head

end Solidity.Source.Agreement
