import Solidity.Source.Agreement.BoolSlotConditional

/-! Conditional normal-local client and raw Source branch controls. The
side-effect controls are not model/compiler correspondence claims. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The actual condition/read, initial relation and Source execution are all
derived internally; neither branch nor desired final result is a premise. -/
theorem bool_cond_init_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (a b : Bool) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons (.bool (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b))
        (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env))
      (model.push (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b)) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_cond_init_step (R := R) (M := M) (k := k) pre tail a b name G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (bool_cond_init_source (R := R) (M := M) (k := k) pre tail _ a b G F 0 nps ph _ st read)
  have he : out = ⟨model.push (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b),
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_cond_init_model pre tail a b name model).symm.trans ran)).symm
  subst out
  exact related

/-- Evaluating the condition itself still needs actual Source fuel. -/
theorem bool_cond_two_timeout (pre tail : List PrimTy) (a b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.declInit (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b)) rfl :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- The true condition selects its first branch in the actual interpreter. -/
theorem bool_cond_true_source (a b : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.declInit (.cond (.local (sourceBoolSlot [] [])) (.bool a) (.bool b)) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool true) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool a) (.cons (.bool true) .nil))), (.nil, st)) := by
  rfl

/-- The false condition selects its second branch, retaining its original local. -/
theorem bool_cond_false_source (a b : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.declInit (.cond (.local (sourceBoolSlot [] [])) (.bool a) (.bool b)) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool false) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) (.cons (.bool false) .nil))), (.nil, st)) := by
  rfl

/-- Reversing the branches is incompatible with the false-input control. -/
theorem bool_cond_reversed_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool false) .nil)) (true,false,()) := by
  intro related
  cases related with
  | cons head tail => exact false_not_true D head

/-- Source-only control: an unselected assignment does not change the old local. -/
theorem bool_cond_unselected_write (old a v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.cond (.bool true) (.bool a)
        (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool a) (.cons (.bool old) .nil))), (.nil, st)) := by
  rfl

/-- Source-only companion: selecting that assignment changes the original local. -/
theorem bool_cond_selected_write (old a v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.cond (.bool false) (.bool a)
        (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool v) (.cons (.bool v) .nil))), (.nil, st)) := by
  rfl

end Solidity.Source.Agreement
