import Solidity.Source.Agreement.BoolSlotAnd

/-! Conjunction normal-local client and raw short-circuit controls. Effectful
Source controls do not supply a model/compiler correspondence for those arms. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Total initial locals, actual left read and Source run are derived internally. -/
theorem bool_and_init_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (b : Bool) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons (.bool ((TEnv.get (modelBoolSlot tail pre) model.env) && b))
        (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env))
      (model.push ((TEnv.get (modelBoolSlot tail pre) model.env) && b)) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_and_init_step (R := R) (M := M) (k := k) pre tail b name G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (bool_and_init_source (R := R) (M := M) (k := k) pre tail _ b G F 0 nps ph _ st read)
  have he : out = ⟨model.push ((TEnv.get (modelBoolSlot tail pre) model.env) && b),
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_and_init_model pre tail b name model).symm.trans ran)).symm
  subst out
  exact related

/-- Even a short-circuit operator must evaluate its actual left operand. -/
theorem bool_and_two_timeout (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.declInit (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b)) rfl :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Source-only: false on the left suppresses the right-hand local write. -/
theorem bool_and_unselected_write (old v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.binary .and (.bool false) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool old) .nil))), (.nil, st)) := by
  rfl

/-- Source-only: true on the left executes the write and returns its actual value. -/
theorem bool_and_selected_write (old v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.binary .and (.bool true) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool v) (.cons (.bool v) .nil))), (.nil, st)) := by
  rfl

/-- The skipped assignment need not have enough horizon to run. -/
theorem bool_and_skipped_rhs_short_fuel (old v : Bool) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F 3 nps ph
      (.declInit (.binary .and (.bool false) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool old) .nil))), (.nil, st)) := by
  rfl

/-- Selecting the same right arm at that horizon times out before its write. -/
theorem bool_and_selected_rhs_short_fuel (old v : Bool) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F 3 nps ph
      (.declInit (.binary .and (.bool true) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- Actual model conjunction and disjunction differ on this constructed input. -/
theorem bool_and_or_model_control (ps : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext ps)) :
    Solidity.Stmt.runC (.declLocal .bool name (some (.binop .and rfl rfl
      (.simple (.bool false)) (.simple (.bool true))))) model =
      .ok ⟨model.push (t := .val .bool) false, List.prefix_refl _⟩ ∧
    Solidity.Stmt.runC (.declLocal .bool name (some (.binop .or rfl rfl
      (.simple (.bool false)) (.simple (.bool true))))) model =
      .ok ⟨model.push (t := .val .bool) true, List.prefix_refl _⟩ := by
  exact ⟨rfl, rfl⟩

/-- Treating false && true as false || true is observably incompatible. -/
theorem bool_and_or_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool false) .nil)) (true,false,()) := by
  intro related
  cases related with
  | cons head tail => exact false_not_true D head

end Solidity.Source.Agreement
