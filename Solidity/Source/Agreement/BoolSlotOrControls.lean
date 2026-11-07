import Solidity.Source.Agreement.BoolSlotOr

/-! Disjunction normal-local client and raw short-circuit controls. Effectful
Source controls do not supply a model/compiler correspondence for those arms. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Total initial locals, actual left read and Source run are derived internally. -/
theorem bool_or_init_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (b : Bool) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons (.bool ((TEnv.get (modelBoolSlot tail pre) model.env) || b))
        (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env))
      (model.push ((TEnv.get (modelBoolSlot tail pre) model.env) || b)) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_or_init_step (R := R) (M := M) (k := k) pre tail b name G F nps ph)
      _ st model (stateLocals_total E C _ model) 3 _ (.nil, st)
      (bool_or_init_source (R := R) (M := M) (k := k) pre tail _ b G F 0 nps ph _ st read)
  have he : out = ⟨model.push ((TEnv.get (modelBoolSlot tail pre) model.env) || b),
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_or_init_model pre tail b name model).symm.trans ran)).symm
  subst out
  exact related

/-- Even a short-circuit operator must evaluate its actual left operand. -/
theorem bool_or_two_timeout (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 2 nps ph
      (.declInit (.binary .or (.local (sourceBoolSlot tail pre)) (.bool b)) rfl :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Source-only: true on the left suppresses the right-hand local write. -/
theorem bool_or_unselected_write (old v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.binary .or (.bool true) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool old) .nil))), (.nil, st)) := by
  rfl

/-- Source-only: false on the left executes the write and returns its actual value. -/
theorem bool_or_selected_write (old v : Bool) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+4) nps ph
      (.declInit (.binary .or (.bool false) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool v) (.cons (.bool v) .nil))), (.nil, st)) := by
  rfl

/-- The skipped assignment need not have enough horizon to run. -/
theorem bool_or_skipped_rhs_short_fuel (old v : Bool) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F 3 nps ph
      (.declInit (.binary .or (.bool true) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool old) .nil))), (.nil, st)) := by
  rfl

/-- Selecting the same right arm at that horizon times out before its write. -/
theorem bool_or_selected_rhs_short_fuel (old v : Bool) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F 3 nps ph
      (.declInit (.binary .or (.bool false) (.assign (.local .here) (.bool v))) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool old) .nil)).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- Actual false || true returns true, retaining the original false local. -/
theorem bool_or_false_true_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execS G F (n+3) nps ph
      (.declInit (.binary .or (.local (sourceBoolSlot [] [])) (.bool true)) rfl :
        RStmt E R M k (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool false) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool false) .nil))), (.nil, st)) := by
  rfl

/-- Replacing this disjunction result with conjunction's false is incompatible. -/
theorem bool_or_and_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool true) (.cons (.bool false) .nil)) (false,false,()) := by
  intro related
  cases related with
  | cons head tail => cases head

end Solidity.Source.Agreement
