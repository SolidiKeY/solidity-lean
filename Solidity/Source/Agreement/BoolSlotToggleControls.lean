import Solidity.Source.Agreement.BoolSlotToggle

/-! Actual read/modify/write clients and restoration controls. These are
resolved normal-local pairs, not original source/compiler/native fixtures. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The operand, Source run and initial relation are derived internally. -/
theorem bool_toggle_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (pre ++ .bool::tail)
      ((localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).set
        (sourceBoolSlot tail pre) (.bool (!(TEnv.get (modelBoolSlot tail pre) model.env))))
      (model.setLocal (modelBoolSlot tail pre) (!(TEnv.get (modelBoolSlot tail pre) model.env))) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_toggle_step (R := R) (M := M) (k := k) pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) 4 _ (.nil, st)
      (bool_toggle_source (R := R) (M := M) (k := k) pre tail _ G F 0 nps ph _ st read)
  have he : out = ⟨model.setLocal (modelBoolSlot tail pre)
      (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_toggle_model pre tail model).symm.trans ran)).symm
  subst out
  exact related

/-- The RHS must read its old operand before assignment can succeed. -/
theorem bool_toggle_three_timeout (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 3 nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))) : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (pre ++ .bool::tail)))
      ls).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- A false old operand yields a true return value and the true updated local. -/
theorem bool_toggle_false_eval (G : Glob E) (F : Fr) (n : Nat) (st : St E) :
    (evalE G F (n+3) (.assign (.local (sourceBoolSlot [] []))
      (.unary .not (.local (sourceBoolSlot [] []))))).run
      (.cons (.bool false) .nil, st) =
      (.ok (.val (.bool true)), (.cons (.bool true) .nil, st)) := by
  rfl

/-- A true old operand yields a false return value and the false updated local. -/
theorem bool_toggle_true_eval (G : Glob E) (F : Fr) (n : Nat) (st : St E) :
    (evalE G F (n+3) (.assign (.local (sourceBoolSlot [] []))
      (.unary .not (.local (sourceBoolSlot [] []))))).run
      (.cons (.bool true) .nil, st) =
      (.ok (.val (.bool false)), (.cons (.bool false) .nil, st)) := by
  rfl

/-- Two actual Source statements read the intervening update, restoring the
original head and retaining the entire original tail and nonlocal state. -/
theorem bool_toggle_twice_head_source (b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+6) nps ph
      (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here))) :
        RStmt E R M k (sourceContext (.bool::ps)) (sourceContext (.bool::ps)))
        (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here)))) .nil))
      (.cons (.bool b) ls)).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) ls)), (.nil, st)) := by
  cases b <;> rfl

/-- The same actual model program restores its complete original state. -/
theorem bool_toggle_twice_head_model (ps : List PrimTy)
    (model : Solidity.State C (modelContext (.bool::ps))) :
    Prog.runC (.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local .here))))
      (.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local .here)))) .nil)) model =
      .ok ⟨model, List.prefix_refl _⟩ := by
  have restored : (model.setLocal .here (!model.env.1)).setLocal .here
      (!(TEnv.get .here (model.setLocal .here (!model.env.1)).env)) = model := by
    simp only [Solidity.State.setLocal, TEnv.set, TEnv.get, Bool.not_not]
    first | rfl | (cases model <;> rfl)
  have ran : Prog.runC
      (.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local .here))))
        (.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local .here)))) .nil)) model =
      .ok ⟨(model.setLocal .here (!model.env.1)).setLocal .here
        (!(TEnv.get .here (model.setLocal .here (!model.env.1)).env)), List.prefix_refl _⟩ := by
    rfl
  simpa only [restored] using ran

/-- Returning the old false operand would contradict the actual new true result. -/
theorem bool_toggle_old_result_refused (D : Layout) :
    ¬ PrimitiveRel D .bool (.bool true) false := by
  intro related
  cases related

end Solidity.Source.Agreement
