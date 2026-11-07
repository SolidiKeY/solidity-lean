import Solidity.Source.Agreement.BoolSlotRepeated

/-! Both actual executions are supplied internally; restoration concerns local
updates, not source/world rollback or compiler/native correspondence. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Concrete importing client: actual Source execution, actual model execution
and their normal-locals correspondence, without any supplied run or operand. -/
theorem bool_double_toggle_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    (execItems G F (n+6) nps ph
      (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
          (.unary .not (.local (sourceBoolSlot tail pre))))) .nil) : RItems E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (pre ++ .bool::tail)))
      (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env)).run (.nil, st) =
      (.ok (.normal (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env)), (.nil, st)) ∧
    Prog.runC
      (.cons (.assignLocal (modelBoolSlot tail pre)
        (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail pre)
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) .nil)) model =
      .ok ⟨model, List.prefix_refl _⟩ ∧
    StateLocalsRel E C (pre ++ .bool::tail)
      (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env) model := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  have source : (execItems G F (n+6) nps ph
      (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
          (.unary .not (.local (sourceBoolSlot tail pre))))) .nil) : RItems E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (pre ++ .bool::tail)))
      (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env)).run (.nil, st) =
      (.ok (.normal (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env)), (.nil, st)) :=
    bool_double_toggle_source pre tail _ G F n nps ph _ st read
  obtain ⟨out, ran, related⟩ :=
    (bool_double_toggle_agree (R := R) (M := M) (k := k) pre tail G F nps ph)
      _ st model (stateLocals_total E C _ model) (n+6) _ (.nil, st) source
  have he : out = ⟨model, List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_double_toggle_model pre tail model).symm.trans ran)).symm
  subst out
  exact ⟨source, bool_double_toggle_model pre tail model, related⟩

/-- Horizon five cannot give a normal two-update result: the second actual
statement has only horizon three. No final locals are invented for an error. -/
theorem bool_double_toggle_five_not_normal (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    ¬ ∃ final journal,
      (execItems G F 5 nps ph
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
          (.unary .not (.local (sourceBoolSlot tail pre)))))
          (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
            (.unary .not (.local (sourceBoolSlot tail pre))))) .nil) : RItems E R M k
          (sourceContext (pre ++ .bool::tail)) (sourceContext (pre ++ .bool::tail)))
        ls).run (.nil, st) = (.ok (.normal final), journal) := by
  rintro ⟨final, journal, ran⟩
  obtain ⟨mid, midSt, firstRun, restRun⟩ := source_cons_cut G F 4 nps ph _ _ ls st final journal ran
  obtain ⟨last, lastSt, secondRun, nilRun⟩ := source_cons_cut G F 3 nps ph _ _ mid midSt final journal restRun
  rw [bool_toggle_three_timeout] at secondRun
  cases secondRun

/-- Source-only countercontrol: updating two different slots changes both;
this is not the same-slot restoration theorem. -/
theorem bool_different_slots_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+6) nps ph
      (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here))) :
        RStmt E R M k (sourceContext [.bool,.bool]) (sourceContext [.bool,.bool]))
        (.stmt (.expr (.assign (.local (.there .here))
          (.unary .not (.local (.there .here))))) .nil))
      (.cons (.bool false) (.cons (.bool false) .nil))).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool true) .nil))), (.nil, st)) := by
  rfl

/-- The actual different-slot result cannot be identified with the old locals. -/
theorem bool_different_slots_restore_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool true) (.cons (.bool true) .nil)) (false,false,()) := by
  intro related
  cases related with
  | cons head tail => cases head

end Solidity.Source.Agreement
