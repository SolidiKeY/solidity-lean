import Solidity.Source.Agreement.BoolSlotSaved

/-! Saved-old-value liveness for computed updates; no compiler, physical memory,
source installation or rollback correspondence is claimed. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The initial locals, old operand and actual Source run are derived internally;
the actual model result retains that same old value in the saved head. -/
theorem bool_saved_toggle_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons (.bool (TEnv.get (modelBoolSlot tail pre) model.env))
        ((localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).set
          (sourceBoolSlot tail pre) (.bool (!(TEnv.get (modelBoolSlot tail pre) model.env)))))
      ((model.setLocal (modelBoolSlot tail pre)
        (!(TEnv.get (modelBoolSlot tail pre) model.env))).push
          (TEnv.get (modelBoolSlot tail pre) model.env)) := by
  have read : (localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
      (sourceBoolSlot tail pre) = .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail _ _
      (stateLocals_total E C _ model))
  obtain ⟨out, ran, related⟩ :=
    (bool_saved_toggle_agree (R := R) (M := M) (k := k) pre tail name G F nps ph)
      _ st model (stateLocals_total E C _ model) 6 _ (.nil, st)
      (bool_saved_toggle_source (R := R) (M := M) (k := k) pre tail _ G F 0 nps ph _ st read)
  have he : out = ⟨(model.setLocal (modelBoolSlot tail pre)
      (!(TEnv.get (modelBoolSlot tail pre) model.env))).push
        (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_saved_toggle_model pre tail name model).symm.trans ran)).symm
  subst out
  exact related

/-- No normal result is fabricated when the computed update lacks its horizon. -/
theorem bool_saved_toggle_five_not_normal (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    ¬ ∃ final journal,
      (execItems G F 5 nps ph
        (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl)
          (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre)))
            (.unary .not (.local (sourceBoolSlot tail (.bool::pre)))))) .nil) : RItems E R M k
          (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
        ls).run (.nil, st) = (.ok (.normal final), journal) := by
  rintro ⟨final, journal, ran⟩
  obtain ⟨mid, midSt, firstRun, restRun⟩ := source_cons_cut G F 4 nps ph _ _ ls st final journal ran
  obtain ⟨last, lastSt, secondRun, nilRun⟩ := source_cons_cut G F 3 nps ph _ _ mid midSt final journal restRun
  rw [bool_toggle_three_timeout] at secondRun
  cases secondRun

/-- A real false input leaves false in the saved copy and true in the original. -/
theorem bool_saved_toggle_false_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+6) nps ph
      (.stmt (.declInit (.local (sourceBoolSlot [] [])) rfl)
        (.stmt (.expr (.assign (.local (sourceBoolSlot [] [.bool]))
          (.unary .not (.local (sourceBoolSlot [] [.bool]))))) .nil) : RItems E R M k
        (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool false) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool true) .nil))), (.nil, st)) := by
  rfl

/-- A real true input leaves true in the saved copy and false in the original. -/
theorem bool_saved_toggle_true_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+6) nps ph
      (.stmt (.declInit (.local (sourceBoolSlot [] [])) rfl)
        (.stmt (.expr (.assign (.local (sourceBoolSlot [] [.bool]))
          (.unary .not (.local (sourceBoolSlot [] [.bool]))))) .nil) : RItems E R M k
        (sourceContext [.bool]) (sourceContext [.bool,.bool]))
      (.cons (.bool true) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool true) (.cons (.bool false) .nil))), (.nil, st)) := by
  rfl

/-- Replacing the live old copy with the newly written false value is unsound. -/
theorem bool_saved_toggle_overwrite_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool true) (.cons (.bool false) .nil)) (false,false,()) := by
  intro related
  cases related with
  | cons head tail => cases head

end Solidity.Source.Agreement
