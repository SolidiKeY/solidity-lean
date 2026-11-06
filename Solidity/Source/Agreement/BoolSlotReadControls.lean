import Solidity.Source.Agreement.BoolSlotRead

/-! Actual read-copy/write histories and controls. No parsed or compiled source,
world adequacy, native observation or full simulation is claimed. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The initializer copies the old value; writing its original slot does not
retroactively change the copy. All surrounding old locals are retained. -/
theorem bool_read_then_assign_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre))) (.bool b))) .nil))
      ls).run (.nil, st) =
      (.ok (.normal (.cons (ls.get (sourceBoolSlot tail pre))
        (ls.set (sourceBoolSlot tail pre) (.bool b)))), (.nil, st)) := by
  rfl

/-- The actual model computation uses the old read in its pushed copy. -/
theorem bool_read_then_assign_model (pre tail : List PrimTy) (b : Bool) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Prog.runC
      (.cons (.declLocal .bool name (some (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail (.bool::pre)) (.simple (.bool b))) .nil)) model =
      .ok ⟨(model.setLocal (modelBoolSlot tail pre) b).push
        (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩ := by
  rfl

/-- Importing consumer: total initial locals and both actual computations
instantiate the sequence producer; no old value, relation or run is supplied. -/
theorem bool_read_then_assign_client (R : List STy) (M : Bool) (k : SCtx)
    (pre tail : List PrimTy) (b : Bool) (name : Var) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) (st : St E) :
    StateLocalsRel E C (.bool::pre ++ .bool::tail)
      (.cons ((localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).get
          (sourceBoolSlot tail pre))
        ((localsOfModel E.layout C model.H (pre ++ .bool::tail) model.env).set
          (sourceBoolSlot tail pre) (.bool b)))
      ((model.setLocal (modelBoolSlot tail pre) b).push
        (TEnv.get (modelBoolSlot tail pre) model.env)) := by
  obtain ⟨out, ran, related⟩ :=
    (bool_read_then_assign_agree (R := R) (M := M) (k := k) pre tail b name G F nps ph)
      _ st model (stateLocals_total E C _ model) 5 _ (.nil, st)
      (bool_read_then_assign_source (R := R) (M := M) (k := k) pre tail b G F 0 nps ph _ st)
  have he : out = ⟨(model.setLocal (modelBoolSlot tail pre) b).push
      (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_read_then_assign_model pre tail b name model).symm.trans ran)).symm
  subst out
  exact related

/-- The read expression retains its actual Source horizon. -/
theorem bool_read_init_one_timeout (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execS G F 1 nps ph
      (.declInit (.local (sourceBoolSlot tail pre)) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
      ls).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- Completing the read does not remove the subsequent write's fuel requirement. -/
theorem bool_read_then_assign_four_timeout (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E) :
    (execItems G F 4 nps ph
      (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre))) (.bool b))) .nil))
      ls).run (.nil, st) = (.error .timeout, (.nil, st)) := by
  rfl

/-- A real false-to-true write leaves the copied false value distinct. -/
theorem bool_read_copy_distinct_source (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.local (sourceBoolSlot [] [])) rfl : RStmt E R M k
        (sourceContext [.bool]) (sourceContext [.bool,.bool]))
        (.stmt (.expr (.assign (.local (sourceBoolSlot [] [.bool])) (.bool true))) .nil))
      (.cons (.bool false) .nil)).run (.nil, st) =
      (.ok (.normal (.cons (.bool false) (.cons (.bool true) .nil))), (.nil, st)) := by
  rfl

/-- Treating this primitive copy as an alias is observably incompatible. -/
theorem bool_read_alias_refused (D : Layout) (C : Contract) (H : HTy) :
    ¬ LocalsRel D C H [.bool,.bool]
      (.cons (.bool false) (.cons (.bool true) .nil)) (true,true,()) := by
  intro related
  cases related with
  | cons head tail => exact false_not_true D head

end Solidity.Source.Agreement
