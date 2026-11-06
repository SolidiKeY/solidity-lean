import Solidity.Source.Agreement.NormalBoolBindings

/-! Raw interpreter controls for boolean literal initialization; no compiler,
installed source or native fixture is claimed. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- A positive Source trace derives both literals, their order and the old tail. -/
theorem two_bool_inits_source (b c : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+4) nps ph
      (.stmt (.declInit (.bool b) rfl : RStmt E R M k (sourceContext ps) (sourceContext (.bool::ps)))
        (.stmt (.declInit (.bool c) rfl : RStmt E R M k (sourceContext (.bool::ps)) (sourceContext (.bool::.bool::ps))) .nil)) ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool c) (.cons (.bool b) ls))), (.nil, st)) := by
  rfl

/-- The actual model interpreter retains nonlocal fields and the old local tail. -/
theorem two_bool_inits_model (b c : Bool) (ps : List PrimTy) (x y : Var)
    (model : Solidity.State C (modelContext ps)) :
    Prog.runC (.cons (.declLocal .bool x (some (.simple (.bool b))))
      (.cons (.declLocal .bool y (some (.simple (.bool c)))) .nil)) model =
      .ok ⟨(model.push (t := .val .bool) b).push (t := .val .bool) c,
        List.prefix_refl _⟩ := by
  rfl

/-- No external step, reached-state, or successful execution hypothesis is
needed to instantiate the two-statement agreement consumer. -/
theorem two_bool_inits_client (R : List STy) (M : Bool) (k : SCtx) (b c : Bool) (ps : List PrimTy) (x y : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    StateLocalsRel E C (.bool::.bool::ps)
      (.cons (.bool c) (.cons (.bool b)
        (localsOfModel E.layout C model.H ps model.env)))
      ((model.push (t := .val .bool) b).push (t := .val .bool) c) := by
  obtain ⟨out, ran, related⟩ := (two_bool_inits_agree (R := R) (M := M) (k := k) b c ps x y G F nps ph)
    _ st model (stateLocals_total E C ps model) 4 _ (.nil, st)
    (two_bool_inits_source (R := R) (M := M) (k := k) b c ps G F 0 nps ph _ st)
  have he : out = ⟨(model.push (t := .val .bool) b).push (t := .val .bool) c,
      List.prefix_refl _⟩ :=
    (Except.ok.inj ((two_bool_inits_model b c ps x y model).symm.trans ran)).symm
  subst out
  exact related

/-- The initializer expression still requires its real Source horizon. -/
theorem bool_init_one_timeout (b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F 1 nps ph (.declInit (.bool b) rfl : RStmt E R M k (sourceContext ps) (sourceContext (.bool::ps))) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Finishing the first initializer does not make a short sequence normal. -/
theorem two_bool_inits_three_timeout (b c : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F 3 nps ph
      (.stmt (.declInit (.bool b) rfl : RStmt E R M k (sourceContext ps) (sourceContext (.bool::ps)))
        (.stmt (.declInit (.bool c) rfl : RStmt E R M k (sourceContext (.bool::ps)) (sourceContext (.bool::.bool::ps))) .nil)) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- A real positive Source result refutes changing its false initializer to a
true model initializer. The normal-step premise is not a freely chosen oracle. -/
theorem false_init_not_true (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    ¬ NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      ps (.bool::ps) G F nps ph (.declInit (.bool false) rfl)
      (.declLocal .bool name (some (.simple (.bool true)))) := by
  intro producer
  obtain ⟨out, ran, related⟩ := producer _ st model (stateLocals_total E C ps model)
    2 _ (.nil, st) (bool_init_source (R := R) (M := M) (k := k) false ps G F 0 nps ph _ st)
  have he : out = ⟨model.push (t := .val .bool) true, List.prefix_refl _⟩ :=
    (Except.ok.inj ran).symm
  subst out
  cases related with
  | cons head tail => exact false_not_true E.layout head

end Solidity.Source.Agreement
