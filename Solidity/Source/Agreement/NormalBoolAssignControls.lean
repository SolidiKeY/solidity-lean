import Solidity.Source.Agreement.NormalBoolAssign

/-! Actual interpreter controls for initialization followed by local overwrite.
These are constructed resolved statement pairs, not compiled source fixtures. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The final Source head is the assigned value, not the initializer. -/
theorem bool_init_assign_source (a b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+5) nps ph
      (.stmt (.declInit (.bool a) rfl : RStmt E R M k
        (sourceContext ps) (sourceContext (.bool::ps)))
        (.stmt (.expr (.assign (.local .here) (.bool b))) .nil)) ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) ls)), (.nil, st)) := by
  rfl

/-- Existing model evaluation derives the same overwrite, retaining the old tail. -/
theorem bool_init_assign_model (a b : Bool) (ps : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext ps)) :
    Prog.runC (.cons (.declLocal .bool name (some (.simple (.bool a))))
      (.cons (.assignLocal .here (.simple (.bool b))) .nil)) model =
      .ok ⟨model.push (t := .val .bool) b, List.prefix_refl _⟩ := by
  rfl

/-- A genuine importing consumer derives initial related locals and both
execution histories; no step/normal-result/desired-state premise is supplied. -/
theorem bool_init_assign_client (R : List STy) (M : Bool) (k : SCtx)
    (a b : Bool) (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    StateLocalsRel E C (.bool::ps)
      (.cons (.bool b) (localsOfModel E.layout C model.H ps model.env))
      (model.push (t := .val .bool) b) := by
  obtain ⟨out, ran, related⟩ :=
    (bool_init_assign_agree (R := R) (M := M) (k := k) a b ps name G F nps ph)
      _ st model (stateLocals_total E C ps model) 5 _ (.nil, st)
      (bool_init_assign_source (R := R) (M := M) (k := k) a b ps G F 0 nps ph _ st)
  have he : out = ⟨model.push (t := .val .bool) b, List.prefix_refl _⟩ :=
    (Except.ok.inj ((bool_init_assign_model a b ps name model).symm.trans ran)).symm
  subst out
  exact related

/-- Assignment needs its real Source location-evaluation horizon. -/
theorem bool_assign_two_timeout (old b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F 2 nps ph
      (.expr (.assign (.local .here) (.bool b)) : RStmt E R M k
        (sourceContext (.bool::ps)) (sourceContext (.bool::ps)))
      (.cons (.bool old) ls)).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- A completed initializer does not bypass the following assignment's horizon. -/
theorem bool_init_assign_four_timeout (a b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F 4 nps ph
      (.stmt (.declInit (.bool a) rfl : RStmt E R M k
        (sourceContext ps) (sourceContext (.bool::ps)))
        (.stmt (.expr (.assign (.local .here) (.bool b))) .nil)) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- A positive false assignment refutes a producer silently retaining true. -/
theorem false_assign_not_true (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext (.bool::ps))) (st : St E) :
    ¬ NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (.bool::ps) (.bool::ps) G F nps ph
      (.expr (.assign (.local .here) (.bool false)))
      (.assignLocal .here (.simple (.bool true))) := by
  intro producer
  obtain ⟨tail, he, relTail⟩ := bool_locals_shape E.layout C model.H ps
    (localsOfModel E.layout C model.H (.bool::ps) model.env)
    model.env.1 model.env.2 (stateLocals_total E C (.bool::ps) model)
  obtain ⟨out, ran, related⟩ := producer _ st model
    (LocalsRel.cons (PrimitiveRel.bool model.env.1) relTail) 3 _ (.nil, st)
    (bool_assign_source (R := R) (M := M) (k := k) model.env.1 false ps G F 0 nps ph tail st)
  have ho : out = ⟨model.setLocal .here true, List.prefix_refl _⟩ :=
    (Except.ok.inj ran).symm
  subst out
  cases related with
  | cons head rest => exact false_not_true E.layout head

end Solidity.Source.Agreement
