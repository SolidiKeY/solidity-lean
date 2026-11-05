import Solidity.Source.Agreement.NormalDefaults

/-! Constructed existing declaration pairs, not source/compiler/native fixtures.
These clients discharge the earlier per-statement hypotheses with actual
primitive producers and retain the entire incoming local tail and states. -/
namespace Solidity.Source.Agreement

variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

theorem two_defaults_source (p q : PrimTy) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+4) nps ph
      (.stmt (.declVar (sourceTy p) : RStmt E R M k _ _)
        (.stmt (.declVar (sourceTy q)) .nil)) ls).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout q (PrimTy.dflt q))
        (.cons (ofModel E.layout p (PrimTy.dflt p)) ls))), (.nil, st)) := by
  cases p <;> cases q <;> rfl

theorem two_defaults_model (p q : PrimTy) (ps : List PrimTy) (x y : Var)
    (model : Solidity.State C (modelContext ps)) :
    Prog.runC (.cons (.declLocal p x none) (.cons (.declLocal q y none) .nil)) model =
      .ok ⟨(model.push (t := .val p) (PrimTy.dflt p)).push (t := .val q) (PrimTy.dflt q),
        List.prefix_refl _⟩ := by
  rfl

/-- A real importing consumer, with no supplied step fact, chosen result,
initial relation or successful-run premise. Both evaluator results and the
ordered final correspondence are derived from the same initial local values. -/
theorem two_defaults_client (p q : PrimTy) (ps : List PrimTy) (x y : Var)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    (execItems G F (n+4) nps ph
      (.stmt (.declVar (sourceTy p) : RStmt E R M k _ _)
        (.stmt (.declVar (sourceTy q)) .nil))
      (localsOfModel E.layout C model.H ps model.env)).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout q (PrimTy.dflt q))
        (.cons (ofModel E.layout p (PrimTy.dflt p))
          (localsOfModel E.layout C model.H ps model.env)))), (.nil, st)) ∧
    Prog.runC (.cons (.declLocal p x none) (.cons (.declLocal q y none) .nil)) model =
      .ok ⟨(model.push (t := .val p) (PrimTy.dflt p)).push (t := .val q) (PrimTy.dflt q),
        List.prefix_refl _⟩ ∧
    StateLocalsRel E C (q::p::ps)
      (.cons (ofModel E.layout q (PrimTy.dflt q))
        (.cons (ofModel E.layout p (PrimTy.dflt p))
          (localsOfModel E.layout C model.H ps model.env)))
      ((model.push (t := .val p) (PrimTy.dflt p)).push (t := .val q) (PrimTy.dflt q)) := by
  have source : (execItems G F (n+4) nps ph
      (.stmt (.declVar (sourceTy p) : RStmt E R M k _ _)
        (.stmt (.declVar (sourceTy q)) .nil))
      (localsOfModel E.layout C model.H ps model.env)).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout q (PrimTy.dflt q))
        (.cons (ofModel E.layout p (PrimTy.dflt p))
          (localsOfModel E.layout C model.H ps model.env)))), (.nil, st)) :=
    two_defaults_source p q ps G F n nps ph _ st
  obtain ⟨out, ran, related⟩ := (two_defaults_agree p q ps x y G F nps ph)
    _ st model (stateLocals_total E C ps model) (n+4) _ (.nil, st) source
  have he : out = ⟨(model.push (t := .val p) (PrimTy.dflt p)).push (t := .val q) (PrimTy.dflt q),
      List.prefix_refl _⟩ := (Except.ok.inj ((two_defaults_model p q ps x y model).symm.trans ran)).symm
  subst out
  exact ⟨source, two_defaults_model p q ps x y model, related⟩

/-- Even primitive declaration needs its real default-evaluation horizon. -/
theorem default_one_timeout (p : PrimTy) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F 1 nps ph (.declVar (sourceTy p) : RStmt E R M k _ _) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- Fuel three can finish the first primitive declaration but not the second;
this Source timeout is not model divergence or EVM gas exhaustion. -/
theorem two_defaults_three_timeout (p q : PrimTy) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F 3 nps ph
      (.stmt (.declVar (sourceTy p) : RStmt E R M k _ _)
        (.stmt (.declVar (sourceTy q)) .nil)) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  cases p <;> rfl

/-- Binder labels do not choose the value or change the existing operation. -/
theorem default_name_independent (p : PrimTy) (ps : List PrimTy) (x y : Var)
    (model : Solidity.State C (modelContext ps)) :
    Solidity.Stmt.runC (.declLocal p x none) model =
      Solidity.Stmt.runC (.declLocal p y none) model := by
  rfl

/-- A positive Source declaration and total initial locals refute a fabricated
producer which changes the real boolean default from false to true. -/
theorem false_default_not_true (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    ¬ NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      ps (.bool::ps) G F nps ph (.declVar .bool)
      (.declLocal .bool name (some (.simple (.bool true)))) := by
  intro producer
  obtain ⟨out, ran, related⟩ := producer _ st model (stateLocals_total E C ps model)
    2 _ (.nil, st) (default_source (R := R) (M := M) (k := k) .bool ps G F 0 nps ph _ st)
  have he : out = ⟨model.push (t := .val .bool) true, List.prefix_refl _⟩ :=
    (Except.ok.inj ran).symm
  subst out
  cases related with
  | cons head tail => exact false_not_true E.layout head

end Solidity.Source.Agreement
