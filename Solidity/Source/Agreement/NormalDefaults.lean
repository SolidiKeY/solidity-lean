import Solidity.Source.Agreement.NormalComposition

/-! Concrete normal-step producers for existing primitive declarations without
initializers. Only the already supported bool/uint256/int256 defaults are
related; no type/profile/default semantics, compiler association, Source owner
API, or full-state simulation is introduced or changed. -/
namespace Solidity.Source.Agreement

variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The existing Source default and existing model default retain their value
and range evidence. No chosen source value or range premise is supplied. -/
theorem primitive_default (D : Layout) (p : PrimTy) :
    Source.Val.default D (sourceTy p) = some (ofModel D p (PrimTy.dflt p)) := by
  cases p <;> rfl

/-- Actual Source declaration result at its sufficient horizon; all unrelated
Source journal/state fields and the entire incoming local tail are retained. -/
theorem default_source (p : PrimTy) (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F (n+2) nps ph (.declVar (sourceTy p) : RStmt E R M k _ _) ls).run (.nil, st) =
      (.ok (.normal (.cons (ofModel E.layout p (PrimTy.dflt p)) ls)), (.nil, st)) := by
  cases p <;> rfl

/-- Actual model declaration result. The name is binder metadata; the existing
operation changes only the local environment, keeping the complete model state. -/
theorem default_model (p : PrimTy) (ps : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext ps)) :
    Solidity.Stmt.runC (.declLocal p name none) model =
      .ok ⟨model.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩ := by
  rfl

/-- A real producer discharging NormalStmtObligation for this explicit pair;
no successful run, final local value or arbitrary step fact is assumed. -/
theorem default_step (p : PrimTy) (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      ps (p::ps) G F nps ph (.declVar (sourceTy p)) (.declLocal p name none) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      rw [default_source] at ran
      have he : (.cons (ofModel E.layout p (PrimTy.dflt p)) ls) = ls' :=
        Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
      subst ls'
      refine ⟨⟨model.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩,
        default_model p ps name model, ?_⟩
      exact LocalsRel.cons (ofModel_related E.layout p (PrimTy.dflt p)) related

/-- Two declaration pairs instantiate both conditional step hypotheses of the
previous sequence consumer. Each default and intermediate context is derived. -/
theorem two_defaults_agree (p q : PrimTy) (ps : List PrimTy) (x y : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      ps (q::p::ps) G F nps ph
      (.stmt (.declVar (sourceTy p)) (.stmt (.declVar (sourceTy q)) .nil))
      (.cons (.declLocal p x none) (.cons (.declLocal q y none) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (default_step p ps x G F nps ph) (default_step q (p::ps) y G F nps ph)

end Solidity.Source.Agreement
