import Solidity.Source.Agreement.NormalDefaults

/-! Concrete boolean literal initialization in the existing Source and model
interpreters. This relates primitive locals, not source/compiler or world adequacy. -/
namespace Solidity.Source.Agreement

variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Literal initialization retains the incoming local tail and Source state. -/
theorem bool_init_source (b : Bool) (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F (n+2) nps ph
      (.declInit (.bool b) rfl : RStmt E R M k _ _) ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) ls)), (.nil, st)) := by
  rfl

/-- The selected model initializer pushes the actual literal. -/
theorem bool_init_model (b : Bool) (ps : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext ps)) :
    Solidity.Stmt.runC (.declLocal .bool name (some (.simple (.bool b)))) model =
      .ok ⟨model.push (t := .val .bool) b, List.prefix_refl _⟩ := by
  rfl

/-- A literal initializer discharges the normal-step premise without a supplied
successful execution or chosen final value. Errors at short horizons are excluded
only by the actual normal-result antecedent. -/
theorem bool_init_step (b : Bool) (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      ps (.bool::ps) G F nps ph (.declInit (.bool b) rfl)
      (.declLocal .bool name (some (.simple (.bool b)))) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      rw [bool_init_source] at ran
      have he : (.cons (.bool b) ls) = ls' :=
        Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
      subst ls'
      refine ⟨⟨model.push (t := .val .bool) b, List.prefix_refl _⟩,
        bool_init_model b ps name model, ?_⟩
      exact LocalsRel.cons (PrimitiveRel.bool b) related

/-- The existing sequence consumer now has two concrete literal producers. -/
theorem two_bool_inits_agree (b c : Bool) (ps : List PrimTy) (x y : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      ps (.bool::.bool::ps) G F nps ph
      (.stmt (.declInit (.bool b) rfl) (.stmt (.declInit (.bool c) rfl) .nil))
      (.cons (.declLocal .bool x (some (.simple (.bool b))))
        (.cons (.declLocal .bool y (some (.simple (.bool c)))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (bool_init_step b ps x G F nps ph) (bool_init_step c (.bool::ps) y G F nps ph)

end Solidity.Source.Agreement
