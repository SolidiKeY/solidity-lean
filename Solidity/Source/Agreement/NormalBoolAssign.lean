import Solidity.Source.Agreement.NormalBoolBindings

/-! Head-local boolean assignment in the existing interpreters. These are
primitive-local producers, not a general Source or compiler simulation. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- The actual local write changes the head and retains the entire old tail. -/
theorem bool_assign_source (old b : Bool) (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execS G F (n+3) nps ph
      (.expr (.assign (.local .here) (.bool b)) :
        RStmt E R M k (sourceContext (.bool::ps)) (sourceContext (.bool::ps)))
      (.cons (.bool old) ls)).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) ls)), (.nil, st)) := by
  rfl

/-- The actual model assignment retains nonlocal fields and the local tail. -/
theorem bool_assign_model (b : Bool) (ps : List PrimTy)
    (model : Solidity.State C (modelContext (.bool::ps))) :
    Solidity.Stmt.runC (.assignLocal .here (.simple (.bool b))) model =
      .ok ⟨model.setLocal .here b, List.prefix_refl _⟩ := by
  rfl

/-- Related boolean locals expose the same actual head and related old tail. -/
theorem bool_locals_shape (D : Layout) (C : Contract) (H : HTy)
    (ps : List PrimTy) (ls : Locals D (sourceContext (.bool::ps)))
    (v : Bool) (ws : TEnv C H (modelContext ps))
    (related : LocalsRel D C H (.bool::ps) ls (v, ws)) :
    ∃ tail, ls = .cons (.bool v) tail ∧ LocalsRel D C H ps tail ws := by
  cases related with
  | cons head tail =>
    cases head
    exact ⟨_, rfl, tail⟩

/-- Concrete normal-step producer: no supplied reached state or final value. -/
theorem bool_assign_step (b : Bool) (ps : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (.bool::ps) (.bool::ps) G F nps ph
      (.expr (.assign (.local .here) (.bool b)))
      (.assignLocal .here (.simple (.bool b))) := by
  intro ls st model related fuel ls' journal ran
  obtain ⟨tail, he, relTail⟩ := bool_locals_shape E.layout C model.H ps ls
    model.env.1 model.env.2 related
  subst ls
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      cases n with
      | zero => cases ran
      | succ n =>
        rw [bool_assign_source] at ran
        have he : (.cons (.bool b) tail) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        refine ⟨⟨model.setLocal .here b, List.prefix_refl _⟩,
          bool_assign_model b ps model, ?_⟩
        exact LocalsRel.cons (PrimitiveRel.bool b) relTail

/-- Initialization followed by overwrite instantiates both real step producers. -/
theorem bool_init_assign_agree (a b : Bool) (ps : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      ps (.bool::ps) G F nps ph
      (.stmt (.declInit (.bool a) rfl)
        (.stmt (.expr (.assign (.local .here) (.bool b))) .nil))
      (.cons (.declLocal .bool name (some (.simple (.bool a))))
        (.cons (.assignLocal .here (.simple (.bool b))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (bool_init_step a ps name G F nps ph) (bool_assign_step b ps G F nps ph)

end Solidity.Source.Agreement
