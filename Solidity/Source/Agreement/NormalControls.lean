import Solidity.Source.Agreement.NormalComposition

/-! Constructive and negative controls for normal-sequence composition. The
explicit no-op pair is an auxiliary associated pair, not a compiler selection
or source-admission theorem. The actual Source evaluation is exhibited; normal
agreement does not convert horizon exhaustion or early exits into completion. -/
namespace Solidity.Source.Agreement

variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- A concrete step producer needs no external hypothesis for the explicit
Source skip / model empty-block pair. This supplies a nonvacuous instance of
the conditional per-statement interface, not a default for arbitrary pairs. -/
theorem skip_step (ps : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      ps ps G F nps ph .skip (.block .nil) := by
  intro ls st model related n ls' journal ran
  cases n with
  | zero => cases ran
  | succ n =>
    change (Except.ok (Source.Out.normal ls), (.nil, st)) =
      (Except.ok (Source.Out.normal ls'), journal) at ran
    have he : ls = ls' := Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
    subst ls'
    exact ⟨⟨model, List.prefix_refl _⟩, rfl, related⟩

/-- Real positive Source execution with its full original journal and locals;
the horizon is sufficient by the existing evaluator, not a run premise. -/
theorem two_skips_source (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+3) nps ph
      (.stmt (.skip : RStmt E R M k _ _) (.stmt .skip .nil)) ls).run (.nil, st) =
      (.ok (.normal ls), (.nil, st)) := by
  rfl

/-- The two-statement theorem consumes real step producers rather than a
whole-program simulation premise. -/
theorem two_skips_agree (ps : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      ps ps G F nps ph (.stmt .skip (.stmt .skip .nil))
      (.cons (.block .nil) (.cons (.block .nil) .nil)) := by
  exact normal_two G F nps ph .skip .skip (.block .nil) (.block .nil)
    (skip_step ps G F nps ph) (skip_step ps G F nps ph)

/-- No initial relation, chosen result, or successful-run certificate is a
premise. Existing total primitive locals and the actual Source run supply the
inputs to the importing composition consumer. -/
theorem two_skips_client (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    (execItems G F (n+3) nps ph
      (.stmt (.skip : RStmt E R M k _ _) (.stmt .skip .nil))
      (localsOfModel E.layout C model.H ps model.env)).run (.nil, st) =
        (.ok (.normal (localsOfModel E.layout C model.H ps model.env)), (.nil, st)) ∧
    ∃ out, Prog.runC (.cons (.block .nil) (.cons (.block .nil) .nil)) model = .ok out ∧
      StateLocalsRel E C ps (localsOfModel E.layout C model.H ps model.env) out.st := by
  refine ⟨two_skips_source ps G F n nps ph _ st, ?_⟩
  exact (two_skips_agree (R := R) (M := M) (k := k) ps G F nps ph)
    _ st model (stateLocals_total E C ps model) (n+3) _ (.nil, st)
    (two_skips_source (R := R) (M := M) (k := k) ps G F n nps ph _ st)

/-- Horizon zero retains the actual timeout, even for the normal no-op pair. -/
theorem zero_horizon (ps : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F 0 nps ph (.nil : RItems E R M k _ _) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rfl

/-- A normal prefix consumer does not erase a real early-return tag. -/
theorem early_return (ps : List PrimTy) (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext ps)) (st : St E) :
    (execItems G F (n+2) nps ph
      (.stmt (.ret rfl : RStmt E [] M k _ _) (.stmt .skip .nil)) ls).run (.nil, st) =
      (.ok (.ret ls), (.nil, st)) := by
  rfl

/-- The producer premise cannot be inhabited for an incompatible pair. The
actual positive Source skip run and existing total locals expose the mismatch,
so this control does not rely on an impossible input relation. -/
theorem skip_revert_refused (ps : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (model : Solidity.State C (modelContext ps)) (st : St E) :
    ¬ NormalStmtObligation (C := C) (R := R) (M := M) (k := k) ps ps G F nps ph .skip .revert := by
  intro producer
  obtain ⟨out, ran, _⟩ := producer _ st model (stateLocals_total E C ps model)
    1 _ (.nil, st) rfl
  cases ran

end Solidity.Source.Agreement
