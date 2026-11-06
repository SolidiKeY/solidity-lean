import Solidity.Source.Agreement.BoolSlotNot

/-! Actual short-circuit conjunction of a corresponding local and a literal.
Only existing resolved normal-local interpreter pairs are related. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Operational component exposing the actual left lookup. The producer below
derives it internally; the right literal is evaluated only when selected. -/
theorem bool_and_init_source (pre tail : List PrimTy) (c b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool c) :
    (execS G F (n+3) nps ph
      (.declInit (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b)) rfl :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool (c && b)) ls)), (.nil, st)) := by
  have hr : (evalE G F (n+1) (.local (sourceBoolSlot tail pre))).run (ls, st) =
      (.ok (.val (.bool c)), (ls, st)) := by
    change (Except.ok (ε := Halt) (RVal.val (ls.get (sourceBoolSlot tail pre))), (ls, st)) = _
    rw [read]
  have hc : (evalE G F (n+2)
      (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b))).run (ls, st) =
      (.ok (.val (.bool (c && b))), (ls, st)) :=
    source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool c)) _ hr (by cases c <;> rfl)
  have hb : (do getV (← convRV F (n+2) .bool (← evalE G F (n+2)
      (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b))))).run (ls, st) =
      (.ok (.bool (c && b)), (ls, st)) :=
    source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool (c && b))) _ hc (by rfl)
  dsimp only [ExceptT.run] at hb
  have hs : (EM.sub (Γ := []) ls (do getV (← convRV F (n+2) .bool (← evalE G F (n+2)
      (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b)))))).run (.nil, st) =
      (.ok (.bool (c && b), ls), (.nil, st)) := by
    simp only [EM.sub, ExceptT.run, ExceptT.mk, hb]
  exact source_run_bind_ok _ _ (.nil, st) (.nil, st)
    (Source.Val.bool (c && b), ls) _ hs (by rfl)

/-- Actual model short-circuit evaluation reads the same old left operand. -/
theorem bool_and_init_model (pre tail : List PrimTy) (b : Bool) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.declLocal .bool name
      (some (.binop .and rfl rfl (.simple (.local (modelBoolSlot tail pre)))
        (.simple (.bool b))))) model =
      .ok ⟨model.push ((TEnv.get (modelBoolSlot tail pre) model.env) && b), List.prefix_refl _⟩ := by
  simp only [Solidity.Stmt.runC, Solidity.TRun.declLocal, Solidity.Val.evalT, Solidity.Simple.evalT]
  cases TEnv.get (modelBoolSlot tail pre) model.env <;> rfl

/-- Concrete normal-step producer: no supplied left operand, favorable branch
or independent successful interpreter result is a premise. -/
theorem bool_and_init_step (pre tail : List PrimTy) (b : Bool) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.declInit (.binary .and (.local (sourceBoolSlot tail pre)) (.bool b)) rfl)
      (.declLocal .bool name (some (.binop .and rfl rfl (.simple (.local (modelBoolSlot tail pre)))
        (.simple (.bool b))))) := by
  intro ls st model related fuel ls' journal ran
  have read : ls.get (sourceBoolSlot tail pre) =
      .bool (TEnv.get (modelBoolSlot tail pre) model.env) :=
    bool_related_eq E.layout _ _ (bool_slot_get_related E.layout C model.H pre tail ls model.env related)
  cases fuel with
  | zero => cases ran
  | succ n =>
    cases n with
    | zero => cases ran
    | succ n =>
      cases n with
      | zero => cases ran
      | succ n =>
        rw [bool_and_init_source pre tail _ b G F n nps ph ls st read] at ran
        have he : (.cons (.bool ((TEnv.get (modelBoolSlot tail pre) model.env) && b)) ls) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        exact ⟨⟨model.push ((TEnv.get (modelBoolSlot tail pre) model.env) && b),
          List.prefix_refl _⟩, bool_and_init_model pre tail b name model,
          LocalsRel.cons (PrimitiveRel.bool _) related⟩

end Solidity.Source.Agreement
