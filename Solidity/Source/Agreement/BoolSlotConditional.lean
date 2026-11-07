import Solidity.Source.Agreement.BoolSlotNot

/-! Conditional initialization selected by an actual corresponding local read.
Branches are boolean literals; generic expression/source adequacy is not claimed. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Operational Source component retaining the actual condition lookup. The
concrete producer derives this lookup from its input environments. -/
theorem bool_cond_init_source (pre tail : List PrimTy) (c a b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool c) :
    (execS G F (n+3) nps ph
      (.declInit (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b)) rfl :
        RStmt E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (.bool::pre ++ .bool::tail))) ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool (bif c then a else b)) ls)), (.nil, st)) := by
  have hr : (evalE G F (n+1) (.local (sourceBoolSlot tail pre))).run (ls, st) =
      (.ok (.val (.bool c)), (ls, st)) := by
    change (Except.ok (ε := Halt) (RVal.val (ls.get (sourceBoolSlot tail pre))), (ls, st)) = _
    rw [read]
  have hc : (evalE G F (n+2)
      (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b))).run (ls, st) =
      (.ok (.val (.bool (bif c then a else b))), (ls, st)) :=
    source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool c)) _ hr (by cases c <;> rfl)
  have hb : (do getV (← convRV F (n+2) .bool (← evalE G F (n+2)
      (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b))))).run (ls, st) =
      (.ok (.bool (bif c then a else b)), (ls, st)) :=
    source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool (bif c then a else b))) _ hc (by rfl)
  dsimp only [ExceptT.run] at hb
  have hs : (EM.sub (Γ := []) ls (do getV (← convRV F (n+2) .bool (← evalE G F (n+2)
      (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b)))))).run (.nil, st) =
      (.ok (.bool (bif c then a else b), ls), (.nil, st)) := by
    simp only [EM.sub, ExceptT.run, ExceptT.mk, hb]
  exact source_run_bind_ok _ _ (.nil, st) (.nil, st)
    (Source.Val.bool (bif c then a else b), ls) _ hs (by rfl)

/-- Actual model ternary evaluation selects the same branch from its old local. -/
theorem bool_cond_init_model (pre tail : List PrimTy) (a b : Bool) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.declLocal .bool name
      (some (.ternary (.simple (.local (modelBoolSlot tail pre)))
        (.simple (.bool a)) (.simple (.bool b))))) model =
      .ok ⟨model.push (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b),
        List.prefix_refl _⟩ := by
  simp only [Solidity.Stmt.runC, Solidity.TRun.declLocal, Solidity.Val.evalT,
    Solidity.Simple.evalT, Solidity.boolT]
  cases TEnv.get (modelBoolSlot tail pre) model.env <;> rfl

/-- All actual normal Source runs of this pair agree on the selected literal;
no chosen condition value or successful-run premise is added to the producer. -/
theorem bool_cond_init_step (pre tail : List PrimTy) (a b : Bool) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.declInit (.cond (.local (sourceBoolSlot tail pre)) (.bool a) (.bool b)) rfl)
      (.declLocal .bool name (some (.ternary (.simple (.local (modelBoolSlot tail pre)))
        (.simple (.bool a)) (.simple (.bool b))))) := by
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
        rw [bool_cond_init_source pre tail _ a b G F n nps ph ls st read] at ran
        have he : (.cons (.bool (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b)) ls) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        exact ⟨⟨model.push (bif TEnv.get (modelBoolSlot tail pre) model.env then a else b),
          List.prefix_refl _⟩, bool_cond_init_model pre tail a b name model,
          LocalsRel.cons (PrimitiveRel.bool _) related⟩

end Solidity.Source.Agreement
