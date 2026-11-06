import Solidity.Source.Agreement.BoolSlotRead

/-! Boolean negation of an actual local read in the existing interpreters.
This is an explicit normal-local producer, not generic Source adequacy. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Boolean correspondence determines the actual Source constructor and value. -/
theorem bool_related_eq (D : Layout) (v : Source.Val D .bool) (b : Bool)
    (related : PrimitiveRel D .bool v b) : v = .bool b := by
  cases related
  rfl

/-- Forward execution law for the existing Source monad, retaining its actual
intermediate locals/state; this does not select a computation. -/
theorem source_run_bind_ok {Γ : RCtx} {α β : Type}
    (m : EM E Γ α) (f : α → EM E Γ β)
    (initial middle : Locals E.layout Γ × St E) (a : α)
    (out : Except Halt β × (Locals E.layout Γ × St E))
    (hm : m.run initial = (.ok a, middle)) (hf : (f a).run middle = out) :
    (m >>= f).run initial = out := by
  change (ExceptT.bindCont f (m.run initial).1) (m.run initial).2 = out
  rw [hm]
  exact hf

/-- Actual unary evaluation preserves its input locals/state and returns the
negated old lookup; this is an operational component, not a supplied outcome. -/
theorem bool_not_eval_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n : Nat)
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (evalE G F (n+2) (.unary .not (.local (sourceBoolSlot tail pre)))).run
      (ls, st) = (.ok (.val (.bool (!b))), (ls, st)) := by
  have hr : (evalE G F (n+1) (.local (sourceBoolSlot tail pre))).run (ls, st) =
      (.ok (.val (.bool b)), (ls, st)) := by
    change (Except.ok (ε := Halt) (RVal.val (ls.get (sourceBoolSlot tail pre))), (ls, st)) = _
    rw [read]
  exact source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool b)) _ hr (by rfl)

/-- Operational helper: the only read premise is the actual old local lookup.
The public producer below derives it internally from the related input states. -/
theorem bool_not_init_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (execS G F (n+3) nps ph
      (.declInit (.unary .not (.local (sourceBoolSlot tail pre))) rfl : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
      ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool (!b)) ls)), (.nil, st)) := by
  have hu : (evalE G F (n+2) (.unary .not (.local (sourceBoolSlot tail pre)))).run
      (ls, st) = (.ok (.val (.bool (!b))), (ls, st)) :=
    bool_not_eval_source pre tail b G F n ls st read
  have hb : (do getV (← convRV F (n+2) .bool
      (← evalE G F (n+2) (.unary .not (.local (sourceBoolSlot tail pre)))))).run
      (ls, st) = (.ok (.bool (!b)), (ls, st)) :=
    source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool (!b))) _ hu (by rfl)
  dsimp only [ExceptT.run] at hb
  have hs : (EM.sub (Γ := []) ls (do getV (← convRV F (n+2) .bool
      (← evalE G F (n+2) (.unary .not (.local (sourceBoolSlot tail pre))))))).run
      (.nil, st) = (.ok (.bool (!b), ls), (.nil, st)) := by
    simp only [EM.sub, ExceptT.run, ExceptT.mk, hb]
  exact source_run_bind_ok _ _ (.nil, st) (.nil, st) (Source.Val.bool (!b), ls) _ hs (by rfl)

/-- Existing model negation reads the actual old environment and pushes its inverse. -/
theorem bool_not_init_model (pre tail : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.declLocal .bool name
      (some (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))))) model =
      .ok ⟨model.push (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩ := by
  rfl

/-- Actual local-read negation discharges the normal-step premise without a
supplied read value or desired successful interpreter result. -/
theorem bool_not_init_step (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.declInit (.unary .not (.local (sourceBoolSlot tail pre))) rfl)
      (.declLocal .bool name (some (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))))) := by
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
        rw [bool_not_init_source pre tail _ G F n nps ph ls st read] at ran
        have he : (.cons (.bool (!(TEnv.get (modelBoolSlot tail pre) model.env))) ls) = ls' :=
          Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
        subst ls'
        exact ⟨⟨model.push (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩,
          bool_not_init_model pre tail name model,
          LocalsRel.cons (PrimitiveRel.bool _) related⟩

end Solidity.Source.Agreement
