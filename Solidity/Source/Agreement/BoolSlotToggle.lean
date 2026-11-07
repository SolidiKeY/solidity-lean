import Solidity.Source.Agreement.BoolSlotNot

/-! Computed-RHS local assignment in unchanged Source/model semantics. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual RHS evaluation precedes the write; the expression returns the new
value and its exact updated locals, retaining every Source nonlocal field. -/
theorem bool_toggle_eval_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n : Nat)
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (evalE G F (n+3) (.assign (.local (sourceBoolSlot tail pre))
      (.unary .not (.local (sourceBoolSlot tail pre))))).run (ls, st) =
      (.ok (.val (.bool (!b))), (ls.set (sourceBoolSlot tail pre) (.bool (!b)), st)) := by
  exact source_run_bind_ok _ _ (ls, st) (ls, st) (.val (.bool (!b))) _
    (bool_not_eval_source pre tail b G F n ls st read) (by rfl)

/-- The statement consumes that same evaluated assignment, discarding its value
only after the actual local write. -/
theorem bool_toggle_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (execS G F (n+4) nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))) : RStmt E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (pre ++ .bool::tail)))
      ls).run (.nil, st) =
      (.ok (.normal (ls.set (sourceBoolSlot tail pre) (.bool (!b)))), (.nil, st)) := by
  have he : (evalE G F (n+3) (.assign (.local (sourceBoolSlot tail pre))
      (.unary .not (.local (sourceBoolSlot tail pre))))).run (ls, st) =
      (.ok (.val (.bool (!b))), (ls.set (sourceBoolSlot tail pre) (.bool (!b)), st)) :=
    bool_toggle_eval_source pre tail b G F n ls st read
  dsimp only [ExceptT.run] at he
  have hs : (EM.sub (Γ := []) ls (evalE G F (n+3)
      (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))).run (.nil, st) =
      (.ok (.val (.bool (!b)), ls.set (sourceBoolSlot tail pre) (.bool (!b))), (.nil, st)) := by
    simp only [EM.sub, ExceptT.run, ExceptT.mk, he]
  exact source_run_bind_ok _ _ (.nil, st) (.nil, st)
    (RVal.val (Source.Val.bool (!b)), ls.set (sourceBoolSlot tail pre) (.bool (!b))) _ hs (by rfl)

/-- The model reads its old selected value before updating that same slot. -/
theorem bool_toggle_model (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Solidity.Stmt.runC (.assignLocal (modelBoolSlot tail pre)
      (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) model =
      .ok ⟨model.setLocal (modelBoolSlot tail pre)
        (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩ := by
  rfl

/-- Concrete computed-RHS producer; the operand and write value are derived
from the same actual initial environments, not independent chosen values. -/
theorem bool_toggle_step (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalStmtObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (pre ++ .bool::tail) G F nps ph
      (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))
      (.assignLocal (modelBoolSlot tail pre)
        (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) := by
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
        cases n with
        | zero => cases ran
        | succ n =>
          rw [bool_toggle_source pre tail _ G F n nps ph ls st read] at ran
          have he : (ls.set (sourceBoolSlot tail pre)
              (.bool (!(TEnv.get (modelBoolSlot tail pre) model.env)))) = ls' :=
            Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
          subst ls'
          exact ⟨⟨model.setLocal (modelBoolSlot tail pre)
              (!(TEnv.get (modelBoolSlot tail pre) model.env)), List.prefix_refl _⟩,
            bool_toggle_model pre tail model,
            bool_slot_set_related E.layout C model.H pre tail ls model.env _ related⟩

end Solidity.Source.Agreement
