import Solidity.Correctness.Elab.StmtCongruence

/-! Instantiated statement agreement, capture order, and failure boundaries. -/
namespace Solidity.Examples.ElabTotal.StmtCongruence
open Solidity ElabAgree
variable (C : Contract) [FreshNames]

private def guarded (rc : ElabRec C) : ElabRec C :=
  { rc with hoist := fun e => do
      if (← read).unchecked then rc.hoist e else throw "outside unchecked scope" }

/-- The replacement hoister may differ at other scopes. The generic theorem
still transports every statement's complete run at this unchecked scope. -/
example (rc : ElabRec C) (sc : ElabScope) (hsc : sc.unchecked = true) (s : RawStmt) :
    Agree sc (hoistStmtWith C rc s) (hoistStmtWith C (guarded C rc) s) := by
  apply hoistStmtWith_agree
  · intro e st m
    change rc.hoist e sc st m =
      (if sc.unchecked = true then rc.hoist e else throw "outside unchecked scope") sc st m
    rw [if_pos hsc]
  all_goals intros; exact agree_refl _ _

private def capture (_ : RawExpr) : ElabM (SProg C × RawExpr) := do
  let x ← freshCapture "se"
  pure ([], .name (toString x))

/-- `l = b.push()` captures the receiver before the assignment target. -/
example (rc : ElabRec C) (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo)
    (l b : RawExpr) :
    hoistStmtWith C {rc with hoist := capture C} (.assignPush l b) sc st m =
      .ok ((([], .assignPush (.name (toString (Var.fresh "se" (st.2 + 1))))
        (.name (toString (Var.fresh "se" st.2)))), (st.1, st.2 + 2)), m) := by
  rfl

/-- A failed receiver prevents the target from being hoisted. -/
example (rc : ElabRec C) (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistStmtWith C {rc with hoist := fun e => match e with
      | .name "receiver" => throw "receiver boundary"
      | _ => throw "target boundary"} (.assignPush (.name "target") (.name "receiver")) sc st m =
      .error "receiver boundary" := by
  rfl

end Solidity.Examples.ElabTotal.StmtCongruence
