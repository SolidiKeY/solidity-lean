import Solidity.Correctness.Lowering.Sim.Match.Cases

/-!
# The captures of a statement (ls2-expressions)

What `hoistStmtWith` returns, at an arbitrary callback record, on the arms
that are a leaf or one callback:

* statements without a capture arm keep the statement and the state
  (`hoistStmt_revert`, `hoistStmt_block`, `hoistStmt_unchecked`,
  `hoistStmt_checked`);
* `b.push()++` is the captures of `b` (`hoistStmt_pushIncDec`), a constrained
  callback, so the frozen case holds there from `RecSim`
  (`hoistStmt_pushIncDec_sat`);
* a declaration `T x = y` of a name is the captures of `rc.hoistTop y`
  (`hoistStmt_decl`; the same arm takes every initializer but a call), a
  callback `RecSim` does not constrain
  (`Sim/Expr/Strength.lean`).
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan)

variable [FreshNames] (C : Contract) (rc : ElabRec C)

theorem hoistStmt_revert : hoistStmtWith C rc .revert = pure ([], .revert) := rfl

theorem hoistStmt_block (ss : List RawStmt) :
    hoistStmtWith C rc (.block ss) = pure ([], .block ss) := rfl

theorem hoistStmt_unchecked (ss : List RawStmt) :
    hoistStmtWith C rc (.unchecked ss) = pure ([], .unchecked ss) := rfl

theorem hoistStmt_checked (o : OFMode) (ss : List RawStmt) :
    hoistStmtWith C rc (.checked o ss) = pure ([], .checked o ss) := rfl

theorem hoistStmt_pushIncDec (op : IncDec) (b : RawExpr) :
    hoistStmtWith C rc (.pushIncDec op b) = (do
      let (P, b) ← rc.hoist b
      pure (P, .pushIncDec op b)) := rfl

theorem hoistStmt_decl (T : RawTy) (x y : String) :
    hoistStmtWith C rc (.decl T x (some (.name y))) = (do
      let (P, r) ← rc.hoistTop (.name y)
      pure (P, .decl T x (some r))) := rfl

omit [FreshNames] in
/-- A successful run of a callback followed by a pure repackaging is a run of
the callback. -/
theorem ran_map {α β : Type} (x : ElabM (SProg C × α)) (f : α → β) {sc : ElabScope}
    {st st' : ECtx × Nat} {out : SProg C × β}
    (ran : ElabRan (do let (P, a) ← x; pure (P, f a)) sc st out st') :
    ∃ a, ElabRan x sc st (out.1, a) st' := by
  obtain ⟨m, m', run⟩ := ran
  cases hx : ((x.run sc).run st).run m with
  | error e =>
    have : (((do let (P, a) ← x; pure (P, f a) : ElabM (SProg C × β)).run sc).run st).run m
        = .error e := by
      show (do let r ← ((x.run sc).run st).run m; _) = _
      rw [hx]; rfl
    rw [this] at run; cases run
  | ok r =>
    obtain ⟨⟨⟨P, a⟩, st₁⟩, m₁⟩ := r
    have : (((do let (P, a) ← x; pure (P, f a) : ElabM (SProg C × β)).run sc).run st).run m
        = .ok (((P, f a), st₁), m₁) := by
      show (do let r ← ((x.run sc).run st).run m; _) = _
      rw [hx]; rfl
    rw [this] at run; cases run
    exact ⟨a, m, m', hx⟩

/-- **The frozen case at `b.push()++`**: its captures are a constrained
callback's, so `RecSim` gives the site obligation. -/
theorem hoistStmt_pushIncDec_sat (sim : RecSim C rc) (op : IncDec) (b : RawExpr)
    (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × RawStmt) (st' : ECtx × Nat)
    (ran : ElabRan (hoistStmtWith C rc (.pushIncDec op b)) sc st out st') :
    hoistStmtQ C (.pushIncDec op b) sc st out st' := by
  rw [hoistStmt_pushIncDec] at ran
  obtain ⟨a, ran⟩ := ran_map C _ _ ran
  exact sim.1 b sc st _ st' ran

end Solidity.Correctness.Lowering.Sim
