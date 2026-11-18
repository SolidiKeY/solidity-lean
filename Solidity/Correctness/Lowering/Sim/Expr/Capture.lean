import Solidity.Correctness.Lowering.Sim.Match.Cases
import Solidity.Correctness.Lowering.Sim.Expr.Run

/-!
# The captures of a statement (ls2-expressions)

What `hoistStmtWith` returns, at an arbitrary callback record, on the arms
that are a leaf or one callback:

* statements without a capture arm keep the statement and the state
  (`hoistStmt_revert`, `hoistStmt_unchecked`; every statement in the arm's
  default case is the same);
* `b.push()++` is the captures of `b` (`hoistStmt_pushIncDec`), a constrained
  callback, so the frozen case holds there from `RecSim`
  (`hoistStmt_pushIncDec_sat`);
* a declaration `T x = y` of a name is the captures of `rc.hoistTop y`
  (`hoistStmt_decl`; the same arm takes every initializer but a call), a
  callback `RecSim` does not constrain
  (`Sim/Expr/Strength.lean`).

For a capture predicate `S` with `Pieces S` (`Sim/Expr/Run.lean`) the arms
emit captures in `S`, from the obligations of the callbacks they call as
hypotheses: `hoistStmt_leaf_emits`, `hoistStmt_pushIncDec_emits`,
`hoistStmt_decl_emits` (`rc.hoistTop`), `hoistStmt_opAssign_emits`
(`rc.hoist`, `captureExpr`).
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan)

variable [FreshNames] (C : Contract) (rc : ElabRec C)

theorem hoistStmt_revert : hoistStmtWith C rc .revert = pure ([], .revert) := rfl

theorem hoistStmt_unchecked (ss : List RawStmt) :
    hoistStmtWith C rc (.unchecked ss) = pure ([], .unchecked ss) := rfl

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

theorem hoistStmt_opAssign (op : BinOp) (l r : RawExpr) (h : l.hasIncDec = false) :
    hoistStmtWith C rc (.opAssign op l r) = (do
      let (P, r) ← rc.hoist r
      let (Q, l) ← rc.hoist l
      pure (P ++ [] ++ Q, .opAssign op l r)) := by
  show (do
    let (P, r) ← rc.hoist r
    let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, l) ← rc.hoist l
    pure (P ++ Pc ++ Q, RawStmt.opAssign op l r)) = _
  rw [h]
  rfl

theorem hoistStmt_opAssign_effect (op : BinOp) (l r : RawExpr) (h : l.hasIncDec = true) :
    hoistStmtWith C rc (.opAssign op l r) = (do
      let (P, r) ← rc.hoist r
      let (Pc, r) ← captureExpr C r
      let (Q, l) ← rc.hoist l
      pure (P ++ Pc ++ Q, .opAssign op l r)) := by
  show (do
    let (P, r) ← rc.hoist r
    let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, l) ← rc.hoist l
    pure (P ++ Pc ++ Q, RawStmt.opAssign op l r)) = _
  rw [h]
  rfl

variable {C rc} {S : ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop}

/-- A statement without a capture arm emits no captures. -/
theorem hoistStmt_leaf_emits (ok : Pieces S) {s : RawStmt}
    (leaf : s = .revert ∨ ∃ ss, s = .unchecked ss) {sc : ElabScope} {st st' : ECtx × Nat}
    {out : SProg C × RawStmt} (ran : ElabRan (hoistStmtWith C rc s) sc st out st') :
    S sc st out.1 st' := by
  have h : hoistStmtWith C rc s = pure ([], s) := by
    obtain rfl | ⟨ss, rfl⟩ := leaf
    · exact hoistStmt_revert C rc
    · exact hoistStmt_unchecked C rc ss
  rw [h] at ran
  obtain ⟨h₁, h₂⟩ := ran_pure ran
  rw [h₁, h₂]
  exact ok.nil sc st

/-- `b.push()++` emits the captures of `b`. -/
theorem hoistStmt_pushIncDec_emits (hoist : Emits S rc.hoist) {op : IncDec} {b : RawExpr}
    {sc : ElabScope} {st st' : ECtx × Nat} {out : SProg C × RawStmt}
    (ran : ElabRan (hoistStmtWith C rc (.pushIncDec op b)) sc st out st') :
    S sc st out.1 st' := by
  rw [hoistStmt_pushIncDec] at ran
  obtain ⟨a, ran⟩ := ran_map C _ _ ran
  exact hoist _ _ _ _ _ ran

/-- A declaration of a name emits the captures of `rc.hoistTop`. -/
theorem hoistStmt_decl_emits (top : Emits S rc.hoistTop) {T : RawTy} {x y : String}
    {sc : ElabScope} {st st' : ECtx × Nat} {out : SProg C × RawStmt}
    (ran : ElabRan (hoistStmtWith C rc (.decl T x (some (.name y)))) sc st out st') :
    S sc st out.1 st' := by
  rw [hoistStmt_decl] at ran
  obtain ⟨a, ran⟩ := ran_map C _ (fun r => RawStmt.decl T x (some r)) ran
  exact top _ _ _ _ _ ran

/-- A compound assignment emits the captures of its right side, the capture
of that value where the target has an effect, then the target's. -/
theorem hoistStmt_opAssign_emits (ok : Pieces S) (hoist : Emits S rc.hoist)
    (capture : Emits S (captureExpr C)) {op : BinOp} {l r : RawExpr} {sc : ElabScope}
    {st st' : ECtx × Nat} {out : SProg C × RawStmt}
    (ran : ElabRan (hoistStmtWith C rc (.opAssign op l r)) sc st out st') :
    S sc st out.1 st' := by
  cases hl : l.hasIncDec
  · rw [hoistStmt_opAssign C rc op l r hl] at ran
    obtain ⟨⟨P, r'⟩, st₁, r₁, r₂⟩ := ran_bind ran
    obtain ⟨⟨Q, l'⟩, st₂, r₃, r₄⟩ := ran_bind r₂
    obtain ⟨h₁, h₂⟩ := ran_pure r₄
    rw [h₁, h₂, List.append_nil]
    exact ok.append (hoist _ _ _ _ _ r₁) (hoist _ _ _ _ _ r₃)
  · rw [hoistStmt_opAssign_effect C rc op l r hl] at ran
    obtain ⟨⟨P, r'⟩, st₁, r₁, r₂⟩ := ran_bind ran
    obtain ⟨⟨Pc, r''⟩, st₂, r₃, r₄⟩ := ran_bind r₂
    obtain ⟨⟨Q, l'⟩, st₃, r₅, r₆⟩ := ran_bind r₄
    obtain ⟨h₁, h₂⟩ := ran_pure r₆
    rw [h₁, h₂]
    exact ok.append (ok.append (hoist _ _ _ _ _ r₁) (capture _ _ _ _ _ r₃)) (hoist _ _ _ _ _ r₅)

end Solidity.Correctness.Lowering.Sim
