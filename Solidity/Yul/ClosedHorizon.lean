import Solidity.Yul.ClosedRun

/-! Closed-word horizon independence. The four-way induction retains the actual
AST/environment and profiles; it has no source-state or dirty-bit premise. -/
namespace Solidity.Yul.Closed

structure StableAt (fuel : Nat) : Prop where
  expr : ∀ {F n r} (env : FunctionEnv F) (he : EnvWordP env)
    (e : Expr F [] n r) (h : ExprWordP e) (vars : Values n),
    Refines (evalExpr fuel env he e h vars) (evalExpr (fuel + 1) env he e h vars)
  stmt : ∀ {F} {c : Control} {n} (env : FunctionEnv F) (he : EnvWordP env)
    (s : Stmt F [] c n) (h : StmtWordP s) (vars : Values n),
    Refines (evalStmtNode fuel s env he h vars) (evalStmtNode (fuel + 1) s env he h vars)
  cases : ∀ {F} {c : Control} {n} (env : FunctionEnv F) (he : EnvWordP env)
    (arms : Cases F [] c n) (h : CasesWordP arms) (selector : Word) (vars : Values n),
    Refines (evalCasesNode fuel arms env he h selector vars)
      (evalCasesNode (fuel + 1) arms env he h selector vars)
  loop : ∀ {F} {c : Control} {n} (env : FunctionEnv F) (he : EnvWordP env)
    (cond : Expr F [] n 1) (hc : ExprWordP cond)
    (post : Stmt F [] ⟨c.function, false⟩ n) (hp : StmtWordP post)
    (body : Stmt F [] ⟨c.function, true⟩ n) (hb : StmtWordP body) (vars : Values n),
    Refines (evalLoop fuel env he cond hc post hp body hb vars)
      (evalLoop (fuel + 1) env he cond hc post hp body hb vars)

theorem stableAt_zero : StableAt 0 where
  expr _ _ _ _ _ := Refines.none _
  stmt _ _ _ _ _ := Refines.none _
  cases _ _ _ _ _ _ := Refines.none _
  loop _ _ _ _ _ _ _ _ _ := Refines.none _

syntax "word_horizon_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| word_horizon_go [$ls,*]) => `(tactic| repeat' (first
    | unfold applyStmtRun
    | unfold applyCasesRun
    | (with_reducible exact Refines.none _)
    | (with_reducible exact Refines.refl _)
    | (first $[| with_reducible apply $ls:ident]*)
    | (apply Refines.map)
    | (refine Refines.bind ?_ ?_)
    | (with_reducible intro _)
    | (with_reducible rfl)
    | split
    | (dsimp only)))

syntax "word_horizon_unfold" ident ident : tactic
macro_rules
  | `(tactic| word_horizon_unfold $f $n) => `(tactic| (
    conv => lhs; simp only [$f:ident]
    generalize hm : $n + 1 = m
    conv => rhs; simp only [$f:ident]
    subst hm))

theorem expr_step {fuel : Nat} (ih : StableAt fuel) {F n r}
    (env : FunctionEnv F) (he : EnvWordP env)
    (e : Expr F [] n r) (h : ExprWordP e) (vars : Values n) :
    Refines (evalExpr (fuel + 1) env he e h vars)
      (evalExpr (fuel + 1 + 1) env he e h vars) := by
  cases e <;> word_horizon_unfold evalExpr fuel <;>
    word_horizon_go [ih.expr, ih.stmt, collectValues_refines]

theorem stmt_step {fuel : Nat} (ih : StableAt fuel) {F c n}
    (env : FunctionEnv F) (he : EnvWordP env)
    (s : Stmt F [] c n) (h : StmtWordP s) (vars : Values n) :
    Refines (evalStmtNode (fuel + 1) s env he h vars)
      (evalStmtNode (fuel + 1 + 1) s env he h vars) := by
  cases s <;> word_horizon_unfold evalStmtNode fuel <;>
    word_horizon_go [ih.expr, ih.stmt, ih.cases, ih.loop, collectValues_refines]

theorem cases_step {fuel : Nat} (ih : StableAt fuel) {F c n}
    (env : FunctionEnv F) (he : EnvWordP env)
    (arms : Cases F [] c n) (h : CasesWordP arms) (selector : Word) (vars : Values n) :
    Refines (evalCasesNode (fuel + 1) arms env he h selector vars)
      (evalCasesNode (fuel + 1 + 1) arms env he h selector vars) := by
  cases arms <;> word_horizon_unfold evalCasesNode fuel <;>
    word_horizon_go [ih.stmt, ih.cases]

theorem loop_step {fuel : Nat} (ih : StableAt fuel) {F} {c : Control} {n}
    (env : FunctionEnv F) (he : EnvWordP env)
    (cond : Expr F [] n 1) (hc : ExprWordP cond)
    (post : Stmt F [] ⟨c.function, false⟩ n) (hp : StmtWordP post)
    (body : Stmt F [] ⟨c.function, true⟩ n) (hb : StmtWordP body) (vars : Values n) :
    Refines (evalLoop (fuel + 1) env he cond hc post hp body hb vars)
      (evalLoop (fuel + 1 + 1) env he cond hc post hp body hb vars) := by
  word_horizon_unfold evalLoop fuel
  word_horizon_go [ih.expr, ih.stmt, ih.loop]

theorem stableAt (fuel : Nat) : StableAt fuel := by
  induction fuel with
  | zero => exact stableAt_zero
  | succ fuel ih => exact ⟨expr_step ih, stmt_step ih, cases_step ih, loop_step ih⟩

theorem Refines.trans {α} {a b c : Option α} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c := fun result h => hbc result (hab result h)

theorem evalExpr_refines_add (fuel extra : Nat) {F n r}
    (env : FunctionEnv F) (he : EnvWordP env) (e : Expr F [] n r)
    (h : ExprWordP e) (vars : Values n) :
    Refines (evalExpr fuel env he e h vars) (evalExpr (fuel + extra) env he e h vars) := by
  induction extra with
  | zero => exact Refines.refl _
  | succ extra ih => exact ih.trans ((stableAt (fuel + extra)).expr env he e h vars)

theorem evalStmt_refines_add (fuel extra : Nat) {F c n}
    (env : FunctionEnv F) (he : EnvWordP env) (s : Stmt F [] c n)
    (h : StmtWordP s) (vars : Values n) :
    Refines (evalStmt fuel env he s h vars) (evalStmt (fuel + extra) env he s h vars) := by
  induction extra with
  | zero => exact Refines.refl _
  | succ extra ih => exact ih.trans ((stableAt (fuel + extra)).stmt env he s h vars)

theorem evalCases_refines_add (fuel extra : Nat) {F c n}
    (env : FunctionEnv F) (he : EnvWordP env) (arms : Cases F [] c n)
    (h : CasesWordP arms) (selector : Word) (vars : Values n) :
    Refines (evalCases fuel env he arms h selector vars)
      (evalCases (fuel + extra) env he arms h selector vars) := by
  induction extra with
  | zero => exact Refines.refl _
  | succ extra ih => exact ih.trans ((stableAt (fuel + extra)).cases env he arms h selector vars)

theorem evalLoop_refines_add (fuel extra : Nat) {F} {c : Control} {n}
    (env : FunctionEnv F) (he : EnvWordP env)
    (cond : Expr F [] n 1) (hc : ExprWordP cond)
    (post : Stmt F [] ⟨c.function, false⟩ n) (hp : StmtWordP post)
    (body : Stmt F [] ⟨c.function, true⟩ n) (hb : StmtWordP body) (vars : Values n) :
    Refines (evalLoop fuel env he cond hc post hp body hb vars)
      (evalLoop (fuel + extra) env he cond hc post hp body hb vars) := by
  induction extra with
  | zero => exact Refines.refl _
  | succ extra ih => exact ih.trans ((stableAt (fuel + extra)).loop env he cond hc post hp body hb vars)

theorem evalExpr_stable {lo hi : Nat} (hlh : lo ≤ hi) {F n r}
    (env : FunctionEnv F) (he : EnvWordP env) (e : Expr F [] n r)
    (h : ExprWordP e) (vars : Values n) {result : Values r}
    (done : evalExpr lo env he e h vars = some result) :
    evalExpr hi env he e h vars = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlh
  exact evalExpr_refines_add lo extra env he e h vars result done

theorem evalStmt_stable {lo hi : Nat} (hlh : lo ≤ hi) {F c n}
    (env : FunctionEnv F) (he : EnvWordP env) (s : Stmt F [] c n)
    (h : StmtWordP s) (vars : Values n) {result : Outcome c n}
    (done : evalStmt lo env he s h vars = some result) :
    evalStmt hi env he s h vars = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlh
  exact evalStmt_refines_add lo extra env he s h vars result done

theorem evalExpr_completed_unique {lo hi : Nat} {F n r}
    (env : FunctionEnv F) (he : EnvWordP env) (e : Expr F [] n r)
    (h : ExprWordP e) (vars : Values n) {left right : Values r}
    (hl : evalExpr lo env he e h vars = some left)
    (hr : evalExpr hi env he e h vars = some right) : left = right := by
  cases Nat.le_total lo hi with
  | inl hle => exact Option.some.inj ((evalExpr_stable hle env he e h vars hl).symm.trans hr)
  | inr hle => exact Option.some.inj (hl.symm.trans (evalExpr_stable hle env he e h vars hr))

theorem evalStmt_completed_unique {lo hi : Nat} {F c n}
    (env : FunctionEnv F) (he : EnvWordP env) (s : Stmt F [] c n)
    (h : StmtWordP s) (vars : Values n) {left right : Outcome c n}
    (hl : evalStmt lo env he s h vars = some left)
    (hr : evalStmt hi env he s h vars = some right) : left = right := by
  cases Nat.le_total lo hi with
  | inl hle => exact Option.some.inj ((evalStmt_stable hle env he s h vars hl).symm.trans hr)
  | inr hle => exact Option.some.inj (hl.symm.trans (evalStmt_stable hle env he s h vars hr))

end Solidity.Yul.Closed
