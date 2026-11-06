import Solidity.Yul.ClosedRun

/-! Exact local-word update laws for the closed evaluator. These are calculus
preparation, not a Source statement/dirty-bit embedding or full Y09 rule table.
The distinct-target premise is genuine; independent source paths alone do not
prove distinct intrinsic slots for an arbitrary supplied symbol table. -/
namespace Solidity.Yul.Closed

theorem writeTarget_same {n} (index : Fin n) (value : Word) (vars : Values n) :
    writeTarget (.local index) value vars index = value := by
  change (if index = index then value else vars index) = value
  rw [if_pos rfl]

theorem writeTarget_other {n} (target index : Fin n) (value : Word) (vars : Values n)
    (different : index ≠ target) :
    writeTarget (.local target) value vars index = vars index := by
  change (if index = target then value else vars index) = vars index
  rw [if_neg different]

theorem writeTarget_shadow {n} (index : Fin n) (first second : Word) (vars : Values n) :
    writeTarget (.local index) second (writeTarget (.local index) first vars) =
      writeTarget (.local index) second vars := by
  funext point
  by_cases same : point = index
  · subst point
    rw [writeTarget_same, writeTarget_same]
  · rw [writeTarget_other _ _ _ _ same, writeTarget_other _ _ _ _ same,
      writeTarget_other _ _ _ _ same]

theorem writeTarget_commute {n} (first second : Fin n) (a b : Word) (vars : Values n)
    (different : first ≠ second) :
    writeTarget (.local first) a (writeTarget (.local second) b vars) =
      writeTarget (.local second) b (writeTarget (.local first) a vars) := by
  funext point
  by_cases one : point = first
  · subst point
    rw [writeTarget_same, writeTarget_other _ _ _ _ different, writeTarget_same]
  · by_cases two : point = second
    · subst point
      rw [writeTarget_other _ _ _ _ one, writeTarget_same, writeTarget_same]
    · rw [writeTarget_other _ _ _ _ one, writeTarget_other _ _ _ _ two,
        writeTarget_other _ _ _ _ two, writeTarget_other _ _ _ _ one]

/-- Any slot outside the complete target vector retains its original word. -/
theorem writeValues_outside {n} (arity : Nat) (positions : Fin arity → Fin n)
    (values : Values arity) (vars : Values n) (index : Fin n)
    (outside : ∀ selected, index ≠ positions selected) :
    writeValues arity (fun selected => .local (positions selected)) values vars index = vars index := by
  induction arity generalizing vars with
  | zero => rfl
  | succ arity ih =>
    change writeValues arity (fun selected => .local (positions selected.castSucc))
      (fun selected => values selected.castSucc)
      (writeTarget (.local (positions (Fin.last arity))) (values (Fin.last arity)) vars) index = _
    rw [ih _ _ _ (fun selected => outside selected.castSucc)]
    exact writeTarget_other _ _ _ _ (outside (Fin.last arity))

/-- Every distinct target receives its corresponding already-evaluated RHS.
No width conversion/cleanup occurs. Duplicate targets are deliberately excluded. -/
theorem writeValues_at {n} (arity : Nat) (positions : Fin arity → Fin n)
    (distinct : Function.Injective positions) (values : Values arity) (vars : Values n)
    (selected : Fin arity) :
    writeValues arity (fun selected => .local (positions selected)) values vars
      (positions selected) = values selected := by
  induction arity generalizing vars with
  | zero => exact Fin.elim0 selected
  | succ arity ih =>
    apply Fin.lastCases (motive := fun selected =>
      writeValues (arity+1) (fun selected => .local (positions selected)) values vars
        (positions selected) = values selected) ?_ ?_ selected
    · change writeValues arity (fun selected => .local (positions selected.castSucc))
        (fun selected => values selected.castSucc)
        (writeTarget (.local (positions (Fin.last arity))) (values (Fin.last arity)) vars)
          (positions (Fin.last arity)) = _
      rw [writeValues_outside]
      · exact writeTarget_same _ _ _
      · intro other same
        have bad := congrArg Fin.val (distinct same)
        change arity = other.val at bad
        omega
    · intro other
      change writeValues arity (fun selected => .local (positions selected.castSucc))
        (fun selected => values selected.castSucc)
        (writeTarget (.local (positions (Fin.last arity))) (values (Fin.last arity)) vars)
          (positions other.castSucc) = values other.castSucc
      apply ih
      intro a b same
      exact Fin.castSucc_inj.mp (distinct same)

theorem evalStmt_assign (fuel : Nat) {F c n r} (environment : FunctionEnv F)
    (he : EnvWordP environment) (targets : Fin r → Target [] n) (e : Expr F [] n r)
    (h : StmtWordP (Stmt.assign (c := c) targets e)) (vars : Values n) :
    evalStmt (fuel+1) environment he (Stmt.assign (c := c) targets e) h vars =
      (do let values ← evalExpr fuel environment he e h.2 vars
          pure ⟨writeValues r targets values vars, .normal⟩) := rfl

/-- Exact assignment landing at every distinct target, including function RHSs.
The RHS completion premise uses the actual evaluator, environment and horizon. -/
theorem evalStmt_assign_at (fuel : Nat) {F c n r} (environment : FunctionEnv F)
    (he : EnvWordP environment) (positions : Fin r → Fin n)
    (distinct : Function.Injective positions) (e : Expr F [] n r)
    (h : StmtWordP (Stmt.assign (c := c) (fun i => .local (positions i)) e))
    (vars : Values n) (values : Values r)
    (rhs : evalExpr fuel environment he e h.2 vars = some values) (selected : Fin r) :
    (evalStmt (fuel+1) environment he
      (Stmt.assign (c := c) (fun i => .local (positions i)) e) h vars).map
        (fun result => result.vars (positions selected)) = some (values selected) := by
  rw [evalStmt_assign, rhs]
  change some (writeValues r (fun i => .local (positions i)) values vars (positions selected)) = _
  rw [writeValues_at r positions distinct]


/-- Collecting successful operands preserves every operand position. -/
theorem collectValues_allSome (arity : Nat) (values : Values arity) :
    collectValues arity (fun i => some (values i)) = some values := by
  induction arity with
  | zero =>
    change some Fin.elim0 = some values
    congr 1
    funext i
    exact Fin.elim0 i
  | succ arity ih =>
    change (collectValues arity (fun i => some (values i.castSucc))).bind
      (fun rest => some (Fin.lastCases (values (Fin.last arity)) rest)) = some values
    rw [ih]
    change some (Fin.lastCases (values (Fin.last arity)) (fun i => values i.castSucc)) = some values
    congr 1
    funext i
    apply Fin.lastCases (motive := fun i =>
      Fin.lastCases (values (Fin.last arity)) (fun i => values i.castSucc) i = values i) ?_ ?_ i
    · exact Fin.lastCases_last
    · intro i
      exact Fin.lastCases_castSucc i

theorem evalExpr_literal (fuel : Nat) {F n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (value : Word)
    (h : ExprWordP (Expr.literal (F := F) (X := []) (n := n) value)) (vars : Values n) :
    evalExpr (fuel+1) environment he (.literal value) h vars =
      some (fun _ => value) := rfl

/-- Concrete agreement for EVERY arity-indexed pure builtin on literal inputs.
No particular arithmetic boundary case or caller-supplied result is assumed. -/
theorem evalExpr_pure_literals (fuel : Nat) {F n a} (environment : FunctionEnv F)
    (he : EnvWordP environment) (op : Pure a) (inputs : Values a)
    (h : ExprWordP (Expr.builtin (F := F) (X := []) (n := n)
      (.pure op) (fun i => .literal (inputs i)))) (vars : Values n) :
    evalExpr (fuel+2) environment he (.builtin (.pure op) (fun i => .literal (inputs i))) h vars =
      some (fun _ => op.eval inputs) := by
  rw [evalExpr_builtin (fuel+1) environment he _ (.pure op)]
  change (collectValues a (fun i => some (inputs i))).bind
    (fun inputs => some (fun _ => op.eval inputs)) = _
  rw [collectValues_allSome]
  rfl

/-- Actual whole-statement landing for a literal assignment. The raw input
word survives exactly; this is a Yul-local law, not a Solidity pipeline theorem. -/
theorem evalStmt_assign_literal (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (target : Fin n) (value : Word)
    (h : StmtWordP (Stmt.assign (F := F) (c := c)
      (fun _ : Fin 1 => .local target) (.literal value))) (vars : Values n) :
    evalStmt (fuel+2) environment he
      (Stmt.assign (c := c) (fun _ : Fin 1 => .local target) (.literal value)) h vars =
      some ⟨writeTarget (.local target) value vars, .normal⟩ := rfl

/-- A pure-builtin assignment lands with its exact EVM word result for all26
operations, including zero divisors. It has no Solidity Panic branch. -/
theorem evalStmt_assign_pure_literals (fuel : Nat) {F c n a} (environment : FunctionEnv F)
    (he : EnvWordP environment) (target : Fin n) (op : Pure a) (inputs : Values a)
    (h : StmtWordP (Stmt.assign (F := F) (c := c)
      (fun _ : Fin 1 => .local target)
      (.builtin (.pure op) (fun i => .literal (inputs i))))) (vars : Values n) :
    evalStmt (fuel+3) environment he
      (Stmt.assign (c := c) (fun _ : Fin 1 => .local target)
        (.builtin (.pure op) (fun i => .literal (inputs i)))) h vars =
      some ⟨writeTarget (.local target) (op.eval inputs) vars, .normal⟩ := by
  rw [evalStmt_assign, evalExpr_pure_literals]
  rfl

end Solidity.Yul.Closed
