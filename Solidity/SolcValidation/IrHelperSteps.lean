import Solidity.SolcValidation.IrHelperSim

/-!
# Statement-level steps of solc's helpers

Per-statement evaluation lemmas over arbitrary scopes and values: a call of
`cleanup_t_uint256`/`cleanup_t_int256` on a variable, a call of a panic helper,
and a pure binary operation on two variables. Each is proved once over an
abstract environment (any `E` whose lookup yields the helper's closure), so the
body proofs of `checked_sub_t_uint256` and `checked_div_t_int256` compose them
with `rw` instead of unfolding the whole body in one `simp`.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

abbrev sigCleanupU : FnSig := ⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩
abbrev sigCleanupI : FnSig := ⟨"cleanup_t_int256", ["value"], ["cleaned"]⟩
abbrev sigPanic11 : FnSig := ⟨"panic_error_0x11", [], []⟩
abbrev sigPanic12 : FnSig := ⟨"panic_error_0x12", [], []⟩

/-- The body of a cleanup helper (`cleaned := value`) returns its argument. -/
theorem cleanup_block (k : Nat) (body : Block (helperSigs ++ []) ⟨true, false⟩ (["value"] ++ ["cleaned"]))
    (hb : body = bodyCleanupU) (v : Word) (s : σ) :
    evalBlock M ctx (k + 4) helperEnv body (.cons v (.cons 0 .nil)) s = .ok (s, .cons v (.cons v .nil), .normal) := by
  subst hb
  simp only [bodyCleanupU, evalBlock, evalItems, evalStmt, evalExpr, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self]

/-- A call of `cleanup_t_uint256` on a variable returns the variable's value. -/
theorem cleanupU_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F sigCleanupU)
    (hE : E.lookup m = ⟨_, helperEnv, bodyCleanupU⟩) {L : List String} {n : String} (mv : Mem L n)
    (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 7) E (.call m (.cons (.var n mv) .nil)) vs s = .ok (s, fun _ => vs.get mv) := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  rw [cleanup_block M ctx (k + 2) bodyCleanupU rfl]
  simp only [run_ok_bind, Vals.drop_cons, Vals.drop_nil, toFn_single]

/-- `cleanup_t_int256` has the same body. -/
theorem cleanupI_block (k : Nat) (v : Word) (s : σ) :
    evalBlock M ctx (k + 4) helperEnv bodyCleanupI (.cons v (.cons 0 .nil)) s = .ok (s, .cons v (.cons v .nil), .normal) :=
  cleanup_block M ctx k bodyCleanupI rfl v s

/-- A call of `cleanup_t_int256` on a variable returns the variable's value. -/
theorem cleanupI_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F sigCleanupI)
    (hE : E.lookup m = ⟨_, helperEnv, bodyCleanupI⟩) {L : List String} {n : String} (mv : Mem L n)
    (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 7) E (.call m (.cons (.var n mv) .nil)) vs s = .ok (s, fun _ => vs.get mv) := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  rw [cleanupI_block M ctx (k + 2)]
  simp only [run_ok_bind, Vals.drop_cons, Vals.drop_nil, toFn_single]

/-- `x := cleanup_t_uint256(y)`. -/
theorem assign_cleanupU (k : Nat) {F : List FnSig} {c : Ctl} (E : FunEnv F) (m : Mem F sigCleanupU)
    (hE : E.lookup m = ⟨_, helperEnv, bodyCleanupU⟩) {L : List String} {n n' : String} (t : Mem L n)
    (mv : Mem L n') (vs : Vals L) (s : σ) :
    evalStmt (c := c) M ctx (k + 8) E (.assign [⟨n, t⟩] (.call m (.cons (.var n' mv) .nil))) vs s =
      .ok (s, vs.set t (vs.get mv), .normal) := by
  simp only [evalStmt]
  rw [cleanupU_call M ctx k E m hE mv vs s]
  simp only [run_ok_bind, run_pure, assignAll]

/-- `x := cleanup_t_int256(y)`. -/
theorem assign_cleanupI (k : Nat) {F : List FnSig} {c : Ctl} (E : FunEnv F) (m : Mem F sigCleanupI)
    (hE : E.lookup m = ⟨_, helperEnv, bodyCleanupI⟩) {L : List String} {n n' : String} (t : Mem L n)
    (mv : Mem L n') (vs : Vals L) (s : σ) :
    evalStmt (c := c) M ctx (k + 8) E (.assign [⟨n, t⟩] (.call m (.cons (.var n' mv) .nil))) vs s =
      .ok (s, vs.set t (vs.get mv), .normal) := by
  simp only [evalStmt]
  rw [cleanupI_call M ctx k E m hE mv vs s]
  simp only [run_ok_bind, run_pure, assignAll]

/-- A pure binary operation on two variables, assigned to one variable. -/
theorem assign_pure2 (k : Nat) {F : List FnSig} {c : Ctl} (E : FunEnv F) (p : Solidity.Yul.Pure 2)
    {L : List String} {n a b : String} (t : Mem L n) (ma : Mem L a) (mb : Mem L b) (vs : Vals L) (s : σ) :
    evalStmt (c := c) M ctx (k + 5) E (.assign [⟨n, t⟩] (.op (.evm (.pure p)) (.cons (.var a ma) (.cons (.var b mb) .nil)))) vs s =
      .ok (s, vs.set t (Solidity.Yul.Pure.eval p (word2 (vs.get ma) (vs.get mb))), .normal) := by
  simp only [evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, consFn_two, assignAll]

/-- The body of a panic helper runs solc's panic sequence. -/
theorem panic11_block (k : Nat) (s : σ) :
    evalBlock M ctx (k + 10) helperEnv bodyPanic11 .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M 0x11 s := by
  simp only [bodyPanic11, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure,
    consFn_two, panicRun, panicSelector]
  rcases M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, ↓reduceIte]
    rcases M.run .«mstore» (word2 4 17) s1 with e | ⟨s2, r2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, ↓reduceIte]
      rcases M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
      · simp only [run_error_bind, run_error_map]
      · simp only [run_ok_bind, run_ok_map, ↓reduceIte]

/-- The same for `panic_error_0x12`. -/
theorem panic12_block (k : Nat) (s : σ) :
    evalBlock M ctx (k + 10) helperEnv bodyPanic12 .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M 0x12 s := by
  simp only [bodyPanic12, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure,
    consFn_two, panicRun, panicSelector]
  rcases M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, ↓reduceIte]
    rcases M.run .«mstore» (word2 4 18) s1 with e | ⟨s2, r2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, ↓reduceIte]
      rcases M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
      · simp only [run_error_bind, run_error_map]
      · simp only [run_ok_bind, run_ok_map, ↓reduceIte]

theorem toFn_nil : (Vals.nil : Vals []).toFn = fun i => i.elim0 := by
  funext i
  exact i.elim0

/-- A call of `panic_error_0x11` runs solc's panic sequence. -/
theorem panic11_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F sigPanic11)
    (hE : E.lookup m = ⟨_, helperEnv, bodyPanic11⟩) {L : List String} (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m .nil) vs s = (fun s => (s, fun i => i.elim0)) <$> panicRun M 0x11 s := by
  simp only [evalExpr, evalArgs, run_ok_bind, Vals.ofFn, Vals.zeros, Vals.append_nil']
  rw [hE]
  rw [panic11_block M ctx (k + 1)]
  rcases panicRun M 0x11 s with e | s'
  · simp only [run_error_map, run_error_bind]
  · simp only [run_ok_map, run_ok_bind, run_pure, Vals.drop_nil, toFn_nil]

/-- A call of `panic_error_0x12` runs solc's panic sequence. -/
theorem panic12_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F sigPanic12)
    (hE : E.lookup m = ⟨_, helperEnv, bodyPanic12⟩) {L : List String} (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m .nil) vs s = (fun s => (s, fun i => i.elim0)) <$> panicRun M 0x12 s := by
  simp only [evalExpr, evalArgs, run_ok_bind, Vals.ofFn, Vals.zeros, Vals.append_nil']
  rw [hE]
  rw [panic12_block M ctx (k + 1)]
  rcases panicRun M 0x12 s with e | s'
  · simp only [run_error_map, run_error_bind]
  · simp only [run_ok_map, run_ok_bind, run_pure, Vals.drop_nil, toFn_nil]

/-- `if cond { panic_error_0x11() }`, once the condition's value is known. -/
theorem if_panic11 (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (m : Mem ([] ++ F) sigPanic11)
    (hE : (FunEnv.group [] Bodies.nil E).lookup m = ⟨_, helperEnv, bodyPanic11⟩)
    (vs : Vals L) (s : σ) (v : Word) (hc : evalExpr M ctx (k + 16) E cond vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 17) E (.if_ cond (.mk [] .nil (.stmt (.discard (.call m .nil)) .nil))) vs s =
      if v = 0 then .ok (s, vs, .normal) else (fun s => (s, vs, .normal)) <$> panicRun M 0x11 s := by
  simp only [evalStmt, hc, run_ok_bind]
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, run_pure]
  · simp only [z, ↓reduceIte, evalBlock, evalItems, evalStmt]
    rw [panic11_call M ctx (k + 1) _ m hE vs s]
    rcases panicRun M 0x11 s with e | s'
    · simp only [run_error_map, run_error_bind]
    · simp only [run_ok_map, run_ok_bind, run_pure, ↓reduceIte]

/-- `if cond { panic_error_0x12() }`, once the condition's value is known. -/
theorem if_panic12 (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (m : Mem ([] ++ F) sigPanic12)
    (hE : (FunEnv.group [] Bodies.nil E).lookup m = ⟨_, helperEnv, bodyPanic12⟩)
    (vs : Vals L) (s : σ) (v : Word) (hc : evalExpr M ctx (k + 16) E cond vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 17) E (.if_ cond (.mk [] .nil (.stmt (.discard (.call m .nil)) .nil))) vs s =
      if v = 0 then .ok (s, vs, .normal) else (fun s => (s, vs, .normal)) <$> panicRun M 0x12 s := by
  simp only [evalStmt, hc, run_ok_bind]
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, run_pure]
  · simp only [z, ↓reduceIte, evalBlock, evalItems, evalStmt]
    rw [panic12_call M ctx (k + 1) _ m hE vs s]
    rcases panicRun M 0x12 s with e | s'
    · simp only [run_error_map, run_error_bind]
    · simp only [run_ok_map, run_ok_bind, run_pure, ↓reduceIte]


/-- A statement that ends normally passes its values and state on. -/
theorem items_stmt_normal (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (st : Stmt F c L) (rest : Items F c L g) (vs vs' : Vals L) (s s' : σ)
    (h : evalStmt M ctx k E st vs s = .ok (s', vs', .normal)) :
    evalItems M ctx (k + 1) E (.stmt st rest) vs s = evalItems M ctx k E rest vs' s' := by
  simp only [evalItems, h, run_ok_bind, ↓reduceIte]

/-- The last statement of a block decides its result. -/
theorem items_last (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (st : Stmt F c L) (vs : Vals L) (s : σ) :
    evalItems (g := g) M ctx (k + 2) E (.stmt st .nil) vs s = evalStmt M ctx (k + 1) E st vs s := by
  simp only [evalItems]
  rcases evalStmt M ctx (k + 1) E st vs s with e | ⟨s', vs', fl⟩
  · simp only [run_error_bind]
  · cases fl <;> simp only [run_ok_bind, run_pure, ↓reduceIte, reduceCtorEq]

/-- A pure binary operation on two variables. -/
theorem pure2_expr (k : Nat) {F : List FnSig} (E : FunEnv F) (p : Solidity.Yul.Pure 2)
    {L : List String} {a b : String} (ma : Mem L a) (mb : Mem L b) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 4) E (.op (.evm (.pure p)) (.cons (.var a ma) (.cons (.var b mb) .nil))) vs s =
      .ok (s, fun _ => Solidity.Yul.Pure.eval p (word2 (vs.get ma) (vs.get mb))) := by
  simp only [evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, consFn_two]

/-- `gt(sub(x, y), x)` is solc's underflow test. -/
theorem sub_gt (x y : Word) :
    x.val < (Solidity.Yul.Pure.eval .«sub» (word2 x y)).val ↔ x.val < y.val := by
  have h : x.val < (x.val + 2 ^ 256 - y.val) % 2 ^ 256 ↔ x.val < y.val := by
    have w : x.val < (Solidity.Yul.word (x.val + 2 ^ 256 - y.val)).val ↔ x.val < y.val := sub_wraps x y
    rw [word_val] at w
    exact w
  rw [pure_sub_val]
  exact h

/-- `checked_sub_t_uint256`'s body, from its entry values (parameters `x y`, return `diff = 0`). -/
theorem checked_sub_body (k : Nat) (x y : Word) (s : σ) :
    evalBlock M ctx (k + 30) helperEnv bodySub (.cons x (.cons y (.cons 0 .nil))) s =
      if y.val ≤ x.val then .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val - y.val)) .nil)), .normal)
      else (fun s => (s, .cons x (.cons y (.cons (Solidity.Yul.Pure.eval .«sub» (word2 x y)) .nil)), .normal)) <$>
        panicRun M 0x11 s := by
  simp only [bodySub, evalBlock]
  rw [items_stmt_normal M ctx _ _ _ _ _ _ _ _ (assign_cleanupU M ctx _ _ _ rfl _ _ _ _),
    items_stmt_normal M ctx _ _ _ _ _ _ _ _ (assign_cleanupU M ctx _ _ _ rfl _ _ _ _),
    items_stmt_normal M ctx _ _ _ _ _ _ _ _ (assign_pure2 M ctx _ _ _ _ _ _ _ _), items_last,
    if_panic11 M ctx _ _ _ _ rfl _ _ _ (pure2_expr M ctx _ _ _ _ _ _ _)]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, pure_gt, word2_zero, word2_one]
  by_cases le : y.val ≤ x.val
  · have no : ¬ x.val < (Solidity.Yul.Pure.eval .«sub» (word2 x y)).val :=
      fun h => absurd ((sub_gt x y).mp h) (Nat.not_lt.mpr le)
    rw [if_pos ((truth_eq_zero _).mpr (decide_eq_false no)), if_pos le, pure_sub_of_le x y le]
  · have yes : x.val < (Solidity.Yul.Pure.eval .«sub» (word2 x y)).val := (sub_gt x y).mpr (Nat.lt_of_not_le le)
    rw [if_neg (fun h => absurd ((truth_eq_zero _).mp h) (by simp only [yes, decide_true, Bool.true_eq_false, not_false_eq_true])),
      if_neg le]



theorem consFn_succ {k : Nat} (w : Word) (ws : Fin k → Word) (i : Fin k) : consFn w ws i.succ = ws i := rfl

/-- A call of a two-argument, one-result helper on two variables runs its body
from the entry values (parameters bound, return variable `0`). -/
theorem call2 (k : Nat) {nm r : String} {F : List FnSig} (E : FunEnv F) (m : Mem F ⟨nm, ["x", "y"], [r]⟩)
    (body : HelperBody ["x", "y"] [r]) (hE : E.lookup m = ⟨_, helperEnv, body⟩)
    {L : List String} {a b : String} (ma : Mem L a) (mb : Mem L b) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 4) E (.call m (.cons (.var a ma) (.cons (.var b mb) .nil))) vs s =
      (fun (out : σ × Vals (["x", "y"] ++ [r]) × Flow) => (out.1, (Vals.drop ["x", "y"] out.2.1).toFn)) <$>
        evalBlock M ctx (k + 3) helperEnv body (.cons (vs.get ma) (.cons (vs.get mb) (.cons 0 .nil))) s := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [consFn_succ, consFn_zero]
  rcases evalBlock M ctx (k + 3) helperEnv body _ s with e | ⟨s', out, fl⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map]

def subCall : Expr (helperSigs ++ []) ArgNames 1 :=
  .call (s := ⟨"checked_sub_t_uint256", ["x", "y"], ["diff"]⟩)
    (.there (.there (.there (.there (.there .here))))) argPair

/-- A call of `checked_sub_t_uint256`: the difference, or solc's `Panic(0x11)` sequence. -/
theorem checked_sub_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 34) helperEnv subCall (argVals x y) s =
      if y.val ≤ x.val then .ok (s, fun _ => Solidity.Yul.word (x.val - y.val))
      else (fun s => (s, fun _ => Solidity.Yul.Pure.eval .«sub» (word2 x y))) <$> panicRun M 0x11 s := by
  rw [subCall, argPair, call2 M ctx (k + 30) helperEnv _ bodySub rfl]
  simp only [argVals, Vals.get_here, Vals.get_there]
  rw [checked_sub_body M ctx (k + 3)]
  by_cases le : y.val ≤ x.val
  · simp only [le, ↓reduceIte, run_ok_map, Vals.drop_cons, Vals.drop_nil, toFn_single]
    rfl
  · simp only [le, ↓reduceIte]
    rcases panicRun M 0x11 s with e | s'
    · simp only [run_error_map]
    · simp only [run_ok_map, Vals.drop_cons, Vals.drop_nil, toFn_single]
      rfl

def mulCall : Expr (helperSigs ++ []) ArgNames 1 :=
  .call (s := ⟨"checked_mul_t_uint256", ["x", "y"], ["product"]⟩)
    (.there (.there (.there (.there (.there (.there (.there .here))))))) argPair

/-- A call of `checked_mul_t_uint256` (the call-site form of `checked_mul_body`). -/
theorem checked_mul_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 34) helperEnv mulCall (argVals x y) s =
      if x.val * y.val < 2 ^ 256 then .ok (s, fun _ => Solidity.Yul.word (x.val * y.val))
      else (fun s => (s, fun _ => Solidity.Yul.word (x.val * y.val))) <$> panicRun M 0x11 s := by
  rw [mulCall, argPair, call2 M ctx (k + 30) helperEnv _ bodyMul rfl]
  simp only [argVals, Vals.get_here, Vals.get_there]
  rw [checked_mul_body M ctx (k + 3)]
  by_cases fits : x.val * y.val < 2 ^ 256
  · simp only [fits, ↓reduceIte, run_ok_map, Vals.drop_cons, Vals.drop_nil, toFn_single]
    rfl
  · simp only [fits, ↓reduceIte]
    rcases panicRun M 0x11 s with e | s'
    · simp only [run_error_map]
    · simp only [run_ok_map, Vals.drop_cons, Vals.drop_nil, toFn_single]
      rfl


/-! ## Expressions without calls, at any sufficient fuel -/

theorem var_gen {F : List FnSig} (E : FunEnv F) {L : List String} {n : String} (m : Mem L n)
    (vs : Vals L) (s : σ) (j : Nat) :
    evalExpr M ctx (j + 1) E (.var n m) vs s = .ok (s, fun _ => vs.get m) := rfl

theorem lit_gen {F : List FnSig} (E : FunEnv F) {L : List String} (l : Lit) (vs : Vals L) (s : σ) (j : Nat) :
    evalExpr M ctx (j + 1) E (.lit l) vs s = .ok (s, fun _ => l.value) := rfl

theorem consFn_one (w : Word) : consFn w Fin.elim0 = fun _ => w := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl

theorem op1_gen {F : List FnSig} (E : FunEnv F) (p : Solidity.Yul.Pure 1) {L : List String}
    (e : Expr F L 1) (vs : Vals L) (s : σ) (v : Word) (d : Nat)
    (h : ∀ j, evalExpr M ctx (j + d) E e vs s = .ok (s, fun _ => v)) (j : Nat) :
    evalExpr M ctx (j + d + 3) E (.op (.evm (.pure p)) (.cons e .nil)) vs s =
      .ok (s, fun _ => Solidity.Yul.Pure.eval p (fun _ => v)) := by
  have h1 : evalExpr M ctx (j + d + 1) E e vs s = .ok (s, fun _ => v) := by
    rw [Nat.add_right_comm]; exact h (j + 1)
  simp only [evalExpr.eq_4, evalArgs.eq_3, evalArgs.eq_2, evalOp, h1, run_ok_bind, run_pure, consFn_one]

theorem op2_gen {F : List FnSig} (E : FunEnv F) (p : Solidity.Yul.Pure 2) {L : List String}
    (e1 e2 : Expr F L 1) (vs : Vals L) (s : σ) (v1 v2 : Word) (d : Nat)
    (h1 : ∀ j, evalExpr M ctx (j + d) E e1 vs s = .ok (s, fun _ => v1))
    (h2 : ∀ j, evalExpr M ctx (j + d) E e2 vs s = .ok (s, fun _ => v2)) (j : Nat) :
    evalExpr M ctx (j + d + 4) E (.op (.evm (.pure p)) (.cons e1 (.cons e2 .nil))) vs s =
      .ok (s, fun _ => Solidity.Yul.Pure.eval p (word2 v1 v2)) := by
  have g2 : evalExpr M ctx (j + d + 1) E e2 vs s = .ok (s, fun _ => v2) := by
    rw [Nat.add_right_comm]; exact h2 (j + 1)
  have g1 : evalExpr M ctx (j + d + 2) E e1 vs s = .ok (s, fun _ => v1) := by
    rw [Nat.add_right_comm]; exact h1 (j + 2)
  simp only [evalExpr.eq_4, evalArgs.eq_3, evalArgs.eq_2, evalOp, g1, g2, run_ok_bind, run_pure, consFn_two]

/-! ## A panic that may return -/

/-- solc's panic sequence when `b` holds; nothing otherwise. On a machine
whose `revert` halts the sequence never returns; on others execution goes on. -/
def panicIf {σ : Type} (M : Machine σ) (b : Bool) (code : Word) (s : σ) : Run σ σ :=
  if b then panicRun M code s else .ok s

/-- The machine's `revert` never returns (as on the EVM): it halts with `HaltKind.revert`.
A property a consumer's machine proves; no theorem here assumes it unless it says so. -/
def RevertHalts {σ : Type} (M : Machine σ) : Prop :=
  ∀ (xs : Fin 2 → Word) (s : σ), ∃ s', M.run .«revert» xs s = .error (.halt s' .revert)

/-- On such a machine anything after `revert` is irrelevant. -/
theorem revert_bind_halts {σ α : Type} (M : Machine σ) (h : RevertHalts M) (xs : Fin 2 → Word) (s : σ)
    (cont cont' : σ × (Fin 0 → Word) → Run σ α) :
    M.run .«revert» xs s >>= cont = M.run .«revert» xs s >>= cont' := by
  obtain ⟨s', hs⟩ := h xs s
  rw [hs]
  rfl

/-- … and the panic sequence ends in a halt, so what follows it is irrelevant too. -/
theorem panicRun_bind_halts {σ α : Type} (M : Machine σ) (h : RevertHalts M) (code : Word) (s : σ)
    (cont cont' : σ → Run σ α) :
    panicRun M code s >>= cont = panicRun M code s >>= cont' := by
  simp only [panicRun]
  rcases M.run .«mstore» (word2 0 panicSelector) s with e | ⟨s1, r1⟩
  · rfl
  simp only [run_ok_bind]
  rcases M.run .«mstore» (word2 4 code) s1 with e | ⟨s2, r2⟩
  · rfl
  obtain ⟨s', hs⟩ := h (word2 0 36) s2
  simp only [run_ok_bind, hs]
  rfl

/-- On such a machine the panic sequence ends in a fault (the halt, or an earlier machine fault). -/
theorem panicRun_error_of_halts {σ : Type} (M : Machine σ) (h : RevertHalts M) (code : Word) (s : σ) :
    ∃ e, panicRun M code s = .error e := by
  simp only [panicRun]
  rcases M.run .«mstore» (word2 0 panicSelector) s with e | ⟨s1, r1⟩
  · exact ⟨e, rfl⟩
  simp only [run_ok_bind]
  rcases M.run .«mstore» (word2 4 code) s1 with e | ⟨s2, r2⟩
  · exact ⟨e, rfl⟩
  obtain ⟨s', hs⟩ := h (word2 0 36) s2
  simp only [run_ok_bind, hs]
  exact ⟨_, rfl⟩

/-- So a result that factors through the panic sequence is exactly its fault. -/
theorem panic_factor_halts {σ α : Type} (M : Machine σ) (h : RevertHalts M) (code : Word) (s : σ)
    (r : Run σ α) (hr : ∃ cont, r = panicRun M code s >>= cont) :
    ∃ e, panicRun M code s = .error e ∧ r = .error e := by
  obtain ⟨cont, hc⟩ := hr
  obtain ⟨e, he⟩ := panicRun_error_of_halts M h code s
  exact ⟨e, he, by rw [hc, he]; rfl⟩

/-- `if cond { panic() }` as a `panicIf`. -/
theorem if_panic_as (v : Word) (code : Word) {L : List String} (vs : Vals L) (s : σ) :
    (if v = 0 then (.ok (s, vs, .normal) : Run σ (σ × Vals L × Flow))
      else (fun s => (s, vs, .normal)) <$> panicRun M code s) =
      (fun s => (s, vs, .normal)) <$> panicIf M (v != 0) code s := by
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, panicIf, bne_self_eq_false, Bool.false_eq_true, run_ok_map]
  · have nz : (v != 0) = true := bne_iff_ne.mpr z
    simp only [z, ↓reduceIte, panicIf, nz]

/-- A statement whose result is a mapped machine run passes its values on after it. -/
theorem items_stmt_map (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (st : Stmt F c L) (rest : Items F c L g) (vs vs' : Vals L) (s : σ) (R : Run σ σ)
    (h : evalStmt M ctx k E st vs s = (fun s => (s, vs', .normal)) <$> R) :
    evalItems M ctx (k + 1) E (.stmt st rest) vs s = R >>= fun s' => evalItems M ctx k E rest vs' s' := by
  simp only [evalItems, h]
  rcases R with e | s'
  · simp only [run_error_map, run_error_bind]
  · simp only [run_ok_map, run_ok_bind, ↓reduceIte]

theorem truth_bne (b : Bool) : (Solidity.Yul.truth b != 0) = b := by
  cases b <;> rfl

theorem lit_min : (57896044618658097711785492504343953926634992332820282019728792003956564819968 : Word).val = 2 ^ 255 := rfl

/-- `sub(0, 1)` is the all-ones word. -/
theorem sub_zero_one : (Solidity.Yul.Pure.eval .«sub» (word2 0 1)).val = 2 ^ 256 - 1 := by
  rw [pure_sub_val]
  have v0 : (0 : Word).val = 0 := rfl
  have v1 : (1 : Word).val = 1 := rfl
  rw [v0, v1, Nat.zero_add, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos 256) Nat.one_pos)]

/-- `checked_div_t_int256`'s body, from its entry values (parameters `x y`, return `r = 0`):
`Panic(0x12)` for a zero divisor, then `Panic(0x11)` for `min / -1`, then `sdiv`. -/
theorem checked_div_body (k : Nat) (x y : Word) (s : σ) :
    evalBlock M ctx (k + 60) helperEnv bodyDiv (.cons x (.cons y (.cons 0 .nil))) s =
      panicIf M (y.val == 0) 0x12 s >>= fun s =>
        panicIf M (x.val == 2 ^ 255 && y.val == 2 ^ 256 - 1) 0x11 s >>= fun s =>
          .ok (s, .cons x (.cons y (.cons (Solidity.Yul.Pure.eval .«sdiv» (word2 x y)) .nil)), .normal) := by
  simp only [bodyDiv, evalBlock]
  rw [items_stmt_normal M ctx _ _ _ _ _ _ _ _ (assign_cleanupI M ctx _ _ _ rfl _ _ _ _),
    items_stmt_normal M ctx _ _ _ _ _ _ _ _ (assign_cleanupI M ctx _ _ _ rfl _ _ _ _)]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there]
  rw [items_stmt_map M ctx (k + 56) _ _ _ _ _ _ _
    ((if_panic12 M ctx (k + 39) _ _ _ _ _ _ _
      (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (k + 51))).trans (if_panic_as M _ _ _ _))]
  · rw [pure_iszero, truth_bne]
    refine congrArg (bind (panicIf M (y.val == 0) 18 s)) (funext fun s' => ?_)
    rw [items_stmt_map M ctx (k + 55) _ _ _ _ _ _ _
      ((if_panic11 M ctx (k + 38) _ _ _ _ _ _ _
        (op2_gen M ctx _ _ _ _ _ _ _ _ 9
          (fun j => op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (j + 4))
          (op2_gen M ctx _ _ _ _ _ _ _ _ 5 (fun j => var_gen M ctx _ _ _ _ (j + 4))
            (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (lit_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _))) (k + 41))).trans
        (if_panic_as M _ _ _ _))]
    · simp only [pure_and, pure_eq, word2_zero, word2_one, truth_and, sub_zero_one, lit_min, truth_bne]
      refine congrArg (bind (panicIf M _ 17 s')) (funext fun s'' => ?_)
      rw [items_last M ctx (k + 53), assign_pure2 M ctx (k + 49)]
      simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there]
    · rfl
  · rfl

end

end Solidity.SolcValidation.IrSyntax
