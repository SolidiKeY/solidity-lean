import Solidity.SolcValidation.IrExpHelpers
import Solidity.SolcValidation.IrExpModel
import Solidity.SolcValidation.IrHelperSteps

/-!
# Simulation of solc's `checked_exp_t_uint256_t_uint256`

On any machine and state, the helper group of `SolcValidation/IrExpHelpers.lean`
runs as the arithmetic model of `SolcValidation/IrExpModel.lean`: without any
machine effect it returns `base ^ exponent` when that fits in a word, and
otherwise its first machine effect is solc's `Panic(0x11)` sequence from the
entry state (after it, on a machine whose `revert` returns, the code goes on;
`∃ cont` leaves that continuation unspecified).

The proofs compose statement-level lemmas with `rw` (see
`SolcValidation/IrHelperSteps.lean`); the loop of `checked_exp_helper` is
handled by strong induction on the exponent, with fuel `steps e` (the number of
loop turns) above a constant.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- The runtime environment of the `checked_exp` group. -/
def expEnv : FunEnv (expSigs ++ []) := .group expSigs expBodies .nil

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-! ## Generic statement steps -/

theorem assign_of (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) {n : String}
    (t : Mem L n) (e : Expr F L 1) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E e vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 1) E (.assign [⟨n, t⟩] e) vs s = .ok (s, vs.set t v, .normal) := by
  simp only [evalStmt, h, run_ok_bind, run_pure, assignAll]

theorem if_of (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (b : Block F c L) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E cond vs s = .ok (s, fun _ => v)) :
    evalStmt M ctx (k + 1) E (.if_ cond b) vs s =
      if v = 0 then .ok (s, vs, .normal) else evalBlock M ctx k E b vs s := by
  simp only [evalStmt, h, run_ok_bind]
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, run_pure]
  · simp only [z, ↓reduceIte]

theorem block_empty (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (items : Items ([] ++ F) c L 0) (vs : Vals L) (s : σ) :
    evalBlock M ctx (k + 1) E (.mk [] .nil items) vs s = evalItems M ctx k (.group [] .nil E) items vs s := rfl

theorem items_nil (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (vs : Vals L) (s : σ) :
    evalItems (c := c) (g := g) M ctx (k + 1) E .nil vs s = .ok (s, vs, .normal) := rfl

theorem items_stmt_flow (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (st : Stmt F c L) (rest : Items F c L g) (vs vs' : Vals L) (s s' : σ) (fl : Flow)
    (h : evalStmt M ctx k E st vs s = .ok (s', vs', fl)) (nn : fl ≠ .normal) :
    evalItems M ctx (k + 1) E (.stmt st rest) vs s = .ok (s', vs', fl) := by
  simp only [evalItems, h, run_ok_bind, nn, ↓reduceIte, run_pure]

theorem leave_stmt (k : Nat) {F : List FnSig} {l : Bool} {L : List String} (E : FunEnv F) (vs : Vals L) (s : σ) :
    evalStmt (c := ⟨true, l⟩) M ctx (k + 1) E .leave vs s = .ok (s, vs, .leave) := rfl

/-! ## The small helpers of the group -/

theorem pure_shr_one (v : Word) : Solidity.Yul.Pure.eval .«shr» (word2 1 v) = Solidity.Yul.word (v.val / 2) := by
  have def_ : Solidity.Yul.Pure.eval .«shr» (word2 1 v) =
      if (1 : Word).val ≥ 256 then Solidity.Yul.word 0 else Solidity.Yul.word (v.val >>> (1 : Word).val) := rfl
  have one : (1 : Word).val = 1 := rfl
  rw [def_, one, if_neg (by decide), Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- The panic body over any scope (`expPanic11` is this term). -/
def panicBody (G : List FnSig) : Block G ⟨true, false⟩ ([] ++ []) :=
  (.mk [] .nil (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 35408467139433450592217433187231851964531694900788300625387963629091585785856, 35408467139433450592217433187231851964531694900788300625387963629091585785856, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 4, 4, rfl⟩) (.cons (.lit ⟨.num 17, 17, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 36, 36, rfl⟩) .nil)))) .nil))))

theorem expPanic11_eq : expPanic11 = panicBody _ := rfl

theorem panicBody_run (k : Nat) {G : List FnSig} (E : FunEnv G) (s : σ) :
    evalBlock M ctx (k + 10) E (panicBody G) .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M 0x11 s := by
  simp only [panicBody, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure,
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

/-- A call of `panic_error_0x11` runs solc's panic sequence. -/
theorem exp_panic_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F ⟨"panic_error_0x11", [], []⟩)
    (hE : E.lookup m = ⟨_, expEnv, expPanic11⟩) {L : List String} (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m .nil) vs s = (fun s => (s, fun i => i.elim0)) <$> panicRun M 0x11 s := by
  simp only [evalExpr, evalArgs, run_ok_bind, Vals.ofFn, Vals.zeros, Vals.append_nil']
  rw [hE, expPanic11_eq, panicBody_run M ctx (k + 1)]
  rcases panicRun M 0x11 s with e | s'
  · simp only [run_error_map, run_error_bind]
  · simp only [run_ok_map, run_ok_bind, run_pure, Vals.drop_nil, toFn_nil]

/-- `if cond { panic_error_0x11() }` in the `checked_exp` group, as a `panicIf`. -/
theorem exp_if_panic (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (m : Mem ([] ++ F) ⟨"panic_error_0x11", [], []⟩)
    (hE : (FunEnv.group [] Bodies.nil E).lookup m = ⟨_, expEnv, expPanic11⟩)
    (vs : Vals L) (s : σ) (v : Word) (hc : evalExpr M ctx (k + 16) E cond vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 17) E (.if_ cond (.mk [] .nil (.stmt (.discard (.call m .nil)) .nil))) vs s =
      (fun s => (s, vs, .normal)) <$> panicIf M (v != 0) 0x11 s := by
  rw [if_of M ctx (k + 16) E _ _ vs s v hc]
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, panicIf, bne_self_eq_false, Bool.false_eq_true, run_ok_map]
  · have nz : (v != 0) = true := bne_iff_ne.mpr z
    simp only [z, ↓reduceIte, panicIf, nz]
    rw [block_empty, items_last M ctx (k + 13)]
    simp only [evalStmt]
    rw [exp_panic_call M ctx (k + 1) _ m hE vs s]
    rcases panicRun M 0x11 s with e | s'
    · simp only [run_error_map, run_error_bind]
    · simp only [run_ok_map, run_ok_bind, run_pure, ↓reduceIte]

/-- A call of `cleanup_t_uint256` on a variable returns the variable's value. -/
theorem exp_cleanup_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F ⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩)
    (hE : E.lookup m = ⟨_, expEnv, expCleanupU⟩) {L : List String} {n : String} (mv : Mem L n)
    (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 7) E (.call m (.cons (.var n mv) .nil)) vs s = .ok (s, fun _ => vs.get mv) := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [expCleanupU, evalBlock, evalItems, evalStmt, evalExpr, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self, Vals.drop_cons, Vals.drop_nil, toFn_single]

/-- A call of `shift_right_1_unsigned` on a variable halves it. -/
theorem exp_shr_call (k : Nat) {F : List FnSig} (E : FunEnv F) (m : Mem F ⟨"shift_right_1_unsigned", ["value"], ["newValue"]⟩)
    (hE : E.lookup m = ⟨_, expEnv, expShr1⟩) {L : List String} {n : String} (mv : Mem L n)
    (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m (.cons (.var n mv) .nil)) vs s =
      .ok (s, fun _ => Solidity.Yul.word ((vs.get mv).val / 2)) := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [expShr1, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self, Vals.drop_cons, Vals.drop_nil, toFn_single,
    consFn_two, pure_shr_one]

/-! ## The loop of `checked_exp_helper` -/

/-- The scope of `checked_exp_helper`'s body. -/
abbrev HL : List String := ["_power", "_base", "exponent", "max", "power", "base"]
abbrev EF : List FnSig := [] ++ (expSigs ++ [])

/-- The environment of a body of the group. -/
def expE1 : FunEnv EF := .group [] .nil expEnv

def loopCond : Expr EF HL 1 :=
  (.op (.evm (.pure .«gt»)) (.cons (.var "exponent" (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil)))

def loopBody : Block EF ⟨true, true⟩ HL :=
  (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) (.cons (.op (.evm (.pure .«div»)) (.cons (.var "max" (.there (.there (.there .here)))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.if_ (.op (.evm (.pure .«and»)) (.cons (.var "exponent" (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil))) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there (.there .here))))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "power" (.there (.there (.there (.there .here))))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil))) (.stmt (.assign [⟨"base", (.there (.there (.there (.there (.there .here)))))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil)))) (.stmt (.assign [⟨"exponent", (.there (.there .here))⟩] (.call (.there (.there .here)) (.cons (.var "exponent" (.there (.there .here))) .nil))) .nil)))))

theorem helper_eq : expExpHelper =
    .mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there (.there .here))))⟩] (.var "_power" .here))
      (.stmt (.assign [⟨"base", (.there (.there (.there (.there (.there .here)))))⟩] (.var "_base" (.there .here)))
        (.stmt (.for_ (.run loopCond (.mk [] .nil .nil) loopBody)) .nil))) := rfl

def hv (p0 b0 e mx p b : Word) : Vals HL := .cons p0 (.cons b0 (.cons e (.cons mx (.cons p (.cons b .nil)))))

theorem if_of_ne (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (b : Block F c L) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E cond vs s = .ok (s, fun _ => v)) (nz : v ≠ 0) :
    evalStmt M ctx (k + 1) E (.if_ cond b) vs s = evalBlock M ctx k E b vs s := by
  rw [if_of M ctx k E cond b vs s v h, if_neg nz]

theorem if_of_eq (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F)
    (cond : Expr F L 1) (b : Block F c L) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E cond vs s = .ok (s, fun _ => v)) (z : v = 0) :
    evalStmt M ctx (k + 1) E (.if_ cond b) vs s = .ok (s, vs, .normal) := by
  rw [if_of M ctx k E cond b vs s v h, if_pos z]

theorem and_one_val (e : Word) : (Solidity.Yul.Pure.eval .«and» (word2 e 1)).val = e.val % 2 := by
  have one : (1 : Word).val = 1 := rfl
  rw [pure_and, word2_zero, word2_one, one, Nat.and_one_is_mod, word_val,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem gt_div_bne (mx b : Word) :
    (Solidity.Yul.Pure.eval .«gt» (word2 b (Solidity.Yul.Pure.eval .«div» (word2 mx b))) != 0) =
      decide (mx.val / b.val < b.val) := by
  rw [pure_gt, word2_zero, word2_one, pure_div, word2_zero, word2_one, word_div_val, truth_bne]

/-- One turn of the loop body. -/
theorem loop_body (i : Nat) (p0 b0 e mx p b : Word) (hmx : mx.val = maxWord) (s : σ) :
    (maxWord / b.val < b.val → ∃ cont, evalBlock M ctx (i + 40) expE1 loopBody (hv p0 b0 e mx p b) s =
      panicRun M 0x11 s >>= cont) ∧
    (¬ maxWord / b.val < b.val → evalBlock M ctx (i + 40) expE1 loopBody (hv p0 b0 e mx p b) s =
      .ok (s, hv p0 b0 (Solidity.Yul.word (e.val / 2)) mx
        (if e.val % 2 = 1 then Solidity.Yul.word (p.val * b.val) else p) (Solidity.Yul.word (b.val * b.val)), .normal)) := by
  simp only [loopBody, hv]
  rw [block_empty, items_stmt_map M ctx (i + 38) _ _ _ _ _ _ _
    ((exp_if_panic M ctx (i + 21) _ _ _ rfl _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 5 (fun j => var_gen M ctx _ _ _ _ (j + 4))
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _)) (i + 28))))]
  simp only [Vals.get_here, Vals.get_there, gt_div_bne, hmx]
  constructor
  · intro big
    exact ⟨_, by rw [panicIf, if_pos (decide_eq_true big)]⟩
  · intro ok
    rw [panicIf, if_neg (fun h => ok (of_decide_eq_true h)), run_ok_bind]
    by_cases odd : e.val % 2 = 1
    · rw [items_stmt_normal M ctx (i + 37) _ _ _ _ _ _ _
        ((if_of_ne M ctx (i + 36) _ _ _ _ _ _
          (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (i + 31)) _).trans
          ((block_empty M ctx (i + 35) _ _ _ _).trans ((items_last M ctx (i + 33) _ _ _ _).trans
            (assign_pure2 M ctx (i + 29) _ _ _ _ _ _ _))))]
      · rw [items_stmt_normal M ctx (i + 36) _ _ _ _ _ _ _ (assign_pure2 M ctx (i + 31) _ _ _ _ _ _ _),
          items_last M ctx (i + 34),
          assign_of M ctx (i + 34) _ _ _ _ _ _ (exp_shr_call M ctx (i + 22) _ _ _ _ _ _)]
        · simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, pure_mul, word2_zero, word2_one,
            odd, ↓reduceIte]
        · rfl
      · intro z
        have := and_one_val e
        simp only [Vals.get_here, Vals.get_there] at z
        rw [z] at this
        rw [odd] at this
        exact absurd this (by decide)
    · have z : Solidity.Yul.Pure.eval .«and» (word2 e 1) = 0 := by
        apply Fin.ext
        rw [and_one_val]
        have : (0 : Word).val = 0 := rfl
        rw [this]
        omega
      rw [items_stmt_normal M ctx (i + 37) _ _ _ _ _ _ _
        (if_of_eq M ctx (i + 36) _ _ _ _ _ _
          (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (i + 31)) z)]
      rw [items_stmt_normal M ctx (i + 36) _ _ _ _ _ _ _ (assign_pure2 M ctx (i + 31) _ _ _ _ _ _ _),
        items_last M ctx (i + 34),
        assign_of M ctx (i + 34) _ _ _ _ _ _ (exp_shr_call M ctx (i + 22) _ _ _ _ _ _)]
      · simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, pure_mul, word2_zero, word2_one,
          odd, ↓reduceIte]
      · rfl

/-! ## The loop, by induction on the exponent -/

/-- The number of loop turns for an exponent. -/
def steps (e : Nat) : Nat := if e ≤ 1 then 0 else steps (e / 2) + 1
termination_by e
decreasing_by omega

theorem steps_le : ∀ (n e : Nat), e < 2 ^ (n + 1) → steps e ≤ n := by
  intro n
  induction n with
  | zero =>
    intro e h
    rw [steps, if_pos (by omega)]
    exact Nat.le_refl 0
  | succ n ih =>
    intro e h
    rw [steps]
    by_cases le : e ≤ 1
    · rw [if_pos le]; omega
    · rw [if_neg le]
      have : e / 2 < 2 ^ (n + 1) := by
        rw [Nat.pow_succ] at h
        omega
      have := ih (e / 2) this
      omega

theorem word_val_lt (n : Nat) (h : n < 2 ^ 256) : (Solidity.Yul.word n).val = n := Nat.mod_eq_of_lt h

theorem word_mod (n : Nat) : Solidity.Yul.word (n % 2 ^ 256) = Solidity.Yul.word n := by
  apply Fin.ext
  rw [word_val, word_val, Nat.mod_mod]

theorem gt_one_val (e : Word) : Solidity.Yul.Pure.eval .«gt» (word2 e 1) = Solidity.Yul.truth (1 < e.val) := by
  rw [pure_gt, word2_zero, word2_one]
  rfl

theorem truth_eq_zero_iff (b : Bool) : Solidity.Yul.truth b = 0 ↔ b = false := truth_eq_zero b

section Iterate
variable {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (cond : Expr F L 1)
  (body : Block F ⟨c.function, true⟩ L)

theorem empty_block (k : Nat) {c' : Ctl} (vs : Vals L) (s : σ) :
    evalBlock (c := c') M ctx (k + 2) E (.mk [] .nil .nil) vs s = .ok (s, vs, .normal) := rfl

theorem iter_exit (k : Nat) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E cond vs s = .ok (s, fun _ => v)) (z : v = 0) :
    iterate (c := c) M ctx (k + 1) E cond (.mk [] .nil .nil) body vs s = .ok (s, vs, .normal) := by
  simp only [iterate, h, run_ok_bind, z, ↓reduceIte, run_pure]

theorem iter_step (k : Nat) (vs vs' : Vals L) (s s' : σ) (v : Word)
    (h : evalExpr M ctx (k + 2) E cond vs s = .ok (s, fun _ => v)) (nz : v ≠ 0)
    (hb : evalBlock M ctx (k + 2) E body vs s = .ok (s', vs', .normal)) :
    iterate (c := c) M ctx (k + 3) E cond (.mk [] .nil .nil) body vs s =
      iterate M ctx (k + 2) E cond (.mk [] .nil .nil) body vs' s' := by
  rw [iterate]
  simp only [h, run_ok_bind, nz, ↓reduceIte, hb, empty_block, reduceCtorEq]

theorem iter_panic (k : Nat) (vs : Vals L) (s : σ) (v : Word) (R : Run σ σ)
    (h : evalExpr M ctx k E cond vs s = .ok (s, fun _ => v)) (nz : v ≠ 0)
    (hb : ∃ cont, evalBlock M ctx k E body vs s = R >>= cont) :
    ∃ cont, iterate (c := c) M ctx (k + 1) E cond (.mk [] .nil .nil) body vs s = R >>= cont := by
  obtain ⟨cont, hb⟩ := hb
  simp only [iterate, h, run_ok_bind, nz, ↓reduceIte, hb]
  exact ⟨_, bind_assoc _ _ _⟩
end Iterate

/-- The loop of `checked_exp_helper` runs as `expLoop`. -/
theorem loop_run : ∀ (e j : Nat) (p0 b0 mx : Word) (p b : Nat), e < 2 ^ 256 → p < 2 ^ 256 →
    b < 2 ^ 256 → mx.val = maxWord → ∀ (s : σ),
    match expLoop p b e with
    | some (p', b', e') => iterate (c := ⟨true, false⟩) M ctx (j + steps e + 45) expE1 loopCond (.mk [] .nil .nil) loopBody
        (hv p0 b0 (Solidity.Yul.word e) mx (Solidity.Yul.word p) (Solidity.Yul.word b)) s =
        .ok (s, hv p0 b0 (Solidity.Yul.word e') mx (Solidity.Yul.word p') (Solidity.Yul.word b'), .normal)
    | none => ∃ cont, iterate (c := ⟨true, false⟩) M ctx (j + steps e + 45) expE1 loopCond (.mk [] .nil .nil) loopBody
        (hv p0 b0 (Solidity.Yul.word e) mx (Solidity.Yul.word p) (Solidity.Yul.word b)) s =
        panicRun M 0x11 s >>= cont := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro j p0 b0 mx p b eW pW bW hmx s
    have hc : ∀ i, evalExpr M ctx (i + 5) expE1 loopCond
        (hv p0 b0 (Solidity.Yul.word e) mx (Solidity.Yul.word p) (Solidity.Yul.word b)) s =
        .ok (s, fun _ => Solidity.Yul.truth (1 < e)) := by
      intro i
      rw [loopCond, hv, op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) i]
      simp only [Vals.get_here, Vals.get_there]
      rw [gt_one_val, word_val_lt e eW]
    by_cases le : e ≤ 1
    · rw [expLoop_exit p b e le]
      have fuel : j + steps e + 45 = (j + steps e + 44) + 1 := rfl
      rw [fuel, iter_exit M ctx _ _ _ _ _ _ _ (hc (j + steps e + 39))
        ((truth_eq_zero_iff _).mpr (decide_eq_false (by omega)))]
    · have st : steps e = steps (e / 2) + 1 := by rw [steps, if_neg le]
      have fuel : j + steps e + 45 = (j + steps (e / 2) + 43) + 3 := by omega
      have nz : Solidity.Yul.truth (1 < e) ≠ 0 :=
        fun h => absurd ((truth_eq_zero_iff _).mp h) (by simp only [decide_eq_false_iff_not, Nat.not_lt]; omega)
      have body := loop_body M ctx (j + steps (e / 2) + 5) p0 b0 (Solidity.Yul.word e) mx
        (Solidity.Yul.word p) (Solidity.Yul.word b) hmx s
      rw [word_val_lt b bW, word_val_lt e eW, word_val_lt p pW] at body
      by_cases big : maxWord / b < b
      · rw [expLoop_panic p b e le big]
        rw [fuel]
        exact iter_panic M ctx _ _ _ (j + steps (e / 2) + 45) _ s _ _ (hc (j + steps (e / 2) + 40)) nz
          (body.1 big)
      · rw [expLoop_step p b e le big, fuel,
          iter_step M ctx _ _ _ (j + steps (e / 2) + 43) _ _ s s _ (hc (j + steps (e / 2) + 40)) nz (body.2 big)]
        have pW' : (if e % 2 = 1 then p * b % 2 ^ 256 else p) < 2 ^ 256 := by
          split
          · exact Nat.mod_lt _ (by decide)
          · exact pW
        have h := ih (e / 2) (by omega) j p0 b0 mx _ (b * b % 2 ^ 256) (by omega) pW' (Nat.mod_lt _ (by decide)) hmx s
        have pv : (if e % 2 = 1 then Solidity.Yul.word (p * b) else Solidity.Yul.word p) =
            Solidity.Yul.word (if e % 2 = 1 then p * b % 2 ^ 256 else p) := by
          split
          · exact (word_mod _).symm
          · rfl
        rw [pv, ← word_mod (b * b)]
        exact h

theorem for_stmt (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (lp : Loop F c L)
    (vs : Vals L) (s : σ) : evalStmt M ctx (k + 1) E (.for_ lp) vs s = evalLoop M ctx k E lp vs s := rfl

theorem loop_run_eq (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (cond : Expr F L 1)
    (post : Block F ⟨c.function, false⟩ L) (body : Block F ⟨c.function, true⟩ L) (vs : Vals L) (s : σ) :
    evalLoop M ctx (k + 1) E (.run cond post body) vs s = iterate M ctx k E cond post body vs s := rfl

theorem one_word : (1 : Word) = Solidity.Yul.word 1 := rfl

/-- `checked_exp_helper(1, b, e, max)`'s body runs the loop from `power = 1`. -/
theorem helper_run (j : Nat) (b e : Nat) (mx : Word) (eW : e < 2 ^ 256) (bW : b < 2 ^ 256)
    (hmx : mx.val = maxWord) (s : σ) :
    match expLoop 1 b e with
    | some (p', b', e') => evalBlock M ctx (j + steps e + 51) expEnv expExpHelper
        (hv 1 (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0 0) s =
        .ok (s, hv 1 (Solidity.Yul.word b) (Solidity.Yul.word e') mx (Solidity.Yul.word p') (Solidity.Yul.word b'), .normal)
    | none => ∃ cont, evalBlock M ctx (j + steps e + 51) expEnv expExpHelper
        (hv 1 (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0 0) s = panicRun M 0x11 s >>= cont := by
  rw [helper_eq, block_empty, hv,
    items_stmt_normal M ctx (j + steps e + 49) _ _ _ _ _ _ _ (assign_of M ctx _ _ _ _ _ _ _ (var_gen M ctx _ _ _ _ _)),
    items_stmt_normal M ctx (j + steps e + 48) _ _ _ _ _ _ _ (assign_of M ctx _ _ _ _ _ _ _ (var_gen M ctx _ _ _ _ _))]
  have fuel2 : j + steps e + 48 = (j + steps e + 46) + 2 := rfl
  rw [fuel2, items_last, for_stmt, loop_run_eq]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there]
  rw [one_word]
  have h := loop_run M ctx e j 1 (Solidity.Yul.word b) mx 1 b eW (by decide) bW hmx s
  rw [← one_word] at h
  exact h

end

end Solidity.SolcValidation.IrSyntax
