import Solidity.SolcValidation.IrExpHelpers
import Solidity.SolcValidation.IrExpModel
import Solidity.SolcValidation.IrHelperSteps

/-!
# Simulation of solc's `checked_exp_t_uint256_t_uint256`

On any machine and state, the helper group of `SolcValidation/IrExpHelpers.lean`
runs as the arithmetic model of `SolcValidation/IrExpModel.lean`: without any
machine effect it returns `base ^ exponent` when that fits in a word. Otherwise
its result factors through solc's `Panic(0x11)` sequence from the entry state
(`∃ cont, … = panicRun M 0x11 s >>= cont`). That form is only informative when
the panic sequence faults: on a machine whose `revert` halts (`RevertHalts M`)
the result is exactly that fault (`checked_exp_overflow_halts`); on a machine
whose `revert` returns, it says nothing about the body's effects.

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
abbrev expE1 : FunEnv EF := .group [] .nil expEnv

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
        have : (Solidity.Yul.Pure.eval .«and» (word2 e 1)).val = e.val % 2 := and_one_val e
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
      have : steps (e / 2) ≤ n := ih (e / 2) this
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

/-! ## `checked_exp_unsigned`, statement by statement -/

abbrev LU : List String := ["base", "exponent", "max", "power"]
abbrev EU : List FnSig := EF

def u1 : Stmt EU ⟨true, false⟩ LU :=
  (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.var "exponent" (.there .here)) .nil)) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 1, 1, rfl⟩)) (.stmt .leave .nil))))

def u2 : Stmt EU ⟨true, false⟩ LU :=
  (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.var "base" .here) .nil)) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 0, 0, rfl⟩)) (.stmt .leave .nil))))

def u3 : Stmt EU ⟨true, false⟩ LU :=
  (.switch (.var "base" .here) (.cons ⟨.num 1, 1, rfl⟩ (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 1, 1, rfl⟩)) (.stmt .leave .nil))) (.cons ⟨.num 2, 2, rfl⟩ (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 255, 255, rfl⟩) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«exp»)) (.cons (.lit ⟨.num 2, 2, rfl⟩) (.cons (.var "exponent" (.there .here)) .nil)))) (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "max" (.there (.there .here))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt .leave .nil))))) .nil)))

def u4 : Stmt EU ⟨true, false⟩ LU :=
  (.if_ (.op (.evm (.pure .«or»)) (.cons (.op (.evm (.pure .«and»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "base" .here) (.cons (.lit ⟨.num 11, 11, rfl⟩) .nil))) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 78, 78, rfl⟩) .nil))) .nil))) (.cons (.op (.evm (.pure .«and»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "base" .here) (.cons (.lit ⟨.num 307, 307, rfl⟩) .nil))) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 32, 32, rfl⟩) .nil))) .nil))) .nil))) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«exp»)) (.cons (.var "base" .here) (.cons (.var "exponent" (.there .here)) .nil)))) (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "max" (.there (.there .here))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt .leave .nil)))))

def u5 : Stmt EU ⟨true, false⟩ LU :=
  (.assign [⟨"power", (.there (.there (.there .here)))⟩, ⟨"base", .here⟩] (.call (.there (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) (.cons (.var "base" .here) (.cons (.var "exponent" (.there .here)) (.cons (.var "max" (.there (.there .here))) .nil))))))

def u6 : Stmt EU ⟨true, false⟩ LU :=
  (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.op (.evm (.pure .«div»)) (.cons (.var "max" (.there (.there .here))) (.cons (.var "base" .here) .nil))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil)))

def u7 : Stmt EU ⟨true, false⟩ LU :=
  (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "base" .here) .nil))))

theorem unsigned_eq : expExpUnsigned =
    .mk [] .nil (.stmt u1 (.stmt u2 (.stmt u3 (.stmt u4 (.stmt u5 (.stmt u6 (.stmt u7 .nil))))))) := rfl

def uv (b e mx p : Word) : Vals LU := .cons b (.cons e (.cons mx (.cons p .nil)))

theorem block_assign_leave (k : Nat) {F : List FnSig} {l : Bool} {L : List String} (E : FunEnv F) {n : String}
    (t : Mem L n) (lit : Lit) (vs : Vals L) (s : σ) :
    evalBlock (c := ⟨true, l⟩) M ctx (k + 5) E (.mk [] .nil (.stmt (.assign [⟨n, t⟩] (.lit lit)) (.stmt .leave .nil))) vs s =
      .ok (s, vs.set t lit.value, .leave) := by
  rw [block_empty, items_stmt_normal M ctx (k + 3) _ _ _ _ _ _ _ (assign_of M ctx (k + 2) _ _ _ _ _ _ (lit_gen M ctx _ _ _ _ _)),
    items_stmt_flow M ctx (k + 2) _ _ _ _ _ _ _ _ (leave_stmt M ctx (k + 1) _ _ _) (by decide)]

theorem switch_of (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (e : Expr F L 1)
    (cs : Cases F c L) (vs : Vals L) (s : σ) (v : Word) (h : evalExpr M ctx k E e vs s = .ok (s, fun _ => v)) :
    evalStmt M ctx (k + 1) E (.switch e cs) vs s =
      match cs.select v with
      | some b => evalBlock M ctx k E b vs s
      | none => .ok (s, vs, .normal) := by
  simp only [evalStmt, h, run_ok_bind]
  rcases cs.select v with _ | b
  · rfl
  · rfl

theorem iszero_ne (w : Word) (h : w.val = 0) : Solidity.Yul.Pure.eval .«iszero» (fun _ => w) ≠ 0 := by
  rw [pure_iszero, h]
  decide

theorem iszero_eq (w : Word) (h : w.val ≠ 0) : Solidity.Yul.Pure.eval .«iszero» (fun _ => w) = 0 := by
  rw [pure_iszero, (truth_eq_zero _).mpr (beq_eq_false_iff_ne.mpr h)]

theorem u1_zero (k : Nat) (b e mx p : Word) (s : σ) (h : e.val = 0) :
    evalStmt M ctx (k + 10) expE1 u1 (uv b e mx p) s = .ok (s, uv b e mx 1, .leave) := by
  rw [u1, uv, if_of_ne M ctx (k + 9) _ _ _ _ _ _ (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (k + 5)) _]
  · rw [block_assign_leave M ctx (k + 4)]
    rfl
  · exact iszero_ne _ h

theorem u1_ne (k : Nat) (b e mx p : Word) (s : σ) (h : e.val ≠ 0) :
    evalStmt M ctx (k + 10) expE1 u1 (uv b e mx p) s = .ok (s, uv b e mx p, .normal) := by
  rw [u1, uv, if_of_eq M ctx (k + 9) _ _ _ _ _ _ (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (k + 5)) _]
  exact iszero_eq _ h

theorem u2_zero (k : Nat) (b e mx p : Word) (s : σ) (h : b.val = 0) :
    evalStmt M ctx (k + 10) expE1 u2 (uv b e mx p) s = .ok (s, uv b e mx 0, .leave) := by
  rw [u2, uv, if_of_ne M ctx (k + 9) _ _ _ _ _ _ (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (k + 5)) _]
  · rw [block_assign_leave M ctx (k + 4)]
    rfl
  · exact iszero_ne _ h

theorem u2_ne (k : Nat) (b e mx p : Word) (s : σ) (h : b.val ≠ 0) :
    evalStmt M ctx (k + 10) expE1 u2 (uv b e mx p) s = .ok (s, uv b e mx p, .normal) := by
  rw [u2, uv, if_of_eq M ctx (k + 9) _ _ _ _ _ _ (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (k + 5)) _]
  exact iszero_eq _ h

theorem lit_ne (n : Nat) (w : Word) (h : w.val ≠ n) (nW : n < 2 ^ 256) : ¬ ((OfNat.ofNat n : Word) = w) := by
  intro eq
  apply h
  rw [← eq]
  exact Nat.mod_eq_of_lt nW

theorem u3_one (k : Nat) (b e mx p : Word) (s : σ) (h : b.val = 1) :
    evalStmt M ctx (k + 10) expE1 u3 (uv b e mx p) s = .ok (s, uv b e mx 1, .leave) := by
  have hb : b = 1 := Fin.ext h
  subst hb
  rw [u3, uv, switch_of M ctx (k + 9) _ _ _ _ _ _ (var_gen M ctx _ _ _ _ (k + 8))]
  simp only [Vals.get_here, Cases.select, ↓reduceIte]
  rw [block_assign_leave M ctx (k + 4)]
  rfl

theorem u3_other (k : Nat) (b e mx p : Word) (s : σ) (h1 : b.val ≠ 1) (h2 : b.val ≠ 2) :
    evalStmt M ctx (k + 10) expE1 u3 (uv b e mx p) s = .ok (s, uv b e mx p, .normal) := by
  rw [u3, uv, switch_of M ctx (k + 9) _ _ _ _ _ _ (var_gen M ctx _ _ _ _ (k + 8))]
  simp only [Vals.get_here, Cases.select, lit_ne 1 b h1 (by decide), lit_ne 2 b h2 (by decide), ↓reduceIte]

theorem lit_val (n : Nat) (h : n < 2 ^ 256) : (OfNat.ofNat n : Word).val = n := Nat.mod_eq_of_lt h

theorem pure_lt (xs : Fin 2 → Word) :
    Solidity.Yul.Pure.eval .«lt» xs = Solidity.Yul.truth ((xs 0).val < (xs 1).val) := rfl

theorem gt_bne (a b : Word) : (Solidity.Yul.Pure.eval .«gt» (word2 a b) != 0) = decide (b.val < a.val) := by
  rw [pure_gt, word2_zero, word2_one, truth_bne]

theorem panicIf_false (code : Word) (s : σ) : panicIf M false code s = .ok s := rfl
theorem panicIf_true (code : Word) (s : σ) : panicIf M true code s = panicRun M code s := rfl

theorem word_le_max (mx w : Word) (hmx : mx.val = maxWord) : decide (mx.val < w.val) = false := by
  have : w.val < 2 ^ 256 := w.isLt
  rw [hmx]
  exact decide_eq_false (by unfold maxWord; omega)

/-- `case 2` of the switch: `2 ** e`, with the panic for `e > 255`. -/
theorem u3_two (k : Nat) (b e mx p : Word) (s : σ) (h : b.val = 2) (hmx : mx.val = maxWord) :
    (255 < e.val → ∃ cont, evalStmt M ctx (k + 45) expE1 u3 (uv b e mx p) s = panicRun M 0x11 s >>= cont) ∧
    (¬ 255 < e.val → evalStmt M ctx (k + 45) expE1 u3 (uv b e mx p) s =
      .ok (s, uv b e mx (Solidity.Yul.Pure.eval .«exp» (word2 2 e)), .leave)) := by
  have hb : b = 2 := Fin.ext h
  subst hb
  rw [u3, uv, switch_of M ctx (k + 44) _ _ _ _ _ _ (var_gen M ctx _ _ _ _ (k + 43))]
  simp only [Vals.get_here, Cases.select, lit_ne 1 2 (by decide) (by decide), ↓reduceIte]
  rw [block_empty, items_stmt_map M ctx (k + 42) _ _ _ _ _ _ _
    (exp_if_panic M ctx (k + 25) _ _ _ rfl _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (k + 36)))]
  simp only [Vals.get_here, Vals.get_there, gt_bne, lit_val 255 (by decide)]
  constructor
  · intro big
    rw [decide_eq_true big, panicIf_true]
    exact ⟨_, rfl⟩
  · intro le
    rw [decide_eq_false le, panicIf_false, run_ok_bind,
      items_stmt_normal M ctx (k + 41) _ _ _ _ _ _ _ (assign_of M ctx (k + 40) _ _ _ _ _ _
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (lit_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _) (k + 35))),
      items_stmt_map M ctx (k + 40) _ _ _ _ _ _ _
        (exp_if_panic M ctx (k + 23) _ _ _ rfl _ _ _
          (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _) (k + 34)))]
    simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, gt_bne, word_le_max _ _ hmx,
      panicIf_false, run_ok_bind]
    rw [items_stmt_flow M ctx (k + 39) _ _ _ _ _ _ _ _ (leave_stmt M ctx (k + 38) _ _ _) (by decide)]
    rfl

/-- The small-range shortcut: `exp(base, exponent)` directly. -/
theorem u4_run (k : Nat) (b e mx p : Word) (s : σ) (hmx : mx.val = maxWord) :
    let small := (decide (b.val < 11) && decide (e.val < 78)) || (decide (b.val < 307) && decide (e.val < 32))
    (small = true → evalStmt M ctx (k + 45) expE1 u4 (uv b e mx p) s =
      .ok (s, uv b e mx (Solidity.Yul.Pure.eval .«exp» (word2 b e)), .leave)) ∧
    (small = false → evalStmt M ctx (k + 45) expE1 u4 (uv b e mx p) s = .ok (s, uv b e mx p, .normal)) := by
  intro small
  have hc := op2_gen M ctx expE1 .«or» _ _ (uv b e mx p) s _ _ 9
    (op2_gen M ctx _ .«and» _ _ _ _ _ _ 5
      (op2_gen M ctx _ .«lt» _ _ _ _ _ _ 1 (var_gen M ctx _ (n := "base") .here _ _) (lit_gen M ctx _ ⟨.num 11, 11, rfl⟩ _ _))
      (op2_gen M ctx _ .«lt» _ _ _ _ _ _ 1 (var_gen M ctx _ (n := "exponent") (.there .here) _ _) (lit_gen M ctx _ ⟨.num 78, 78, rfl⟩ _ _)))
    (op2_gen M ctx _ .«and» _ _ _ _ _ _ 5
      (op2_gen M ctx _ .«lt» _ _ _ _ _ _ 1 (var_gen M ctx _ (n := "base") .here _ _) (lit_gen M ctx _ ⟨.num 307, 307, rfl⟩ _ _))
      (op2_gen M ctx _ .«lt» _ _ _ _ _ _ 1 (var_gen M ctx _ (n := "exponent") (.there .here) _ _) (lit_gen M ctx _ ⟨.num 32, 32, rfl⟩ _ _)))
    (k + 31)
  simp only [uv, Vals.get_here, Vals.get_there, pure_or, pure_and, pure_lt, word2_zero, word2_one,
    lit_val 11 (by decide), lit_val 78 (by decide), lit_val 307 (by decide), lit_val 32 (by decide),
    truth_and, truth_or] at hc
  constructor
  · intro yes
    rw [u4, uv, if_of_ne M ctx (k + 44) _ _ _ _ _ _ hc _]
    · rw [block_empty, items_stmt_normal M ctx (k + 42) _ _ _ _ _ _ _ (assign_of M ctx (k + 41) _ _ _ _ _ _
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _) (k + 36))),
        items_stmt_map M ctx (k + 41) _ _ _ _ _ _ _
          (exp_if_panic M ctx (k + 24) _ _ _ rfl _ _ _
            (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _) (k + 35)))]
      simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, gt_bne, word_le_max _ _ hmx,
        panicIf_false, run_ok_bind]
      rw [items_stmt_flow M ctx (k + 40) _ _ _ _ _ _ _ _ (leave_stmt M ctx (k + 39) _ _ _) (by decide)]
      rfl
    · intro z
      exact absurd ((truth_eq_zero _).mp z) (fun h => Bool.noConfusion (yes.symm.trans h))
  · intro no
    rw [u4, uv, if_of_eq M ctx (k + 44) _ _ _ _ _ _ hc _]
    exact (truth_eq_zero _).mpr no

theorem u5_run (j : Nat) (b e : Nat) (mx p : Word) (bW : b < 2 ^ 256) (eW : e < 2 ^ 256)
    (hmx : mx.val = maxWord) (s : σ) :
    match expLoop 1 b e with
    | some (p', b', _) => evalStmt M ctx (j + steps e + 60) expE1 u5
        (uv (Solidity.Yul.word b) (Solidity.Yul.word e) mx p) s =
        .ok (s, uv (Solidity.Yul.word b') (Solidity.Yul.word e) mx (Solidity.Yul.word p'), .normal)
    | none => ∃ cont, evalStmt M ctx (j + steps e + 60) expE1 u5
        (uv (Solidity.Yul.word b) (Solidity.Yul.word e) mx p) s = panicRun M 0x11 s >>= cont := by
  have hl : expE1.lookup (s := ⟨"checked_exp_helper", ["_power", "_base", "exponent", "max"], ["power", "base"]⟩)
      (.there (.there (.there .here))) = ⟨_, expEnv, expExpHelper⟩ := rfl
  have hr := helper_run M ctx (j + 7) b e mx eW bW hmx s
  rw [u5, uv]
  simp only [evalStmt, evalExpr, evalArgs, run_ok_bind, run_pure, Vals.get_here, Vals.get_there]
  rw [hl]
  simp only [Vals.ofFn, consFn_zero, consFn_succ, Vals.zeros, Vals.append_cons', Vals.append_nil']
  rcases hE : expLoop 1 b e with _ | ⟨p', b', e'⟩
  · rw [hE] at hr
    obtain ⟨cont, hc⟩ := hr
    simp only [hv, one_word] at hc
    rw [show j + steps e + 58 = j + 7 + steps e + 51 by omega, one_word, hc]
    simp only [bind_assoc]
    exact ⟨_, rfl⟩
  · rw [hE] at hr
    simp only [hv, one_word] at hr
    rw [show j + steps e + 58 = j + 7 + steps e + 51 by omega, one_word, hr]
    simp only [run_ok_bind, Vals.drop_cons, Vals.drop_nil, assignAll, Vals.set_here, Vals.set_there]
    rfl

theorem gt_div_bne' (mx b p : Word) :
    (Solidity.Yul.Pure.eval .«gt» (word2 p (Solidity.Yul.Pure.eval .«div» (word2 mx b))) != 0) =
      decide (mx.val / b.val < p.val) := by
  rw [pure_gt, word2_zero, word2_one, pure_div, word2_zero, word2_one, word_div_val, truth_bne]

theorem u6_run (k : Nat) (b e mx p : Word) (s : σ) :
    evalStmt M ctx (k + 40) expE1 u6 (uv b e mx p) s =
      (fun s => (s, uv b e mx p, .normal)) <$> panicIf M (decide (mx.val / b.val < p.val)) 0x11 s := by
  rw [u6, uv, exp_if_panic M ctx (k + 23) _ _ _ rfl _ _ _
    (op2_gen M ctx _ _ _ _ _ _ _ _ 5 (fun j => var_gen M ctx _ _ _ _ (j + 4))
      (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _)) (k + 30))]
  simp only [Vals.get_here, Vals.get_there, gt_div_bne']

theorem u7_run (k : Nat) (b e mx p : Word) (s : σ) :
    evalStmt M ctx (k + 5) expE1 u7 (uv b e mx p) s =
      .ok (s, uv b e mx (Solidity.Yul.word (p.val * b.val)), .normal) := by
  rw [u7, uv, assign_pure2]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, pure_mul, word2_zero, word2_one]
  rfl

theorem items_stmt_bind (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F)
    (st : Stmt F c L) (rest : Items F c L g) (vs : Vals L) (s : σ) (R : Run σ σ)
    (h : ∃ cont, evalStmt M ctx k E st vs s = R >>= cont) :
    ∃ cont, evalItems M ctx (k + 1) E (.stmt st rest) vs s = R >>= cont := by
  obtain ⟨cont, h⟩ := h
  simp only [evalItems, h, bind_assoc]
  exact ⟨_, rfl⟩

theorem exp_word (a : Word) (e : Nat) (eW : e < 2 ^ 256) :
    Solidity.Yul.Pure.eval .«exp» (word2 a (Solidity.Yul.word e)) = Solidity.Yul.word (a.val ^ e % 2 ^ 256) := by
  apply Fin.ext
  have h : Solidity.Yul.Pure.eval .«exp» (word2 a (Solidity.Yul.word e)) =
      Solidity.Yul.powWord a (Solidity.Yul.word e).val := rfl
  rw [h, Solidity.Yul.powWord_correct, word_val_lt e eW, word_val, Nat.mod_mod]

/-- The body of `checked_exp_unsigned(base, exponent, max)` (with `max = 2^256 - 1`) runs as
`expUnsigned`: the returned `power` is the model's value, or the result factors through the panic. -/
theorem unsigned_run (j : Nat) (b e : Nat) (mx : Word) (bW : b < 2 ^ 256) (eW : e < 2 ^ 256)
    (hmx : mx.val = maxWord) (s : σ) :
    match expUnsigned b e with
    | some r => ∃ vs fl, evalBlock M ctx (j + 400) expEnv expExpUnsigned
        (uv (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0) s = .ok (s, vs, fl) ∧
        vs.get (.there (.there (.there .here))) = Solidity.Yul.word r
    | none => ∃ cont, evalBlock M ctx (j + 400) expEnv expExpUnsigned
        (uv (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0) s = panicRun M 0x11 s >>= cont := by
  have wb : (Solidity.Yul.word b).val = b := word_val_lt b bW
  have we : (Solidity.Yul.word e).val = e := word_val_lt e eW
  rw [unsigned_eq, block_empty]
  unfold expUnsigned
  by_cases e0 : e = 0
  · rw [if_pos e0]
    dsimp only
    rw [items_stmt_flow M ctx (j + 398) _ _ _ _ _ _ _ _ (u1_zero M ctx (j + 388) _ _ _ _ s (by rw [we, e0])) (by decide)]
    exact ⟨_, _, rfl, rfl⟩
  rw [if_neg e0, items_stmt_normal M ctx (j + 398) _ _ _ _ _ _ _ (u1_ne M ctx (j + 388) _ _ _ _ s (by rw [we]; exact e0))]
  by_cases b0 : b = 0
  · rw [if_pos b0]
    dsimp only
    rw [items_stmt_flow M ctx (j + 397) _ _ _ _ _ _ _ _ (u2_zero M ctx (j + 387) _ _ _ _ s (by rw [wb, b0])) (by decide)]
    exact ⟨_, _, rfl, rfl⟩
  rw [if_neg b0, items_stmt_normal M ctx (j + 397) _ _ _ _ _ _ _ (u2_ne M ctx (j + 387) _ _ _ _ s (by rw [wb]; exact b0))]
  by_cases b1 : b = 1
  · rw [if_pos b1]
    dsimp only
    rw [items_stmt_flow M ctx (j + 396) _ _ _ _ _ _ _ _ (u3_one M ctx (j + 386) _ _ _ _ s (by rw [wb, b1])) (by decide)]
    exact ⟨_, _, rfl, rfl⟩
  rw [if_neg b1]
  by_cases b2 : b = 2
  · rw [if_pos b2]
    have t := u3_two M ctx (j + 351) (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0 s (by rw [wb, b2]) hmx
    rw [we] at t
    by_cases big : 255 < e
    · rw [if_pos big]
      dsimp only
      exact items_stmt_bind M ctx (j + 396) _ _ _ _ s _ (t.1 big)
    · rw [if_neg big]
      dsimp only
      rw [items_stmt_flow M ctx (j + 396) _ _ _ _ _ _ _ _ (t.2 big) (by decide)]
      refine ⟨_, _, rfl, ?_⟩
      have two : (Solidity.Yul.word b) = 2 := Fin.ext (by rw [wb, b2]; rfl)
      show Solidity.Yul.Pure.eval .«exp» (word2 2 (Solidity.Yul.word e)) = _
      rw [exp_word 2 e eW]
      rfl
  rw [if_neg b2, items_stmt_normal M ctx (j + 396) _ _ _ _ _ _ _
    (u3_other M ctx (j + 386) _ _ _ _ s (by rw [wb]; exact b1) (by rw [wb]; exact b2))]
  have t4 := u4_run M ctx (j + 350) (Solidity.Yul.word b) (Solidity.Yul.word e) mx 0 s hmx
  simp only [wb, we] at t4
  by_cases small : (b < 11 ∧ e < 78) ∨ (b < 307 ∧ e < 32)
  · rw [if_pos small]
    dsimp only
    have sm : ((decide (b < 11) && decide (e < 78)) || (decide (b < 307) && decide (e < 32))) = true := by
      rcases small with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h1, h2, decide_true, Bool.and_self, Bool.true_or]
      · simp only [h1, h2, decide_true, Bool.and_self, Bool.or_true]
    rw [items_stmt_flow M ctx (j + 395) _ _ _ _ _ _ _ _ (t4.1 sm) (by decide)]
    refine ⟨_, _, rfl, ?_⟩
    show Solidity.Yul.Pure.eval .«exp» (word2 (Solidity.Yul.word b) (Solidity.Yul.word e)) = _
    rw [exp_word _ e eW, wb]
  have sm : ((decide (b < 11) && decide (e < 78)) || (decide (b < 307) && decide (e < 32))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply small
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  rw [if_neg small, items_stmt_normal M ctx (j + 395) _ _ _ _ _ _ _ (t4.2 sm)]
  have st : steps e ≤ 255 := steps_le 255 e eW
  obtain ⟨j', hj⟩ : ∃ j', j + 395 = (j' + steps e + 60) + 1 := ⟨j + 334 - steps e, by omega⟩
  have t5 := u5_run M ctx j' b e mx 0 bW eW hmx s
  have spec := expLoop_spec e 1 b (by omega) (Nat.le_refl 1) (by omega) bW
  rw [hj]
  revert t5 spec
  rcases expLoop 1 b e with _ | ⟨p', b', e'⟩
  · intro t5 _
    exact items_stmt_bind M ctx _ _ _ _ _ s _ t5
  · intro t5 ⟨_, _, h3, h4, _⟩
    have pW : p' < 2 ^ 256 := by omega
    have b'0 : 0 < b' := by omega
    dsimp only
    dsimp only at t5
    rw [items_stmt_normal M ctx _ _ _ _ _ _ _ _ t5]
    have fuel : j' + steps e + 60 = (j' + steps e + 19) + 40 + 1 := rfl
    rw [fuel, items_stmt_map M ctx _ _ _ _ _ _ _ _ (u6_run M ctx (j' + steps e + 19) _ _ _ _ s)]
    simp only [hmx, word_val_lt b' h4, word_val_lt p' pW]
    by_cases over : maxWord / b' < p'
    · rw [if_pos over, decide_eq_true over, panicIf_true]
      exact ⟨_, rfl⟩
    · rw [if_neg over, decide_eq_false over, panicIf_false, run_ok_bind]
      have fuel2 : j' + steps e + 19 + 40 = (j' + steps e + 57) + 2 := by omega
      rw [fuel2, items_last, show j' + steps e + 57 + 1 = (j' + steps e + 53) + 5 by omega, u7_run]
      refine ⟨_, _, rfl, ?_⟩
      show Solidity.Yul.word ((Solidity.Yul.word p').val * (Solidity.Yul.word b').val) = _
      rw [word_val_lt p' pW, word_val_lt b' h4, word_mod]

/-! ## `checked_exp_t_uint256_t_uint256` -/

theorem word_self (w : Word) : Solidity.Yul.word w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)

theorem drop_power (vs : Vals (["base", "exponent", "max"] ++ ["power"])) :
    (Vals.drop ["base", "exponent", "max"] vs).toFn ⟨0, by decide⟩ = vs.get (.there (.there (.there .here))) := by
  match vs with
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => rfl

theorem max_lit_val : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Word).val = maxWord := rfl

/-- The body of `checked_exp_t_uint256_t_uint256(base, exponent)` on any machine and state:
`power = base ** exponent` with no machine effect when it fits in a word; otherwise the
result factors through solc's `Panic(0x11)` sequence from the entry state (informative
when that sequence faults; see `checked_exp_overflow_halts`). -/
theorem checked_exp_body (j : Nat) (x y : Word) (s : σ) :
    (x.val ^ y.val < 2 ^ 256 → evalBlock M ctx (j + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s =
      .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val ^ y.val)) .nil)), .normal)) ∧
    (¬ x.val ^ y.val < 2 ^ 256 → ∃ cont, evalBlock M ctx (j + 420) expEnv expExpU256
      (.cons x (.cons y (.cons 0 .nil))) s = panicRun M 0x11 s >>= cont) := by
  have hl : expE1.lookup (s := ⟨"checked_exp_unsigned", ["base", "exponent", "max"], ["power"]⟩)
      (.there (.there (.there (.there .here)))) = ⟨_, expEnv, expExpUnsigned⟩ := rfl
  have hu := unsigned_run M ctx (j + 14) x.val y.val _ x.isLt y.isLt max_lit_val s
  rw [expUnsigned_correct x.val y.val x.isLt, word_self, word_self] at hu
  rw [expExpU256, block_empty,
    items_stmt_normal M ctx (j + 418) _ _ _ _ _ _ _ (assign_of M ctx _ _ _ _ _ _ _ (exp_cleanup_call M ctx (j + 410) _ _ rfl _ _ _)),
    items_stmt_normal M ctx (j + 417) _ _ _ _ _ _ _ (assign_of M ctx _ _ _ _ _ _ _ (exp_cleanup_call M ctx (j + 409) _ _ rfl _ _ _)),
    items_last M ctx (j + 415)]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there]
  simp only [evalStmt, evalExpr, evalArgs, run_ok_bind, run_pure, Vals.get_here, Vals.get_there]
  rw [hl]
  simp only [Vals.ofFn, consFn_zero, consFn_succ, Vals.zeros, Vals.append_cons', Vals.append_nil']
  constructor
  · intro fits
    rw [if_pos fits] at hu
    obtain ⟨vs, fl, h, hp⟩ := hu
    simp only [uv] at h
    rw [h]
    simp only [run_ok_bind, assignAll, Vals.set_here, Vals.set_there]
    rw [drop_power, hp]
  · intro over
    rw [if_neg over] at hu
    obtain ⟨cont, h⟩ := hu
    simp only [uv] at h
    rw [h]
    simp only [bind_assoc]
    exact ⟨_, rfl⟩

/-- On a machine whose `revert` halts, an overflowing `checked_exp_t_uint256_t_uint256`
ends exactly with the fault of solc's `Panic(0x11)` sequence run from the entry state. -/
theorem checked_exp_overflow_halts (j : Nat) (x y : Word) (s : σ) (h : RevertHalts M)
    (over : ¬ x.val ^ y.val < 2 ^ 256) :
    ∃ e, panicRun M 0x11 s = .error e ∧
      evalBlock M ctx (j + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s = .error e :=
  panic_factor_halts M h 0x11 s _ ((checked_exp_body M ctx j x y s).2 over)

end

end Solidity.SolcValidation.IrSyntax
