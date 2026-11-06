import Solidity.SolcValidation.IrHelpers

/-!
# Simulation of solc's checked-arithmetic helpers

For the helper terms of `SolcValidation/IrHelpers.lean` (certified readings of
the real solc 0.8.38 IR): calling `checked_add_t_uint256` (`checked_add_sim`),
and running the body of `checked_mul_t_uint256` from its entry values
(`checked_mul_body`), on any two words, any machine and any state, either
returns the mathematical result or runs solc's panic sequence
(`mstore(0, Panic selector)`, `mstore(4, code)`, `revert(0, 0x24)`).
`checked_sub_t_uint256`, `checked_div_t_int256` and the call-site form of
`checked_mul_t_uint256` are proved in `SolcValidation/IrHelperSteps.lean` by
composing statement-level lemmas.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- The runtime environment of the helper group. -/
def helperEnv : FunEnv (helperSigs ++ []) := .group helperSigs helperBodies .nil

/-- The two argument names of a helper call site. -/
abbrev ArgNames : List String := ["a", "b"]

def argVals (x y : Word) : Vals ArgNames := .cons x (.cons y .nil)

def argPair : Args (helperSigs ++ []) ArgNames 2 :=
  .cons (.var "a" .here) (.cons (.var "b" (.there .here)) .nil)

/-- `Panic(uint256)` selector `0x4e487b71`, left-aligned. -/
def panicSelector : Word := 35408467139433450592217433187231851964531694900788300625387963629091585785856

def word2 (a b : Word) : Fin 2 → Word := fun i => if i.val = 0 then a else b

/-- solc's panic sequence on the machine, for a panic code. -/
def panicRun {σ : Type} (M : Machine σ) (code : Word) (s : σ) : Run σ σ := do
  let (s, _) ← M.run .«mstore» (word2 0 panicSelector) s
  let (s, _) ← M.run .«mstore» (word2 4 code) s
  let (s, _) ← M.run .«revert» (word2 0 36) s
  pure s

/-! Index-generic evaluation lemmas for intrinsic values (simp then never
instantiates the `match` equations at literal name lists). -/
@[simp] theorem Vals.get_here {x : String} {L : List String} (v : Word) (vs : Vals L) :
    (Vals.cons (x := x) v vs).get .here = v := rfl
@[simp] theorem Vals.get_there {x y : String} {L : List String} (v : Word) (vs : Vals L) (m : Mem L y) :
    (Vals.cons (x := x) v vs).get (.there m) = vs.get m := rfl
@[simp] theorem Vals.set_here {x : String} {L : List String} (v w : Word) (vs : Vals L) :
    (Vals.cons (x := x) v vs).set .here w = .cons w vs := rfl
@[simp] theorem Vals.set_there {x y : String} {L : List String} (v w : Word) (vs : Vals L) (m : Mem L y) :
    (Vals.cons (x := x) v vs).set (.there m) w = .cons v (vs.set m w) := rfl
@[simp] theorem Vals.drop_cons {x : String} {xs L : List String} (v : Word) (vs : Vals (xs ++ L)) :
    Vals.drop (x :: xs) (Vals.cons (x := x) v vs) = Vals.drop xs vs := rfl
@[simp] theorem Vals.drop_nil {L : List String} (vs : Vals L) : Vals.drop [] vs = vs := rfl

@[simp] theorem run_ok_bind {σ α β : Type} (a : α) (f : α → Run σ β) :
    ((Except.ok a : Run σ α) >>= f) = f a := rfl
@[simp] theorem run_error_bind {σ α β : Type} (e : Fault σ) (f : α → Run σ β) :
    ((Except.error e : Run σ α) >>= f) = Except.error e := rfl
@[simp] theorem run_pure {σ α : Type} (a : α) : (pure a : Run σ α) = Except.ok a := rfl
@[simp] theorem run_ok_map {σ α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Run σ α)) = Except.ok (f a) := rfl
@[simp] theorem run_error_map {σ α β : Type} (e : Fault σ) (f : α → β) :
    (f <$> (Except.error e : Run σ α)) = Except.error e := rfl

@[simp] theorem Vals.append_nil' {L : List String} (vs : Vals L) : Vals.append Vals.nil vs = vs := rfl
@[simp] theorem Vals.append_cons' {x : String} {xs L : List String} (v : Word) (front : Vals xs) (vs : Vals L) :
    Vals.append (Vals.cons (x := x) v front) vs = Vals.cons v (Vals.append front vs) := rfl

/-! The owner's pure operations at the shapes the helpers use (stated by `rfl`;
`sub`, whose definition adds `2^256`, is deliberately absent). -/
section PureShapes
open Solidity.Yul
@[simp] theorem pure_add (xs : Fin 2 → Word) : Pure.eval .«add» xs = word ((xs 0).val + (xs 1).val) := rfl
@[simp] theorem pure_mul (xs : Fin 2 → Word) : Pure.eval .«mul» xs = word ((xs 0).val * (xs 1).val) := rfl
@[simp] theorem pure_div (xs : Fin 2 → Word) : Pure.eval .«div» xs = word ((xs 0).val / (xs 1).val) := rfl
@[simp] theorem pure_gt (xs : Fin 2 → Word) : Pure.eval .«gt» xs = truth ((xs 1).val < (xs 0).val) := rfl
@[simp] theorem pure_eq (xs : Fin 2 → Word) : Pure.eval .«eq» xs = truth ((xs 0).val == (xs 1).val) := rfl
@[simp] theorem pure_or (xs : Fin 2 → Word) : Pure.eval .«or» xs = word ((xs 0).val ||| (xs 1).val) := rfl
@[simp] theorem pure_and (xs : Fin 2 → Word) : Pure.eval .«and» xs = word ((xs 0).val &&& (xs 1).val) := rfl
@[simp] theorem pure_iszero (xs : Fin 1 → Word) : Pure.eval .«iszero» xs = truth ((xs 0).val == 0) := rfl
end PureShapes

/-- The flow test after a normal statement, without deciding anything else. -/
theorem ite_normal {α : Type} (a b : α) : (if Flow.normal = Flow.normal then a else b) = a := if_pos rfl

/-- A block without functions adds nothing to the environment. -/
@[simp] theorem lookup_empty_group {F : List FnSig} {s : FnSig} (E : FunEnv F) (m : Mem ([] ++ F) s) :
    (FunEnv.group [] Bodies.nil E).lookup m = E.lookup m := rfl

@[simp] theorem lookup_cleanupU :
    helperEnv.lookup (s := ⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩) .here =
      ⟨_, helperEnv, bodyCleanupU⟩ := rfl
@[simp] theorem lookup_cleanupI :
    helperEnv.lookup (s := ⟨"cleanup_t_int256", ["value"], ["cleaned"]⟩) (.there .here) =
      ⟨_, helperEnv, bodyCleanupI⟩ := rfl
@[simp] theorem lookup_panic11 :
    helperEnv.lookup (s := ⟨"panic_error_0x11", [], []⟩) (.there (.there .here)) =
      ⟨_, helperEnv, bodyPanic11⟩ := rfl
@[simp] theorem lookup_panic12 :
    helperEnv.lookup (s := ⟨"panic_error_0x12", [], []⟩) (.there (.there (.there .here))) =
      ⟨_, helperEnv, bodyPanic12⟩ := rfl
@[simp] theorem lookup_add :
    helperEnv.lookup (s := ⟨"checked_add_t_uint256", ["x", "y"], ["sum"]⟩)
      (.there (.there (.there (.there .here)))) = ⟨_, helperEnv, bodyAdd⟩ := rfl

@[simp] theorem consFn_zero {k : Nat} (w : Word) (ws : Fin k → Word) (h : 0 < k + 1) :
    consFn w ws ⟨0, h⟩ = w := rfl

@[simp] theorem consFn_zero_lit {k : Nat} (w : Word) (ws : Fin k → Word) : consFn w ws 0 = w := rfl

@[simp] theorem word_div_val (a : Word) (b : Nat) :
    (Solidity.Yul.word (a.val / b)).val = a.val / b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

theorem consFn_two (a b : Word) : consFn a (consFn b Fin.elim0) = word2 a b := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem toFn_single {x : String} (w : Word) :
    (Vals.cons (x := x) w Vals.nil).toFn = fun _ => w := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl

@[simp] theorem word2_zero (a b : Word) : word2 a b 0 = a := rfl
@[simp] theorem word2_one (a b : Word) : word2 a b 1 = b := rfl

theorem truth_eq_zero (b : Bool) : Solidity.Yul.truth b = 0 ↔ b = false := by
  cases b <;> decide

theorem word_val (n : Nat) : (Solidity.Yul.word n).val = n % 2 ^ 256 := rfl

/-- The wrapped sum is below an operand exactly when the sum overflows. -/
theorem add_wraps (x y : Word) :
    (Solidity.Yul.word (x.val + y.val)).val < x.val ↔ ¬ x.val + y.val < 2 ^ 256 := by
  have hx : x.val < 2 ^ 256 := x.isLt
  have hy : y.val < 2 ^ 256 := y.isLt
  rw [word_val]
  constructor
  · intro h ok
    rw [Nat.mod_eq_of_lt ok] at h
    omega
  · intro h
    have big : 2 ^ 256 ≤ x.val + y.val := Nat.le_of_not_lt h
    have red : (x.val + y.val) % 2 ^ 256 = x.val + y.val - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt (by omega)]
    rw [red]
    omega

@[simp] theorem lookup_sub :
    helperEnv.lookup (s := ⟨"checked_sub_t_uint256", ["x", "y"], ["diff"]⟩)
      (.there (.there (.there (.there (.there .here))))) = ⟨_, helperEnv, bodySub⟩ := rfl
@[simp] theorem lookup_div :
    helperEnv.lookup (s := ⟨"checked_div_t_int256", ["x", "y"], ["r"]⟩)
      (.there (.there (.there (.there (.there (.there .here)))))) = ⟨_, helperEnv, bodyDiv⟩ := rfl
@[simp] theorem lookup_mul :
    helperEnv.lookup (s := ⟨"checked_mul_t_uint256", ["x", "y"], ["product"]⟩)
      (.there (.there (.there (.there (.there (.there (.there .here))))))) = ⟨_, helperEnv, bodyMul⟩ := rfl

/-- The wrapped difference exceeds the minuend exactly when the subtraction underflows. -/
theorem sub_wraps (x y : Word) :
    x.val < (Solidity.Yul.word (x.val + 2 ^ 256 - y.val)).val ↔ x.val < y.val := by
  have hx : x.val < 2 ^ 256 := x.isLt
  have hy : y.val < 2 ^ 256 := y.isLt
  rw [word_val]
  by_cases le : y.val ≤ x.val
  · have red : (x.val + 2 ^ 256 - y.val) % 2 ^ 256 = x.val - y.val := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [red]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

@[simp] theorem truth_or (a b : Bool) :
    Solidity.Yul.word ((Solidity.Yul.truth a).val ||| (Solidity.Yul.truth b).val) =
      Solidity.Yul.truth (a || b) := by
  cases a <;> cases b <;> decide

@[simp] theorem truth_and (a b : Bool) :
    Solidity.Yul.word ((Solidity.Yul.truth a).val &&& (Solidity.Yul.truth b).val) =
      Solidity.Yul.truth (a && b) := by
  cases a <;> cases b <;> decide

@[simp] theorem truth_iszero (a : Bool) :
    Solidity.Yul.truth ((Solidity.Yul.truth a).val == 0) = Solidity.Yul.truth (!a) := by
  cases a <;> decide

/-- solc's multiplication check: `x = 0 ∨ y = (x·y mod 2^256) / x` exactly when `x·y` fits. -/
theorem mul_fits (x y : Word) :
    ((x.val == 0) || (y.val == (Solidity.Yul.word (x.val * y.val)).val / x.val)) = true ↔
      x.val * y.val < 2 ^ 256 := by
  have hy : y.val < 2 ^ 256 := y.isLt
  rw [word_val]
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (zero | same)
    · rw [zero, Nat.zero_mul]; exact Nat.two_pow_pos 256
    · apply Classical.byContradiction
      intro big
      have pos : 0 < x.val := by
        rcases Nat.eq_zero_or_pos x.val with z | p
        · rw [z, Nat.zero_mul] at big; exact absurd (Nat.two_pow_pos 256) big
        · exact p
      have small : x.val * y.val % 2 ^ 256 < x.val * y.val :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 256)) (Nat.le_of_not_lt big)
      have : x.val * y.val % 2 ^ 256 / x.val < y.val :=
        (Nat.div_lt_iff_lt_mul pos).mpr (by rw [Nat.mul_comm y.val x.val]; exact small)
      omega
  · intro fits
    rcases Nat.eq_zero_or_pos x.val with z | p
    · exact Or.inl z
    · right
      rw [Nat.mod_eq_of_lt fits, Nat.mul_div_cancel_left _ p]

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

def addCall : Expr (helperSigs ++ []) ArgNames 1 :=
  .call (s := ⟨"checked_add_t_uint256", ["x", "y"], ["sum"]⟩)
    (.there (.there (.there (.there .here)))) argPair

theorem checked_add_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 20) helperEnv addCall (argVals x y) s =
      if x.val + y.val < 2 ^ 256 then .ok (s, fun _ => Solidity.Yul.word (x.val + y.val))
      else (fun s => (s, fun _ => Solidity.Yul.word (x.val + y.val))) <$> panicRun M 0x11 s := by
  simp only [addCall, argPair, argVals, evalArgs, evalExpr, Vals.get, bind, Except.bind, pure,
    Except.pure, lookup_add, lookup_empty_group, lookup_cleanupU, lookup_panic11, bodyAdd, bodyCleanupU,
    bodyPanic11, evalBlock, evalItems, evalStmt, Vals.ofFn, Vals.append, Vals.zeros, Vals.set,
    assignAll, consFn, evalOp, Vals.drop]
  simp only [↓reduceIte, List.cons_append, List.nil_append, List.append_eq, List.length_cons,
    List.length_nil, Nat.reduceAdd, Vals.drop, toFn_single, Fin.zero_eta, Fin.isValue,
    Fin.succ_zero_eq_one, Vals.get, Vals.set, Solidity.Yul.Pure.eval, Nat.reducePow, consFn_zero_lit,
    consFn_two, word2_one, Vals.get_here, Vals.get_there, panicRun, run_pure, map_bind, run_ok_map]
  by_cases ok : x.val + y.val < 2 ^ 256
  · have keep : ¬ (Solidity.Yul.word (x.val + y.val)).val < x.val := fun h => (add_wraps x y).mp h ok
    rw [if_pos ((truth_eq_zero _).mpr (decide_eq_false keep))]
    simp only [↓reduceIte, Vals.drop, toFn_single, List.length_cons, List.length_nil, Nat.reduceAdd, ok]
  · have wraps : (Solidity.Yul.word (x.val + y.val)).val < x.val := (add_wraps x y).mpr ok
    rw [if_neg (fun h => absurd ((truth_eq_zero _).mp h) (by simp only [wraps, decide_true, Bool.true_eq_false, not_false_eq_true]))]
    simp only [ok, if_false]
    simp only [panicSelector] at *
    rcases h1 : M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
    · simp only [bind, Except.bind]
    · rcases h2 : M.run .«mstore» (word2 4 17) s1 with e | ⟨s2, r2⟩
      · simp only [↓reduceIte, Fin.isValue, h2, bind, Except.bind]
      · rcases h3 : M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
        · simp only [↓reduceIte, Fin.isValue, h2, h3, bind, Except.bind]
        · simp only [↓reduceIte, Fin.isValue, h2, h3, Vals.drop, toFn_single, List.length_cons,
            List.length_nil, Nat.reduceAdd, bind, Except.bind]

/-- The owner's `sub` on two words, by value (kept folded in the proofs below). -/
theorem pure_sub_val (x y : Word) :
    (Solidity.Yul.Pure.eval .«sub» (word2 x y)).val = (x.val + 2 ^ 256 - y.val) % 2 ^ 256 := rfl

theorem pure_sub_of_le (x y : Word) (le : y.val ≤ x.val) :
    Solidity.Yul.Pure.eval .«sub» (word2 x y) = Solidity.Yul.word (x.val - y.val) := by
  apply Fin.ext
  have shift : x.val + 2 ^ 256 - y.val = (x.val - y.val) + 2 ^ 256 := by omega
  rw [pure_sub_val, word_val, shift, Nat.add_mod_right]

/-- `checked_mul_t_uint256`'s body, from its entry values (parameters `x y`, return `product = 0`). -/
theorem checked_mul_body (k : Nat) (x y : Word) (s : σ) :
    evalBlock M ctx (k + 30) helperEnv bodyMul (.cons x (.cons y (.cons 0 .nil))) s =
      if x.val * y.val < 2 ^ 256 then .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val * y.val)) .nil)), .normal)
      else (fun s => (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val * y.val)) .nil)), .normal)) <$>
        panicRun M 0x11 s := by
  simp only [bodyMul, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, Vals.get_here, Vals.get_there, run_ok_bind, run_pure,
    lookup_empty_group, lookup_cleanupU, lookup_panic11, bodyCleanupU, bodyPanic11, Vals.ofFn,
    Vals.append, Vals.zeros, assignAll, Vals.set_here, Vals.set_there, Vals.drop_cons, Vals.drop_nil,
    evalOp, consFn_two, consFn_zero, toFn_single, word2_zero, word2_one, ↓reduceIte, evalInit,
    Vals.append_nil', Vals.append_cons', pure_mul, pure_div, pure_eq, pure_or, pure_iszero,
    consFn_zero_lit, word_div_val, truth_or, truth_iszero]
  by_cases fits : x.val * y.val < 2 ^ 256
  · have c : ((x.val == 0) || (y.val == (Solidity.Yul.word (x.val * y.val)).val / x.val)) = true :=
      (mul_fits x y).mpr fits
    rw [if_pos ((truth_eq_zero _).mpr (by rw [c]; rfl)), if_pos fits]
    rfl
  · have c : ((x.val == 0) || (y.val == (Solidity.Yul.word (x.val * y.val)).val / x.val)) = false :=
      Bool.eq_false_iff.mpr fun h => fits ((mul_fits x y).mp h)
    rw [if_neg (fun h => by rw [c] at h; exact absurd ((truth_eq_zero _).mp h) (by decide)), if_neg fits]
    simp only [panicRun, panicSelector]
    rcases h1 : M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
    · simp only [run_error_bind, run_error_map]
    · rcases h2 : M.run .«mstore» (word2 4 17) s1 with e | ⟨s2, r2⟩
      · simp only [h2, run_ok_bind, run_error_bind, run_error_map, ↓reduceIte]
      · rcases h3 : M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
        · simp only [h2, h3, run_ok_bind, run_error_bind, run_error_map, ↓reduceIte]
        · simp only [h2, h3, run_ok_bind, run_pure, run_ok_map, ↓reduceIte, Vals.drop_cons, Vals.drop_nil]
end

end Solidity.SolcValidation.IrSyntax
