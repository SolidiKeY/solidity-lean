import Solidity.SolcValidation.IrPushHelpers
import Solidity.SolcValidation.IrAbiSim

/-!
# Simulation of solc's storage-array push

On any machine and state, the body of solc 0.8.38's
`array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(array, value0)`
(`SolcValidation/IrPushHelpers.lean`) performs exactly this sequence of machine
effects (`push_body`), each step on the state the previous one returned:

1. `sload(array)`, giving the old length `l`;
2. `Panic(0x41)` when `l ≥ 2^64`;
3. `sstore(array, l + 1)`;
4. `sload(array)` again (the index check of `storage_array_index_access`), giving `l'`,
   and `Panic(0x32)` unless `l < l'`;
5. `mstore(0, array)` and `keccak256(0, 32)`, giving the data area `h`;
6. `sload(h + l)` (the old slot content) and `sstore(h + l, value0)`.

A machine whose storage reads return what was stored (the physical storage of
VX4/VY4, not assumed here) therefore stores the value at `keccak(array) + l` and
the length `l + 1` at `array`; that reading, and the relation to the source's
`push`, are G01's and D3's and are not asserted here. The update of the slot is
`update_byte_slice_dynamic32(old, 0, value)`, which is `value` (`slice_zero`).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def pushEnv : FunEnv (pushSigs ++ []) := .group pushSigs pushBodies .nil
abbrev pushE1 : FunEnv ([] ++ (pushSigs ++ [])) := .group [] .nil pushEnv

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- A call of a one-argument copy function (`r := value`) returns its argument's value. -/
theorem copy_call {F G : List FnSig} (E : FunEnv F) (env : FunEnv G) {nm r : String}
    (m : Mem F ⟨nm, ["value"], [r]⟩)
    (hE : E.lookup m = ⟨G, env, .mk [] .nil (.stmt (.assign [⟨r, .there .here⟩] (.var "value" .here)) .nil)⟩)
    {L : List String} (arg : Expr F L 1) (vs : Vals L) (s : σ) (v : Word) (d : Nat)
    (ha : ∀ j, evalExpr M ctx (j + d) E arg vs s = .ok (s, fun _ => v)) (j : Nat) :
    evalExpr M ctx (j + d + 7) E (.call m (.cons arg .nil)) vs s = .ok (s, fun _ => v) := by
  have h1 : evalExpr M ctx (j + d + 5) E arg vs s = .ok (s, fun _ => v) := by
    rw [Nat.add_right_comm]; exact ha (j + 5)
  simp only [evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, h1, run_ok_bind, run_pure, Vals.ofFn, consFn_zero,
    Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [evalBlock, evalItems, evalStmt, evalExpr, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self, Vals.drop_cons, Vals.drop_nil, toFn_single]

/-- `convert_t_uint256_to_t_uint256(x) = cleanup(identity(cleanup(x)))` returns `x`. -/
theorem convert_call (k : Nat) {F : List FnSig} (E : FunEnv F)
    (m : Mem F ⟨"convert_t_uint256_to_t_uint256", ["value"], ["converted"]⟩)
    (hE : E.lookup m = ⟨_, pushEnv, pushConvert⟩) {L : List String} {n : String} (mv : Mem L n) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 40) E (.call m (.cons (.var n mv) .nil)) vs s = .ok (s, fun _ => vs.get mv) := by
  simp only [evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, evalExpr.eq_3, run_ok_bind, run_pure, Vals.ofFn, consFn_zero,
    Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hE, pushConvert, block_empty, items_last M ctx (k + 36),
    assign_of M ctx (k + 36) _ _ _ _ _ _
      (copy_call M ctx _ pushEnv _ rfl _ _ _ _ 15
        (copy_call M ctx _ pushEnv _ rfl _ _ _ _ 8
          (copy_call M ctx _ pushEnv _ rfl _ _ _ _ 1 (fun j => var_gen M ctx _ _ _ _ j))) (k + 14))]
  simp only [Vals.get_here, Vals.set_here, Vals.set_there, Vals.drop_cons, Vals.drop_nil, toFn_single, run_ok_bind]

theorem shl_zero (v : Word) : Solidity.Yul.Pure.eval .«shl» (word2 0 v) = v := by
  have def_ : Solidity.Yul.Pure.eval .«shl» (word2 0 v) =
      if (0 : Word).val ≥ 256 then Solidity.Yul.word 0 else Solidity.Yul.word (v.val <<< (0 : Word).val) := rfl
  have z : (0 : Word).val = 0 := rfl
  rw [def_, z, if_neg (by decide), Nat.shiftLeft_zero, word_self]

/-- A call of `shift_left_dynamic(bits, value)` with `bits = 0` returns `value`. -/
theorem shl_call {F : List FnSig} (E : FunEnv F)
    (m : Mem F ⟨"shift_left_dynamic", ["bits", "value"], ["newValue"]⟩)
    (hE : E.lookup m = ⟨_, pushEnv, pushShiftLeft⟩)
    {L : List String} (e1 e2 : Expr F L 1) (vs : Vals L) (s : σ) (v : Word) (d : Nat)
    (h1 : ∀ j, evalExpr M ctx (j + d) E e1 vs s = .ok (s, fun _ => 0))
    (h2 : ∀ j, evalExpr M ctx (j + d) E e2 vs s = .ok (s, fun _ => v)) (j : Nat) :
    evalExpr M ctx (j + d + 12) E (.call m (.cons e1 (.cons e2 .nil))) vs s = .ok (s, fun _ => v) := by
  have g2 : evalExpr M ctx (j + d + 9) E e2 vs s = .ok (s, fun _ => v) := by
    rw [Nat.add_right_comm]; exact h2 (j + 9)
  have g1 : evalExpr M ctx (j + d + 10) E e1 vs s = .ok (s, fun _ => 0) := by
    rw [Nat.add_right_comm]; exact h1 (j + 10)
  simp only [evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, g1, g2, run_ok_bind, run_pure, Vals.ofFn, consFn_zero,
    consFn_succ, Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [pushShiftLeft, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, Vals.get_here, Vals.get_there,
    run_ok_bind, run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self, Vals.drop_cons, Vals.drop_nil,
    toFn_single, consFn_two, shl_zero]

theorem and_not_max (w : Word) :
    Solidity.Yul.Pure.eval .«and» (word2 w (Solidity.Yul.Pure.eval .«not» (fun _ => 115792089237316195423570985008687907853269984665640564039457584007913129639935))) = 0 := by
  apply Fin.ext
  have hn : Solidity.Yul.Pure.eval .«not» (fun _ => (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Word)) =
      Solidity.Yul.word 0 := rfl
  rw [pure_and, word2_zero, word2_one, hn]
  show (w.val &&& (0 % 2 ^ 256)) % 2 ^ 256 = 0
  rw [Nat.zero_mod, Nat.and_zero]

theorem or_zero_and_max (v : Word) :
    Solidity.Yul.Pure.eval .«or» (word2 0 (Solidity.Yul.Pure.eval .«and» (word2 v 115792089237316195423570985008687907853269984665640564039457584007913129639935))) = v := by
  apply Fin.ext
  rw [pure_or, word2_zero, word2_one, pure_and, word2_zero, word2_one]
  have hm : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Word).val = 2 ^ 256 - 1 := rfl
  have z : (0 : Word).val = 0 := rfl
  rw [hm, z, word_val, word_val, Nat.and_two_pow_sub_one_of_lt_two_pow v.isLt, Nat.mod_eq_of_lt v.isLt,
    Nat.zero_or, Nat.mod_eq_of_lt v.isLt]

theorem mul_zero_8 : Solidity.Yul.Pure.eval .«mul» (word2 0 8) = 0 := rfl

/-- `update_byte_slice_dynamic32(old, 0, v)`: the result is `v` (the whole word is replaced). -/
theorem slice_zero (k : Nat) (old v : Word) (s : σ) :
    evalBlock M ctx (k + 60) pushEnv pushUpdateSlice (.cons old (.cons 0 (.cons v (.cons 0 .nil)))) s =
      .ok (s, .cons 0 (.cons 0 (.cons v (.cons v .nil))), .normal) := by
  rw [pushUpdateSlice, block_empty,
    items_let1 M ctx (k + 57) _ _ _ _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (k + 52)),
    items_let1 M ctx (k + 56) _ _ _ _ _ _
      (shl_call M ctx _ _ rfl _ _ _ _ _ 1 (fun j => by
        simp only [var_gen M ctx _ _ _ _ j, Vals.get_here, Vals.get_there, mul_zero_8]) (lit_gen M ctx _ _ _ _) (k + 43))]
  simp only [Vals.get_here, Vals.get_there]
  rw [items_stmt_normal M ctx (k + 56) _ _ _ _ _ _ _ (assign_of M ctx (k + 55) _ _ _ _ _ _
      (shl_call M ctx _ _ rfl _ _ _ _ _ 1 (fun j => var_gen M ctx _ _ _ _ j) (fun j => var_gen M ctx _ _ _ _ j) (k + 42)))]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, mul_zero_8]
  rw [items_stmt_normal M ctx (k + 55) _ _ _ _ _ _ _ (assign_of M ctx (k + 54) _ _ _ _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 4 (fun j => var_gen M ctx _ _ _ _ (j + 3))
        (op1_gen M ctx _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _)) (k + 46))),
    items_last M ctx (k + 53), assign_of M ctx (k + 53) _ _ _ _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 5 (fun j => var_gen M ctx _ _ _ _ (j + 4))
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _)) (k + 44))]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, and_not_max, or_zero_and_max,
    run_ok_map, Vals.drop_cons, Vals.drop_nil]

theorem consFn_const (a b : Word) : consFn a (fun _ : Fin 1 => b) = word2 a b := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem prepare_body (k : Nat) (v : Word) (s : σ) :
    evalBlock M ctx (k + 4) pushEnv pushPrepareStore (.cons v (.cons 0 .nil)) s = .ok (s, .cons v (.cons v .nil), .normal) := by
  simp only [pushPrepareStore, evalBlock, evalItems, evalStmt, evalExpr, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self]

/-- `update_storage_value_t_uint256_to_t_uint256(slot, 0, v)`: `sload(slot)`, then `sstore(slot, v)`. -/
theorem updateStorage_body (k : Nat) (sl v : Word) (s : σ) :
    evalBlock M ctx (k + 120) pushEnv pushUpdateStorage (.cons sl (.cons 0 (.cons v .nil))) s =
      M.run .«sload» (fun _ => sl) s >>= fun r =>
        (fun r' => (r'.1, .cons sl (.cons 0 (.cons v .nil)), .normal)) <$> M.run .«sstore» (word2 sl v) r.1 := by
  have hp : (FunEnv.group [] Bodies.nil pushEnv).lookup (s := ⟨"prepare_store_t_uint256", ["value"], ["ret"]⟩)
      (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) =
      ⟨_, pushEnv, pushPrepareStore⟩ := rfl
  have hs : (FunEnv.group [] Bodies.nil pushEnv).lookup (s := ⟨"update_byte_slice_dynamic32", ["value", "shiftBytes", "toInsert"], ["result"]⟩)
      (.there (.there (.there (.there (.there (.there (.there .here))))))) = ⟨_, pushEnv, pushUpdateSlice⟩ := rfl
  rw [pushUpdateStorage, block_empty, items_let1 M ctx (k + 117) _ _ _ _ _ _ (convert_call M ctx (k + 77) _ _ rfl _ _ _),
    items_last M ctx (k + 116)]
  simp only [evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, Vals.get_here, Vals.get_there,
    Vals.ofFn, Vals.zeros, Vals.append_cons', Vals.append_nil', consFn_one]
  rw [hp, hs]
  rw [prepare_body M ctx (k + 104)]
  simp only [run_ok_bind, Vals.drop_cons, Vals.drop_nil, toFn_single]
  rcases M.run .«sload» (fun _ => sl) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, consFn_zero, consFn_succ]
    rw [slice_zero M ctx (k + 52)]
    simp only [run_ok_bind, Vals.drop_cons, Vals.drop_nil, toFn_single, consFn_const]
    rcases M.run .«sstore» (word2 sl v) s1 with err | ⟨s2, w2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, run_ok_map, Vals.drop_cons, Vals.drop_nil]

/-- `array_length(value)`: `sload(value)`. -/
theorem length_call (k : Nat) {F : List FnSig} (E : FunEnv F)
    (m : Mem F ⟨"array_length_t_array$_t_uint256_$dyn_storage_ptr", ["value"], ["length"]⟩)
    (hE : E.lookup m = ⟨_, pushEnv, pushLength⟩) {L : List String} {n : String} (mv : Mem L n) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m (.cons (.var n mv) .nil)) vs s =
      (fun r => (r.1, fun _ => r.2 0)) <$> M.run .«sload» (fun _ => vs.get mv) s := by
  simp only [evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, evalExpr.eq_3, run_ok_bind, run_pure, Vals.ofFn, consFn_zero,
    Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [pushLength, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, Vals.get_here, run_ok_bind,
    run_pure, consFn_one]
  rcases M.run .«sload» (fun _ => vs.get mv) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map, assignAll, Vals.set_here, Vals.set_there, ↓reduceIte, Vals.drop_cons,
      Vals.drop_nil, toFn_single]
    rfl

/-- `array_dataslot(ptr)`: `mstore(0, ptr)`, then `keccak256(0, 32)`. -/
theorem dataslot_call (k : Nat) {F : List FnSig} (E : FunEnv F)
    (m : Mem F ⟨"array_dataslot_t_array$_t_uint256_$dyn_storage_ptr", ["ptr"], ["data"]⟩)
    (hE : E.lookup m = ⟨_, pushEnv, pushDataSlot⟩) {L : List String} {n : String} (mv : Mem L n) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 16) E (.call m (.cons (.var n mv) .nil)) vs s =
      (fun r => (r.1, fun _ => r.2 0)) <$>
        (M.run .«mstore» (word2 0 (vs.get mv)) s >>= fun r => M.run .«keccak256» (word2 0 32) r.1) := by
  simp only [evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, evalExpr.eq_3, run_ok_bind, run_pure, Vals.ofFn, consFn_zero,
    Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [pushDataSlot, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, Vals.get_here, run_ok_bind,
    run_pure, consFn_two, assignAll, Vals.set_here, Vals.set_there, ↓reduceIte]
  rcases M.run .«mstore» (word2 0 (vs.get mv)) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, ↓reduceIte]
    rcases M.run .«keccak256» (word2 0 32) s1 with err | ⟨s2, w2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, run_ok_map, ↓reduceIte]
      refine congrArg Except.ok (Prod.ext rfl ?_)
      funext i
      match i with
      | ⟨0, _⟩ => rfl

theorem panic41_block (k : Nat) (s : σ) :
    evalBlock M ctx (k + 10) pushEnv pushPanic41 .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M 0x41 s := by
  simp only [pushPanic41, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure,
    consFn_two, panicRun, panicSelector]
  rcases M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, ↓reduceIte]
    rcases M.run .«mstore» (word2 4 0x41) s1 with e | ⟨s2, r2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, ↓reduceIte]
      rcases M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
      · simp only [run_error_bind, run_error_map]
      · simp only [run_ok_bind, run_ok_map, ↓reduceIte]

theorem panic32_block (k : Nat) (s : σ) :
    evalBlock M ctx (k + 10) pushEnv pushPanic32 .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M 0x32 s := by
  simp only [pushPanic32, evalBlock, evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure,
    consFn_two, panicRun, panicSelector]
  rcases M.run .«mstore» (word2 0 _) s with e | ⟨s1, r1⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, ↓reduceIte]
    rcases M.run .«mstore» (word2 4 0x32) s1 with e | ⟨s2, r2⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, ↓reduceIte]
      rcases M.run .«revert» (word2 0 36) s2 with e | ⟨s3, r3⟩
      · simp only [run_error_bind, run_error_map]
      · simp only [run_ok_bind, run_ok_map, ↓reduceIte]

/-- `if cond { p() }` for a panic helper `p` whose body runs `panicRun M code`. -/
theorem if_panic_gen (k : Nat) {F G : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (env : FunEnv G)
    {nm : String} (body : Block G ⟨true, false⟩ ([] ++ [])) (code : Word)
    (hb : ∀ j s, evalBlock M ctx (j + 10) env body .nil s = (fun s => (s, .nil, .normal)) <$> panicRun M code s)
    (cond : Expr F L 1) (m : Mem ([] ++ F) ⟨nm, [], []⟩)
    (hE : (FunEnv.group [] Bodies.nil E).lookup m = ⟨G, env, body⟩)
    (vs : Vals L) (s : σ) (v : Word) (hc : evalExpr M ctx (k + 16) E cond vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 17) E (.if_ cond (.mk [] .nil (.stmt (.discard (.call m .nil)) .nil))) vs s =
      (fun s => (s, vs, .normal)) <$> panicIf M (v != 0) code s := by
  rw [if_of M ctx (k + 16) E _ _ vs s v hc]
  by_cases z : v = 0
  · simp only [z, ↓reduceIte, panicIf, bne_self_eq_false, Bool.false_eq_true, run_ok_map]
  · have nz : (v != 0) = true := bne_iff_ne.mpr z
    simp only [z, ↓reduceIte, panicIf, nz]
    rw [block_empty, items_last M ctx (k + 13)]
    simp only [evalStmt, evalExpr, evalArgs, run_ok_bind, Vals.ofFn, Vals.zeros, Vals.append_nil']
    rw [hE]
    dsimp only
    rw [hb (k + 2)]
    rcases panicRun M code s with e | s'
    · simp only [run_error_map, run_error_bind]
    · simp only [run_ok_map, run_ok_bind, run_pure, Vals.drop_nil]

/-- A `let x := e` whose initializer runs a machine effect. -/
theorem items_let1_eff (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F) {x : String}
    {α : Type} (e : Expr F L 1) (rest : Items F c (x :: L) g) (vs : Vals L) (s : σ) (X : Run σ (σ × α)) (f : α → Word)
    (h : evalExpr M ctx k E e vs s = (fun r => (r.1, fun _ => f r.2)) <$> X) :
    evalItems M ctx (k + 2) E (.let_ [x] (some e) rest) vs s =
      X >>= fun r => (fun r' => (r'.1, Vals.drop [x] r'.2.1, r'.2.2)) <$> evalItems M ctx (k + 1) E rest (.cons (f r.2) vs) r.1 := by
  simp only [evalItems, evalInit, h]
  rcases X with err | ⟨s1, a⟩
  · simp only [run_error_map, run_error_bind]
  · simp only [run_ok_map, run_ok_bind, run_pure, Vals.ofFn, Vals.append_cons', Vals.append_nil']
    rcases evalItems M ctx (k + 1) E rest (.cons (f a) vs) s1 with err | ⟨s2, out, fl⟩
    · simp only [run_error_bind, run_error_map]
    · simp only [run_ok_bind, run_ok_map]

theorem iszero_lt_bne (i l : Word) :
    (Solidity.Yul.Pure.eval .«iszero» (fun _ => Solidity.Yul.Pure.eval .«lt» (word2 i l)) != 0) = !decide (i.val < l.val) := by
  rw [pure_iszero, pure_lt, word2_zero, word2_one]
  cases decide (i.val < l.val) <;> rfl

theorem add_mul_one (h i : Word) :
    Solidity.Yul.Pure.eval .«add» (word2 h (Solidity.Yul.Pure.eval .«mul» (word2 i 1))) =
      Solidity.Yul.word (h.val + i.val) := by
  rw [pure_add, word2_zero, word2_one, pure_mul, word2_zero, word2_one]
  have one : (1 : Word).val = 1 := rfl
  rw [one, Nat.mul_one, word_self]

/-- `storage_array_index_access(array, index)`: `sload(array)` (the length `l`), `Panic(0x32)`
unless `index < l`, then the data area `keccak256` of `array` (after `mstore(0, array)`);
returns `slot = area + index`, `offset = 0`. -/
theorem index_body (k : Nat) (a i : Word) (s : σ) :
    evalBlock M ctx (k + 120) pushEnv pushIndexAccess (.cons a (.cons i (.cons 0 (.cons 0 .nil)))) s =
      M.run .«sload» (fun _ => a) s >>= fun r1 =>
      panicIf M (!decide (i.val < (r1.2 0).val)) 0x32 r1.1 >>= fun s2 =>
      M.run .«mstore» (word2 0 a) s2 >>= fun r3 =>
      (fun r4 => (r4.1, .cons a (.cons i (.cons (Solidity.Yul.word ((r4.2 0).val + i.val)) (.cons 0 .nil))), .normal)) <$>
        M.run .«keccak256» (word2 0 32) r3.1 := by
  rw [pushIndexAccess, block_empty, items_let1_eff M ctx (k + 117) _ _ _ _ _ _ (fun w : Fin 1 → Word => w 0)
    (length_call M ctx (k + 105) _ _ rfl _ _ _)]
  simp only [Vals.get_here]
  rcases M.run .«sload» (fun _ => a) s with err | ⟨s1, w1⟩
  · simp only [run_error_bind]
  simp only [run_ok_bind]
  rw [items_stmt_map M ctx (k + 117) _ _ _ _ _ _ _
    (if_panic_gen M ctx (k + 100) _ pushEnv pushPanic32 0x32 (panic32_block M ctx) _ _ rfl _ _ _
      (op1_gen M ctx _ _ _ _ _ _ 5
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (var_gen M ctx _ _ _ _)) (k + 108)))]
  simp only [Vals.get_here, Vals.get_there, iszero_lt_bne]
  rcases panicIf M (!decide (i.val < (w1 0).val)) 0x32 s1 with err | s2
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rw [items_let1_eff M ctx (k + 115) _ _ _ _ _ _ (fun w : Fin 1 → Word => w 0) (dataslot_call M ctx (k + 99) _ _ rfl _ _ _)]
  simp only [Vals.get_here, Vals.get_there]
  rcases M.run .«mstore» (word2 0 a) s2 with err | ⟨s3, w3⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rcases M.run .«keccak256» (word2 0 32) s3 with err | ⟨s4, w4⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind, run_ok_map]
  rw [items_stmt_normal M ctx (k + 115) _ _ _ _ _ _ _ (assign_of M ctx (k + 114) _ _ _ _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 5 (fun j => var_gen M ctx _ _ _ _ (j + 4))
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _)) (k + 105))),
    items_last M ctx (k + 113), assign_of M ctx (k + 113) _ _ _ _ _ _ (lit_gen M ctx _ _ _ _ (k + 112))]
  simp only [Vals.get_here, Vals.get_there, Vals.set_here, Vals.set_there, add_mul_one, run_ok_map,
    Vals.drop_cons, Vals.drop_nil]

theorem toFn_two0 {x y : String} (a b : Word) (h : 0 < 2) :
    (Vals.cons (x := x) a (Vals.cons (x := y) b Vals.nil)).toFn ⟨0, h⟩ = a := rfl
theorem toFn_two1 {x y : String} (a b : Word) (h : 0 < 1) :
    (Vals.cons (x := x) a (Vals.cons (x := y) b Vals.nil)).toFn (Fin.succ ⟨0, h⟩) = b := rfl

theorem sload_expr (k : Nat) {F : List FnSig} (E : FunEnv F) {L : List String} {n : String} (mv : Mem L n)
    (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 3) E (.op (.evm .«sload») (.cons (.var n mv) .nil)) vs s =
      (fun r => (r.1, fun _ => (fun w : Fin 1 → Word => w 0) r.2)) <$> M.run .«sload» (fun _ => vs.get mv) s := by
  simp only [evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, consFn_one]
  rcases M.run .«sload» (fun _ => vs.get mv) s with err | ⟨s1, w⟩
  · simp only [run_error_map]
  · simp only [run_ok_map]
    refine congrArg Except.ok (Prod.ext rfl ?_)
    funext i
    match i with
    | ⟨0, _⟩ => rfl

theorem sstore_stmt (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) {n : String}
    (ma : Mem L n) (e2 : Expr F L 1) (vs : Vals L) (s : σ) (v : Word)
    (h2 : evalExpr M ctx (k + 4) E e2 vs s = .ok (s, fun _ => v)) :
    evalStmt (c := c) M ctx (k + 8) E (.discard (.op (.evm .«sstore») (.cons (.var n ma) (.cons e2 .nil)))) vs s =
      (fun s => (s, vs, .normal)) <$> ((·.1) <$> M.run .«sstore» (word2 (vs.get ma) v) s) := by
  simp only [evalStmt, evalExpr.eq_4, evalArgs.eq_3, evalArgs.eq_2, h2, evalExpr.eq_3, evalOp, run_ok_bind, run_pure,
    consFn_two]
  rcases M.run .«sstore» (word2 (vs.get ma) v) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map]

theorem lt_2_64_bne (l : Word) :
    (Solidity.Yul.Pure.eval .«iszero» (fun _ => Solidity.Yul.Pure.eval .«lt» (word2 l 18446744073709551616)) != 0) =
      !decide (l.val < 2 ^ 64) := by
  rw [iszero_lt_bne]
  rfl

/-- The body of `array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(array, value0)`
on any machine: the effect sequence of the module docstring, each step from the state the
previous one returned. -/
theorem push_body (k : Nat) (a v : Word) (s : σ) :
    evalBlock M ctx (k + 300) pushEnv pushPush (.cons a (.cons v .nil)) s =
      M.run .«sload» (fun _ => a) s >>= fun r1 =>
      panicIf M (!decide ((r1.2 0).val < 2 ^ 64)) 0x41 r1.1 >>= fun s2 =>
      M.run .«sstore» (word2 a (Solidity.Yul.word ((r1.2 0).val + 1))) s2 >>= fun r3 =>
      M.run .«sload» (fun _ => a) r3.1 >>= fun r4 =>
      panicIf M (!decide ((r1.2 0).val < (r4.2 0).val)) 0x32 r4.1 >>= fun s5 =>
      M.run .«mstore» (word2 0 a) s5 >>= fun r6 =>
      M.run .«keccak256» (word2 0 32) r6.1 >>= fun r7 =>
      M.run .«sload» (fun _ => Solidity.Yul.word ((r7.2 0).val + (r1.2 0).val)) r7.1 >>= fun r8 =>
      (fun r9 => (r9.1, .cons a (.cons v .nil), .normal)) <$>
        M.run .«sstore» (word2 (Solidity.Yul.word ((r7.2 0).val + (r1.2 0).val)) v) r8.1 := by
  rw [pushPush, block_empty, items_let1_eff M ctx (k + 297) _ _ _ _ _ _ (fun w : Fin 1 → Word => w 0)
    (sload_expr M ctx (k + 294) _ _ _ _)]
  simp only [Vals.get_here]
  rcases M.run .«sload» (fun _ => a) s with err | ⟨s1, w1⟩
  · simp only [run_error_bind]
  simp only [run_ok_bind]
  rw [items_stmt_map M ctx (k + 297) _ _ _ _ _ _ _
    (if_panic_gen M ctx (k + 280) _ pushEnv pushPanic41 0x41 (panic41_block M ctx) _ _ rfl _ _ _
      (op1_gen M ctx _ _ _ _ _ _ 5
        (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _)) (k + 288)))]
  simp only [Vals.get_here, lt_2_64_bne]
  rcases panicIf M (!decide ((w1 0).val < 2 ^ 64)) 0x41 s1 with err | s2
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rw [items_stmt_map M ctx (k + 296) _ _ _ _ _ _ _
    (sstore_stmt M ctx (k + 288) _ _ _ _ _ _
      (op2_gen M ctx _ _ _ _ _ _ _ _ 1 (var_gen M ctx _ _ _ _) (lit_gen M ctx _ _ _ _) (k + 287)))]
  simp only [Vals.get_here, Vals.get_there, pure_add, word2_zero, word2_one, show (1 : Word).val = 1 from rfl]
  rcases M.run .«sstore» (word2 a (Solidity.Yul.word ((w1 0).val + 1))) s2 with err | ⟨s3, w3⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind, run_ok_map]
  have hi : (FunEnv.group [] Bodies.nil pushEnv).lookup
      (s := ⟨"storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr", ["array", "index"], ["slot", "offset"]⟩)
      (.there (.there (.there (.there (.there .here))))) = ⟨_, pushEnv, pushIndexAccess⟩ := rfl
  have hu : (FunEnv.group [] Bodies.nil pushEnv).lookup
      (s := ⟨"update_storage_value_t_uint256_to_t_uint256", ["slot", "offset", "value_0"], []⟩)
      (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) =
      ⟨_, pushEnv, pushUpdateStorage⟩ := rfl
  simp only [evalItems, evalInit, evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, evalExpr.eq_3, run_ok_bind, run_pure,
    Vals.get_here, Vals.get_there, Vals.ofFn, consFn_zero, consFn_succ, Vals.zeros, Vals.append_cons', Vals.append_nil']
  rw [hi]
  dsimp only
  rw [index_body M ctx (k + 173)]
  rcases M.run .«sload» (fun _ => a) s3 with err | ⟨s4, w4⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rcases panicIf M (!decide ((w1 0).val < (w4 0).val)) 0x32 s4 with err | s5
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rcases M.run .«mstore» (word2 0 a) s5 with err | ⟨s6, w6⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rcases M.run .«keccak256» (word2 0 32) s6 with err | ⟨s7, w7⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind, run_ok_map, Vals.drop_cons, Vals.drop_nil, toFn_two0, toFn_two1, Vals.append_cons',
    Vals.append_nil']
  simp only [evalStmt, evalExpr.eq_5, evalArgs.eq_3, evalArgs.eq_2, evalExpr.eq_3, run_ok_bind, run_pure,
    Vals.get_here, Vals.get_there, Vals.ofFn, consFn_zero, consFn_succ, Vals.zeros]
  rw [hu]
  simp only [Vals.append_cons', Vals.append_nil']
  rw [updateStorage_body M ctx (k + 172)]
  rcases M.run .«sload» (fun _ => Solidity.Yul.word ((w7 0).val + (w1 0).val)) s7 with err | ⟨s8, w8⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind]
  rcases M.run .«sstore» (word2 (Solidity.Yul.word ((w7 0).val + (w1 0).val)) v) s8 with err | ⟨s9, w9⟩
  · simp only [run_error_bind, run_error_map]
  simp only [run_ok_bind, run_ok_map, ↓reduceIte, Vals.drop_cons, Vals.drop_nil]

end

end Solidity.SolcValidation.IrSyntax
