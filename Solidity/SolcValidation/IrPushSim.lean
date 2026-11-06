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
    have := ha (j + 5); rw [Nat.add_right_comm] at this; exact this
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
    have := h2 (j + 9); rw [Nat.add_right_comm] at this; exact this
  have g1 : evalExpr M ctx (j + d + 10) E e1 vs s = .ok (s, fun _ => 0) := by
    have := h1 (j + 10); rw [Nat.add_right_comm] at this; exact this
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

end

end Solidity.SolcValidation.IrSyntax
