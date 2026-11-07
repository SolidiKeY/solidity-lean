import Solidity.SolcValidation.IrAbiHelpers
import Solidity.SolcValidation.IrExpSim

/-!
# Simulation of solc's `abi_decode_tuple_t_uint256`

On any machine and state, the body of solc 0.8.38's decoder of one `uint256`
from calldata (`SolcValidation/IrAbiHelpers.lean`), entered with
`(headStart, dataEnd)`, does one of two things: when `slt(sub(dataEnd, headStart), 32)`
holds, its result factors through `revert(0, 0)` from the entry state (exactly that
fault on a machine whose `revert` halts: `decodeTuple_short_halts`); otherwise its only machine
effect is `calldataload(headStart)`, and it returns that word. The validator
`validator_revert_t_uint256` never fires for a `uint256` (its cleanup is the
identity), which `validator_body` proves.

What a calldata word means (the ABI relation to source arguments) is G01's and
is not asserted here.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def abiEnv : FunEnv (abiSigs ++ []) := .group abiSigs abiBodies .nil
abbrev abiE1 : FunEnv ([] ++ (abiSigs ++ [])) := .group [] .nil abiEnv

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- A call of any cleanup closure (`cleaned := value`) on a variable returns its value. -/
theorem cleanup_call_any (k : Nat) {F G : List FnSig} (E : FunEnv F) (env : FunEnv G)
    (m : Mem F ⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩)
    (hE : E.lookup m = ⟨G, env, .mk [] .nil (.stmt (.assign [⟨"cleaned", .there .here⟩] (.var "value" .here)) .nil)⟩)
    {L : List String} {n : String} (mv : Mem L n) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 7) E (.call m (.cons (.var n mv) .nil)) vs s = .ok (s, fun _ => vs.get mv) := by
  simp only [evalExpr, evalArgs, run_ok_bind, run_pure, Vals.ofFn, consFn_zero, Vals.zeros,
    Vals.append_cons', Vals.append_nil']
  rw [hE]
  simp only [evalBlock, evalItems, evalStmt, evalExpr, Vals.get_here, run_ok_bind,
    run_pure, assignAll, Vals.set_there, Vals.set_here, ite_self, Vals.drop_cons, Vals.drop_nil, toFn_single]

theorem iszero_eq_self (v : Word) :
    Solidity.Yul.Pure.eval .«iszero» (fun _ => Solidity.Yul.Pure.eval .«eq» (word2 v v)) = 0 := by
  rw [pure_iszero, pure_eq, word2_zero, word2_one, beq_self_eq_true]
  rfl

/-- `validator_revert_t_uint256(value)`: no effect. -/
theorem validator_body (k : Nat) (v : Word) (s : σ) :
    evalBlock M ctx (k + 20) abiEnv abiValidator (.cons v .nil) s = .ok (s, .cons v .nil, .normal) := by
  rw [abiValidator, block_empty, items_last M ctx (k + 17),
    if_of_eq M ctx (k + 17) _ _ _ _ _ _
      (op1_gen M ctx _ _ _ _ _ _ 11
        (op2_gen M ctx _ _ _ _ _ _ _ _ 7 (fun j => var_gen M ctx _ _ _ _ (j + 6))
          (fun j => cleanup_call_any M ctx j _ abiEnv _ rfl _ _ _)) (k + 3)) _]
  simp only [Vals.get_here]
  exact iszero_eq_self v

/-- `abi_decode_t_uint256(offset, end)`: `calldataload(offset)`, returned. -/
theorem decodeU256_body (k : Nat) (o e : Word) (s : σ) :
    evalBlock M ctx (k + 40) abiEnv abiDecodeU256 (.cons o (.cons e (.cons 0 .nil))) s =
      (fun r => (r.1, .cons o (.cons e (.cons (r.2 0) .nil)), .normal)) <$> M.run .«calldataload» (fun _ => o) s := by
  have hl : abiE1.lookup (s := ⟨"validator_revert_t_uint256", ["value"], []⟩) (.there (.there .here)) =
      ⟨_, abiEnv, abiValidator⟩ := rfl
  rw [abiDecodeU256, block_empty]
  simp only [evalItems, evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, Vals.get_here, consFn_one]
  rcases M.run .«calldataload» (fun _ => o) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map, assignAll, Vals.set_here, Vals.set_there, ↓reduceIte,
      Vals.get_here, Vals.get_there, Vals.ofFn, Vals.zeros, Vals.append_nil', Vals.append_cons']
    rw [hl, validator_body M ctx (k + 15)]
    rfl

/-- A call of `revert_error_…()`: `revert(0, 0)` on the machine. -/
theorem abi_revert_call (k : Nat) {F : List FnSig} (E : FunEnv F)
    (m : Mem F ⟨"revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b", [], []⟩)
    (hE : E.lookup m = ⟨_, abiEnv, abiRevert⟩) {L : List String} (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 12) E (.call m .nil) vs s =
      (fun r => (r.1, fun i => i.elim0)) <$> M.run .«revert» (word2 0 0) s := by
  simp only [evalExpr, evalArgs, run_ok_bind, Vals.ofFn, Vals.zeros, Vals.append_nil']
  rw [hE, abiRevert, block_empty, items_last M ctx (k + 8)]
  simp only [evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, consFn_two]
  rcases M.run .«revert» (word2 0 0) s with err | ⟨s1, w⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map, Vals.drop_nil, toFn_nil]

theorem word2_mk0 (a b : Word) (h : 0 < 2) : word2 a b ⟨0, h⟩ = a := rfl
theorem word2_succ0 (a b : Word) (h : 0 < 1) : word2 a b (Fin.succ ⟨0, h⟩) = b := rfl

theorem slt_32 (a : Word) :
    Solidity.Yul.Pure.eval .«slt» (word2 a 32) = Solidity.Yul.truth (decide (Solidity.Yul.signed a < 32)) := rfl

theorem block_stmt (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} (E : FunEnv F) (b : Block F c L)
    (vs : Vals L) (s : σ) : evalStmt M ctx (k + 1) E (.block b) vs s = evalBlock M ctx k E b vs s := rfl

theorem items_let1 (k : Nat) {F : List FnSig} {c : Ctl} {L : List String} {g : Nat} (E : FunEnv F) {x : String}
    (e : Expr F L 1) (rest : Items F c (x :: L) g) (vs : Vals L) (s : σ) (v : Word)
    (h : evalExpr M ctx k E e vs s = .ok (s, fun _ => v)) :
    evalItems M ctx (k + 2) E (.let_ [x] (some e) rest) vs s =
      (fun r => (r.1, Vals.drop [x] r.2.1, r.2.2)) <$> evalItems M ctx (k + 1) E rest (.cons v vs) s := by
  simp only [evalItems, evalInit, h, run_ok_bind, run_pure, Vals.ofFn, Vals.append_cons', Vals.append_nil']
  rcases evalItems M ctx (k + 1) E rest (.cons v vs) s with err | ⟨s1, out, fl⟩
  · simp only [run_error_bind, run_error_map]
  · simp only [run_ok_bind, run_ok_map]

/-- `abi_decode_tuple_t_uint256(headStart, dataEnd)`'s body, from its entry values. -/
theorem decodeTuple_body (k : Nat) (h d : Word) (s : σ) :
    let short := decide (Solidity.Yul.signed (Solidity.Yul.Pure.eval .«sub» (word2 d h)) < 32)
    (short = true → ∃ cont, evalBlock M ctx (k + 80) abiEnv abiDecodeTuple (.cons h (.cons d (.cons 0 .nil))) s =
      M.run .«revert» (word2 0 0) s >>= cont) ∧
    (short = false → evalBlock M ctx (k + 80) abiEnv abiDecodeTuple (.cons h (.cons d (.cons 0 .nil))) s =
      (fun r => (r.1, .cons h (.cons d (.cons (r.2 0) .nil)), .normal)) <$> M.run .«calldataload» (fun _ => h) s) := by
  intro short
  have hc := op2_gen M ctx abiE1 .«slt» _ _
    (L := ["headStart", "dataEnd", "value0"]) (.cons h (.cons d (.cons (0 : Word) .nil))) s _ _ 5
    (op2_gen M ctx _ .«sub» _ _ _ _ _ _ 1 (var_gen M ctx _ (n := "dataEnd") (.there .here) _ _)
      (var_gen M ctx _ (n := "headStart") .here _ _))
    (fun j => lit_gen M ctx _ ⟨.num 32, 32, rfl⟩ _ _ (j + 4)) (k + 68)
  simp only [Vals.get_here, Vals.get_there, slt_32] at hc
  rw [abiDecodeTuple, block_empty]
  constructor
  · intro yes
    simp only [evalItems]
    rw [if_of_ne M ctx (k + 77) _ _ _ _ _ _ hc _]
    · rw [block_empty, items_last M ctx (k + 74)]
      simp only [evalStmt]
      rw [abi_revert_call M ctx (k + 62) _ _ _]
      · rcases M.run .«revert» (word2 0 0) s with err | ⟨s1, w⟩
        · exact ⟨fun _ => .error err, rfl⟩
        · simp only [run_ok_map, run_ok_bind, run_pure, ↓reduceIte]
          exact ⟨fun _ => _, rfl⟩
      · rfl
    · intro z
      exact absurd ((truth_eq_zero _).mp z) (fun hf => Bool.noConfusion (yes.symm.trans hf))
  · intro no
    rw [items_stmt_normal M ctx (k + 78) _ _ _ _ _ _ _
      (if_of_eq M ctx (k + 77) _ _ _ _ _ _ hc ((truth_eq_zero _).mpr no)),
      items_last M ctx (k + 76), block_stmt, block_empty,
      items_let1 M ctx (k + 73) _ _ _ _ _ _ (lit_gen M ctx _ _ _ _ (k + 72)), items_last M ctx (k + 72)]
    have hl : (FunEnv.group [] .nil abiE1).lookup (s := ⟨"abi_decode_t_uint256", ["offset", "end"], ["value"]⟩)
        (.there (.there (.there .here))) = ⟨_, abiEnv, abiDecodeU256⟩ := rfl
    simp only [evalStmt, evalExpr, evalArgs, evalOp, run_ok_bind, run_pure, Vals.get_here, Vals.get_there,
      consFn_two, pure_add, word2_zero, word2_one]
    rw [hl]
    simp only [Vals.ofFn, Vals.zeros, Vals.append_cons', Vals.append_nil', word2_mk0, word2_succ0]
    have h0 : Solidity.Yul.word (h.val + (0 : Word).val) = h := by
      rw [show (0 : Word).val = 0 from rfl, Nat.add_zero, word_self]
    rw [h0, decodeU256_body M ctx (k + 31)]
    rcases M.run .«calldataload» (fun _ => h) s with err | ⟨s1, w⟩
    · simp only [run_error_map, run_error_bind]
    · simp only [run_ok_map, run_ok_bind, Vals.drop_cons, Vals.drop_nil, toFn_single, assignAll,
        Vals.set_here, Vals.set_there]

/-- On a machine whose `revert` halts, short calldata ends exactly with the fault of
`revert(0, 0)` run from the entry state. -/
theorem decodeTuple_short_halts (k : Nat) (h d : Word) (s : σ) (hr : RevertHalts M)
    (short : decide (Solidity.Yul.signed (Solidity.Yul.Pure.eval .«sub» (word2 d h)) < 32) = true) :
    ∃ e, M.run .«revert» (word2 0 0) s = .error e ∧
      evalBlock M ctx (k + 80) abiEnv abiDecodeTuple (.cons h (.cons d (.cons 0 .nil))) s = .error e := by
  obtain ⟨cont, hc⟩ := (decodeTuple_body M ctx k h d s).1 short
  obtain ⟨s', hs⟩ := hr (word2 0 0) s
  exact ⟨_, hs, by rw [hc, hs]; rfl⟩

end

end Solidity.SolcValidation.IrSyntax
