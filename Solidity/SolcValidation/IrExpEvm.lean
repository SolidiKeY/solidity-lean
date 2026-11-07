import Solidity.Evm.Exp
import Solidity.SolcValidation.IrCensusTransfer

/-!
# solc's imported `checked_exp` against `Evm/Exp.lean` and the EVM `EXP`

Three exponentiations are related here, all on words below `2^256`:

- `expUnsigned` (`SolcValidation/IrExpModel.lean`), the arithmetic model of solc's
  `checked_exp_unsigned`, which the imported IR helper runs as
  (`checked_exp_body`, and `census_checked_exp_body` for the parsed Census program);
- this compiler's checked `**` code (`uTail .pow`, `Evm/Layout.lean`), whose run on
  the word-cell machine `exp_tail` (`Evm/Exp.lean`) gives: `a ^ b`, or a revert
  exactly when `a ^ b ≥ 2^256`;
- the value of the Yul `exp` builtin (the EVM `EXP` instruction), the owner's
  `Pure.eval .exp` (`powWord`, `a ^ b mod 2^256`, `Yul/Words.lean`); solc's helper
  does not call it, so this compares its result with what an unchecked `exp` gives.

`expUnsigned_evm`: the model succeeds with `v` exactly when the compiled code
returns `v`, and fails exactly when it reverts. `expUnsigned_opcode`: when the
model succeeds its value is the `EXP` instruction's (no wrap happened); it fails
exactly when `EXP` would wrap. `checked_exp_vs_evm`/`census_checked_exp_vs_evm`:
on the same operands the imported IR helper (the extracted group, and the parsed
Census program's own body) returns the compiled code's value with no machine
effect when that code returns, and runs solc's panic sequence (`Panic(0x11)`)
when it reverts (`checked_exp_vs_evm_halts`: on a machine whose `revert` halts,
the helper then ends with exactly the panic's fault). The two machines are
different models (the IR runs on any `Machine`, `Evm/Exp.lean` on this compiler's
word-cell machine, and `uTail .pow` is this compiler's code, not solc's): what is
related is the outcome on equal operands, not their states, and revert payloads
(solc's `Panic(0x11)` against this compiler's revert) are not compared. `Evm/Exp.lean` is not edited.
All statements are over abstract words; no large numeral is reduced.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

theorem lt_W_iff (n : Nat) : n < Solidity.Evm.W ↔ n < 2 ^ 256 := Iff.rfl

/-- The model and the compiled checked `**` code agree: the model's value is
the code's result, and the model fails exactly when the code reverts. -/
theorem expUnsigned_evm (m : Solidity.Evm.Machine) (st : List Solidity.Evm.Word) (a b : Nat)
    (haW : a < 2 ^ 256) (hbW : b < 2 ^ 256) :
    (∀ v, expUnsigned a b = some v → ∃ hv : v < Solidity.Evm.W,
      Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val ⟨v, hv⟩ :: st } 0) ∧
    (expUnsigned a b = none →
      Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[b] :: w[a] :: st } = .revert) := by
  have ht : Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[b] :: w[a] :: st } =
      if _ : a ^ b < Solidity.Evm.W then .ok { m with stack := w[a ^ b] :: st } 0 else .revert :=
    Solidity.Evm.exp_tail m st haW hbW
  rw [expUnsigned_correct a b haW]
  constructor
  · intro v hv
    by_cases h : a ^ b < 2 ^ 256
    · rw [if_pos h, Option.some.injEq] at hv
      subst hv
      exact ⟨h, by rw [ht, dif_pos (show _ < Solidity.Evm.W from h)]⟩
    · rw [if_neg h] at hv
      exact Option.noConfusion hv
  · intro hn
    by_cases h : a ^ b < 2 ^ 256
    · rw [if_pos h] at hn
      exact Option.noConfusion hn
    · rw [ht, dif_neg (show ¬ _ < Solidity.Evm.W from h)]

/-- When the model succeeds, its value is the EVM `EXP` instruction's on the same
words; it fails exactly when `EXP` wraps (its value is then not `a ^ b`). -/
theorem expUnsigned_opcode (x y : Word) :
    (∀ v, expUnsigned x.val y.val = some v →
      Solidity.Yul.Pure.eval .«exp» (word2 x y) = Solidity.Yul.word v) ∧
    (expUnsigned x.val y.val = none ↔
      (Solidity.Yul.Pure.eval .«exp» (word2 x y)).val ≠ x.val ^ y.val) := by
  have hval : (Solidity.Yul.Pure.eval .«exp» (word2 x y)).val = x.val ^ y.val % 2 ^ 256 :=
    Solidity.Yul.powWord_correct x y.val
  rw [expUnsigned_correct x.val y.val x.isLt]
  constructor
  · intro v hv
    by_cases h : x.val ^ y.val < 2 ^ 256
    · rw [if_pos h, Option.some.injEq] at hv
      subst hv
      apply Fin.ext
      rw [hval, word_val]
    · rw [if_neg h] at hv
      exact Option.noConfusion hv
  · rw [hval]
    by_cases h : x.val ^ y.val < 2 ^ 256
    · rw [if_pos h, Nat.mod_eq_of_lt h]
      exact ⟨fun hn => Option.noConfusion hn, fun hne => absurd rfl hne⟩
    · rw [if_neg h]
      refine ⟨fun _ heq => h ?_, fun _ => rfl⟩
      rw [← heq]
      exact Nat.mod_lt _ (Nat.pow_pos (by decide))

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- The imported `checked_exp_t_uint256_t_uint256` body and the compiled checked
`**` code agree on equal operands: a result of the compiled code is the helper's
return value (with no machine effect), and a revert of the compiled code is the
helper running solc's `Panic(0x11)` sequence first. -/
theorem checked_exp_vs_evm (j : Nat) (x y : Word) (s : σ)
    (m : Solidity.Evm.Machine) (st : List Solidity.Evm.Word) :
    (∀ (v : Nat) (hv : v < Solidity.Evm.W),
      Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[y.val] :: w[x.val] :: st } =
        .ok { m with stack := .val ⟨v, hv⟩ :: st } 0 →
      evalBlock M ctx (j + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word v) .nil)), .normal)) ∧
    (Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[y.val] :: w[x.val] :: st } = .revert →
      ∃ cont, evalBlock M ctx (j + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M 0x11 s >>= cont) := by
  have ht := Solidity.Evm.exp_tail m st (a := x.val) (b := y.val) x.isLt y.isLt
  have body := checked_exp_body M ctx j x y s
  constructor
  · intro v hv hrun
    by_cases h : x.val ^ y.val < 2 ^ 256
    · rw [ht, dif_pos (show _ < Solidity.Evm.W from h)] at hrun
      have hv' : x.val ^ y.val = v := by
        cases hrun
        rfl
      rw [← hv']
      exact body.1 h
    · rw [ht, dif_neg (show ¬ _ < Solidity.Evm.W from h)] at hrun
      exact Solidity.Evm.Out.noConfusion hrun
  · intro hrun
    by_cases h : x.val ^ y.val < 2 ^ 256
    · rw [ht, dif_pos (show _ < Solidity.Evm.W from h)] at hrun
      exact Solidity.Evm.Out.noConfusion hrun
    · exact body.2 h

/-- Under `RevertHalts M`, a revert of the compiled code is the helper ending with
exactly the fault of solc's panic sequence, from the entry state. -/
theorem checked_exp_vs_evm_halts (j : Nat) (x y : Word) (s : σ) (h : RevertHalts M)
    (m : Solidity.Evm.Machine) (st : List Solidity.Evm.Word)
    (hrun : Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[y.val] :: w[x.val] :: st } =
      .revert) :
    ∃ e, panicRun M 0x11 s = .error e ∧
      evalBlock M ctx (j + 420) expEnv expExpU256 (.cons x (.cons y (.cons 0 .nil))) s = .error e := by
  have ht := Solidity.Evm.exp_tail m st (a := x.val) (b := y.val) x.isLt y.isLt
  by_cases hfit : x.val ^ y.val < 2 ^ 256
  · rw [ht, dif_pos (show _ < Solidity.Evm.W from hfit)] at hrun
    exact Solidity.Evm.Out.noConfusion hrun
  · exact checked_exp_overflow_halts M ctx j x y s h hfit

/-- The same for the certified Census tree's own `checked_exp_t_uint256_t_uint256`. -/
theorem census_checked_exp_vs_evm (j : Nat) (x y : Word) (s : σ)
    (m : Solidity.Evm.Machine) (st : List Solidity.Evm.Word) :
    (∀ (v : Nat) (hv : v < Solidity.Evm.W),
      Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[y.val] :: w[x.val] :: st } =
        .ok { m with stack := .val ⟨v, hv⟩ :: st } 0 →
      evalBlock M ctx (j + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word v) .nil)), .normal)) ∧
    (Solidity.Evm.run (Solidity.Evm.uTail .pow) { m with stack := w[y.val] :: w[x.val] :: st } = .revert →
      ∃ cont, evalBlock M ctx (j + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M 0x11 s >>= cont) := by
  simp only [cd_exp_eq]
  exact checked_exp_vs_evm M ctx j x y s m st

end

end Solidity.SolcValidation.IrSyntax
