# BalancesFit: every account balance stays below 2^256

Batch `move6-20261106`, task `balances-fit`. Branch
`cloud/move6-20261106/balances-fit`, based on the VY5 lane
(`cloud/moved2-20261105/vy5-composition`), which brings Nat-valued account
balances (`Source/Monetary.lean`). No VY5 typing file (`Source/Types.lean`,
`Typing.lean`, `WellTyped.lean`) and no existing declaration was changed; the
work is three new modules.

## Why

`BALANCE` of an instance evaluates `Monetary.wordView balance`, i.e.
`balance % 2^256` (`Source/Eval.lean`, the `.balance` arm). That is the exact
balance only if the balance fits in 256 bits. The invariant is VY5's
`ExecState.BalancesFit` (`Source/MonetaryWorld.lean`): every *current* account
balance **and every account saved in the journal** is `< 2^256`. The saved
half is needed because rollback restores saved accounts
(`savedWide_undo_not_fit` shows a fitting world whose undo does not fit).

## 1. Writer inventory

Every Source-level writer of `Account.balance` (`rg` over `withBalance`,
`balance :=`, `.account _ fun`, `Op.account`; Bridge/vendor EVM accounts are
`UInt256` and out of scope):

| Writer | Location | Guard | Preservation theorem |
|---|---|---|---|
| initial state `St.init` (all `Account.empty`, empty journal) | `Source/Semantics.lean` | — (balance 0) | `St.init_balancesFit` (new) |
| `credit` (tx value, env credits/callbacks) | `Source/Eval.lean` | `b + v < 2^256`, else revert | `MonetaryExecution.credit_preserves` (VY5) |
| `debit` (value sent outside) | `Source/Eval.lean` | `v ≤ b`, else `false` | `MonetaryExecution.debit_preserves` (VY5) |
| `ExecState.transferNat` / `transfer` (instance-to-instance call value) | `Source/World.lean` | `amount ≤ bs ∧ bd + amount < 2^256` | `ExecState.transferNat_balancesFit`, `transfer_balancesFit` (VY5) |
| `deploy`: opening write of the new account | `Source/Semantics.lean` | `old + value < 2^256`, else revert | `deploy_open_balancesFit` (new) |
| `deploy`: code installation | `Source/Semantics.lean` | — (balance unchanged) | `deploy_code_balancesFit` (new) |
| storage / transient writes (`applyOp`, `setCell`, `writeAt`) | `Source/Machine.lean` | — (balance unchanged) | `MonetaryStorage.setCell_preserves`, `writeAt_preserves` (VY5) |
| rollback (`undo`, `undoN`, `rollbackTo`, `CallFrame.rollback`), `endTx` | `Source/World.lean`, `Eval.lean` | — | `ExecState.undoN_balancesFit`, `rollback_balancesFit`, `endTx_balancesFit` (VY5) |
| `Authority.writeSource` | `Source/MonetaryAuthoritySource.lean` | **none** (writes an unchecked Nat) | `Authority.writeSource_balancesFit` (premise `Fits (authority.balance address)`), `Authority.writeSource_fit` (premise `authority.Fit`), guarded `Authority.writeSourceChecked?` + `writeSourceChecked?_balancesFit` (new) |
| EIP-6780 self-beneficiary burn (`balance := 0`) | `Yul/World/Lifecycle.lean` | — | `selfBeneficiary_balancesFit` (new) |
| EIP-6780 destruct transfer | `Yul/World/Lifecycle.lean` | `transferNat`'s guard | `destructTransfer_balancesFit` (new) |
| lifecycle finalization (erase to `Account.empty`, clear journal) | `Yul/World/Lifecycle.lean` | — | `finish_balancesFit` (new) |
| read-only history writes `withBalance amount.val` (`amount : Word`) | `Lowering/Readonly/StaticJournal.lean` | Word type | `ExecState.apply_wordBalance_balancesFit` (new) |

Generic: `ExecState.apply_account_balancesFit` (any account update whose new
balance fits) and `ExecState.apply_sameBalance_balancesFit` (any update keeping
the balance). Remaining `withBalance`/`balance :=` hits are fixtures in
`*Controls*`/`*Checks*` files and `Backend/Transient/SourceCallback.lean`
(a fixed literal 93), not semantics.

`Authority.writeSource`: the assignment asked to guard it or add the premise at
its single caller. It has **no caller** anywhere in the repository, so the
premise lives on its preservation theorem, and a guarded variant
`writeSourceChecked?` (refuses a non-fitting amount, equal to `writeSource` on a
fitting one: `writeSourceChecked?_of_fits`) is provided for a future caller.
`Authority.source_amount`, `source_undo` and `request_postFee` are unchanged.
`Authority.set_fit` keeps a fitting authority under a fitting `set`.

## 2–3. BALANCE is exact

`Yul/Views/SourceBalanceExact.lean`, over VY5's actual-evaluator run lemma
`sourceBalanceLocal_run`:

- `sourceBalanceLocal_exact`: for an instance (`code = some _`) on a state with
  `ExecState.BalancesFit`, `evalE` of `address(x).balance` returns
  `uintValueOfWord ⟨balance, fit⟩`, and leaves the state unchanged;
- `sourceBalanceLocal_exact_int`: the same as `intWrap u256 balance`.

External (`code = none`) addresses read G01's Word ledger and are unaffected.

## 4. Witness and negative controls (`Source/MonetaryFit.lean`)

- `edgeState`: address 0 holds `2^256 - 1`, journal non-empty;
  `edgeState_fit`.
- `transferNat_hypotheses_satisfiable`: a fitting state whose transfer of the
  whole edge balance to address 1 succeeds (recipient lands at `2^256 - 1`) and
  fits — the transfer theorem's premises are inhabited.
- `unguarded_write_breaks`: from `edgeState`, an unguarded
  `withBalance 2^256` write breaks the invariant.
- `wideAuthority_writeSource_breaks`: `wideAuthority.writeSource` breaks it,
  while `writeSourceChecked?` refuses (`none`).
- `sourceBalanceLocal_wide`: an instance holding exactly `2^256` is observed by
  `BALANCE` as `0`, and its state is not `BalancesFit`.

## Gates

See the CLOUD-RESULT block in the final marker commit for the recorded runs.

## Limitations

- Per-writer laws. A theorem that every Source execution (the mutual
  evaluator: `runTx`, `deploy`, `callAddr`, `envLoop`, …) preserves
  `BalancesFit` is **not** proved; it is an induction over the whole evaluator
  and would compose the per-writer laws above.
- `BALANCE` exactness is proved for a local-address operand (the profile of
  `sourceBalanceLocal_run`); an operand with effects needs its own run lemma.
- `deploy`'s writes are covered by lemmas stated on the exact operations it
  applies, not by a run lemma of `deploy` itself.
