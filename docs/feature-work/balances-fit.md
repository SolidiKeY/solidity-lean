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

Every Source-level writer that *changes* `Account.balance` (`rg` over
`withBalance`, `balance :=`, `.account _ fun`, `Op.account`; EVM `Account .EVM`
balances in `Bridge/` — vendor and `SolidityBridge/HashBridge` — are `UInt256`
and out of scope). Account updates that keep the balance
— nonce bumps (`Yul/World/CreationFrames.lean` `creationNonceOp`) and the Yul
view storage writes (`Yul/Views/FiniteWorld.lean`, `ScalarWorld.lean`,
`PackedCellUpdate.lean`, `ActualScalarWrite.lean`, …) — are covered generically
by `ExecState.apply_sameBalance_balancesFit` and not listed one by one:

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
| read-only `History.balance` step (`withBalance b`, `b : Monetary.Balance`) | `Lowering/Readonly/StaticJournal.lean` | **none** (a structural history relation, not an executed writer) | only its Word form `History.balance_word` is covered, by `ExecState.apply_wordBalance_balancesFit` (new); the unbounded Nat step is not |

Generic: `ExecState.apply_account_balancesFit` (any account update whose new
balance fits) and `ExecState.apply_sameBalance_balancesFit` (any update keeping
the balance). Remaining `withBalance`/`balance :=` hits are not semantic writers:
fixtures in `*Controls*`/`*Checks*` files, `Backend/Transient/SourceCallback.lean`
(a fixed literal 93), the `savedWide` witness in `Source/MonetaryWorld.lean`, this
lane's own controls in `Source/MonetaryFit.lean`, the held test
`tests/yul-composition/held/FailureDriver.lean`, and `GlobT.withBalance` in
`Calculus/` (a different type, not a Source account).

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

External (`code = none`) addresses read G01's Word ledger. **Gap:** `deploy`
opens the new account with `code := none` and installs code only after the
constructor returns, so `address(this).balance` *during a constructor* takes
the ledger branch, not the Nat balance just credited; `sourceBalanceLocal_exact`
(which needs `code = some _`) says nothing about that case. This is pre-existing
semantics, recorded here, not changed.

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

## Reviews

Read-only finder and skeptic reviews (no Lean server), after the modules
elaborated. Neither found a semantic writer missing, a vacuous or circular
statement, a `deploy_*` lemma that differs from `deploy`, or a changed existing
declaration. Confirmed findings, all fixed in this document:

- the StaticJournal row claimed a Word guard; `History.balance` takes an
  unbounded Nat (row corrected, recorded as a limitation);
- balance-keeping account updates (nonce bump, Yul view storage writes) were
  not mentioned (scope sentence added; generic theorem cited);
- the list of non-semantic `withBalance` hits and the Bridge scope were
  incomplete (completed);
- `BALANCE` during a constructor reads the ledger branch (gap recorded).

Not acted on: `sourceBalanceLocal_wide` is conditional (a negative control by
design; the guards make such a state unreachable from `St.init`); the
generated `docs/module-map/source-definitions.md` places the row at the end of
the preceding table, as `fragments.sh` generates it.

## Gates

- Lean MCP diagnostics: the three new modules elaborate with no errors or
  warnings; every new theorem's `#print axioms` is pinned by `#guard_msgs` and
  lies within `propext`, `Classical.choice`, `Quot.sound`.
- `node scripts/check-axiom-pins.mjs --write`: 22 new pins recorded, 0 errors.
- `scripts/coord-tools/gate.sh checkpoint` (base
  `origin/cloud/moved2-20261105/vy5-composition`): PASS on all nine gates
  (build-touched, library — `Build completed successfully (6055 jobs)` —,
  trust, orphans, layers, roots, fragments, doc-paths, axiom-pins). This VM had
  no shipped Lake cache, so it was a from-scratch build (~2.5 h).
- `./run-lean.sh` (40 min wall): `Build completed successfully (6473 jobs)`,
  no `error:`; it then exits 1 in its final step, `scripts/check-solkey.sh`,
  because the sibling `../solkey` checkout is at `b8d5f88`, not the pin
  `473da8944c` (167 sort mismatches there; this lane touches no rule or
  annotation).
- Pinned rerun: `scripts/check-solkey.sh --key tests/migration/solkey/…/solidityProgramRules.key`
  (the vendored snapshot, byte-identical to `473da8944c`'s file):
  `solkeycheck: OK — annotations match`.

## Limitations

- Per-writer laws. A theorem that every Source execution (the mutual
  evaluator: `runTx`, `deploy`, `callAddr`, `envLoop`, …) preserves
  `BalancesFit` is **not** proved; it is an induction over the whole evaluator
  and would compose the per-writer laws above.
- `BALANCE` exactness is proved for a local-address operand (the profile of
  `sourceBalanceLocal_run`); an operand with effects needs its own run lemma.
- `BALANCE` of an account under construction (code not yet installed) reads
  the Word ledger, not the account's Nat balance; see section 2–3.
- The unbounded `History.balance` step of `Lowering/Readonly/StaticJournal.lean`
  is a proof-side relation and is not shown to preserve the invariant.
- `deploy`'s writes are covered by lemmas stated on the exact operations it
  applies, not by a run lemma of `deploy` itself.
