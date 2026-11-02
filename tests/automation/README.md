# AU03 warning fixtures

`LiteralCtorNotice.sol` has a constructor-only literal loop. It checks that
source-import warnings also run outside the function-row loop.
`LiteralCtorNotice.ast.json` was generated with the existing SolKey-pinned
solc 0.8.34, using the existing generator (no compiler/dependency installation):

```sh
node scripts/solc-ast.mjs --solkey /workspace/.setup/solkey \
  --soljson /workspace/.setup/soljson \
  --source tests/automation/LiteralCtorNotice.sol \
  --out tests/automation/LiteralCtorNotice.ast.json --no-wrapper
```

The importing LoopNotices example pins FNV-1a `0xa7ef25dc4cfa9c6d`.
This is a diagnostic/import test, not a compiler correctness claim. Separate
Lean validity/refutation certificates check unchanged literal-loop results.

## Imported axiom audit guard

`ImportedAudit.lean` compares memoized policy decisions with full axiom
traversal across warm imports, generated-name reuse, nonstandard dependencies
and changed import snapshots. Synthetic declarations are restored before the
command ends. Pages CI runs it after building the frontend:

```sh
lake env lean -j1 --tstack=131072 tests/automation/ImportedAudit.lean
```
