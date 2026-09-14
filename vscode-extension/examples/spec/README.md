# SolSpec examples

Worked contracts for the NatSpec specification language. The language
reference is `../../../docs/spec-language.md`.

Run one from the extension directory:

```sh
npm install && npx tsc
node out/specCli.js examples/spec/Bank.sol ..      # verdicts
node out/specCli.js examples/spec/Bank.sol .. --show   # + the generated Lean
```

(`..` is the Lake package directory — `lean/solidity`, which holds
`lakefile.toml` next to `Solidity.lean`. Omit it and the CLI
walks up from the `.sol` file looking for one.)

The first run builds `Solidity.Spec.Tactic`, which is
not part of the default `lake build`; later runs reuse the cache.

## `Bank.sol` — the core of the language

A two-account ledger. Shows a contract invariant, `requires`/`ensures`
with `old()`, `modifies`, the partial (`@custom:partial`) reading with
`reverts_when`, a named return value, and a ghost `@custom:assert`.

It is also the contract that `Solidity/Spec/Examples.lean`
writes out by hand, so the two can be compared side by side: `--show`
should produce the same theorem shapes.

The interesting obligation is `Bank_transfer_range`. It is not a clause
anybody wrote — it is what `uint256` means on the way out, and it needs
both `@custom:requires amount <= balSender` (no underflow on
`balSender -= amount`) and the contract invariant (no overflow on
`balTo += amount`). Delete either and the range obligation is the one
that fails.

## `Vault.sol` — the rest of the surface

Mappings (`balances[who] = amount` read back at the same key), arrays and
`push`, struct fields, a branch on a symbolic condition (`sol_spec` splits
it and both branches must establish the postcondition), a bounded
quantifier in a precondition, and a ghost assertion between two writes.

The last function, `loopy`, is deliberately outside the verified
fragment: the semantics has no loop rule. It is *reported* — a warning on
its own line saying why — rather than silently skipped, which is the
distinction the whole reporting layer exists to keep.
