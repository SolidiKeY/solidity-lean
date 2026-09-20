# Solidity Lean Formalization

Lean 4 formalization of the Solidity-in-KeY calculus, including its syntax,
rewrite rules, executable semantics, soundness and uniqueness results, and
worked derivations. `Solidity/Evm/` additionally compiles
a fragment of the Solidity AST to an EVM-style stack machine (instruction
semantics modeled on [NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean))
with a machine-checked proof that compilation — including solc-style
`uint` overflow guards and the balance-checked `transfer` — preserves
the executable semantics — see `docs/compiler-verification.md`.

## Build

```sh
lake build Solidity     # the formalization; elaboration is the test suite
./run-lean.sh           # the same, then the solkey cross-check below
```

The package declares no dependencies at all — no Mathlib, nothing — so
`lake build` clones nothing. It pins its compiler in `lean-toolchain`. On
NixOS, `run-lean.sh` uses the wrappers in `scripts/lean-vscode/bin` to select
a compatible Lean and Lake installation.

Three further Lake targets are deliberately outside the default build, because
each is a large batch of symbolic executions that would multiply the cost of an
ordinary build: `SolidityExamples` (`./scripts/check-examples.sh`),
`SolidityCorpus` (`./scripts/check-solkey-parity.sh`) and `SolidityCalculus`
(`./scripts/check-calculus-parity.sh`).

## Relationship to solkey

The calculus formalized here is implemented as KeY taclets by
[solkey](https://github.com/SolidiKeY/solkey). Two checks keep the two
honest, and both expect a solkey checkout beside this repository
(`../solkey`; override with `--key`/`SOLKEY_RULES` and `--solkey`):

- `lake exe solkeycheck` (`./scripts/check-solkey.sh`, run by `run-lean.sh`)
  cross-checks the sort annotations in `Solidity/SortCheck/Annotations.lean`
  against solkey's `solidityProgramRules.key`. **It currently reports 78 rows
  of drift** — a known, pre-existing gap described in `AGENTS.md`; re-syncing
  it is its own change. Without a checkout it prints `SKIPPED` and exits 0.
- `scripts/solkey-port.mjs` regenerates `Solidity/Examples/Solkey/` from
  solkey's `.sol` example suites; `./scripts/check-solkey-parity.sh` diffs the
  verdicts against `tests/solkey/expected.tsv`.
- The same pass also regenerates `Solidity/Examples/Derivations/Solkey/`,
  which proves the *same* obligations from `Rules.lean` alone —
  `./scripts/check-calculus-parity.sh`, table in
  `tests/solkey/expected-calculus.tsv`, scoreboard in
  `docs/calculus-parity.md`. The distinction is the point: `sol_wp` never
  reads the rule table, so the first check says the interpreter agrees with
  solkey and the second says the calculus does.

`docs/lean-key-rule-map.md` is the name-by-name map between the two rule
sets.

The project-local `.codex/config.toml` starts `scripts/run-lean-mcp.sh` for
Codex diagnostics when Codex is started from this package root after the
repository is trusted. Restart Codex after first cloning (or after changing
MCP configuration), then check `/mcp` for
`lean_lsp`. `.mcp.json` provides the equivalent configuration for clients that
use that format. The launcher creates `.venv` on first use and installs the
version pinned in `scripts/lean-mcp-requirements.txt`.

See `docs/module-map.md` for the module map and `AGENTS.md` for the working
conventions.
