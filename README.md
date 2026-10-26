# Solidity Lean Formalization

Lean 4 formalization of the Solidity-in-KeY calculus: a typed Solidity
syntax, an executable semantics, the taclets as one inductive judgement in
its own notation, each proved sound against the semantics, a sequent
calculus with a soundness theorem, symbolic execution,
decision procedures for the first-order goals, type soundness, a verified
compiler to an EVM-style machine (`docs/compiler-verification.md`), and
worked examples. The design follows mini-solkey, a small readable copy of
the calculus; `docs/kernel-port.md` says what came from where.

## Examples online

**<https://solidikey.github.io/solidity-lean/>** — the worked examples as
Lean shows them: Solidity contracts and their proofs, with the goal and the
messages at every line, recorded from Lean's language server when the site
was built. Pick a project (the Solidity calculus, or Velvet) and an example
at the top; a link names the file and line. `docs/site.md` says how the site
is built and how to add an example.

The Velvet examples are Solidity contracts, each on one page with its
specification (`contract C { … }`, `Bridge/SolidityVelvet/Contract.lean`),
every function proved by Velvet's `loom_solve`:

- [The test suite](https://solidikey.github.io/solidity-lean/#project=Velvet&file=SolidityVelvet/TestSuite.lean) — one
  contract of 83 of solkey's `TestSuite.sol` functions, feature by feature
  (arithmetic and its reverts, logic, `if`, `require`/`assert`, storage
  roots, mappings, arrays, `push`/`pop`, `delete`, loops), all proved by
  `prove_contract TestSuite by loom_solve`
- [Solidity patterns](https://solidikey.github.io/solidity-lean/#project=Velvet&file=SolidityVelvet.lean) — a counting loop, the largest
  balance, ERC20's `transfer`
- [A bank](https://solidikey.github.io/solidity-lean/#project=Velvet&file=SolidityVelvet/Bank.lean) — `deposit`, `withdraw` and
  `balance`, other accounts untouched
- [An ERC20 token](https://solidikey.github.io/solidity-lean/#project=Velvet&file=SolidityVelvet/Token.lean) — `mint`,
  `transfer`, `approve` and `transferFrom`
- [Loops over storage arrays](https://solidikey.github.io/solidity-lean/#project=Velvet&file=SolidityVelvet/Loops.lean) — the
  total balance, a holder's index, the winning proposal

solkey's test suite is here too: its
[`TestSuite.sol`](tests/migration/solkey/keyext.solidity.examples/TestSuite.sol)
(617 functions, from solkey
[`473da8944c`](https://github.com/SolidiKeY/solkey/blob/473da8944ca7329e6b76819863591407db26e7ec/keyext.solidity.examples/TestSuite.sol)),
imported from solc's AST, with an obligation per public function and a
theorem per obligation (`lake build SolkeyTestSuite`):

- [The import](https://solidikey.github.io/solidity-lean/#project=Solidity&file=Solidity/Solkey/TestSuite.lean) — what
  was elaborated, skipped and excluded, and why
- [The report](https://solidikey.github.io/solidity-lean/#project=Solidity&file=Solidity/TestSuite/Report.lean) — every
  function derived, refuted or not an obligation (552 derived of 617)
- [Derived obligations](https://solidikey.github.io/solidity-lean/#project=Solidity&file=Solidity/TestSuite/Derived1.lean) — the
  first of the proofs, each by `sol_prove`
- [Refuted obligations](https://solidikey.github.io/solidity-lean/#project=Solidity&file=Solidity/TestSuite/Refuted.lean) — the
  false ones, each with a certified counterexample (`sol_refute`)

## Build

```sh
lake build Solidity     # the formalization; elaboration is the test suite
./run-lean.sh           # the same, then the solkey cross-check below
```

The package declares no dependencies at all — no Mathlib, nothing — so
`lake build` clones nothing. It pins its compiler in `lean-toolchain`. On
NixOS, `run-lean.sh` uses the wrappers in `scripts/lean-vscode/bin` to select
a compatible Lean and Lake installation.

## Relationship to solkey

The calculus formalized here is implemented as KeY taclets by
[solkey](https://github.com/SolidiKeY/solkey). `lake exe solkeycheck`
(`./scripts/check-solkey.sh`, run by `run-lean.sh`) cross-checks the sort
annotations in `Solidity/SortCheck/Annotations.lean` against solkey's
`solidityProgramRules.key`, from a checkout beside this repository
(`../solkey`; override with `--key`/`SOLKEY_RULES`). Without a checkout it
prints `SKIPPED` and exits 0. `Calculus/RuleShapes.lean` checks which of
solkey's taclets the rule table claims, and `docs/lean-key-rule-map.md` is
the name-by-name map between the two rule sets.

The project-local `.codex/config.toml` starts `scripts/run-lean-mcp.sh` for
Codex diagnostics when Codex is started from this package root after the
repository is trusted. Restart Codex after first cloning (or after changing
MCP configuration), then check `/mcp` for
`lean_lsp`. `.mcp.json` provides the equivalent configuration for clients that
use that format. The launcher creates `.venv` on first use and installs the
version pinned in `scripts/lean-mcp-requirements.txt`.

## Optional bridge: Mathlib, Loom and Velvet

`Bridge/` is a separate Lake package that connects the core to Mathlib,
CSLib, an external EVM, [Loom](https://github.com/verse-lab/loom)'s VC
generator and [Velvet](https://github.com/verse-lab/velvet), the Dafny-style
verifier built on Loom (`docs/bridge.md`). The core does not depend on it.

```sh
cd Bridge && lake exe cache get && lake build   # or ../scripts/check-bridge.sh
```

See `docs/module-map.md` for the module map, `docs/README.md` for the rest of
the documents, and `AGENTS.md` for the working conventions.
