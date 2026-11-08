# Solidity Lean

A dependency-free Lean 4 model of Solidity syntax, execution and program logic,
with proof automation and compiler-correctness results for explicit admitted
fragments. Source declarations and tests define the supported fragment.
A model proof is not automatically source-to-executable-EVM correctness; see
[the correctness boundary](docs/correctness.md).

[Examples](https://solidikey.github.io/solidity-lean/) ·
[Offline IDE](https://solidikey.github.io/solidity-lean/ide/) ·
[CLI](docs/cli.md) · [Editor setup](vscode/README.md)

## Build

Install the pinned `lean-toolchain` and follow the resource and writer-lock
rules in [contributing.md](docs/contributing.md).

```sh
./run-lean.sh
# Optional separate package with external libraries:
./run-lean.sh --bridge
```

The core has no external dependencies. `Bridge/` is optional and has its own
pinned dependencies. [AGENTS.md](AGENTS.md) holds working constraints;
[docs/README.md](docs/README.md) locates retained guidance.

The calculus follows [SolKey](https://github.com/SolidiKeY/solkey);
[lean-key-rule-map.md](docs/lean-key-rule-map.md) records the rule correspondence.
