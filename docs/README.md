# The documents

One line each. `docs/module-map.md` is the one to open first; the rest are
referenced from it and from `AGENTS.md`.

| Document | What it is |
|---|---|
| [module-map.md](module-map.md) | One row per module: what it defines and why it exists, with the open problems flagged. The index to the tree. |
| [lean-key-rule-map.md](lean-key-rule-map.md) | The authority for the name-by-name map from solkey's taclets to this package's `RuleName`s. Do not restate it in a module docstring. |
| [solkey-parity.md](solkey-parity.md) | What `sol_wp` — the *interpreter* — proves of solkey's suites. Scoreboard for `tests/solkey/expected.tsv`. |
| [calculus-parity.md](calculus-parity.md) | What `Calculus/Rules.lean` alone proves of the same suites. Scoreboard for `tests/solkey/expected-calculus.tsv`. A number from the first says nothing about the second: `sol_wp` never reads the rule table. |
| [paper-parity.md](paper-parity.md) | One row per worked example of the paper, naming the chain in `Solidity/Paper/` that is it, or the reason there is none. Add a row before adding a chain. |
| [soundness-hypotheses.md](soundness-hypotheses.md) | One section per hypothesis family of the `<rule>_sound` theorems: what frees it, and the attempts so far. The counts are `#soundness_ledger`'s. |
| [solc-alignment.md](solc-alignment.md) | Where the interpreter follows solc rather than KeY, and why. |
| [compiler-verification.md](compiler-verification.md) | The EVM compiler and its forward-simulation proof. |
| [kernel-port.md](kernel-port.md) | The plan and progress tracker for porting mini-solkey's typed kernel (typed syntax, `Taclet` judgement, residue-free completeness, `Proves.sound`) into `Solidity/Kernel/`. |
| [solkey-feedback.md](solkey-feedback.md) | Improvement ideas flowing Lean → solkey. The only outbound document. |
