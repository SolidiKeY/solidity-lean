# The documents

One line each. `docs/module-map.md` is the one to open first; the rest are
referenced from it and from `AGENTS.md`.

| Document | What it is |
|---|---|
| [module-map.md](module-map.md) | One row per module: what it defines and why it exists. The index to the tree. |
| [kernel-port.md](kernel-port.md) | Where each mini-solkey chapter landed, the decisions taken on the way, and what is still to port. |
| [lean-key-rule-map.md](lean-key-rule-map.md) | The authority for the name-by-name map from solkey's taclets to the `Taclet` constructors. Do not restate it in a module docstring. |
| [examples-port.md](examples-port.md) | Where each storage example of the untyped layer went in `Solidity/Examples/`, or why it was dropped. |
| [solc-alignment.md](solc-alignment.md) | Where the interpreter follows solc rather than KeY, and why. |
| [compiler-verification.md](compiler-verification.md) | The EVM compiler: removed with the untyped syntax, to be ported. |
| [solkey-feedback.md](solkey-feedback.md) | Improvement ideas flowing Lean → solkey. The only outbound document. |
