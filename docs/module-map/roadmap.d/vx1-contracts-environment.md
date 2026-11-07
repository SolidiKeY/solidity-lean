
# VX1 full-scope proposal leaf

| Module | What it defines |
|---|---|
| `Language/EnvironmentFields/Contracts.lean` | Provisional G01 D1–D6/H38 byte-memory, artifact/oracle and run-indexed contracts in the preserved FullScope namespace; no producer certificate or freeze. |
| `Language/EnvironmentFields/ContractControls.lean` | Inhabited and falsifying toy models for unsafe writeback, opacity, exact compilation, artifact soundness, oracle linkage and optimizer refinement; independent of production Source/EVM adequacy. |
| `Language/EnvironmentFields/Frozen.lean` | Frozen version 1 (`Solidity.Roadmap.FullScope.V1`) of the G01 full-scope relation contracts D1–D6 and their bundle `Contract`, with the D1 oracle, D5, D1→D6, totality and adequacy lemmas; changes go to a new `V2` namespace (H57). |
| `Language/EnvironmentFields/FrozenControls.lean` | One toy model inhabiting the whole V1 bundle with live domains (joint satisfiability, H62/H69), and negative controls: rejecting compiler, always-reverting target, empty or shifted physical relation, overlapping fields, unsafe-block rewriting. |
| `Language/EnvironmentFields/Consequences.lean` | Backward completion and exact-observation consequences of the unchanged V1 run-indexed certificate; conditional consumer lemmas, not production adequacy. |
