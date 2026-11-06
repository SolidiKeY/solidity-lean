# override-validation bounded checkpoint

Producer `83b80fa731b3ce35be01846e06da882daab8ee78`. Imports only:

- `Solidity/Frontend/OverrideValidation/Attributes.lean`
- `Solidity/Frontend/OverrideValidation/Graph.lean`
- `Solidity/Frontend/OverrideValidation/Routes.lean`

Statements, premises, exclusions and proof budgets are retained. This does not
establish completion of the lane or discharge its remaining producer obligations.
Touched/library checkpoint gates passed.
Separate read-only finder and skeptic reviews must pass before publication.
Reviews use exact diff/dependency packets; nested shell access is unavailable.

The initial skeptic proposed treating constant getters as view for override checking. That finding was refuted by hash-pinned solc 0.8.38: constants may override pure functions in both legacy and via-IR; regular and immutable getters may not. ABI output remains view. The original implementation is retained. Twelve direct compiler controls and compiler hash/version are retained in the coordinator receipt.

Independent finder and skeptic passed with no confirmed findings.
