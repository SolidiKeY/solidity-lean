# Optimizer obligation

[Authoritative source](../../Solidity/Optimizer).

The full-scope decision requires observational correctness, including failures and divergent/resource-limited behavior, for the actual optimization pipeline. Local constant-folding or pass-composition theorems do not provide that producer. Retain the H38 owner-review hold and D6 contract; target-only fixtures or a smaller partial relation cannot replace the required source/target semantics.
