# EVM interpretation

[Authoritative source](../../Solidity/Roadmap/Evm.lean).

Use the pinned Osaka observation/fork policy and exact external reference revision. Core component machines abstract resources and context; they are not interchangeable with the full EVM. Preserve ordered return/revert/log observations, sender funds, call/creation rollback and explicit fixed hash/precompile assumptions at the Bridge boundary. Follow the binding [scope decisions](../solidity-scope.md), including per-run hash-region assumptions.
