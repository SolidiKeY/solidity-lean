import Solidity.Yul.Compilation.P20InterfaceV2

/-! The representation-aware P20 interface is core. Its concrete local-store
regression controls depend on non-core assignment fixtures and are published
in the [VY3 review snapshot](https://github.com/SolidiKeY/solidity-lean/blob/e36cd2491ea6deced730ee103f999847574c2124/tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean).
That snapshot contains `tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean`;
the master publication `eee9cd7651a81b1f0cb702d8812c794339be7146` of this
compatibility module did not include that test file. Snapshot availability
is not master integration or general P20 adequacy.
Keep this compatibility module free of non-core control imports. -/
