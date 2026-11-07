import Solidity.Yul.Compilation.P20InterfaceV2

/-! The representation-aware P20 interface is core. Its concrete local-store
regression controls depend on non-core assignment fixtures and are available
in-tree at `tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean`.
Their bounded regression slice does not establish general P20 adequacy.
Keep this compatibility module free of non-core control imports. -/
