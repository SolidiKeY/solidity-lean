# Storage layout red team

| Module | Its examples |
|---|---|
| `Examples/RedTeam/StorageLayout/BoolPacking.lean` | Concrete full-word/solc mismatches for adjacent booleans, fixed and dynamic boolean arrays, packed structs and the following field. External metadata reproduced by `check-solc.cjs` and `Layout.sol` beside the module. |
| `Examples/RedTeam/StorageLayout/ReferenceChecks.lean` | Executable independent Keccak vectors for dynamic arrays, mappings inside mapped structs, packed boolean array base and ERC-7201 namespace; reference runner `check-reference.py`. |
