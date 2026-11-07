# VT1 central registration proposal

COORD owns these changes; this lane has not edited generated roots/maps/trust pins.

Regenerate Solidity.lean to add:
- `import Solidity.SolcValidation.Dialect`
- `import Solidity.Frontend.SolcJson.IrImport`

Proposed docs/module-map/yul.md row (the automatic heuristic suggested bytecode-selection.md):
| `SolcValidation/Dialect.lean` | Arity-indexed compiler object-dialect operation vocabulary, IR modes and code-bearing artifact roots; syntax only. |

Proposed docs/module-map/frontend.md row:
| `Frontend/SolcJson/IrImport.lean` | Certified exact standard-JSON source/contract/IR-channel extraction; Yul parsing and compiler authentication remain separate. |

Proposed core classification: add exact `Solidity.SolcValidation.Dialect` to CORE
in scripts/check-layers.mjs and docs/parallelism.md. Its closure is only the
dependency-free Yul.Builtins. IrImport imports Lean JSON and remains frontend.

New theorem inventory for central integration:
- Solidity.SolcValidation.evm_name: []
- Solidity.SolcValidation.mode_distinct: []
- Solidity.Frontend.SolcJson.Ir.Selection.sound: []
- Solidity.Frontend.SolcJson.Ir.Selection.complete: []
- Solidity.Frontend.SolcJson.Ir.ContractSelection.sound: [propext]

Root/orphan gates fail until central serialized registration is integrated.
These rows and axiom sets are a proposal, not an edited trust pin or final gate.

## C03 addition after adopting published master 8495f1de

Add `import Solidity.SolcValidation.DataLayout` to the generated root.
Proposed docs/module-map/yul.md row:
| `SolcValidation/DataLayout.lean` | Intrinsically bounded artifact byte references, unique data-label tables, exact size/offset/byte correspondence and present-label lookup completeness. |
Add exact `Solidity.SolcValidation.DataLayout` to CORE alongside Dialect.
Its import closure is Dialect and Yul.Builtins, with no Lean frontend import.

New standard-axiom inventory (all source-level axioms remain unchanged):
- DataRef.bytes_length: [propext, Quot.sound]
- DataRef.datasize_exact: [propext, Quot.sound]
- DataRef.dataoffset_exact: []
- DataRef.byte_exact: [propext, Quot.sound]
- DataSelection.sound: []
- selectData_complete: [propext]
All names are in Solidity.SolcValidation. Central re-pin/registration remains COORD.

## C04 addition after adopting f77cf60d

Add `import Solidity.SolcValidation.DataResolution` to the generated root.
Proposed docs/module-map/yul.md row:
| `SolcValidation/DataResolution.lean` | Unique object-data table resolution, selection extensionality, exact completeness and success iff membership; source-label association remains separate. |
Add exact `Solidity.SolcValidation.DataResolution` to CORE. Closure is DataLayout,
Dialect and Yul.Builtins only. New public theorem axiom sets:
- DataTable.selection_unique: [propext, Quot.sound]
- DataSelection.ext: []
- DataTable.select_complete: [propext, Quot.sound]
- DataTable.select_iff: [propext]
All names are in Solidity.SolcValidation. No new axioms declared; COORD owns pins.
