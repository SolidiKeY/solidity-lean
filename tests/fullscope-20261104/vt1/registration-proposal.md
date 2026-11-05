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
