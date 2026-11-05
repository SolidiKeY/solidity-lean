# COORD serialized registration proposal

Do not apply in the lane: shared/generated files are COORD-owned.

Add generated Solidity.lean imports (register.sh --check reports exactly these):

```
import Solidity.Optimizer.Controls
import Solidity.Optimizer.Laws
import Solidity.Optimizer.Pass
import Solidity.Optimizer.RoadmapComposition
```

Add four modules to CORE in scripts/check-layers.mjs; imports already stay below
elaborators. Create docs/module-map/optimizer.md and link it from the area index:

| Modules | Purpose |
|---|---|
| `Optimizer/Pass.lean` | Intrinsic total passes, preservation, executable sound validators and guarded proposals. |
| `Optimizer/Laws.lean` | Pipeline laws, equality/reject validators and rejection controls. |
| `Optimizer/RoadmapComposition.lean` | Total-pass embedding and existing Roadmap.Cert.comp adapter, concrete certificates still required. |
| `Optimizer/Controls.lean` | Framework-only accepting/negative/combination controls, syntax inhabitants and axiom reports. |

Tool outputs: evidence/registration.log and evidence/module-map.log.
No feature catalog or trust pin changes proposed here. X01 owns D1–D6 binding.
