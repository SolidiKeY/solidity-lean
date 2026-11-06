Production registration proposal: no new module or generated-root change is
needed. The exported patch adds `ByteTable` declarations inside the existing
registered BYTE control module. V15 must approve/apply that exact-file patch.

| Existing production module | Proposed description after owner migration |
|---|---|
| `Bridge/SolidityBridge/RoadmapV15/P10/ByteObservationControls.lean` | Intrinsic parameterized native BYTE execution and typed nine-row byte table; all original control signatures and negative/refusal observations retained. |

The additive test modules are registered only in their owned standalone package:

| Test module | Purpose |
|---|---|
| `GenericP10.ByteFixture` | Typed parameterized execution, finite fixture values and kernel byte algebra |
| `GenericP10.ByteControls` | Exact-instance overlay of every original BYTE declaration |
| `GenericP10.Correspondence` | Kernel equality for all 21 complete public original propositions |
| `GenericP10.AxiomAudit` | Local fixed-allowlist guards for 48 headlines |

This fragment has not been applied to a central module map or root.
