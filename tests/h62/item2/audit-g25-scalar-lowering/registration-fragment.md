# Registration handoff (not applied)

No generated root, central map, source interface or axiom pin is edited.
These validated additive modules remain in the authorized tests directory.
Coordinator/owner approval is required to move/register them elsewhere.

| Audit-only target or module group | Purpose and boundary |
|---|---|
| `AllWitnesses.lean` and its 46 witness imports | Exactly one full-telescope joint witness per frozen public statement; 311 total. |
| `KernelCensus.lean`, `WitnessCommand.lean`, `WitnessCommandChecks.lean` | Census/fidelity elaborator support and adversarial checks. Imports Lean; never register in dependency-free core roots. |
| `Fixtures.lean` | Shared actual intrinsic input/model data; no new premises. |
| `ScalarTotality.lean`, `ClosedTotality.lean`, `EnvironmentTotality.lean`, `SuccessControls.lean` | Pure proofs for the supported component/program families and negative/failure/capacity controls. |
| `BoundaryVectors.lean`, `SuccessAxioms.lean` | Audit IO/export and axiom-report targets; never register in core roots. |

A separately approved audit test target can import AllWitnesses and SuccessAxioms
at their existing locations. The quoted module component is
`tests.h62.item2.«audit-g25-scalar-lowering»`. No core registration is proposed
for the audit package; its pure proof modules may be extracted only after owner
review of their final import graph. Existing originals stay unchanged.
