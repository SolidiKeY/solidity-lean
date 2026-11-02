# H14 routine glue — P8a-SPEC

These are statements for separate Terra commits, not Lean axioms or placeholders.
No frozen `Producer` or realization inhabitant is supplied. Producer and
soundness arguments, actual failure execution, origins and SourceSpec remain
with VY5; CR owns admission/extraction and final Producer assembly.

| Module | Lemma statement | Why routine |
|---|---|---|
| `Solidity/Lowering/P8/FailureProjection.lean` | `points_withPoints (r : Resource) (p : Choices) : points (withPoints r p) = p` | Existing transferred `Bound.failures_with`/field projections. |
| same | `horizon_withPoints (r : Resource) (p : Choices) : (withPoints r p).horizon = r.horizon` | Existing transferred `Bound.horizon_with`. |
| same | `failureFree_noFail (n : Nat) (balances : Nat → Nat) : NoFail (points (failureFree n balances))` | Existing transferred `noFailures_noFail`. |
| `Solidity/Lowering/P8/SourceRealization.lean` | `machineAgreement : MachineAgreement` | Definitional equality with actual `Source.sourceLangEvents`; no resource adequacy asserted. |

Actual failure schedules are NOT consulted by the current bare-horizon Source
session. Do not fill this gap by ignoring schedules, choosing a favorable
operational reference, or weakening the frozen resource-point law. These routine
facts do not construct `FailureProjection S` or `SourceRealization` for a real S.
