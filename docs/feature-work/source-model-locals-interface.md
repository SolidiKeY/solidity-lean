# SS-AGREE: primitive locals interface

This checkpoint states a normal-result locals obligation; it does not prove
source interpreter/model execution agreement or adopt a source interpretation.

`Agreement/PrimitiveTypes` and `Primitive` reuse exactly the two owned value
producers from 3d4f8d7f5f1f. They preserve bool/uint/int types and derive source
integer range evidence from the model value. `Locals` adds intrinsic contexts,
a total model-to-source local environment producer, its correspondence proof,
and an ordered false/true client. `StateLocalsRel` compares **only locals**.
It has no heap, storage, calldata, ledger, event or resource consequences.

`Agreement.NormalLocalsObligation` in `NormalStatement.lean` names actual `execItems` and
`Prog.runC` executions, retaining the source journal state. It is an unproved,
one-direction normal-result clause for an explicit program pair. It supplies
no arbitrary observer or future execution theorem. It does not handle source
return/break/continue, errors, reverse termination, or frame agreement. In
particular horizon timeout is not model divergence. Its normal-result premise
can be vacuous for a non-normal program; no program agreement follows merely
from this proposition being defined. The total locals producer witnesses the
value interface, not a successful program simulation.

The whole-step producer is blocked on lane VY5, H16: finalized
`Source/Machine.lean` St/EM and `Source/Eval.lean` resource/horizon interfaces.
Association of the actual source elaboration with the model elaboration,
heap/storage/input relations, error/panic/resource correspondence and full
simulation remain open. Neither elaborator is changed. H22 ExtCall
construction and all H16 producer files remain untouched.

## Checked scope

Four complete clean owning-file MCP responses and five bounded per-file gates
(including the actual public-signature/axiom audit) pass. All 17 audited
public declarations are axiom-free or use only propext, Classical.choice and
Quot.sound. The actual 50-job importing closure passes; this includes cached,
fetched and freshly elaborated unchanged dependencies, not a cold full build.
The two-local producer is the nontrivial value client; it is not a program
simulation witness. Finder and skeptic independently read source and raw
records without replaying checks; no source defect remained. The finder API
name correction is applied.

Retained failures include the first model/source Ctx name collision, a runner
Lake-version option-ordering error before any gate, and an inline summary
collector regex error before writes. Each repair has separate records in
`/workspace/next10-driver-agreement-locals`. No resource/proof limit was raised.
H12 full-lane gates were not replayed for this interface-only checkpoint.
Historical documentation/source/native failures and the original assignment
remain open. No integration or source-correctness claim follows.

Conditional normal-only nil/cons execution composition and nonvacuous no-op
clients are now in [source-normal-composition.md](source-normal-composition.md).
That later increment keeps per-statement producer facts explicit; it does not
turn the value/local checks above into full Source/model agreement.
