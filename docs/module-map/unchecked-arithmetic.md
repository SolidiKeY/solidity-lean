<!-- Generated from docs/module-map/unchecked-arithmetic.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
| `Correctness/Lowering/Total/Contract.lean` | Universal loop-production candidate and explicit semantic coverage obligations. |
| `Correctness/Lowering/Total/Relation.lean` | Finite lowering derivations and caller-preserving fresh-name equivalence. |
| `Correctness/Sim/Examples.lean` | Checked boundary examples for the simulation framework. |
| `Correctness/Sim/Lang.lean` | Instantiate the simulation framework with the existing Lang adapter. |
| `Correctness/Sim/Observation.lean` | Observation diagrams over the roadmap's unchanged prefix order. |
| `Correctness/Sim/Steps.lean` | Finite transition closures and reusable simulation diagrams. |
# Unchecked arithmetic

| Module | Purpose |
|---|---|
| `Correctness/Lowering/Unchecked/CalleeMode.lean` | Caller mode at the internal-call boundary; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/Composition.lean` | Composition of arithmetic/effect obligations; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/CompoundOne.lean` | Compound-one evaluation for integer lvalues; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/IntegerOne.lean` | The exact constant one at every integer type; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/IntegerUpdate.lean` | Shared integer compound-update ingredient; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/LocalUpdate.lean` | Shared local compound-one and prefix update; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/PanicData.lean` | Panic bytes at the unchecked boundary; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/Relation.lean` | Unchecked arithmetic and effect relation groundwork; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/CallWitness.lean` | An elaborated unchecked caller with a checked callee; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/RawOne.lean` | Supplied raw compound-one/increment association; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/WrappingArithmetic.lean` | Shared typed wrapping arithmetic; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/WordAssociation.lean` | Supplied word-value association; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/WordProgram.lean` | Supplied wrapping word-update programs; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/UpdateArithmetic.lean` | Shared typed update arithmetic; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/Discarded.lean` | Discarded increment results; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/SourceOne.lean` | Supplied typed Source one-update boundary; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/PowerV2Arithmetic.lean` | Explicit V2 power operator consumer; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/WordOne.lean` | Exact destination/old-value association for word increments; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/NamedOne.lean` | Named raw/output/program association for one updates; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/PowerCutoffWitness.lean` | Source power cutoff witness; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/VersionedPowerWitness.lean` | V2 operator migration controls; unchecked-lowering component, full production endpoint remains unproved. |
| `Correctness/Lowering/Unchecked/SourceSpelling.lean` | Total raw/typed/named/model update association and actual original-context paired execution; partial producer, full state/resources and pass remain unproved. |
| `Correctness/Lowering/Unchecked/WordUpdateWitness.lean` | Actual-output word-association controls; unchecked-lowering component, full production endpoint remains unproved. |
