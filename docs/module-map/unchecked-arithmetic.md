<!-- Generated from docs/module-map/unchecked-arithmetic.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
| `Correctness/Lowering/Total/Main.lean` | The loop contract composed with the production and family theorems: it is interpretation faithfulness and `Residual` (unproved); `production_correct` derives the consumer from `Residual` and `FullDomain`. |
| `Correctness/Lowering/Total/Decode.lean` | The stage-1 raw-to-Source decoder `Decode.decode`: a chosen Source spelling of the raw input, then Source inference and resolution; every other input is a gap. |
| `Correctness/Lowering/Total/Spells.lean` | The inductive spelling relation `Spells`; the decoder is sound for it and complete if Source inference is (`InferComplete`, unproved). |
| `Correctness/Lowering/Total/Boundary.lean` | The stage-1 boundary: observation policies, general simulation, allocation trace, state relation `loopRel`, and `loopResidualStage1_iff` (four obligations left, unproved; known defects listed). |
| `Correctness/Lowering/Total/Contract.lean` | Universal loop-production candidate and explicit semantic coverage obligations. |
| `Correctness/Lowering/Total/Relation.lean` | Finite lowering derivations and caller-preserving fresh-name equivalence. |
| `Correctness/Lowering/Total/Coverage.lean` | `LowersTo` is functional, and its exact raw output on each loop-family input template. |
| `Correctness/Lowering/Total/Coverage/Checks.lean` | The e1 sample inputs as template instances; the while/break probe's actual output is the only one. |
| `Correctness/Sim/Examples.lean` | Checked boundary examples for the simulation framework. |
| `Correctness/Sim/Lang.lean` | Instantiate the simulation framework with the existing Lang adapter. |
| `Correctness/Sim/Observation.lean` | Observation diagrams over the roadmap's unchanged prefix order. |
| `Correctness/Sim/Steps.lean` | Finite transition closures and reusable simulation diagrams. |
| `Correctness/Lowering/Sim/Match/Relations.lean` | The lowering diagram's value, global and frame relations, context alignment and total matching of locals and globals. |
| `Correctness/Lowering/Sim/Match.lean` | The lowering diagram candidate (`Sim.diagram`): its association, relation-only laws, total initial matching and `caller_bound`. |
| `Examples/Lowering/Sim/Match.lean` | Association smoke of the lowering diagram on one standalone loop (`Assoc` when placed), and uses of its declarations. |
| `Correctness/Lowering/Sim/Match/Cases.lean` | The open-recursion case interface of the lowering diagram: `RunSim`, `SiteSim`, `RecSim` (the instance of `ElabKernelInduction`), `ExprCases`, `StmtCases`, `StateCases`, and their sufficiency (`runs_of_cases`). |
| `Correctness/Lowering/Sim/Smoke.lean` | The case interface on two arms of `elabStmt1With`: stability for every body (`source_stable`), `RunSim` reduced to its lowering and run clauses, the refusing jump arm, and the `revert();` arm from the Source side of its bodies. |
| `Examples/Lowering/Sim/Cases.lean` | Uses of the case interface and its smokes: the induction instance, the families, `diagram.Simulates` from the cases and a loop hypothesis, the jump and `revert();` leaves. |
| `Correctness/Lowering/Sim/Session/Source.lean` | A small-step presentation of the Source session semantics with run coverage and realization. |
| `Examples/Lowering/Sim/Session/Source.lean` | The source session machine on two small programs: coverage, realization and checked paths. |
| `Correctness/Lowering/Sim/Session/Target.lean` | The intrinsic session run's machine covers and realizes it: `covers` (every bound's run prefix is reached in the machine with the bound's failures), `realizes` (every reachable state is a `Prefix.Le`-prefix of the run at a bound with the same failures), and their readings `covers_noFail` / `realizes_noFail` in the machine without failures. |
| `Correctness/Lowering/Sim/Session/Target/Machine.lean` | The intrinsic session run as a `Sim.Machine` per session world, environment and failures: boundary states (history, typed world, actions issued, pending deployment/action/idle/stopped), one step per deployment or action, `observe` the prefix so far; `machine_congr`, front-grown `Path`. |
| `Examples/Lowering/Sim/Session/Target.lean` | One-contract checks: the machine reaches the deployment and request prefix, and the final outcome once idle; the state after the deployment is realized below a run without resource failure. |
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
