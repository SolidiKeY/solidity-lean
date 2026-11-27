| `Solidity/Correctness/Lowering/Sim/CoverageControl.lean` | Exact condition/then/else and default lowered-loop condition/body run-success composition; actual-producer specialization requires explicit `elabKernelTotal`. |
| `Solidity/Examples/Lowering/Sim/CoverageControl.lean` | Actual recursive-producer execution assertions with nonempty branches, preserved counters and seeded memo. |

These helpers advance `Solidity.Goals.loweringBySimulation` without changing
its statement or asserting `Diagram.Total`. Receipts expose entry contexts,
intermediate fresh counters, the complete reader and both state layers.
LS3B must supply the individual condition and scope receipts after establishing
capture, assignment and branch behavior. The default loop emits `LoopAnn.auto`;
arbitrary annotations, raw-loop lowering, remaining grammar cases, capture
reachability, placement, acceptance, concrete nonvacuity and final coverage
validation remain with the original LS3B lane. The executable examples do not
discharge kernel totality or substitute for those obligations.
