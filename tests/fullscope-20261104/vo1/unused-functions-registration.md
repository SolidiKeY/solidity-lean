# COORD registration request: VO1 idle-group pruning

Source: `Solidity/Optimizer/UnusedFunctions.lean`; consumer: future Yul optimizer composition. This is a bounded first O03 unused-function pruning slice, not D6 or whole-lane closure.

Please serialize `scripts/coord-tools/register.sh` to add `import Solidity.Optimizer.UnusedFunctions` to the generated root, and add this proposed row to the compiler-transport area fragment using the central registration tooling:

| `Optimizer/UnusedFunctions.lean` | Immediate idle Yul function-group pruning; complete Tier-A OpenRun outcome equality at fuel ≥2 and exact completion equivalence. General reachability, D6 and compiler/physical integration remain open. |

Then regenerate fragments and any required trust inventory under COORD ownership. No shared root/map/pin was edited by this lane.

Public namespace: `Solidity.Optimizer.UnusedFunctions`. All F/X/control/local indices are retained.

- `pruneIdleGroup : Optimizer.Yul.Pass F X c n`: immediate functions/skip groups become skip; all other ASTs remain exact.
- `prune_policy : Policy.StmtP .A code → Policy.StmtP .A (pruneIdleGroup code)`.
- `prune_run`: for every environment, admitted code and WordState, complete OpenRun outcomes at `fuel + 2` agree.
- `prune_completion`: for each exact Outcome, existential successful horizon equivalence; horizons may differ.
- `idle_group_horizon_one`: original none and pruned normal result, so no identical-small-horizon or physical-gas claim.

Controls: `tests/fullscope-20261104/vo1/UnusedFunctionsControls.lean`. Source/control per-file kernel checks pass; standard axioms only. Full-gate root/orphan checks fail pending this registration. Corpus exceeded the unchanged 290s inner/300s outer group budget after the exact published missing SolKey pin was restored and all274 snapshot files verified; no corpus/full-build PASS claimed. Retain the original goal and full O01–O03 obligations.
