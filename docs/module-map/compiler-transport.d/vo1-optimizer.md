| `Optimizer/CSE.lean` | O03 common-subexpression elimination: typed syntactic equality on pure values (`Val.pbeq_eq`), available-expression invariant; `ConstFold.Prog.cse_empty_runC`. |
| `Optimizer/ConstFold.lean` | O02 constant folding on the typed `Val`; failing operations kept; `Val.cfold_evalT` (equal result in every state). |
| `Optimizer/DeadCode.lean` | O02 dead code after halting statements (`Prog.cut`, `cut_scope`, `Prog.dce_runC`) and dead local stores (`Prog.dse_runC`). |
| `Optimizer/DeadStore.lean` | X06 dead store elimination: last store at a state variable or static memory slot wins (`sstore_dead_runC`, `mstore_dead_runC`, `Heap.writeAddr_writeAddr`); `Prog.dstore_runC`. |
| `Optimizer/Inline.lean` | O03 inlining of void internal calls with value arguments (`inlineBlock_runC` via `Prog.run_wk`); `ConstFold.Prog.inl_runC`. |
| `Optimizer/LICM.lean` | X06 loop-invariant code motion under the loop guard (`licm_runC`, `TLoop.hoist_run`; frame from `Prog.run_frame`/`Prog.run_keeps`); `Prog.licm_runC`. |
| `Optimizer/Loads.lean` | X06 redundant load elimination: static loads, root-separated storage and field-sensitive memory alias analysis; `Prog.rle_empty_runC`. |
| `Optimizer/Pipeline.lean` | Certified O02/O03 pipeline (`round`, `Prog.optimize n`): inline, propagate, simplify, fold, dead code, CSE, loads, dead stores, LICM, unused-variable elimination; `Prog.optimize_runC`. |
| `Optimizer/Propagate.lean` | O02 constant and copy propagation with a fact invariant on locals; `Prog.cprop_empty_runC`. |
| `Optimizer/Simplify.lean` | O02 solc-rule expression simplifier restricted to checked-safe identities; `Val.simp_evalT`, `Prog.simplify_runC`. |
| `Optimizer/StmtFold.lean` | Expression passes lifted to `Prog` (`ValPass`, `Prog.vopt_runC`), dead-branch/`require(true)`/`while(false)` elimination, `Prog.cfold_runC`. |
| `Optimizer/UnusedVar.lean` | O02 unused-variable elimination: proved strengthening (`Prog.str?_wk`) and `Prog.run_wk`; `Prog.uve_runC`. |
