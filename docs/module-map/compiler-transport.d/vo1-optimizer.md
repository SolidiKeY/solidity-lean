| `Optimizer/CSE.lean` | O03 common-subexpression elimination: typed syntactic equality on pure values (`Val.pbeq_eq`), available-expression invariant; `ConstFold.Prog.cse_empty_runC`. |
| `Optimizer/ConstFold.lean` | O02 constant folding on the typed `Val`; failing operations kept; `Val.cfold_evalT` (equal result in every state). |
| `Optimizer/Propagate.lean` | O02 constant and copy propagation with a fact invariant on locals; `Prog.cprop_empty_runC`. |
| `Optimizer/Simplify.lean` | O02 solc-rule expression simplifier restricted to checked-safe identities; `Val.simp_evalT`, `Prog.simplify_runC`. |
| `Optimizer/StmtFold.lean` | Expression passes lifted to `Prog` (`ValPass`, `Prog.vopt_runC`), dead-branch/`require(true)`/`while(false)` elimination, `Prog.cfold_runC`. |
| `Optimizer/UnusedVar.lean` | O02 unused-variable elimination: proved strengthening (`Prog.str?_wk`) and `Prog.run_wk`; `Prog.uve_runC`. |
