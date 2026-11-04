# G19 conditional assignments followed by unconditional bare return

[The component](../../Solidity/Lowering/G19/ConditionalReturn.lean) reuses V07's
conditional assignment transport and G19's existing statement execution. An
actual Source block executes an effectful local-assignment guard, performs the
selected local assignment, then bare-returns. The typed code uses the existing
scoped branch and declares a fresh true return flag. It introduces no lowering
relation, Source evaluator, syntax, profile or refusal change.

`correct` retains eight initial propositions: full `ContextMap.Related`, Boolean
reflection and six exact map equations. These imply the actual Source fuel+6
run, typed run, full weakened reached map relation, captured true flag and
unchanged target globals. Branch donors read the state after the guard's write.
No desired-run, simulation, P8 producer or world adequacy premise is supplied.
The same statement still times out at zero resource.

[Controls](../../Solidity/Lowering/G19/ConditionalReturnControls.lean) cover both
pipelines, checked modes, arbitrary additional fuel and both branch choices.
The true arm changes the first caller local from false to true by reading the
condition local after its write; the false arm changes the original donor cell
from false to true. The ordered observation is fresh return flag, first caller
local, caller condition and caller donor: `[true,true,flag,true]`.

Negative controls reject a wrong branch donor, capturing the caller condition
instead of unconditional return after the false branch, and Source normal
completion instead of bare return. They compare actual Source/typed executions,
not only theorem names. The private branch-choice temporaries are scoped away
before the independent true return capture is introduced.

The initial wrong-flag proof exhausted the unchanged200000-heartbeat limit while
reducing the whole conditional program in `change`. Its raw failure is retained.
Factoring through the existing `ConditionalStatement.target_run` and actual join
equation preserves the same negative statement and fits the original budget.
Failed standard automation attempts also remain evidence; no heartbeat, node,
depth, fuel or process limit was raised. An unused simp argument was removed.
Both independent read-only reviewers checked the actual repair and controls.

All19 requested producer/component/control declarations retain complete exact
types, values and dependencies at100000nodes/depth512, actual standard-axiom sets
and mandatory full-record live replay. All19 printed axiom sets are guarded.
Focused checks use the existing serial12GiB/no-swap/300s wrapper, Lean -j1 and
LEAN_NUM_THREADS=1, with unchanged source/import/tool/object/settings bindings.
Parent execution plus final committed-byte binding is separate from a new-HEAD
full gate, clean-cache equivalence or public release claim. Final independent
finder/skeptic source/artifact reviews run no Lean/server/builds; their results
and raw exits/resources are retained in the external handoff.

This is a Source/typed component, not native EVM RETURN, function-exit dispatch,
general loop/modifier/constructor lowering, solc/Ethereum differential testing,
bytecode/gas adequacy or full-profile Source-to-EVM correctness. Native compiler
integration is separate. G19/G36.01, G54.02 and Backfills A/B remain partial.
G52/G54.01 remain H12-paused. G53 needs actual same-revision selected473da894
strict/corpus/TestSuite evidence; historical048a74de has no matching Lean binding.
Ten Derived17 structural values require their reserved owner's same-statement
smaller proof within100000nodes/512depth. G54.03/G55 await all original children
and final clean/cache/joint-import/executable/trust gates. All457 rows remain open.
SS-NEW/getters await VY5 H16/H19. Goal, ownership, pins and all budgets unchanged.
