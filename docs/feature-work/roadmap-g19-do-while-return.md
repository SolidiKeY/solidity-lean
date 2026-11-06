# G19 context-related do-while assignment followed by bare return

The target program is hand-written. Context mapping relates its locals to Source locals; it does not establish a generated lowering endpoint.

[The new component](../../Solidity/Lowering/G19/AssignmentDoWhileReturn.lean)
extends V07's existing `ContextMap` and assignment operand. Its actual Source
body assigns one Boolean local from another, then bare-returns. The do-while
therefore propagates return without evaluating its arbitrary trailing condition.
No Source semantics, type, profile, refusal or resource carrier is changed.

`correct` retains six initial propositions: `ContextMap.Related`, Boolean
reflection, two slot type equalities and two exact map equations. They imply
the actual Source fuel+6 result, typed target run, full weakened map relation,
a fresh true return flag and unchanged target globals. No desired execution,
P8 inhabitant, world relation or simulation premise is supplied. Target slots
come from the map. The existing capture of the assigned Boolean is overwritten
only in the fresh slot: a false-valued assignment must still capture return true.

[Controls](../../Solidity/Lowering/G19/AssignmentDoWhileReturnControls.lean)
cover both pipelines, both checked modes, arbitrary additional fuel and both
Boolean body values. The body genuinely changes its destination in either
fixture. The complete ordered typed observation is fresh flag, assigned caller
local, donor and the remaining caller local: `[true,flag,flag,!flag]`.
Same-slot assignment is also checked. Negative controls reject using the assigned
false value as the return flag, erroneously evaluating an effectful trailing
condition, and misclassifying Source return as normal completion. A separate
positive evaluator equation establishes that the skipped condition really writes.
The exact statement still times out at zero resource.

This proves one non-recursing do-while shape because the body immediately returns;
the fuel offset is an evaluator cost, not an admitted-source unrolling limit.
This is not arbitrary loop/modifier/constructor lowering, native EVM RETURN,
solc/Ethereum differential agreement, bytecode/gas adequacy or whole-profile
Source-to-EVM correctness. The complete concrete compiler adapter is separate.

Standard automation closed the target equation by `rfl`. The failed standard
composition attempt is retained; the remaining proof uses the actual Source
run and V07 `ContextMap.related_assign`. All15 declarations have full structural
types, values and dependencies extracted and live-replayed at100000nodes/depth512;
all actual standard-axiom lists are guarded in the scoped test. Validation uses
the existing serial12GiB/no-swap/300s wrapper, Lean -j1/LEAN_NUM_THREADS=1.
Checks execute parent plus final owned bytes, followed by exact committed-byte
binding; this is not a new-HEAD full gate or clean/cache equivalence claim.

Independent read-only finder/skeptic reviews inspect the actual proofs, premises,
nontrivial controls, raw extraction/replay, scoped pins and sealed handoff without
Lean/server/builds. Full review results and raw commands/exits/resources remain
in the external checkpoint. H1 cleanup removes only byte-identical mutable
records verified against unchanged sealed archives.

G19/G36.01, G54.02 and Backfills A/B remain partial. G52/G54.01 remain H12-paused.
G53 needs actual same-revision selected473da894 strict/corpus/TestSuite evidence;
historical048a74de lacks matching Lean revision. Ten Derived17 structural values
still need their reserved owner's same-statement repair within100000nodes/512depth.
G54.03/G55 await all original prior children and clean/cache/joint/trust gates.
All457 release rows remain open. SS-NEW/getters await VY5 H16/H19; no goal status,
semantic premise, ownership, pin, budget, push or master merge changes.
