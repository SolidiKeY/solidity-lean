# G19/G36 two reached-state suffixes through the actual compiler

The new `Solidity.Backend.StructuredFlow.ReturnPairCompiler.correct` composes
[the mapped Source component](../../Solidity/Lowering/G19/ReturnPair.lean) with
`Evm.prog_sim` over its actual `Evm.compileProg` output. Its eleven propositions
remain explicit: initial `ContextMap.Related`, Boolean reflection, six exact map
slots, native `Sim` entry, the actual fragment check, and stack capacity.
No representation, Source evaluator, target semantics or compiler is changed.

The theorem proves the actual Source fuel+8 run, typed run, full weakened map
relation, captured flag, unchanged globals and `Evm.StmtOut`. The second suffix
reads the state reached after the first suffix. It does not reset the caller's
condition to the captured value. Both generic fragment/capacity obligations are
proved for the inhabited fixture; they are not globally eliminated.

[Controls](../../Solidity/Backend/StructuredFlow/ReturnPairCompilerControls.lean)
cover both pipelines, all extra fuels and both Boolean outcomes. Their actual
compiled native snapshot, in order, is memory cells 0,1,2,3,5 followed by the
entire stack: `[1,1,!flag,flag,99,77]`. After guard evaluation, false fallthrough really changes both
caller cells from false to true while retaining the false private selector.
True returns skip both assignments. The canary and stack are preserved.
Typed and separate compiled-native negatives reject an omitted second assignment
and a second assignment that reads the stale donor. These are kernel proofs of
this abstract compiler's execution, not pinned solc/Ethereum differential tests.

The captured flag classifies Source return. This is not EVM RETURN emission,
function-exit dispatch, general modifiers/constructors, effectful expressions,
bytecode/gas adequacy, full-profile Source-to-EVM correctness or release closure.
The source fixture imports are reused read-only; no P8 inhabitant is presumed.

Validation uses the existing serial 12 GiB/no-swap/300s wrapper, Lean -j1 and
LEAN_NUM_THREADS=1. Full declarations include type, value, dependencies and
standard-axiom lists at the unchanged 100000-node/512-depth bounds, followed by
live replay. Automation attempts and raw per-file/metadata receipts are retained
externally. Native gates execute the parent plus final owned bytes; committed-byte
binding is checked separately and is not a new-HEAD/full gate claim.

Independent read-only finder/skeptic reviews first identified typed-only mutation
coverage and incomplete axiom-print coverage. Compiled-native negatives and pins
for every requested declaration address those findings; final reviews are retained
in the sealed handoff. No reviewer starts Lean or a server.

G19/G36.01 and Backfills A/B remain partial. G52/G54.01 remain H12-paused;
G53, G54.02, G54.03 and G55 require their original actual producer and final gates.
All 457 release rows and ten Derived17 full-value rows remain open. The latter
requires the reserved owner's same-statement proof-representation repair under
100000 nodes/512 depth. No persistent goal status, premise or budget changes.

The interrupted host structural attempt failed before checker execution: Node
could not initialize V8 within the Python parser's 512 MiB address-space cap.
The JIT-disabled probe also failed. Both raw failures are retained. The unchanged
published layer/orphan scripts subsequently passed using authenticated Node
inputs in the existing 12 GiB/no-swap/300s wrapper; no Lean proof was rerun.
