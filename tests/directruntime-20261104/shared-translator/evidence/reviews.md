# Independent read-only reviews

Finder and skeptic ran as separate agents; neither used Lean or the server.

Finder: extraction preserves 252 string literals in sequence, unchanged helper
bodies and intended callback substitutions. Every nested expression/type/statement
uses its callback, including falseBody. No duplicate reader remains in DirectRuntime.
Caveat: an isolated Reader.expression update does not reconnect Reader.statements.
ReaderControls pins both the disconnected case and recursive step composition.

Skeptic: Shared must not import Testing/Import (cycle). The extracted Shared local
closure is 17 modules, neither Import nor Testing. H1 must monitor outer cgroup
reserve actively; outer_guard now does. LeanTeX lacked -j1; alternate config fixed.
Docker-stop failure must not abandon monitoring; bounded cleanup now handles it.
Native/WASM builders use absolute prefix/bin/lake, bypassing PATH: still pending.

Initial finder counts were corrected by a machine comparison against pinned
compiler ASTJsonExporter.cpp: 58 Solidity JSON node kinds, 16 Yul kinds and
42 RawStmt constructors. The full catalog contains 212 feature entries.

These are preparatory reader reviews, not full assignment acceptance. Full
producer migration, fixture parity/refusals, intrinsic bridge, B/C integrations,
compiled closure/native/WASM gates and final independent reviews remain open.

Final preparatory skeptic review: no confirmed blocker to committing a partial packet. Baseline copy, source hashes, 252 strings, 17-module closure and fixture/exporter provenance independently rechecked. Finder independently corrected counts to 58 Solidity kinds and 42 RawStmt constructors. Neither review establishes full checkpoint completion.

Finder inventory correction: initial per-node feature mapping missed helper-produced pragma/builtin/magic-member alternatives. inventory.py now unions those helper branches conservatively and labels the mapping conditional. Raw mappings now include byte-literal call encoding and function-tag RawTy.named. Full per-form semantic/backend validation remains pending.

Finder final raw mapping correction: RevertStatement names custom-error RawStmt.revertErr; bare RawStmt.revert belongs to builtin FunctionCall lowering. The table marks subtype mappings as examples pending full per-form controls.

## Intrinsic extraction review

Separate finder and skeptic, read-only and no Lean/server, found no implementation
regression. Both producer callbacks are pinned exactly; the assertion body differs
only by callback substitution and a new intrinsic reference guard. This guard
preserves the already-refused default AST fragment and prevents premature reference
input adoption with incorrect diamond binders. Return refusal retains priority.
Specified dispatch still calls existing specObligation. Intrinsic local closure is
104 modules with no other Frontend module. Proof-search and exported wrapper are
unchanged. Arbitrary callbacks are not source-soundness certificates.

Finder's audit issue was fixed with a conservative token scan covering inline
sorry/private axiom forms; this remains source inspection, not a transitive axiom
audit. Skeptic's documentation correction was applied. Full DirectRuntime checking,
producer migration/parity, CR/B/C exact commits and native/WASM gates remain pending.

## Whole-root metadata refusal review

Finder and skeptic independently found two holes in the first uncommitted guard
prototype: nested metadata could be hidden by constant folding, and a per-node
refusal could preempt an old later-sibling error. That prototype was superseded.
The final implementation restores every legacy decoder/recursive call byte-for-
byte (apart from private function/contract decoder names), then runs one existing
J.nodes metadata walk after whole-root success. No second translator is added.

Both reviewers confirmed the folded-child and global root-priority holes closed.
Contract validation skips sibling function bodies. Their requested explicit
malformed-function sibling controls were added and passed. The 38 parity controls
include whole-function later-sibling refusal, folded alias/bool cases, existing
constant-kind diagnostics, valid primitive behavior and explicit producer gaps.
Raw Reader callbacks are decoders; checkedExpression/checkedStatements and public
function/contract wrappers apply metadata admission. Reader signatures are frozen.

Aliases remain refused even if a future custom Reader could resolve them. Full CR
migration must supply declaration-aware operator support; these controls do not
prove full producer diagnostic category/line parity or Admission.scan equivalence.

The component benchmark initially failed due a helper named measure colliding
with Lean; it was renamed and diagnostics passed. No source proof placeholder or
#eval! was added. Skeptic reviewed the final benchmark: identical indexed inputs,
serial alternating samples, all20000 calls checked, substantial timing variability.
Report ranges/samples, never a stable overhead factor or native/WASM gate result.
