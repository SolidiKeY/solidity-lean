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

Finder backfill correction: conditional features appended in Admission.walk are now included: canonicalRethrow, operatorAliases, fixedPoint/commonType and payment-context emptyDataValueCall. They are conditional alternatives, not support claims. Existing fixture subvariants are indexed separately without execution/proof inference.

## Root, request, header and coverage checkpoint

Separate finder and skeptic reviewed the actual source and fixtures read-only,
without Lean/server calls. Findings fixed: missing root tags; malformed selectors
being treated as absent; malformed/nonpositive function IDs escaping duplicate
checking; missing expression type, unary prefix and binary common-type metadata
(including folded descendants). Global function-header identity validation is
separate from skipping unsupported sibling bodies. Legacy decoding/refusal
priority and Reader signatures remain unchanged. Finder also caught a new test's
BinOp.eq typo (fixed to eqB) and omitted stepSound_arms inventory reference.
MCP caught an ambiguous Name annotation (fixed to Lean.Name). No source proof
admissions were added; generated elaborator-error admissions in the first failed
MCP run are not passing evidence. All eight corrected per-file MCP checks and
nine repository per-file gates passed. Both final reviews found no further
confirmed blocker for this increment.

This is bounded refusal/inventory validation, not full producer admission,
AST/Raw source preservation, or backend/runtime closure. Signed int complement
remains a demonstrated raw-success/intrinsic-refusal normalization gap. Complete
CR/B/C adoption, exact theorem/axiom signatures and final full gates remain open.

## H35 inventory and cache packet review

Independent finder and skeptic reviewed read-only without Lean/server use. All32
explicit public Shared declarations plus2runtime entrypoints are inventoried.
Exact-base validation copy preserves git-show source and only appends inspection
commands. Current/base runtime axiom sets match; no new observed axiom or sorryAx.
Partial definitions are opaque to logical axiom traversal: executable closure
and source preservation do not follow. Eleven VM per-file gates and the fresh
340-job owned build passed. The initial Lake version probe failed before build
and its corrected invocation passed.

Both reviewers required strict separation of ship-cache exit1 (missing coordinator
routing, no transfer) from local archive verification. Initial receipt mapping
counts/hardcoded metadata limits were strengthened: mapping schemas/prefix refs
and4owned trace mappings are now checked; exit/failure/toolchain come from gate
logs. Full archive+mapping recheck passed. Final independent reviews found no
further verifier defect. Source-hash/trace freshness relies on the recorded
build, not on colocating hashes in a receipt. Local consistency proves neither
delivery, installed-cache compatibility nor executable closure. H35-CACHE remains
pending and no H35 checkpoint completion is claimed.
