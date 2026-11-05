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

## H41 cache custody and source-reader observation backfill

Separate read-only finder/skeptic reviews used no Lean/server or verifier runs.
They verified57 distinct modern kinds per suite:37standalone entrypoint witnesses
and20syntax kinds with no standalone entrypoint (not all are mere metadata).
Existing-fixture outcomes are11decoded/26refused; freshly compiled outcomes are
14decoded/23refused. Both record37unknown-root refusals. Each has14producer
expression attempts: existing11printed/3refused, fresh9printed/5refused. Different
suite outcomes use different selected nodes and are not same-input regressions.

All8fresh output hashes match their compilation receipts; exact0.8.34/0.8.38
binary/source anchors were checked. Driver uses only existing Shared APIs and
existing producer expression printing; no new translator/IR. Whole subtree
refusals may come from children; decoded/printed is not intrinsic/source/backend
support. Capture is an observation step, not a semantic oracle; independent
identity preflight, frozen noncapture MCP and all12 per-file gates subsequently
passed. Initial excluded-Gap exhaustiveness and reserved-variable syntax errors
in the new test were fixed, with failed logs retained. No source sorry was added.

H41 custody evidence correctly attributes coordinator receipt/SHA verification
to the user message and leaves host receipt unread locally and installation
unverified. H35-CACHE is resolved. No VM ship-cache invocation followed H41.
Four owned source/trace mappings remain those of the received pack. Full lane
adoption, source proofs and runtime closure remain open.

## Composed readers and scoped obligation preparation

Independent read-only finder and skeptic used no Lean/server. No confirmed code
defect remained. Finder identified a stale AxiomInventory comment claiming no new
theorems; corrected to explicitly name the three numerical freshness proofs.
Both confirmed gate evidence:344jobs,14per-file gates,two MCP diagnostics,exit0.
Callback receives renamed syntax; bounds and finite samples are not source
preservation. Producer migration/native-WASM closure/full parity remain open.

## Post-f77 adoption, ledger and H41 cache delta

Independent finder and skeptic reviewed the final owned packet read-only, without
Lean/server execution. Neither found a material defect. Both checked the closure
ledger limits,12composed cases,post-adoption exit0 evidence and six-module cache
mapping/archive verification. Delivery remains coordinator-pending; dependencies,
CR migration,native/WASM closure and full gates remain explicit open obligations.

Final handoff finder/skeptic confirmed actual KeySort377/131/131 and partial
blocker claims. Both identified checkpoint-accounting ambiguity: original queue2
is partial until existing tooling migration/native adoption; concrete API publication
is only a done subtask. Machine report corrected accordingly. No other finding.


## Published9584 and composed57-kind controls

Independent read-only finder/skeptic,no Lean/server,no writes. No confirmed defect
in generalized Reader driver,default frozen capture protection,comparison generator
or inventory. Both checked six exact differences: four existing refusal-reason
changes and two fresh decoded witnesses. Both checked57keys,37unknown-root refusals,
producer printing unchanged and source hashes. Frozen gate/MCP exit0; whole-witness
and child-failure limits retained. Producer migration/native closure remain open.

Final adoption9584 packet finder/skeptic found no material claim defect. Both
confirmed Scope central registration,Compose proposal,fresh KeySort377/131/131,
six-module cache local verification/coordinator-pending status and retained CR/
metadata/native obligations. Their minor historical registration wording ambiguity
was corrected in API-HANDOFF and lane docs. No Lean/server or writes by reviewers.


## Publishedb86 and trusted checker observations

Independent read-only finder/skeptic,no Lean/server/writes,confirmed exact published
comment-only correction and cache byte-delivery attribution. Both found no defect
in DirectResultControls or its claims:actual public checks without listing,diamond
and identity/provenance guards,4proved/4pending/4unsupported. Frozen MCP/per-file
PASS;pending is not refuted and no proof-term/source/native closure claim follows.
No remaining material finding. CR/metadata/runtime obligations remain pending.

Final b86 gate/cache packet finder/skeptic found no material conflation:old047
byte-delivered versus neweb91 locally verified/coordinator-pending;actual bounded
resource and KeySort evidence;source bindings versus native closure. Skeptic noted
stale future-tense cache wording;API-HANDOFF now records completed verification
and current receipt. Neither used Lean/server or wrote files.


## Published8bf and paired modal backfill

Read-only finder/skeptic,no Lean/server/writes,found no confirmed control or
provenance defect. Six source/compiler/AST identities and three identical body-byte
pairs support regression intent;canonical typed/public tags are checked separately.
Frozen MCP/per-file exit0. Three proved/three refuted are trusted model results;
preflight checks counterexample presence,not independent validity/replay. Source/
Lean proof/native preservation and original complex pending cases remain open.

Final raw/provenance packet finder/skeptic found no material defect. Raw and
normalized function IDs/source spans are joined;gated fixture remained byte-identical.
Both confirmed explicit counterexample-presence-only limits,IR-selector versus CR
migration distinction,and preservation of older pending cases/original obligations.

Final8bf resource/KeySort/cache/source-binding finder/skeptic found no claim defect.
Currenteb91 local verification/coordinator-pending delivery is separate from old047
user-reported byte delivery. Provenance is not migration/source preservation/native
closure or RUNTIME_GATE_PASS. Neither used Lean/server or wrote files.


## Published3ad native producer validation

Read-only finder/skeptic,no Lean/server/writes,confirmed safe adoption/existing
unchanged producer script/local prefix policy. Final binary18exact saved outcomes+
2fail-closed controls pass;source/trace/dynlib checks are finite-input provenance.
Both reviewed all14frontend-origin candidates:6linked empty IO-unit initializers
with heartbeat/alloc/OOM handling;8generic JSON,array,string,list,option helpers.
No actual frontend functionality among those14;no policy exception assumed. They
explicitly did NOT certify exhaustive closure for all206modules/full binary.
Resource stop and missing-cc failures are preserved;retry used same limits/reserve
and existing supported CC override. Older source/WASM/migration goals stay open.


Mandatede684 rebase preserved code/WIP;17commits replayed,autostash applied and
three merge-only evidence blobs restored exactly. Post-fix rebased build/axioms/
controls/native18+2/ownership gate exit0. Initial stale-baseline failure retained.


Final packet/rebase finder/skeptic independently checked e684 ancestry and3restored
historical blobs,actual post-rebase exit0 and38-member archive verification. No
material defect found. Native evidence remains18comparisons+2failclosed+14reviewed
candidate bodies;not exhaustive closure,WASM,source preservation or CR migration.
Neither reviewer used Lean/server or wrote files.

Final post-rebase metadata finder/skeptic found no material defect;source/cache/native
identities and pending closure/migration limits are accurate. Skeptic requested
quota/period separator in cpu.max prose;corrected to100000 100000. No Lean/server.


## Published708 adoption review

Independent read-only finder/skeptic confirmed1d8e ancestor708 and zero owned-file
committed differences. Local gate exit0 covers build/axioms/modal/direct/native/
ownership. These are checkpoint compatibility checks,not migration/exhaustive
closure or original-goal completion. Neither used Lean/server or wrote files.

Final708cache/source metadata finder/skeptic found no claim defect. Cache identity,
KeySort/resource evidence and immutable native packet limits are accurate. CR
migration/DR-A-META and remaining native/WASM/source/final obligations stay open.
Neither used Lean/server or wrote files.


## Published1ae durable audit review

Finder/skeptic read-only,no Lean/server/writes. No confirmed guard defect:unique
common ancestor excludes unpublished local work;ambiguous/out-of-base ancestry
fails closed. Caller authorization and fetched ref integrity are prerequisites.
Audit checks current tree differences,not every historical edit. Original pinned
source/proof checks remain unchanged. Rebase receipt correctly distinguishes
source-equivalent cherry-picks from old commit ancestry.

Final1ae metadata finder/skeptic confirmed the ahead-of-publication baseline,
current cache/source fingerprints,KeySort metrics and honest delivery/native
limits. No material finding;no Lean/server/writes. CR and original final gates
remain blocked/open,not completed by these compatibility checks.
