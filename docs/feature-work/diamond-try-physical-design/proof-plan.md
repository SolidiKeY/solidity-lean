# Proof dependency and implementation-decision plan

All new items are obligations/design, not axioms or installed semantics.

| Layer | Must prove constructively / nonvacuity gate | Existing API or exact missing prerequisite |
|---|---|---|
| P0 identity | Same original bytes, compiler binary/options and single invocation bind AST IDs, source maps, Yul, creation/runtime; whole f body and actual caller clauses. Actual source refs resolve to parameter/declaration, not spelling. | Retained ten artifact bundles; source recognition frontend above kernel. Existing metadata/reference hash match is evidence, not proof. |
| P1 typed bytes/ranges | Word-byte inverse, unaligned overwrite, frame preservation, zero-extension, zero-length no-access, natural end no wrap, snapshot length+immutability, copy bounds. Produce examples from operations, not expected vectors. | New pure representation; no existing byte-addressed primitive in word Machine. G46.02/R31 owns missing target byte operations. |
| P2 entry | Fresh external frame, actual compiled free word64=128, zero memory, dispatch/size ABI read and no prefix allocation in callee; caller heap not assumed empty. Construct at least one valid entry witness per pipeline, plus invalid-init counterexample. | Actual pinned prologues/AST; nonvacuous construction required. Word FreeMemory uses cell0 and cannot establish this. |
| P3 stores/slice | Exact ordered source stores produce all bytes at0..100; frame-visible heap unchanged, allocator/zero-slot facts invalidated or re-established correctly, n=0/small/large outcomes split. | typed-interface schemas; source stores no new operation semantics in this design increment. |
| P4 target/source | Relate the same actual bytecode entry/body/halts to P1–P3, with exact stack/operand/source-map frame and backend resource outcome. | Published G46.02 has modules=[] at fb379ae20f10e2c92113453ddd9d40d8f2efbe09; missing byte execution/simulation. Optional Bridge.ExternalEvm/WordOps arithmetic is not memory/gas/call proof. |
| P5 typed producer | Materialize computed immutable snapshot via existing typed bytes object, prove heap extension/new identity/old refs and exact THalt.ofData; n0 empty-data normalization. No proof premise simply assumes hcall. | State.allocPush, Grown, byteWord, TRun.litBytesT_alloc, RevPart.evalT_mem, TRun.revertData_mem. Synthetic allocation is witness only, not extra EVM call/cost. |
| P5b actual callee transport | Exact source resolution/closure binds f declaration, signature and typed body construction; actual Args/CallRet.enterT frame gives sigmaIn, producer halt transports to the original TRun.call halt without equating different Out contexts. No assumed desired hcall. | New BoundCalleeFrame/callee_halt_transport schema; current kernel carries body explicitly. P8 consumer must construct it; absent for current refused source. |
| P6 caller transports | Use actual hcall only after P5b, exact nonzero self, original self=true, no oracle replacement, decoded payload or exact rethrow, caller storage/heap rollback and normal handler scope/tail. | TRun.catchBytes_self_data, TRun.catchData_self_data, existing TryConditions witnesses and call-return bridge; same names/conditions preserved. |
| P7 decoder/result | For generated Error(offset32,len7) and Panic(code67) family, prove exact short/trailing dispatch at actual n. String handler/defaults include read-only shared zero-slot empty sentinel (distinct HRef identities, no physical allocation), actual interior copied-buffer object (msg=data+offset), auxiliary prefix, guard-failure scratch effects, final cursor and default zero-slot string; return ABI order/identity correct. | RevertBytes.decodeError, approved Semantics.decodePanic, AllocBytes/catchData/CallRet.mem and existing scalar return transport. No global Error decoder parity claim (pinned helper has uint64 checks). |
| P8 source automation | Whole source import retains exact unsupported/refused shapes; certificate consumer cannot replace body with assumed bytes; both original pipelines/all ordered observations before status improvement. | Current Body.memoryRethrow? only canonical rethrow, directSelfTryContext rejects these stores. This is an explicit source-admission/policy integration gate, not authorized by design approval or producer-only proof. D3/targets stay unchanged until separate reviewed decision. |

G46.02 published scope: MLOAD/MSTORE/MSTORE8 byte memory, calldata operations,
expansion/resources and RETURN/REVERT ranges. No unmerged implementation imported.
Current task owns narrow five-row shape/source identity, producer witnesses and
catch/return composition; physical byte backend/simulation belongs to G46.02;
optional independent external bridge owns its backend semantics. Existing
reference/ABI lane for invalid_error_encoding is excluded from these five and
is NOT a prerequisite fabricated into this plan. Scalar size arguments use
existing intrinsic Args/ExtCall; no lazy/noncanonical external reference inputs.

## Total outcome / timing ledger

- Caller argument evaluation fails before call: no callee frame or constructor/
  catch handler consumes it. Preserve exact original caller halt/timing.
- Wrong receiver0, missing code, wrong declaration/ABI/selector/value check:
  current caller/callee failure meaning unchanged; no EntryWitness for raw body.
  Refused certificate is not a modeled revert or successful source replay.
- Body entry with initialized frame and feasible memory: store sequence has no
  normal continuation past its terminal revert. Snapshot actual n bytes first,
  then callee frame discarded; data survives caller rollback.
- n0/n3/n6/n35/n36/... must follow exact byte prefix/truncation. n may be any
  uint in the original function. Capacity K is a proof witness, not global n≤256.
  Larger/overflowing/end-above-word requests must remain represented in coverage
  accounting; absence of a range/resource certificate is unknown/refused, not
  arbitrary ordinary revert. No target narrowed to fixture n values.
- Physical memory expansion OOG/stack/invalid and host5M/120s stops are target
  outcomes, not automatically THalt.revert or THalt.exhausted. Any correspondence
  to legacy THalt needs an explicit approved theorem/decision; source-call success
  cannot arise from such stops. Divergence and abstract exhaustion remain distinct.
- Decode failure goes to original raw catch or exact uncaught bytes; decode success
  runs original handler, never catches its subsequent failure. c/d Panic return67
  skips the trailing assert(false) in _2/_3; a/b short failures rethrow before it.
  Caller string defaults/allocations and raw bytes remain in exact original order.
- Legacy callback universal reading remains: actual deterministic witness does
  not prove holdsC/ValidT. Optional callback alternative may use computed d only
  through existing callback APIs; caller-revert/callback counterexamples remain.

## Bounded first milestone versus full release

**M1 implementation proposal, not authorization:** one exact
malformed_panic.sol `c()`→f(0x24), both original compiler pipelines. Deliver whole
bundle/shape identity certificate, fresh-frame/scratch byte representation,
store0/store4/snapshot36 laws, computed bytes-to-typed-object producer-halt certificate (NOT actual-source hcall),
constructed-call Panic binding67/storage/scope/return transport and wrong-init/order/type/
identity controls. This fills the missing *producer component* attached to an
original row, not another arbitrary oracle/decoder helper. It must expose P4 as
an explicit target-byte correspondence obligation with a named producer; no
assumed hcall or abstract never-inhabited EntryWitness counts as completion.
It may be completed as proof-only source-linked certificates while native
admission remains refused; then native original row is STILL BLOCKED, not passed.
To claim an end-to-end native source row M1 additionally needs authorized P4/P5b/P8,
actual both-pipeline replay and all literal observations. Do not silently grant
that admission from a proof-only milestone or this design decision.

First M1 stress controls: same source row d(256) as a *producer-only control*
for preserved word64, n0/35/36/37, wrong free word and alias/frame; original c row
only contributes its actual observation. If cost stops at256, factor word/slice
lemmas rather than raise recursion/heartbeat/fuel/node/test limits.

**M2 after same proof generalization:** original panic a/b/c/d, _2/_3 caught/
uncaught variants, _4 a/b/c plus declared but unobserved d. No extra d observation
is invented for _4. Keep all21calls/pipeline (42total across five files) in
frozen order; any extra synthetic control is separately labeled.

**M3:** Error's four overlapping stores, corrupted allocator protocol, sizes
3/6/67/74/75/256, actual Error payload catch allocation, default empty b3 string
and c/d seven-byte return encoding. General raw ranges/alias/frame preservation
and all ordinary/refusal/resource cases accounted. No general ABI/assembly release.

Full implementation readiness requires P0–P8 and total ledger, standard-only
axiom audits, independent review and source policy approval. Generic D3 remains
excluded; no inTarget/gap certificate/expected verdict change authorized here.

## Checking cost and resource gate (estimates, not measurements)

Historical evidence: 2f41a68a moved Path/MObj to recursors with match twins;
77c6e047 applied recursor kernel reduction; cbecb7aa speed merge preserves costly
certificate strategy; 2fbada13 Fml.grow avoids rebuilding preserved heap content.
GateG0 records 11–13× indexed-match cost and1.7× casesOn versus linked recursor
form, plus prohibitive historical indexed-heap ideas. This design deliberately
does NOT index every State/Fml/Stmt by a physical layout or introduce Nat labels
in Γ, change existing heap identity, or migrate word Machine. FrameMem keeps
State as a field, H as existing State field, with layout proofs in side witness;
only C/Γ and bounded leaf-address/typed refs are intrinsic structural parameters.

Proposed hot functions use recursors on indexed cases and ordinary recursion on
plain byte lists/finite spans, factoring32byte word lemmas and snapshot extension.
Any implemented_by twin needs its equality theorem before use; no trusted eval.
No recursive raw AST evaluator. Prefer named opaque/general rewrite lemmas over
256-byte rfl normalization (the retained earlier maxRecDepth failure is evidence).
Any later layout-index refactor needs prior speed warning/history review.

Planning estimates only: M1 perhaps8–15small algebra/frame/capture lemmas plus
source/byte correspondence modules; per-file checks seconds–minutes,2–6GiB,
M2/M3 cumulative footprint uncertain. No guarantee these fit is claimed. Hard
stop remains whole-group12GiB/zero swap, one heavy group, disk caches, OS headroom,
LEAN_NUM_THREADS1/explicit Lean-j1, unchanged Lean/fixture budgets. Full required
confirmation may approach the retained12,176,072,704byte peak; factor/dependency
repair or report blocked on resource stop, never increase it. No new compiler/
engine/Lean run is used to validate these estimates in the design increment.


## Proposed acyclic module/ownership layout (names only, not files added)

Semantics.State/RevertBytes → proposed Solidity.Evm.TryByteImage →
TryByteOps → TryByteProducer (existing AllocBytes/RevertMemory consumer imports).
TryByteCorrespondence depends on these plus a genuinely proved G46.02 byte-step
interface; optional external-backend instantiation stays under Bridge, never a
core dependency. Frontend.TryByteCertificate depends downward on typed producer/
correspondence and existing frontend source/JSON readers. Examples/proof audits
sit above that. Core cannot import the frontend/elaborator or optional external
EVM package. Register new modules/import edges in owning roots/module-map only
if implementation is later authorized; none is added now.

Kernel BundleKey stores literal code/source identity and intrinsic typed plan
operands, not a runtime untyped JSON statement. Full compiler input/output JSON,
process invocation receipt and same-invocation capture record remain frontend/
external provenance. Kernel checks structural bytes/typed certificates; it does
not magically prove a C++ solc process correct or SHA injective. A restricted
source/AST/compiled-step theorem is required before upgrading the claim.

No new taclet syntax or invented SolKey assembly rule. Reuse current try/catch/
frame/catchData rule names/shapes/side conditions and matching dl/tm printers.
No @custom:key box or changed fixture annotation is a substitute for P5b/P8;
universal callback diamond counterexamples and all original refusals remain.
