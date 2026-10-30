# Original f(size) source construction after the closed carrier

Design only, based on clean a67fa5d8eea431d2363b023b0dd3654d440bfb4c.
The human complete-design approval authorizes this proposal, not its implementation.
The accepted carrier/runner turn01a18d6c-0aa1-7582-ba2d-f6b7780ab8ae is not replayed.
Native12working/8blocked strictEXIT1 remains a failed original-assignment gate.
This supersedes ONLY the future-carrier/source-proposal portions of the
[c36 design](diamond-try-c36-path-design.md) and
[post-M1 design](diamond-try-post-m1-design.md). Their compiler maps, receipts,
refusals, failures and complete original obligations remain retained evidence.
The completed modern runner and Cancun gates are not rerun here.

## Exact source and current consumer boundary

The source is the unchanged upstream semanticTests/tryCatch/malformed_panic.sol,
SHA256522bfa3512517476f4f06cef823b176afe52978eb52393b25783e30d10ccc311.
Both retained original.sol ASTs have SourceUnit141, ownerC140, f7/body6/assembly5,
parameter2 (uint256, scope7), empty returnParameters4. The complete declaration
is public pure f(uint256), selectorb3de648b, span17:216:0. Its ONLY Solidity body
statement is assembly5 (61:166:0), with EXACTLY these ordered Yul expressions:

1. mstore(0,selectorWord), source84:77:0; operand is the original full32-byte
   selector word at94:66:0, not bytes copied from a reference execution.
2. mstore(4,0x43), source174:15:0. This overwrites bytes4..31 of the first store.
3. revert(0,size), source202:15:0. Identifier212:4:0 resolves through assembly's
   single externalReference to parameter2, valueSize1, isSlot=false/isOffset=false.

No extra statements, modifiers, assembly functions, hidden prefix or suffix may
be ignored by a constructor. Prologue mstore(64,128) is NOT one of these source
statements: it belongs to the compiled fresh-frame entry obligation P4/P2.

Caller c105/body104 has no parameters, hidden return74 in returnParameters75.
Its whole body is Try103: Call79/Member77->f7/this76, literal78 value0x24;
clauses in order success85 (assertfalse), Panic96 (binder87:uint, asserttrue,
Return94/Identifier93->87/functionReturnParameters75), catchall102 (assertfalse).
The callee parameter2, caller return74 and handler binder87 are distinct bindings,
although their scalar LTy can be identical. There is no synthetic extra Error
clause in the source. An intrinsic lowering may need an explicit missing-Error
propagation arm; its construction must follow the existing frontend convention.

[Exact bundle keys](diamond-try-c36-path/bundle-identities.json) retain full inputs,
outputs, code and source maps. Compiler0.8.38+1835d247 has binary SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390;
Osaka, optimizerfalse/runs200, appendCBORfalse. Legacy inputf6b4902e/outputd8dd8061,
runtimee335ea9f; viaIR input03fab305/output94f13db8/runtimefaf0d962 are DISTINCT.
Full hashes/whole selected nodes and input settings are copied to the new
external evidence account; no hash injectivity or emitted-code correctness is
inferred. Same AST structure does not identify different code bundles.

Current rejection has TWO independent producers/consumers. In
[Body.lean](../../Solidity/Frontend/SolcJson/Body.lean), memoryRethrow? requires a
singleton Yul statement revert(add(data,32),mload(data)), two matching external
references to a bytes-memory declaration. Original f has three statements and
one uint reference. stmt1's InlineAssembly branch therefore reports
"assembly other than revert(add(data, 32), mload(data))". Admission also classifies
this as unsupported assembly. Separately
[self-try-adapter.mjs](../../scripts/self-try-adapter.mjs) directSelfTryContext
with referenceOnly=false refuses InlineAssembly; solidity-upstream.mjs cannot
obtain the native host context. referenceOnly=true is a reference-runner path,
not a source proof or permission to bypass either refusal. P8 keeps BOTH intact.

## Actual intrinsic APIs now available

All signatures in this section are existing Lean, with implicit universes and
some namespace parameters abbreviated. Exact headers/hashes are retained in the
external evidence. Source metadata uses existing SourceFunction, FunDecl.sourceDecl
and SolcFun.sourceDecl; no second name-only declaration table is proposed.

```text
Input = [.val .uint]; sizeSlot : Idx Input (.val .uint) = .here
State C Gamma; TEnv C sigma.H Gamma
Out C H Delta = { st : State C Delta, ext : H <+: st.H }
TStep C Gamma Delta = (sigma : State C Gamma) -> TRes (Out C sigma.H Delta)
Args.evalT sigma : Args C Gamma ps -> TRes (TEnv C sigma.H ps)
CallRet.enterT (ret : CallRet Gamma rs Gamma') (tau : State C ps)
  : Out C tau.H (rs ++ ps)
Prog C Gamma Delta; Prog.run sigma P = P.runR sigma

TryPanicCarrier.carrier36 : Prog C Input Input
carrier36_halt (tau : State C Input) :
  Prog.run tau carrier36 = .error (THalt.ofData computed36)
args36 : Args C Gamma Input
args36_eval sigma : Args.evalT sigma args36 = .ok (size36,())
empty_entry sigma :
  CallRet.enterT (.rets .nil) (sigma.withEnv (size36,())) =
    <sigma.withEnv (size36,()), List.prefix_refl _>
call_halt sigma : TRun.call args36 (.rets .nil) .refl carrier36.runR sigma
  = .error (THalt.ofData computed36)
catch_halt sigma (hnz : sigma.tx.selfAddress.val != 0) :
  TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true sigma
  = .ok computed36
Examples.Tactics.TryPanicCarrier.normal_return i sigma hnz :
  normalTry i sigma = .ok <sigma.setLocal i codeWord, List.prefix_refl _>
```

These are actual closed constructed-body facts, not missing laws. M1 provides
produced_computed, certifiedProducer_exact, computed36_decode and image_frame;
its bounded FrameMem96 initialization is CONSTRUCTED. State.allocPush/litBytes
allocates a logical ghost object, reads that actual object and halts; its failure
carries immutable bytes. No physical allocation or gas cost is added to f.
call_at_halt intentionally works at6 and every other uint for the constant body.
That theorem is an essential control against calling carrier36 the generic f.
normal_return writes a caller slot and drops handler scope with EXACT Out/Ext;
it does not represent a source Return control token or prove original Return94.

## First missing law: constructive generic source-body derivation

There is no current source-body execution judgment for this refused assembly,
and no existing API `Source.run f7` to which an equation can be proved. Prog has
no byte-addressed physical-frame store/slice primitive. Its typed object memory
has no canonical physical addresses or implicit free-pointer word. Equal logical
states can accompany different scratch images; e.g. same H/env/tx with different
byte4 changes the 36-byte revert slice until actual initialization/stores are
established. This is a representation boundary, not a proof that Prog is
computationally incapable of calculating a byte list with ordinary loops.
Writing such a loop would still need the missing source interpretation/resource
correspondence and could introduce unrelated fuel/allocation behavior.

A raw AST recognizer can check whole nodes and return a typed StorePlan. It
cannot prove source semantic adequacy merely by returning that plan. Conversely,
a record with `originalAtCall`, `hcall`, finalbytes, or body=carrier36 ASSUMED
as a field only hides the missing theorem. The following proposed indexed
derivation makes the new boundary explicit. ALL new identifiers below are
DESIGN PSEUDOCODE, not declarations, accepted evidence or installed semantics.

### One bounded proposal: generic declaration derivation, local36 reduction

The proposal is a proof-side straight-line source derivation for this exact
three-operation body, with a generic parameter and a conditional finite-frame
interpretation. It does NOT extend Stmt/Prog or install a frontend consumer.
It requires later approval even if kept in new proof-only modules.

```text
-- Frontend boundary: actual immutable raw nodes are provenance indices ONLY.
-- They are never an untyped runtime environment/state/value representation.
ResolvedDecl b owner decl ps rs
  -- derives from full sourceUnit/contract member lookup, existing SourceFunction,
  -- exact complete declaration, visibility/mutability/parameters/returns/modifiers
ResolvedLocal resolution param2 : Idx Input (.val .uint)   -- result .here

-- Core proof-side operands stay intrinsic:
WordStore C Gamma := (offset : U256, value : Val C Gamma .uint)
Terminal C Gamma := (offset : U256, length : Val C Gamma .uint)
-- A fixed ordered tuple, NOT arbitrary Yul or a new instruction evaluator:
ThreeOp C Gamma := (first : WordStore C Gamma,
                    second : WordStore C Gamma, terminal : Terminal C Gamma)
originalOps : ThreeOp C Input :=
  ((0,lit selectorWord), (4,lit codeWord), (0,local sizeSlot))

-- Frontend-owned evidence constructors, result indexed by the typed operands:
DerivesStore resolved (exact mstore-expression) 0 (lit selectorWord)
DerivesStore resolved (exact mstore-expression) 4 (lit codeWord)
DerivesTerminal resolved (exact revert-expression) 0 (local sizeSlot)
DerivesWholeF b C resolved originalOps
  -- sole applicable constructor consumes the complete f7/body6/assembly5 list,
  -- exactly the three preceding derivations, resolution of externalReference2,
  -- empty returns/modifiers and exact declaration metadata. NO outcome field.

DerivesWholeC36 b C Gamma return74 args36 selfCall
  -- separate constructor consumes complete c105/body104/try103 and ordered
  -- clauses85/96/102, member77 owner140->7, this76 and literal78;
  -- binds Return94 to parameters75/slot74, identifier93 to binder87.
  -- no inlined-body equality or success outcome is supplied by the constructor.
```

The source resolution proofs must check exact whole AST values, not only IDs,
spans, names, hashes or a claimed enum. IDs are bundle/source-unit scoped.
Parameter resolution returns a typed Idx and proves its declaration association;
local labels remain outside Ctx indices (GateG0). Numeric literal elaboration
proves range and value; `local sizeSlot` remains generic. Parent membership and
source declaration order are constructed from the complete owner node. A
frontend proof may use Lean Json as external parser data, but core witnesses
carry intrinsic operands and resolution evidence, never an erased execution AST.
The original f source does NOT contain prologue64=128: DerivesWholeF must not
invent that source statement or assume physical memory is initially initialized.

The core plan contains ONLY intrinsic operands; the frontend derivation is
indexed by raw source nodes and the resulting core plan. Combined source/plan
reduction theorems live in frontend, importing core one-way. Core BodyCompletedAt
must not refer to DerivesWholeF, BundleKey source AST, Json or source resolution.
The first genuinely new theorem would be `deriveWholeF_operands_sound`: inversion
of this structural derivation reconstructs EXACT source operations, typed local
resolution and preserved generic size, with no skipped statements. It is not a
source-to-Prog semantic theorem. Its input must actually be constructed from each
of the two retained full declarations; no axiomatized certificate parameter.

The next new interpretation/reduction obligation is also explicit:

```text
-- Existing FrameMem already carries arbitrary capacity as a FIELD.
-- Generalize only M1 fresh/entry/image helpers currently specialized to96;
-- use FrameMem C Input with capacity=K, NOT new State/FrameMem indices.
-- Shape/proofs: K multiple32, K>=96; fixed stores fit, zeroAbove/highwater laws.
-- No gas/step/runtime-success flag in these pure indices.
FiniteEntry tau key K mu : Prop :=
  mu equals fresh-zero-frame tau key K after actual modeled prologue64=128
RangeAt mu (n : U256) : Type := ByteSpan mu.capacity with offset0/length n

-- PROPOSED relational rules, finite completed-memory branch only:
-- store rule applies existing store32 to each intrinsic evaluated word;
-- terminal rule snapshots the ACTUAL evaluated local length and halts with
-- bytesHalt/capture. Each rule derives its conclusion, no finalbytes premise.
-- Core relation has NO frontend/raw-source index:
BodyCompletedAt (ops : ThreeOp C Input)
  (tau : State C Input) (mu : FrameMem C Input) (span : RangeAt mu n) result

-- Combined theorem lives in FRONTEND, importing core (never the converse).
-- deriveWholeF_operands_sound projects d to the core originalOps.
wholeF_completed36_reduce (d : DerivesWholeF b C resolved originalOps)
  (init : FiniteEntry tau key K mu)
  (h : TEnv.get sizeSlot tau.env = size36) :
  BodyCompletedAt originalOps tau mu (range36 derived from h/K) result36
  /\ result36 = .error (THalt.ofData computed36)
```

This new relation's operational meaning and capacity generalization need review;
it is NOT an existing universal source semantics, not a new axiom, and not an
executable runner. The theorem must be derived by its store/store/terminal rules,
M1 overlap/snapshot laws and param readback, NOT by a rule that takes the displayed
halt equation. The interpretation is conditional on an initialized finite frame:
it cannot manufacture an actual compiler dispatch/prologue/resource execution.
`FiniteEntry` is inhabited algebraically but its association to the original
invocation is P4, not established by source shape. Generalizing pure FrameMem
capacity must preserve its zeroAbove/resident/store bounds, not erase them.

A final `sourceBodyAt36_carrier_reduction` would compare the RESULT of this
completed-memory derivation to carrier36_halt, at the actual literal entry. It
would be a local proof-side reduction lemma, not global equality of f and
carrier36 or a global source-body definition. It may erase callee ghost Out only
on actual halt; no conclusion about arbitrary normal Out may follow from
`.map(.st)`. A source-to-TRun realization theorem STILL needs an approved source
semantics/representation and exact scoped consumer; it cannot be declared true
by assigning a `realizedBody` field. This distinction is the stop point for the
bounded option. P5b is not closed by this proposal's structural theorem alone.

### Generic size and total alternatives

DerivesWholeF has no n=36 or capacity96 admission condition. Its terminal length
is ALWAYS the actual size parameter. Local hsize follows only from c's literal
Args.evalT and empty_entry, never from a new function/spec assumption. At bounded
completed entry, n0 yields an empty snapshot (THalt.ofData normalizes empty);
n3/n6 yield different short raw data and cannot decode Panic. At n256 a capacity
at least256 is needed; prologue word64=128 and zero tail remain observable in
the raw data even though approved prefix decoding binds67. None can be replaced
by the 36-byte carrier. Wrong plan/provenance certificate is refusal, NOT revert.

For EVERY uint n, either a proposed finite initialized range witness exists
(and the two stores/snapshot rules determine exactly n bytes) or it is absent.
Absence proves neither OOG nor ordinary failure. In the actual EVM alternatives
include pre-body ABI/code/value/context/depth failure; prefix/store/slice memory
expansion OOG; failure during child/caller continuation; exceptional halt; shared
host-step/process stop; or completed raw revert. Huge n cannot be assigned a
fabricated fallback value or source `.revert`. Resource-stop/divergence must
remain non-completed/unknown unless a separately approved target theorem maps
that exact outcome. Current typed source model has no native resource meter for
this assembly. This is a total OUTCOME ACCOUNT, not a proved exhaustive target
execution theorem. The option does not promise all-size completed execution.

## Composition with actual carrier laws and original caller

1. Construct DerivesWholeF from complete source, independently of c. Construct
   DerivesWholeC36 separately, including source Return94; these are missing.
   Derive actual `args = args36` by literal78 elaboration, not as an assumed field.
2. For arbitrary sigma:State C Gamma, args36_eval gives (size36,()); empty_entry
   gives tau:State C Input with SAME H/storage/tx/net/selfBalance. Parameter2
   becomes tau.env.here; caller return74 remains a separately associated
   `i74 : Idx Gamma (.val .uint)`. No caller-slot identity is inferred from shape.
3. Under an independently constructed finite initialized-frame witness, the
   proposed completed36 derivation yields actual computed36. carrier36_halt
   supplies the closed mechanical representative of that RESULT; call_halt is
   already proved for that representative. Claiming the ORIGINAL call uses it
   requires the missing source-to-TRun realization law above, not rewriting by
   a hash/AST check. No opaque hcall premise is introduced as the deliverable.
4. For the constructed selfCall, self=true and actual receiver.env.selfAddress,
   hnz:actual self!=0 give catch_halt, no oracle lookup. Zero receiver and false
   self/empty oracle retain the proved failures. An original c source association
   must prove the exact receiver and inlined selfFrame construction; no address7
   installation premise or normalized tx is substituted.
5. Actual tryCall dispatches decodeError then decodePanic; computed36_decode gives
   codeWord67. Handler env is `[val uint binder87] ++ Gamma`; i74 shifts by one.
   Constructed normal_return already gives EXACT `.ok <sigma.setLocal i74
   codeWord,refl>`, rollback of callee ghost H, original caller fields and scoped
   binder drop. data_transport independently gives exact catchData allocation/
   scope/Ext transport for raw handlers; do not duplicate its theorem.
6. Source Return94 must end c's selected branch, set slot74 through the correct
   shifted index, and suppress remaining source continuation. Current normalTry
   is ONLY assignLocal, no early-return token; it cannot establish that law.
   DerivesWholeC36 must connect the frontend's existing calleeBody/return-tail
   lowering to that branch. c has no later source statement, but returns still
   bind returnParameters75 and must not be conflated with fallthrough. General
   _2/_3 trailing assertfalse controls are separate, not silently covered.
7. For any normal call branch, preserve ret.leaveT, TEnv.wk, output context and
   o1.ext.trans o.ext (and handler extension). No normal Out equality follows
   merely from map(.st); no comparison across differing contexts. Error branches
   restore original sigma before handler; handler error is not recaught. General
   Args failure precedes entry/body (raw TRun.tryCall consumes a call error, so
   source operand hoisting/timing must be established by the frontend before
   attributing that error to child execution). Literal36 itself cannot fail.

Use existing live_both/live_normal_both and M1 aliasCaller nonvacuity: actual old
object0 with two live aliases, fresh ghost1, arbitrary retained H and nonzero
self7 witness, both pipeline labels. They witness the constructed layer only.
No logical frameKey sender/value is normalized: selfFrame rewrites READS, not TTx.
Physical STATICCALL sender=parent self/value0/code-self association is P4's frame
law. Arbitrary sender/value in logical tau is preserved by empty_entry; absence
of reads is not a universal frame-abstraction proof. Callback judgment and its
universal diamond counterexamples stay unchanged; no Valid/ValidC promotion.

## Bounded implementation choice for later review

Proposed option: authorize ONLY generic whole-declaration/callsite derivations
and conditional finite-memory36 reduction, with no consumer/default adoption.
Future owned files would be new proof-side Evm/TryPanicSourcePlan.lean and
Frontend/SolcJson/TryPanicSourcePlan.lean (names provisional), a separate example/
control file, and module registration. The frontend module may inspect raw nodes;
core cannot import frontend/Json/parser or external dependencies. Core witnesses
must remain typed and source identities must not enter hot State/Stmt indices.
No modifications to Body.stmt1, Admission, directSelfTryContext, source targets,
D3, default callbacks or fixture expectations are part of this option.

| Dependency / owner | Exact existing or missing interface | Review boundary |
|---|---|---|
| This task, local cea0539b | TryPanicCarrier.carrier36_halt/args36_eval/empty_entry/call_halt/catch_halt/data_transport; example normal_return | Reuse, do not reprove or request mechanical approval |
| This task, local M1 3ee3855c | TryPanicProducer.produced_computed/certifiedProducer_exact and TryByteImage/ByteCapture typed stores/snapshot/capture | General K and conditional relation are NEW proof work, not approved here |
| Source compiler lane, published8445c3fc203144251b9d1fc9181f7f61a8189522 | Semantics.Run Args.evalT/CallRet.enterT/TRun.call and Frontend.Body.memoryRethrow?; exact blobs in c36 api-provenance | Reuse source metadata/calleeBody/selfFrame; NO published source-assembly semantics or DerivesWholeF theorem |
| This task + frontend source owner | New complete typed source derivation and Return94/slot74 construction; first structural law deriveWholeF_operands_sound | Explicit new relation review; not another general compiler implementation |
| G46.02/R31 and compiler owners | Actual code/stack/byte-memory/STATICCALL/resource simulation of pinned f/c entry; no existing inspected theorem of this exact type | P4 separate; pure stores, source maps/pipeline tags cannot discharge it |
| Frontend/native owner + task try consumer | Missing source-to-TRun realization and checked certificate consumer; current assembly refusals above | P5b representation realization and P8 policy/adoption separately gated |

Published API references are read-only cached published evidence, not imports.
No new foundation inventory or unpublished sibling code is used. The new
proposal does not claim a published source-law signature/commit exists.

Required nonvacuity: actually construct BOTH whole-source derivations from full
retained ASTs; arbitrary live-H entry/literal argument proofs; both distinct
bundle keys; inhabitable finite initialization; actual store/readback/terminal
reduction and full exact Out/Ext controls. Negative controls must mutate whole
body/order/extra suffix, owner/sourceUnit, parameter declaration/scope/type,
selector/arg/member/receiver, binder/return-slot/return-tail, pipeline/bundle,
initial bytes/freeword/frame, alias/newID, wrong bytes and range. Syntactic wrong
certificate must be refused without inventing an operational failure. An unchanged
body called at6 is a positive GENERIC-plan control yielding short data, while
existing constant-carrier call_at_halt remains positive with36 bytes; their
inequality refutes global substitution. n0/n3/n6/n35/n36/n37/n256 and huge-no-range
controls must distinguish finite branch, unknown target outcome and resource stop.

Acceptance requires no assumed hcall/finalbyte/source-adequacy field; full node
coverage; generic parameter; independently derived local36 equality; scoped
return association; standard-only axiom audit and clean per-file diagnostics;
G0 recursor/twin links for any indexed hot fold; acyclic dependency registration.
Estimated warm proof cost seconds–minutes/low single-digitGiB for structural/
finite36 lemmas, UNKNOWN for generic capacity/return/source realization. These
are estimates, not raised proof limits or measured evidence. Inspect prior
speed history before indexed folds/refactors; current recursor/state representation
is retained. Hard12GiB/swap0, serial Lean-j1/threads1, OS/disk headroom and existing
heartbeats/fuel/nodes/gas100M/5Mattempts/120s/literal8000 stay binding.

STOP if the source derivation needs a new operational meaning, source-to-Prog
constructor or target-resource mapping not explicitly approved; if generalized
finite frames erase initialization/bounds; if normal Out/early-return law cannot
be constructed; if full AST/callsite is omitted; or if unchanged proof bounds
fail. Factor proofs and record actual failure, never add a desired certificate.
Passing this option could establish a verified structural source-plan and local
conditional reduction ONLY. Original fixture completion would still require P4,
P5b realization and P8 consumer plus actual full ordered legacy/viaIR replay.
It would NOT be an original-assignment integration delivery.

The concrete later choice is therefore this bounded proof-side relation option
(with its explicitly reviewed new interpretation), or keeping P5b blocked pending
an owner-provided generic source-memory body realization. Neither is implemented
or chosen here. Repeating carrier proofs, global constant f, or assuming
CheckedOriginalAt36 is not a viable third option. No remaining authorized
implementation work is inferred from this design increment.

## Evidence and validation limits

Static checks only: exact retained source/input/output/selected whole-node hashes,
actual current API headers and consumer rejection shape, prior checksum integrity,
whitespace and current/base documentation comparison. Independent read-only
finder/skeptic review scope and actual validation are recorded with the handoff.
No Lean/MCP/compiler/EVM/fixture/build execution, no new theorem/axiom claim,
no source-admission or target progress. Prior310 standard-only audits/full gates
are retained historical evidence; native12/8 strictEXIT1 and historical docEXIT1
remain failures. Both pre-Byzantium fixtures stay blocked/unexecuted; all six
physical/reference source rows and original full-assignment gates remain open.

Actual checks: static source/API/provenance exit0 (1s), both retained bundles and
12 EXTERNAL metadata mutation controls, all2723 prior evidence hashes unchanged.
These controls do not implement a typed recognizer or prove source construction.
Strict documentation check exit1 (3s),20missing plus unchanged ambiguities;
COMPLETE pre-resource-footer output byte-identical to actual retained a67fa5d8
log, zero new findings. Whitespace exit0 (1s). Largest measured check-group
cgroup peak27,316,224bytes, sampled aggregateRSS23,376KiB; memory.max12GiB and
swap.max0 verified, all max/OOM events0. Host has22GiB free disk and about17GiB
MemAvailable; disk caches/writerlease and serial threads1 kept. No Lean/MCP or
compiler/EVM/backend/fixture execution occurred.

Finder's read-only review found no concrete type/source-boundary defect. Skeptic
found a core-to-frontend index dependency in the proposed relation; corrected
core BodyCompletedAt to consume ONLY intrinsic ThreeOp and placed combined
source reduction in frontend. Skeptic confirmed that fix and the existing
FrameMem-capacity clarification. Neither reviewer ran checks/server/Lean/scripts/
compiler/EVM or wrote files; final export integrity is worker-checked, not
reviewer-certified. [Review scope](diamond-try-source-construction/reviews.txt),
[validation](diamond-try-source-construction/validation.json),
[exact doc comparison](diamond-try-source-construction/documentation-comparison.json),
and [delivery](diamond-try-source-construction/delivery.json) retain actual scope.
