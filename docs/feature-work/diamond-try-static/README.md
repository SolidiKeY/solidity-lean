# Historical try compatibility and six source obligations

Evidence-only continuation of `aca22c9396011005a528bb39b29a57ecc5520770`.
No Lean, source fixture, compiler settings, runner/profile, expected observation,
admission, target or callback judgment changed. The prior checkpoint's217
standard-only audits,12/8native(strict exit1),18/2reference and66/140 ordered
comparisons remain **retained**, not freshly rerun or extended here. The human
permits static compatibility investigation; historical EVM execution and runner
implementation/enabling remain unauthorized. No new approval question is asked.

The compiler is pinned solc0.8.38+1835d247, SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
Both exact sources and both pipelines were recompiled only for assembly, AST,
source maps, functionDebugData and Yul. All20historical creation/runtime pairs
are byte-for-byte identical to the retained outputs: three pre-Byzantium forks
plus Byzantium/Osaka controls, not20successful executions. The12additional
Osaka compilations obtain metadata for the six blocked source rows, not replay.
Exact input/output/source hashes and full artifacts are in
`/workspace/next10-diamond-try-evidence/static-frontier/compile-account.json`.
The sources declare `f(bool)` and `g(bool)`; there is no `validf` declaration.

## Static entry, frame and branch correspondence

Both sources use `f(bool)` selector0x98c3a6c1 and `g(bool)` selector0xd48092f7.
Original ordered f inputs are canonical true(1), then false(0), zero incoming
value. This is a description of frozen inputs, **not execution**. The generated
call encodes g's selector followed by the cleaned bool, uses CALL with value0 before Byzantium (STATICCALL has no value operand in the Byzantium/Osaka controls), literal
8000 gas and output length0. Address is `address(this)`; code-size guard requires
successful deployment/installation. Empty return tuple decoding is distinct
from a failed CALL. The no-binding catch needs only the CALL success bit and
returns uint2; it does not require RETURNDATASIZE/COPY or failure payload bytes.
Success returns uint1. Both top-level outputs still require full32-byte uint ABI
encoding. Neither path is established as a gas-sufficient historical execution.

`historical-pcs.json` records each selector PUSH, f/g function entry, gas literal,
CALL, constructor CODECOPY/RETURN, caller return spans, every fd classification,
source identity and JUMP/JUMPI target. Compiler functionDebugData ties original
function IDs10(g)/33(f) to entries; generated-helper names distinguish guards
whose source maps intentionally cover the whole contract. The full external
`*-map.json` retains each instruction and matching legacyAssembly node/tag.
Creation copied runtime begins at the exact byte-identical runtime offset;
fd bytes inside that range are data **for creation**, not constructor execution.
Metadata appendCBOR=false. Unmapped suffix bytes remain listed explicitly.

| Source / pipeline / fork | Runtime offset in creation | Constructor COPY / RETURN PCs | CALL or STATICCALL / gas literal PCs | Intentional g-failure fd PCs |
|---|---:|---|---|---|
| assert_pre_byzantium / legacy / homestead | 31 | [26] / [29] | ['283:CALL'] / [195] | [584] |
| assert_pre_byzantium / legacy / tangerineWhistle | 31 | [26] / [29] | ['283:CALL'] / [195] | [584] |
| assert_pre_byzantium / legacy / spuriousDragon | 31 | [26] / [29] | ['283:CALL'] / [195] | [584] |
| assert_pre_byzantium / legacy / byzantium | 31 | [26] / [29] | ['281:STATICCALL'] / [195] | [582] |
| assert_pre_byzantium / legacy / osaka | 28 | [24] / [26] | ['218:STATICCALL'] / [162] | [506] |
| assert_pre_byzantium / viaIR / homestead | 52 | [30] / [35] | ['974:CALL'] / [899] | [1134] |
| assert_pre_byzantium / viaIR / tangerineWhistle | 44 | [22] / [27] | ['743:CALL'] / [681] | [878] |
| assert_pre_byzantium / viaIR / spuriousDragon | 44 | [22] / [27] | ['793:CALL'] / [731] | [928] |
| assert_pre_byzantium / viaIR / byzantium | 44 | [22] / [27] | ['793:STATICCALL'] / [732] | [943] |
| assert_pre_byzantium / viaIR / osaka | 43 | [22] / [27] | ['682:STATICCALL'] / [622] | [803] |
| require_pre_byzantium / legacy / homestead | 31 | [26] / [29] | ['283:CALL'] / [195] | [330] |
| require_pre_byzantium / legacy / tangerineWhistle | 31 | [26] / [29] | ['283:CALL'] / [195] | [330] |
| require_pre_byzantium / legacy / spuriousDragon | 31 | [26] / [29] | ['283:CALL'] / [195] | [330] |
| require_pre_byzantium / legacy / byzantium | 31 | [26] / [29] | ['281:STATICCALL'] / [195] | [328] |
| require_pre_byzantium / legacy / osaka | 28 | [24] / [26] | ['218:STATICCALL'] / [162] | [264] |
| require_pre_byzantium / viaIR / homestead | 52 | [30] / [35] | ['974:CALL'] / [899] | [1097] |
| require_pre_byzantium / viaIR / tangerineWhistle | 44 | [22] / [27] | ['743:CALL'] / [681] | [843] |
| require_pre_byzantium / viaIR / spuriousDragon | 44 | [22] / [27] | ['793:CALL'] / [731] | [893] |
| require_pre_byzantium / viaIR / byzantium | 44 | [22] / [27] | ['793:STATICCALL'] / [732] | [908] |
| require_pre_byzantium / viaIR / osaka | 43 | [22] / [27] | ['682:STATICCALL'] / [622] | [794] |

### Concrete SpuriousDragon control edges (both original sources)

Legacy runtime CALL283, JUMPI294→298 (failed CALL) versus fallthrough295
(success sets success condition1), then JUMPI302→311 (success tail).
Catch tail starts303/PUSH2; success tail311/PUSH1; both join316 and indirect
return320. The jumps294,302,310→316 are checked local constant destinations;
320 remains an unresolved stack-return edge in the conservative map. The
source return spans are305–310(catch) and314–315(success); expression literals
sit immediately before those spans. f body entry164, g body entry321.
Assert g branches to the Panic helper (fd584); require g(false) has fd330.
No catch-tail fd occurs in these two legacy generated f bodies.

ViaIR CALL793, JUMPI799→847 (success allocation/empty-return check), failure
fallthrough800, JUMPI809→832(success tail) versus810(catch). The unconditional
constant condition at815 targets817, so indirect JUMP816 is bypassed on that
local path; no global reachability result is inferred from this observation.
Catch conversion call828→674 and success conversion843→643 are concrete;
returns831/846 remain indirect. g assert helper929, JUMPI934→937 on false,
JUMP940→882(Panic helper fd928); g's helper call949→929 is concrete. Require
uses its generated require helper/fd893. Exact per-fork PCs and all unresolved
jumps, including ABI helper returns, are in the JSON rather than guessed equal.

The classification is conditional source/region attribution, not a CFG proof.
Constructor nonzero-value, unknown-selector, short/noncanonical bool and
nonpayable guards are setup/ABI rejection. The `extcodesize(this)==0` fd is a
potential **top-level** failure before the try's catch handlers could help; successful
installation rules it out at source level. ViaIR allocation Panic0x41 is a
potential **top-level success-tail** failure; fixed input36/output0 suggests a
small allocation but whole-path overflow/gas sufficiency is not proved. g(false)
fd is intentional inner failure. The assembly emits fd even for old forks;
there it is invalid opcode, not active REVERT. g(true) bypasses its failure
branch at the source/Yul level. A failed selector/ABI branch in g would also be
an inner failure, so not every CALL failure proves the intended g(false) cause.
No unsupported fd is asserted absent merely because an approximate CFG omits it.

## Pinned engine versus upstream harness (code facts, no runtime evidence)

`code-provenance.json` hashes exact installed @ethereumjs/evm10.1.3 files,
reference dependency lock and upstream harness files. Harness bytes are checked
against snapshot1835d247de183f23e7b0e2bc4a50732af525b77c, not the parent
checkout's git revision (the extracted upstream tree has no .git).

| Obligation | Pinned code facts / exact locations | Remaining boundary |
|---|---|---|
| Invalid fd versus REVERT | engine interpreter.js:254–256 throws INVALID_OPCODE for isInvalid; evm.js:1024–1027 charges full message.gasLimit except REVERT/INVALID_EOF. Existing opcode tables omit fd before Byzantium. Active REVERT functions.js:1552–1563 reads memory and preserves return data via interpreter.revert. | At old-fork fd, the REVERT handler never runs. Cannot expect Panic bytes; inner exceptional halt consumes the forwarded allowance. No historical receipt observed. |
| CALL gas and data | opcodes/EIP7928.js:98–125 computes messageGasLimit, checks affordability; util.js:142–150 applies min(request,available−floor(available/64)) from TangerineWhistle, otherwise requested gas. interpreter.js:895–936 resets returnBytes, charges child executionGasUsed and copies data only for success/REVERT; _getReturnCode returns0 on exception. CALL value is0 so no value stipend. | If enough gas remains, request8000 is forwarded; pre-EIP150 insufficient gas can fail caller before child. Post-EIP150 cap can be below8000. No exact enclosing gas sum or step count proved. |
| Catch remaining gas | generated literal gas8000 and Boolean catch mean consuming all inner allowance does not consume all parent gas by itself. No revert bytes needed by catch-all. | Need actual per-frame gas/halts, success output1 and catch output2; 100M source/harness allowance alone is not checked evidence of sufficiency. |
| Account/code setup | EVMHost.cpp:103–118 selects exact EVMC revision; :82–85 funds ten senders with2^100; :305–323 charges intrinsic/create/input gas at depth0; :324–351 increments nonce before RLP creation address (source TODO for EOA convention); :418–438 deducts code-deposit gas and installs returned code. Engine evm.js:1108–1118 increments top-level caller nonce; _executeCreate uses its own journal/address/code-deposit path. | Address/nonce convention and intrinsic charging must be reconciled before comparing gas. Self-call only depends on the actual installed address, but extcodesize/install success still needs a receipt. Do not reuse an expected fixed address or silently subtract/add gas. |
| Rollback | EVMHost.cpp:301 saves accounts and :440–441 restores on non-SUCCESS; includes documented newlyCreatedAccounts/nonce TODOs. Engine evm.js:1178–1186 reverts journal on exception, commits on success; inner caller frame resumes via interpreter._baseCall. | The fixture has no storage writes, but account/code/nonce and caller continuation still need exact boundary evidence. Different VM implementations are not equated by these code excerpts. |
| Harness comparison | ExecutionFramework.h:275 InitialGas=100000000; cpp:183–197 uses host result output, status and gas. SemanticTest.cpp:465–468 ignores failed top-level data mismatch only before returndata support. | Original f rows expect top-level **success** with32-byte1/2, so that old-harness exception does not excuse output mismatch. Host5M instructions/120s are separate reference process limits, not upstream gas semantics. |

No historical EVM was instantiated or called in this continuation. No runner,
profile, fork selection, gas literal, bytecode, host limit or expected bytes was
patched. No gas-free kernel theorem is substituted for this execution gate.

The new evidence removes the inference that any old-fork fd necessarily makes
these original f rows incompatible: at least the g(false) site is the intended
capped inner exceptional halt. It does **not** establish compatibility. The
smallest remaining experiment would require historical execution authorization
which remains unanswered: same exact source/bytecodes, exact selected fork,
zero-value deployment with actual account/nonce/code receipt, f(true) then
f(false), both pipelines, complete outer/inner halt/gas/data and code identities,
100M message gas/5M instructions/120s unchanged. Before that, reconcile the
harness's intrinsic gas and nonce conventions explicitly. This is a refined
reviewable prerequisite, not a repeated approval request or implemented runner.

## Six exact source producer/capture/return obligations

`six-obligations.json` retains exact source hashes (snapshot-checked), AST IDs,
source spans/lines, full Yul operations/external declaration references, calls,
catch binding types and returns in **both compiled pipeline artifacts**. AST IDs
are reported from the legacy artifact and are source declaration identities,
not hand-assigned dispatch keys. Both required pipelines' full artifacts remain
external. The current actual native report still stops early with
`transaction/block/self-address or cross-contract host behavior not adapted`.
The more precise frontend refusals below are code-derived boundaries, **not a
claimed freshly observed native diagnostic**. Do not erase the early refusal.

| Original row | Actual occurrence / missing typed correspondence | Reusable interfaces and boundary |
|---|---|---|
| invalid_error_encoding | g(bytes memory revertMsg) canonical `revert(add(revertMsg,0x20),mload(revertMsg))`; f1/f1a/f1b/f1c through f4 variants pass abi.encodeWithSelector/Signature to exact g declaration and bind two uint returns. Need capture of the produced **actual bytes object**, external ABI copy/key/declaration correspondence, callee parameter identity, then raw halt and caught/uncaught tails. | Args.snocMemory/CallRet.rets, RevPart.mem/TRun.revertData_mem and catchBytes_self_data/catchData_self_data already express object alias/order/rollback and actual byte transport. ABI encoders already exist in Elab/Arms and Lower; do not invent their absence. ExtArg is only `(p:PrimTy)×Simple…p`, ExtKey args List CallValue and the current direct-self external-try admission/signature path excludes reference parameters. General native ABI.program already accepts memory parameters via decoding; this is not a global reference-argument limitation. Direct self host admission separately rejects bytes parameter. A narrow consumer composition is possible **once actual typed external reference admission/copy producer is proved**; implementing that missing ABI lane here would relocate the explicitly pending policy-rejected assignment. No pointer-erasure/fake uint key or forced admission is allowed. |
| malformed_error | f(uint size), four physical stores at0,4,0x24,0x44 then revert(0,size); callers sizes3,6,0x43,0x4a,0x4b,0x100. Need exact overlapping big-endian writes, padding/unwritten memory, size slicing and THalt data; catch Error string object and default/returned string observations then caller scope pop. | Existing decodeError, catchData and memory/string return machinery can consume a proved halt. They do not prove physical layout/mstore→heap correspondence. Requires physical-memory source producer outside scope, including memoryguard/free pointer and string allocation correspondence; no general physical assembly is authorized. |
| malformed_panic | f stores Panic selector at0 and code67 at4, revert(0,size); sizes3/6/36/256, with catch-all and code binder. | Corrected decodePanic/suffix theorem and exact code-capture controls already solve consumer. Missing actual physical producer for all sizes, especially unwritten bytes/tail. Scalar returns need no new general return theorem. |
| malformed_panic_2 | Same producer; no raw catch, a/b must rethrow exact3/6 bytes, c/d return67 and skip trailing assert(false). | Preserve uncaught exact THalt, self flag, rollback and handler/tail timing; existing conditional/rethrow laws consume such witness. No new panic decoder gap remains. Missing same physical producer. |
| malformed_panic_3 | Same producer; Panic+Error without raw catch; a/b exact rethrow, c/d67. | Need same physical producer and unchanged ordered decoder dispatch; matching current decoder is not proof of source execution. |
| malformed_panic_4 | Same producer; Panic+Error+raw catch; a/b0,c/d67. | Need same producer and exact catch-all normal continuation; no new return-shape primitive is needed for these scalar results. |

`published-apis.json` records exact public master
fb379ae20f10e2c92113453ddd9d40d8f2efbe09 commit/blob/hash evidence. Existing
RevertMemory, Heap, Scoped, Run and Evm.MemoryCapture were inspected; the latter
proves its typed compiler fragment's capture step, not arbitrary inline Yul or
solc memory layout. Published Body.lean still accepts only canonical byte-buffer
rethrow; it does not admit these mstore blocks. Our task's self-try adapter is
local committed checkpoint code, absent from that published master, and is
identified as such. No published or unpublished branch was integrated.

Minimal counterexample to a **heap-only physical producer**: take the same typed
heap/env/storage but two physical memories differing only at free-memory word64
(0x80 versus0xa0). The selector/code mstores at0 and4 leave byte95 unchanged;
`revert(0,256)` returns different byte95. HRef.id is object identity, not byte
address, and Heap records no word64, so neither result is derivable solely from
that shared typed state. These are two candidate physical representations, not
a claim both are reachable in the pinned compiled function. Its prologue
mstore(64,0x80) supplies the missing initialization fact; actual prior receipts
indeed contain0x80 at95. A correct source bridge needs that initialization/layout
relation and exact writes/slice theorem, not a supplied reference payload.
A representative zero suffix is sufficient for decoder testing but fails raw
256-byte source equivalence. That boundary is why a literal-payload adapter or
new global memory/target semantics is not implemented here.

Missing producer theorem proposal (not code/axiom): from a **proved** relation
between the compiled frame's initialized physical byte memory and current typed
state, derive the exact big-endian overlapping stores and revert slice; then
feed that produced d into the existing exact self-call/catchData laws. Preserve
argument-evaluation failure before try, sender/value/self frame, finite normal
or actual halt only (never exhausted/diverged→completed failure), rollback,
heap extension identities, result order, full raw bytes and handler scope.
Required negatives: wrong source/callee/size/selector/word order, wrong alias,
wrong object/type, omitted prologue/tail initialization and handler fallthrough.
Owning boundaries: the reference ABI producer belongs to the existing ABI/reference-boundary lane documented in `../abi-hashes.md` (pending service-policy review), not this try task. Physical assembly/layout is the explicit D3 exclusion in coverage-plan, with no authorized implementation owner assigned here. Typed try consumers remain owned by this task (`../diamond-try.md`); `../calls-exceptions.md` owns shared call semantics. These are boundaries, not reassignments.

This layer is physical assembly/layout, explicitly outside the authorized
try-specific composition lane; no theorem is fabricated to cross it. The ABI
reference producer for invalid_error_encoding is a different pending boundary.

## Proportionate validation and review

No implementation or Lean edit occurs, so no rebuild, MCP replay or new axiom
audit is claimed. Actual static compilation/mapping/provenance checks are
serialized under the documented writer lock in12GiB/swap0 groups; LEAN_NUM_THREADS=1
is recorded and no Lean command is needed. Previously passing full checkpoint
is not rerun. Final static controls, doc-path baseline comparison, independent
read-only finder/skeptic reviews and checksum-bound export are recorded below
when complete. All initial analysis failures/corrections remain separate evidence.


### Actual evidence-only validation

`validation.json` records actual command exits/timings/RSS/cgroup peaks, not
inferred gate status. Static metadata compilation32rows passes7seconds,
250204160byte peak; mapper20rows passes1second; pinned provenance collector
passes2seconds. Shared integrity validator passes20maps/32compiler rows and five
negative mutations: actual source hash, bytecode hash, copied runtime boundary,
CALL-vs-STATICCALL opcode, and misattributed allocation helper. These are artifact
controls, not Lean theorems or historical execution. Generated inventory check,
node syntax and whitespace pass. Documentation path check retains **exit1**,
identical20 baseline findings at aca22c93 and zero new findings. No full build,
MCP, fixture replay or axiom audit was rerun; all prior results are retained only.
Every bounded command verifies12GiB/swap0, max/OOM0 and the writer lock; actual
invocation control confirms LEAN_NUM_THREADS=1. No Lean call requires a new Lake
configuration or -j setting in this evidence-only turn. Disk22GiB and OS headroom
are recorded. No unrelated process, setup/user file or tracked runtime config
changed. New modules/import registration and feature inventory regeneration are
inapplicable because no model support changed.

Independent finder/skeptic reviews used no Lean/server/checks/writes. Confirmed
whole-contract `require(x)` misattribution and omitted STATICCALL control sites
were repaired and regression-checked; general memory-argument support was
clarified instead of claiming a global ABI absence. Skeptic's final wording
correction distinguishes the try's handlers from constructor handlers. Earlier
owner `this.g` substring mistake and all prior maps are preserved externally.
No failed report is erased or reclassified as runtime success. Final evidence:
`/workspace/next10-diamond-try-evidence/static-frontier/reviews.txt`,
`attribution-corrections.txt`, `validation.json`, raw logs and exact hashed
compiler/engine/harness artifacts. Original assignment remains12/8native strict1
and18/2reference; no additional fixture gate is closed by static evidence.
