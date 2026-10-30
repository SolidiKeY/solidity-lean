# Complete intrinsic physical-byte producer/correspondence DESIGN

The human selected **prepare the complete design for review**, not implement.
This design-only child ofa9daa3bbc5b55e16951b36b2162f61f5ed644ece stays on the
same VM/thread/branch. No producer, byte interpreter, physical-memory State field,
source admission, target/exclusion/D3 policy, expected byte/verdict, callback,
core semantic rule, axiom or budget changes. Historical A/B/R_fixture/backend
instrumentation/execution remain unapproved. Existing Panic correction is reused,
not repeated. Prior failures/exports/standard-only audits are preserved.

Read [typed interface](typed-interface.md) for proposed structures/signatures,
[proof/milestone plan](proof-plan.md) for dependency/outcome/resource obligations,
and the exact fixture/mechanism/history JSON alongside. No code block here is
an implemented theorem or claim to have passed Lean diagnostics. Original
assignment remains native12working/8blocked strictEXIT1,reference18/2 and66/140
ordered comparisons with217retained standard-only audits, not design success.

## Exact scope and immutable source/compiler identities

Five files only: malformed_error,malformed_panic,malformed_panic_2,_3,_4 under
pinned Solidity1835d247de183f23e7b0e2bc4a50732af525b77c. invalid_error_encoding is
NOT included: its external bytes-reference argument producer belongs to the
policy-pending ABI lane. Each selected callee is actual declaration f#7,
`function f(uint size) public pure` with no returns, but #7 alone is not identity:
bundle/source unit/hash and full declaration are required. Caller IDs vary by
file and are stored, including exact returns, catches and AST external references.

Both compiler pipelines use pinned solc0.8.38+commit.1835d247.Emscripten.clang,
SHA2566c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390,
evmVersion=osaka,optimizer disabled(runs200),metadata appendCBOR=false.
fixture-identities.json contains exact original/compiled source hash, input/
output hashes, source-unit/id, AST/Yul body, function/catch/argument identities,
method selectors, code hashes, settings and prior reference receipt provenance.
These are retained metadata compilations/receipts, not rerun in this increment.
Bytecode digest match holds for all10metadata/reference pipeline pairs; reference
input hashes are retained separately because output selection/preamble/provenance
may differ. Hash agreement is not a new kernel compiler-correctness theorem.

| Original file | f declaration span | Original ordered calls per pipeline | Original outcome account |
|---|---|---|---|
| malformed_error.sol |17:280:0|a,b,b2,b3,c,d|uint0,0,0; default empty string; seven-byte string twice|
| malformed_panic.sol |17:216:0|a,b,c,d|uint0,0,67,67|
| malformed_panic_2.sol |17:216:0|a,b,c,d|exact raw short failures3/6bytes;67,67|
| malformed_panic_3.sol |17:216:0|a,b,c,d|exact raw short failures3/6bytes;67,67|
| malformed_panic_4.sol |17:216:0|a,b,c|uint0,0,67; d is declared but NOT an original observation|

There are21original calls per pipeline,42retained reference observations here,
not44. All complete literal ordered bytes/failure flags remain in the JSON;
its displayed human summaries do not replace them. Original native rows remain
blocked. Extra producer controls, including _4.d, must be labeled separately and
never inflate required observations or change frozen fixtures.

### Same-invocation certificate contract

A future certificate must originate from ONE actual compile input/output pair,
not select convenient AST from legacy and code from viaIR or later retries.
Bind exact source bytes (and explicit preamble/source-map offsets), compiler
binary/options, full output AST/source maps/generated sources/Yul/assembly/
creation+runtime bytes, source id and callee/caller declarations. Generate the
producer from **recognized typed operations**, not reference observations or
postulated Error/Panic payload. Pinned metadata file f-body AST and exact caller
clauses are the recognition input; errorName order, catch binding type/name,
actual referencedDeclaration and size literal/parameter identity are retained.

Kernel-side certificates need exact literal/structural equality/reflection over
embedded artifacts, not an assumption that SHA256 is injective or a trusted
hash oracle. Digests are reproducibility/provenance indices; byte equality and
recognized syntax witnesses carry proof. Pinned solc invocation is a source of
untrusted candidate artifacts, not an axiom of compiler correctness. Restricted
source-parser/AST correspondence, whole recognized body coverage and actual
compiled-byte simulation are independent obligations. If a needed frontend
adequacy theorem is absent, claims stop at certified artifact/typed-plan scope;
no universal Solidity/source adequacy is inferred from finite fixtures. No
mixed-invocation or hash-only hcall is accepted.

## Exact physical operations and compiler initialization

Use half-open byte intervals below. All selected runtime entries initialize
mstore(64,128): legacy shows mstore(0x40,0x80), viaIR deployed object shows the
literal128. Constructor memoryguard initialization is NOT memory inherited by
the callee; external call frames have fresh zero memory. Before f body, actual
uint dispatcher/calldata/value checks must be proved to pass with the actual
size parameter, without preceding callee allocation/writes to the relevant
regions. Scalar parameters remain on stack/calldata; no external bytes ABI
producer is introduced. Source calls use `this.f(n)`; the compiler emits
STATICCALL(gas(),self,...), not historical gas8000. Existing100M/5M/120s apply;
legacy/callback/self/default meanings remain unchanged.

| Region / action | Actual address/byte range | Exact condition |
|---|---|---|
| Fresh frame | all bytes initially zero | Actual frame-init fact, not inferred from typed Heap.empty or caller heap. |
| Compiler prologue | store32 at64 writes[64,96), byte95=0x80 | Ready free pointer128; zero slot[96,128) initially zero; scratch[0,64). |
| Panic selector | store32 at0, `0x4e487b71 <<224`, writes[0,32) | Selector bytes0..3, zeros4..31, big-endian. |
| Panic code | store32 at4,0x43, writes[4,36) | Overlap[4,32) overwritten with zeros, byte35=67; outside0..35 unchanged. |
| Error selector | store32 at0,`0x08c379a0 <<224`,[0,32) | Exact selector/source literal, no guessed bytes. |
| Error offset | store32 at4,0x20,[4,36) | byte35=32; partial overlap with selector word. |
| Error length | store32 at36(0x24),7,[36,68) | byte67=7; overwrites free-word prefix64..67. |
| Error string | store32 at68(0x44),literal"abcdefg",[68,100) | ASCII bytes68..74, zero padding75..99; overwrites free-word suffix68..95 and zero-slot prefix96..99. |
| Terminal raw revert | revert(0,n), snapshot[0,n) | Natural no-wrap range and expansion/resource fact; immutable bytes captured before discarding callee frame. |

For Panic n256, byte95 remains0x80; bytes36..94 and96..255 are zero under the
actual fresh/prologue/no-other-writes premise. For Error n256, the raw stores
**overwrite** the free-memory word: don't copy the Panic tail rule. Allocator
validity after those stores is false/invalidated, but callee immediately reverts,
so no subsequent allocation may silently use that clobbered pointer. The exact
string store writes zeros96..99, so zero-slot value preservation needs a content
proof even though its footprint is touched.

MSTORE is32consecutive big-endian bytes, not a write to cell a. MLOAD reads32
bytes, including unaligned/overlapping intervals; pointer arithmetic/end is
natural and checked where compiler checks it, never silently modular on span
ends. Slice n0 reads no byte and requires no expansion; n3/6are selector-prefix
snapshots; n35lacks the code's last byte; n36contains it. Error slices3,6,67,74
cannot decode a seven-byte reason; n75contains all seven, n256has trailing data.
These mathematical consequences require the typed representation/step proofs
below; they are not current source-execution theorems.

### High-water, free pointer and live ownership are different

Fresh frame high-water0; prologue store[64,96) raises it to3words. Panic stores
keep3words; Error store[68,100) raises it to4words. Terminal revert n>0 expands
to max(currentWords,ceil(n/32)); n0 does not itself expand, although preceding
stores already did. n256 needs8words in either shape. A logical capacity256
witness must NOT pre-charge/pre-expand EVM memory or imply gas sufficiency.
Expansion cost belongs to the future byte backend theorem, not a new model limit.

Solc free pointer128 is not the same as high-water96 and may later be BELOW
high-water after temporary copies. Do not import the word-allocator invariant
“all bytes above cursor are zero” globally. Only exact typed live footprints and
needed zero regions are constrained; temporary/unowned memory may be dirty and
reused with permission. Existing heap/field/frame invariants remain logical,
while physical allocator readiness is tracked separately and can be invalidated.

### Caller allocation/copy/decoding/return requirements

Pinned viaIR try_decode_error_message checks returndata≥0x44, copies actual
returndata[4..end) at current free pointer, checks offset/length≤uint64 and
bounds, finalizes allocation and returns msg pointer. Here offset32/length7
are constants produced by the stores. Existing decodeError agreement is claimed
only for this family, not global noncanonical offset/uint64 parity. Caller
returndatacopy must respect source bounds (not zero-pad) and physical destination;
failed child writes disappear but immutable return bytes survive. Caller free
pointer/heap are the caller's pre-call state plus its actual prefix, not reset
to the callee's128 or corrupted callee word64. Exact decoder allocation guards
and handler failures remain outside callee catches.

For concrete caller addresses, the required prefix theorem may establish p=128
for these no-argument a/b/c/d/b2/b3 entries: outgoing selector at[p,p+32), size
word at[p+4,p+36), output length0; high-water reaches ceil((p+36)/32), but failed
STATICCALL does not run the success-only finalize_allocation. This is conditional
on the exact same compiled prefix, not assumed for arbitrary callers. With p128,
try_decode_error_message copies d[4..n) into[128,128+n−4). Offset32 makes string
object header `msg=160`, bytes at192, length7. On n75/256 success, finalize at
data128 with size71 rounds that allocation to96bytes and sets free pointer224;
logical reason object base is160, NOT128. Prefix[128,160) is auxiliary buffer
ownership, not a second logical bytes object. n256 copy reaches380/high-water384,
above final pointer224: retained bytes/padding and unused dirty tail must not be
mistaken for disjoint live objects or a zero-tail axiom. Returning c/d's string
requires the actual encoder copy from that interior object, not a fresh data
literal or equality of its physical pointer to HRef.id.

The pinned default-string helper returns pointer96 (0x60), not a newly allocated
physical buffer. The logical typed return default object must map to a read-only
empty-sentinel role, not force a second physical allocation or identify distinct
HRef IDs. Mutable object separation remains strict; shared read-only empty
sentinel views are an explicit exception requiring zero length/header and no
writes. An ordinary new bytes(0) may still own a separate allocated header.

On n74, copy occurs before length7/end check fails: no finalize, no logical
reason allocation, but caller scratch/high-water may change. b3 still uses the
actual default string at zero slot96 with length0; later encoder reuses temporary
memory at p. On n67, helper exits on min68bytes before body copy; selector dispatch
may already have touched scratch0. Model decodeError is pure, so correspondence
must frame these target-only writes as unowned temporary effects, not pretend
none occurred. Reuse old outgoing argument buffer only AFTER arguments/call
have consumed it; neither source heap alias nor callee calldata can still point
into that now-reused physical scratch. These are code-derived address formulas
requiring the prefix/decoder/encoder theorems, not new execution observations.

Panic selector dispatch then pinned try_decode_panic_data copies exactly32bytes
from return offset4 when length≥36; approved decodePanic agrees and ignores suffix.
Raw short _2/_3 failures must retain exact3/6bytes, not empty them or encode a new
error. a/b normal catch-all assertions return default uint0. _2/_3 c/d return67
and bypass their trailing assert(false); short rethrows bypass the tail too.
Error b3 returns actual default empty string after raw catch; c/d bind/return
actual "abcdefg" object. Header32/payload/padding/allocation base and final ABI
return order must be proved from same-invocation compiler paths; no EVM-reference
bytes are inputs to these model producers. Full encoded return bytes are tested
separately against unchanged frozen observations.

## Why typed state alone cannot choose the slice

Current State C Γ holds typed storage,H/Heap,TEnv,net,balance,tx; HRef.id denotes
an object, not a physical byte offset, and no field is solc's memory[64]. Consider
the SAME typed state and two candidate physical representations differing only
at free-word64 (128 versus160). Selector/code writes[0,36) leave byte95different,
so revert(0,256) differs. This is an underdetermination counterexample, NOT two
proved reachable pinned executions. Prologue mstore(64,128) rules out the160
candidate only after actual entry/adequacy is established. Assuming a zero-filled
256-byte suffix or deriving bytes from a desired frozen return skips that proof.

The new witness must carry actual frame initialization/layout, relevant heap
objects/alias identities, overlapping write footprints, expansion/high-water,
free-pointer validity/invalidation and immutable snapshots. It is attached to
the actual typed state/frame, not an erased physical state later “validated”.
Do not represent unreachable caller heap objects in a fresh external callee:
TRun's H may contain them, but only frame-reachable refs are relevant residents.
Copies, aliases and old HRef identities are preserved by existing heap-extension
laws. No ordinary recursive-type migration or reference ABI work is taken over.

## Reuse existing mechanisms; do not rename word memory as byte memory

| Existing local/published interface | Reusable part | Explicit missing part |
|---|---|---|
| Evm.Machine.mem Nat→Word, mstoreAt | Typed word values/machine framework | Cell update at a does not affect a+4. Cannot instantiate physical MSTORE with it unchanged. |
| Evm.Memory.ArrayRepr/HeapRepr/StateRepr | Typed source refs, base-per-identity aliases, disjointness/local-frame preservation | Word length/elements at base+1+i, not packed bytes at byte base+32+i. |
| FreeMemory/allocateMachine/AllocatorRepr/GrowsAllocator | Checked growth, old-address preservation and no-wrap proof pattern | Cursor cell0 versus solc byte64; no overlapping byte update/free-word corruption. |
| MemoryCompile.*Frag.correct/compile_correct; MemoryCapture.captureStep_correct | Compositional typed compiler/capture proof shape, correct old-index/alias timing | Only supported word fragment, not arbitrary solc bytecode/Yul. |
| Semantics.AllocBytes.litBytesT_alloc, State.allocPush, HRef.wk | Exact snapshot byteWord object/new identity/heap extension/capture | Need actual physical producer; computed snapshot is witness input, not expected bytes. |
| RevertMemory.revertData_mem/catchBytes_self_data/catchData_self_data | Current actual byte read/revert, self flag, rollback, decoder payload/handler scope | Do not duplicate laws; supply genuine hcall from proved producer PLUS actual declaration/body/frame transport. |
| Bridge.ExternalEvm/WordOps at published master | Optional independent word arithmetic/stack semantics | Its stated scope excludes memory/gas/absolute jumps/calls; not a complete byte/source correspondence theorem. Core stays dependency-free. |

mechanism-provenance.json records exact public master
fb379ae20f10e2c92113453ddd9d40d8f2efbe09 blobs and local hashes (including deliberate
approved Panic delta). Published roadmap G46.02/R31 records byte-memory operation/
expansion/return-range gaps, modules=[]; G48/frontend adequacy is not assumed
complete. These are named missing owner/API obligations, not imported unmerged
work or a request to take over another lane. Full design needs their producer
or explicit approved interface theorem before claiming target correctness.

## Nonvacuous controls, outcomes and release gates

See proof-plan's total ledger. Essential controls include:

- Fresh versus stale/caller frame, wrong word64, wrong compiled prologue, missing
  initialization and unintended intervening writes. Zero-slot/free-word corruption
  must invalidate allocator readiness rather than “prove” any result by false
  premises. Construct a valid image/certificate for each accepted bundle.
- n0,3,6,35,36,37,67,68,74,75,100,256; wrong selector/code/word order/end bounds,
  negative/wrapped-looking source operands, allocation/uint64 overflow and read/
  returndata-copy out-of-bounds. No global n≤256restriction or extra test/fuel cap.
- General overlapping stores are noncommutative; disjoint writes commute. For
  THESE Panic literals, reversing store0/store4 happens to leave the same bytes
  (the overlapping code prefix is zero). Reject wrong source order by provenance,
  not a fabricated claim outputs differ. Use a separate high-bit word/general
  overlap example to detect real order errors; label it synthetic, never frozen.
- Two aliases to one HRef share address/object; deep copy is fresh, old source
  mutation cannot alter snapshot, unrelated object/frame untouched. Wrong ref
  type/root/field/base/overlap must refuse proof construction, not execute a false
  source halt. A fixed small capacity is a certificate choice, not changed semantics.
- Wrong source/declaration/signature/pipeline/compiler/settings/code/body identity,
  extra Yul operation, changed raw range, wrong self/oracle flag/catch bytes or
  handler-tail order all fail recognition/correspondence. A primitive/BoundCalleeFrame/hcall premise
  with no constructive producer is not a pass.

No sorry/axiom/global invariant exemption or rewritten target. If implementation
is later authorized: per-file Lean MCP diagnostics (success/nonpartial/noerrors),
actual axiom audits, independent finder/skeptic, unchanged code-gate suite and
./run-lean.sh; full imports/build/TestSuite/Corpus/frozen,source admission,orphans,
layers,strict automatic/trust,affected script tests and complete original family
both pipelines/ordered bytes. Generated feature inventory only by audit script,
no inflated support. Current documentation baseline remains actualEXIT1; compare
current/base findings and require zero new. Resource/proof failures remain open.
Kernel conditional certificate, source/compiler correspondence, reference receipts
and actual native source replay are four distinct success criteria, not substitutes.

## Concrete implementation decision after review

Design-only approval does not authorize any item below. The reviewable proposal
is: **M1 proof-only narrow intrinsic frame/image+producer/capture component for
malformed_panic.sol c(), with whole-source bundle identity and explicit P4 byte
correspondence gate; keep current admission/D3/targets/refusals.** Authorizing that
would not authorize new .asm semantics or native status changes. A later separate
P4/P8 decision must approve a byte primitive/compiled-adequacy implementation and
certificate consumer before one original native row can pass. If the requested
implementation goal is immediate end-to-end source coverage, that broader exact
scope must be reviewed rather than silently inferred from a proof helper.

The complete design includes full five-row P0–P8/outcome/decode/string transport,
so the bounded proposal is a dependency-cut milestone, not a claim the original
gap is closed by another helper. At present no implementation is selected or
performed, and no question about the already-approved decoder or historical
runner is repeated. Historical backend/ABI/build/abortable-step evidence remains
at a9daa3bb's reviewed report; no backend capability appeared merely because this
physical-memory design was requested. No new backend fetch/load/scan is needed
to relabel that unchanged blocker; both A/B/R_fixture stay unapproved.

## Evidence-only validation/review record

The design reads retained10compiler bundles and42original reference observations;
no compile/engine/fixture/Lean run is repeated. New artifact/design consistency,
current-base documentation comparison and independent read-only reviews follow
below after completion. All cost figures in proof-plan are estimates; no new
proof/semantic performance result is claimed.


### Actual design-integrity gates and reviewed corrections

validation.json records actual bounded commands/exits/timings/aggregate RSS/
cgroup peaks.10bundle/42retained-observation integrity checks pass, with4negative
artifact controls(output hash,callee identity,pipeline and source store order),
mechanism/history hashes and _4.d observation absence. No physical producer,
source parser correctness, byte-step execution, typed signature elaboration or
compiler adequacy theorem is proved by these checks. No new Lean audit/compile/
reference replay/fixture/backend run occurred. Inventory and staged whitespace
pass; doc paths retains actualEXIT1,same20baseline/new0. Exact backend status
remains prior a9daa3bb evidence, not re-scanned or changed by design permission.

Every bounded group verifies12GiB/swap0/max-OOM0, writer lease and
LEAN_NUM_THREADS1, disk caches/OS headroom. No budget/Lake/setup configuration
change. Proof costs in proof-plan remain estimates. No new Lean modules exist,
so per-file MCP/full build/new axiom audit are not claimed freshly passed.

Finder/skeptic reviews were read-only without Lean/server/checks/builds/writes/
EVM. Fixed the missing original-callee transport explicitly as P5b/P8, rather
than claim source hcall from a producer halt. Reviewed refined Error copy/guard/
interior-base/high-water and sentinel rules against actual Yul. Fixed reserved-
region schema to permit only proven read-only empty sentinel, preserving mutable
separation. Actual scope/findings/corrections and raw logs are in external
reviews.txt,review-corrections.txt,layout-refinement.txt. No complete assignment
or integration delivery is certified by this reviewed design checkpoint.
