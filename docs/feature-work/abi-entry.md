# ABI entry (G40)

Status: partial. `Solidity/Backend/AbiEntry/` states the G40 obligations for
calldata decoding, dispatch and entry composition, and proves the parts that
need no new decoder.

- **Interfaces.** `Interface.lean` (source boundary), `CompositionInterface.lean`
  (ordered entry recursion), `RejectionInterface.lean` (conditional rejection
  through the existing checked byte-slice runner) and
  `WordValidationInterface.lean` (emitted primitive validators). They are
  narrow contracts with source-only graph controls, not runtime, decoder or
  admission instances.
  The original source-coverage field remains part of the record.
  `of_exact_result` constructs both fields from exact graph agreement, with
  inhabited graph and empty-relation controls. Dispatch helper equalities are bookkeeping and
  may be definitional; they do not establish runtime dispatch.
- **Proofs.** `WordValidation.lean` gives actual numeric bytecode for
  every semantic word kind: uint/address, signed integer, bool, enum and
  left-aligned bytesN. Oversized unsigned bounds accept every word without
  immediate truncation. `validator` supplies each exact predicate certificate;
  `frameCertificate` exports its code through Selection V2.
  `EntryTransport.lean`, `RawFreeTransport.lean`,
  `EntryComposition.lean` and `EnumEntry.lean` hold the entry-only part of the
  V13 ABI-world work over the existing indexed decoder; the codec and window
  proofs stay in `Backend/AbiWorld`. Eager/lazy correspondence reuses
  `Semantics/AbiEntryProofs.eager_cref`; the public
  `EntryTransport.eager_lazy_body` theorem and its axiom guard are retained.
  `Consumers.lean` inhabits the rejection and composition interfaces.
- **Premises.** `Premises.lean` and `Premises/CalldataViews.lean` (with its
  additive extension `CalldataViewExtensions.lean`) retain the typed G34,
  G35.03 and G24.03 boundaries. V11 supplies V1 structural packing through
  `Backend/MemoryOps/CalldataViewPacking.lean` (`overlappingCalldataViews`) and
  V2 arbitrary-prior-key extension through
  `Backend/MemoryOps/CalldataViewExtension.lean` (`overlappingCalldataViewsV2`).
  Native paths/copies and the G24.03 statement producer remain open.
  Packing consumes already-decoded
  coherent payloads; it does not derive them from calldata bytes.

Open: emitted calldata decoding, dispatch and full entry composition against
the backend, and the G46.02/G46.03 Bridge backfill.

Numeric validation uses the existing gasless scalar runner, retains arbitrary
stack suffixes and checks every stack boundary with an inhabited scratch bound.
It does not certify calldata loads or external EVM execution. Concrete emitted
controls cover dirty sign/padding bits, signed ranges, full-width words, all
factory branches and stack-capacity boundaries. Frame export uses Selection V2;
future memory-copy consumers must use MemoryCopies V2. The weaker V1 capacity
fields are not evidence for this work.

Validation covers source-graph controls, emitted numeric cases and concrete V2
frame witnesses/refusals. Scoped guards pin standard axioms. Independent finder
and skeptic reviews checked exact predicates, suffix preservation and capacity;
these are local runner and stack-bound controls, not external EVM tests.

The partial G46 access interface lives in
`Bridge/SolidityBridge/AccessBridge/Interface.lean`. `Calldata.lean` inhabits its
CALLDATALOAD contract: exact Source word reads at every native offset, charged
fetched-step outcomes and original driver fuel. H7 padding and existing reader
proofs are reused. A constructor installs the exact Source bytes; controls cover
endianness, unaligned/large offsets, zero padding, gas and stack refusal. A
successful charged control checks the exact reached state and preserved tail.
Independent finder/skeptic reviews found no semantic gap; the skeptic requested
this successful control in addition to refusal cases, and it now passes. Driver
budgets zero/one remain distinct from positive-fuel `X` continuation; a negative
control exhibits their different low-budget failures. CALLDATASIZE reuses P10's
existing source-input theorem. Memory/copy and storage bridges remain open, and
no whole Source/world or external EVM adequacy is inferred from these accesses.

`Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean` specifies initial P6 byte-image and active-word
representation, MSIZE payload agreement and full charged/fuel behavior for
MSIZE, MLOAD, MSTORE, MSTORE8 and CALLDATACOPY. Its active-byte word-fit field
prevents MSIZE wrap; it does not bound reserved capacity or calldata admission.
Finder/skeptic reviews found no false signature and required this boundary to
stay explicit: store/copy image preservation remains open; MLOAD payload
agreement is supplied separately by `MemoryLoad.payload`. `MemoryCharged.lean` inhabits these signatures; `MemoryControls.lean` checks
initial P6 images, arbitrary reserved-capacity growth, per-operation successes,
expansion charges and refusals, empty-copy endpoints and MSTORE8 low bytes.
MSIZE successful native execution reuses the existing P10 theorem. Independent
reviews found no semantic gap; the requested stack-overflow control is included.
Scoped guards pin standard axioms. Store/copy image preservation and post-load
active-image adequacy remain open.

`Bridge/SolidityBridge/AccessBridge/HostWriteControls.lean` exhibits a successful
charged MSTORE8 whose reached state fails the P6 post-image relation. The initial
image is inhabited, its one-byte span fits reserved capacity, and the reached
active byte extent fits the EVM word. At offset `2^64`, the pinned logical
`ByteArray.write` casts its destination gap to USize zero and writes at address
zero; P6 preserves that exterior byte. The original gate accepts maximum-word
gas. Thus unrestricted P6 store-image preservation needs resolution by the
read-only pinned-writer owner. No capacity/gas exclusion or changed relation is
introduced. This is a logical-model counterexample, without a source-program
reachability or external-runtime claim. Independent reviews confirmed the
obstruction and requested the combined charged-post witness, now included.

`Bridge/SolidityBridge/AccessBridge/MemoryLoadInterface.lean` separately specifies
MLOAD payload agreement with the existing P6 byte image at every native offset,
plus unchanged physical bytes. It adds no capacity/offset restriction. Charged
execution uses the existing memory certificate; post active-extent representation
and Source-origin adequacy remain separate obligations.

`MemoryLoad.lean` inhabits the MLOAD payload contract using the existing clipped
reader, H7 padding, byte-order/range theorems and active-extent agreement. Its
byte-only initializer supplies logical initial images without a native allocator
or Source-origin claim. `MemoryLoadControls.lean` checks full and clipped backing
with ordered nonzero bytes across a word boundary, right padding, both zero
guards, large offsets, unchanged bytes and wrong-endian refusal for either
pipeline tag. Independent finder/skeptic reviews found no issue; scoped guards
pin standard axioms. Post-load active-image adequacy remains open.

The published dependencies now supply eight AccessBridge modules, including
`HostWriteControls.lean`, and both V11 structural packing producers. V2 extends
arbitrary valid prior packings, preserving captured keys and assigning fresh
keys to new identities; the V1 first-representative policy is not imposed on
prior keys. These owner proofs are reused rather than reimplemented. Only
`Calldata.lean` remains outside the imported Bridge increment. The pinned writer
counterexample remains a counterexample, not a store/copy repair.

V09's `Backend/Passes/RelatedMemoryCapture.lean` supplies aligned local memory
capture and selected-map pointer readback; it does not supply the general
statement interface. General P1 selection, P10 decoding/call correspondence,
physical origin, concrete P8 admission and whole-program adequacy remain open.

H26 exposes `Backend/MemoryOps/PhysicalByteWorldInterface.lean` on master. The
AccessBridge `ByteWorldInterface.lean` states a paired-load consumer contract
against its exact explicit `ByteWorld.Producer.load` field. Initial P6/native
images, selected numeric word cells, address scaling and stack capacity remain
explicit. Concrete byte-program realization and Source provenance are not
supplied by this interface. The published RawUint Source proof modules are
reused rather than reimplemented; their helper branch and omitted consumer/doc
remain preserved.

`ByteWorldLoad.paired_load` now proves that consumer contract, reusing the
published `Producer.load_at` for the intrinsic load, conditional byte-target
run and preserved word frame. Existing pinned `MemoryLoad.payload` and byte
roundtrip proofs derive the native reader and complete ordered 32-byte
serialization from the same initial image. Native serialization equals
`Semantics.wordBytes` of the initial word; native numeric equality to that word
was not established by that first certificate. Neither an encoder inverse, concrete
byte-load code realization nor Source/compiler origin is assumed implicitly.
Native physical bytes are unchanged; post-active-word representation remains
a separate obligation. Existing charged/failure certificates are unchanged.

`ByteWorldLoadControls.lean` constructs actual initial P6/native and numeric-word
images for every finite word in either pipeline, with distinct saved tails.
Its paired use remains explicitly conditional on the pending producer. The
literal byte-slice MLOAD refusal is not a native MLOAD refusal or an
impossibility proof for all programs; the oversized-tail control concerns the
contract domain, not native overflow execution. Independent read-only finder
and skeptic reviews found no semantic gap. The finder's reuse request was
fixed by consuming `Producer.load_at` instead of repeating its proof.

`ByteWorldNumericInterface.lean` adds a numeric consequence while retaining the
original paired contract and all its input premises. `ByteWorldNumeric` proves the existing serializer equals `Failure.digits`, then
reuses `Failure.read_digits` to derive exact numeric equality for every finite
word. Its stronger paired certificate reuses the first transport, without
assuming an encoder inverse. The inhabited controls now exercise this numeric
consequence for every word in either pipeline, retaining both saved tails. Code realization, Source origin and post-active
representation remain open.

Numeric checkpoint validation: per-file diagnostics reported zero errors; the
selected Bridge closure passed 1223 jobs (4 seconds), and the core checkpoint
library passed 3410 jobs (3 seconds). Trust, orphans, layers, generated roots
and doc paths passed. That historical checkpoint reported 6553 standard-only pins and a missing
public wrapper pin. The public theorem and guard are now restored; current
exact-head gate outcomes are recorded in the latest sealed handoff. Independent
read-only finder and skeptic reviews passed with no findings. The full original
queue and its producer, physical-store/copy and provenance obligations remain open.

`MemoryLoadExtentInterface.lean` adds exact native MLOAD active-word accounting
and an iff for the post-image of the published `P6ByteMemory.touch`. This is
separate from raw payload and charged execution. Intrinsic/native offset
correspondence and the actual 32-byte span are explicit; the iff exposes the
existing post-active word-fit boundary without narrowing calldata admission.
The earlier absence of a local FrameMem read method is not a blocker: the
published P6 adapter already supplies `touch` and its byte/carrier laws.

`MemoryLoadExtent.lean` proves native active-word accounting at every offset,
without modular loss in the word count, and the exact post-image iff using
`P6ByteMemory.touch_image`. Complete physical bytes, logical state and invocation
key are preserved by the existing operations. A full post-image holds exactly
when its existing strict active-byte word-fit field holds; no new admission
restriction or unconditional post-image is asserted. Controls construct initial
images for either pipeline, expand a crossed-word read, and exhibit a fitting
aligned last word ending at the word-size boundary whose raw post-image fails
word-fit. They allocate no enormous native buffer and claim no charged success
or Source reachability. Charged access/failure certificates remain unchanged.

Dependency audit: the exact H26 consumer field is supplied conditionally, not
realized by a concrete byte program. `Backend/Passes/EntryReception.lean` is an
admitted Boolean handoff, not emitted raw decoding or selector dispatch. V11's
structural V1/V2 view producers are available; deriving coherent raw views,
emitted decoding and dispatch remain owned G40 work. Native G35.03 copy/slice
and general V09 G24.03 composition are separate producer obligations. These
facts do not justify classifying every remaining G40 proof as externally blocked.
Independent read-only finder and skeptic reviews of this extent checkpoint
passed with no findings. They confirmed that all-offset word-count accounting
and the exact post-image iff do not narrow admission, and that the endpoint
control is raw-model evidence rather than a charged-execution claim.

`MemoryLoadExecutionInterface.lean` extends the existing access, raw-load and
extent certificates with actual fetched charged MLOAD/P6 linkage. It retains
all original gate refusals and budgets. The success branch takes the actual
gate result, initial image, stack and bounded span; it must derive execution,
loaded bytes, saved tail and the exact existing post-image boundary. It assumes
no desired value, run or reached state, nor a concrete byte-world producer.

`MemoryLoadExecution.success` now supplies that linkage. It proves directly
that the MLOAD gate changes gas without changing memory, active words or the
stack, then reuses `MemoryCharged.load_charged`, `MemoryLoad.payload` and
`MemoryLoadExtent.post_image`. The reached state and value are derived from
actual execution. Existing error branches, gas charges, full reached-state
formula and zero/one driver budgets are retained by the extended certificate.
No desired run, code-realization producer or Source-origin premise is supplied.
The post-image iff keeps the already-proved strict word-fit boundary explicit.
`MemoryLoadControls` adds a real nonzero ordered charged load at gas 3 with two
saved tail words and its P6 image, for either pipeline and arbitrary continuation
fuel; gas 2 actually refuses despite a valid initial image. These are pinned
logical-runtime checks, not external EVM tests or Source/compiler adequacy.
Independent read-only finder and skeptic reviews passed with no findings. They
confirmed the gate result is not an assumed run or poststate, inheritance keeps
all original failure/resource equations, and both charged controls use inhabited
initial images. The remaining full G40 and G46 correspondence obligations are
unchanged; this checkpoint does not supply a complete lane gate or producer.

`ValueGateInterface.lean` states a bounded intrinsic G40 value-check contract:
selection through the public checked compiler, exact emitted instruction shape,
and execution for every machine. It covers payable bypass and non-payable zero
value, preserving the complete successful machine. It does not certify runtime
selector dispatch, failure bytes, gas, or Source/physical entry provenance.
`ValueGate.lean` implements the typed require family and proves the public
`Evm.Compiler.compile` selects it for every base, context and fragment. Any
selected result has the exact five-instruction non-payable gate (or empty
payable bypass), and actual intrinsic execution accepts exactly payable or zero
value. Success preserves the complete machine, including stack, word
memory, storage and environment, with no residual skip. Nonzero rejection is
the existing intrinsic revert outcome; it does not independently certify empty
ABI revert bytes, rollback, native gas/stack limits, Source dispatch or an
emitted physical entry. No desired compiled value or run is an input premise.
`ValueGateControls` uses an inhabited nonempty context and two distinct saved
stack words with protected nonzero memory. Public selection, zero acceptance,
all-word payable bypass, arbitrary nonzero rejection, maximum-word rejection
and a payable/nonzero refusal of a false revert claim are checked.

Independent read-only finder and skeptic reviews passed with no findings. They
confirmed actual public selection, arbitrary selected-result execution, complete
successful machine preservation, and the explicit intrinsic-only boundary.

`ValueGateBodyInterface.lean` states actual public-compiler selection and exact
intrinsic execution for a value gate followed by any typed body admitted by the
existing core classifier, including context-changing bodies. This is a supported
compiler family, not an exclusion from the original full G40 obligation. It
assumes neither a desired body outcome nor a compiled artifact or run. Native
failure bytes/resources and Source entry/provenance remain separate.
`ValueGateBody.lean` constructs that typed prefix through the existing public
compiler. Both the body and guarded whole are actually selected, and any such
selected results satisfy exact intrinsic composition: allowed values run the
body on the unchanged input machine; rejected values revert before the suffix.
The result retains the body's complete outcome, including fault, revert and
residual skip. It reuses the prior value-gate proof and existing run-append
laws rather than assuming body execution. The core-classifier premise is the
actual existing check for this supported family, not a new Source/profile
admission or a supplied compiled-body result.
Controls select a context-growing scalar declaration, prove its genuine fresh
word-memory mutation, preserve the old cell and two saved stack words, and
exercise zero/payable execution versus nonzero rejection. Raw fault and skip
controls belong only to the arbitrary-suffix helper; they do not pretend those
suffixes have been admitted by the typed-body compiler. Full G40 decoding,
selector dispatch, memory-body/profile closure and Source/native failure-byte
adequacy remain open.
Independent read-only finder and skeptic reviews passed with no findings. They
confirmed genuine public selection, no assumed body execution, complete outcome
preservation and non-vacuous mutation controls. Both distinguished the supported
core family from the remaining full G40/profile obligation.

`CalldataWordInterface.lean` and Bridge `AbiWordInterface.lean` state exact
all-offset zero-padded word agreement and the existing numeric validators'
agreement with the indexed semantic word decoder. Native charged-load failures
and budgets are inherited. Raw word access is not an entry span/length check;
short input may zero-pad, while full entry still has its original guards.
Validator execution remains in the existing numeric runner, not a newly proved
fetched native validator sequence. Decoder fuel and free-memory parameters
remain explicit rather than being hidden by a success premise.
`CalldataWord.lean` reuses `Yul.Views.abi_readBytes_fit` and the published reader
bound to identify every semantic byte window and source word read. Bridge
`AbiWord.lean` then reuses the native calldata certificate and existing
`WordValidation.validator` proofs. The native word, its lossless numeric-runner
representation and every kind's flag agree with `Semantics.AbiEntry.load`.
Positive-fuel semantic word rejection is exactly the false flag, for all length
and free-memory parameters. No decoded payload or desired run is assumed.
The extended certificate retains every original charged-load failure and low
budget; native execution of the validator code itself remains open.
Controls install exact bytes with a nonempty unaligned prefix and ordered
suffix, check uint/address acceptance and bool/enum/bytesN rejection, preserve
both saved tail words in an actual fetched load with exact reached state and
charge, and retain large-offset/empty-input zero padding. Empty raw word access
is not entry acceptance. Zero decoder fuel remains distinct from rejection.
Aggregate decoding, emitted span/offset/length guards, full native validator
composition, dispatch and Source/physical entry adequacy remain open.
Independent read-only finder and skeptic reviews passed on semantics. They
identified a nested duplicate axiom guard for `fetched_word`; the guard block
was corrected to one matching annotation per print. Final diagnostics report
zero errors and both focused review follow-ups confirm the fix with no
outstanding findings. Neither review used a Lean server or build.

`HeadCheckInterface.lean` states the ordinary indexed decoder's initial
selector-inclusive short-head predicate over an actual size word. Its explicit
word-to-byte-length equality is an initial representation fact; native size
loading and coverage of Source inputs are not supplied. A true flag means this
initial guard rejects; a false flag does not imply entry success. Receive and
fallback selection use their separate paths and are not replaced by this check.
`HeadCheck.lean` emits the actual short-head flag through the existing unsigned
bound emitter and exports a non-vacuous Selection V2 frame. Arbitrary semantic
head extents at or above the word range reject every size word rather than
truncating an immediate. The complete saved numeric suffix is preserved and
capacity holds under the explicit one-extra-word bound. When the size word
represents the actual byte length, its flag is exactly the semantic initial
predicate; short input has the original early `.revert` even at zero fuel.
Controls cover empty/one-word selector boundaries, mixed static tuple/dynamic
heads, oversized static metadata, actual height refusal and an inhabited V2
frame. A passed head followed by a dirty bool still rejects; a complete empty
head can succeed with no decode fuel. These preserve phase/error distinctions.
Native size-word correspondence and its Source-input coverage remain open;
no word-size relation is silently adopted as a global input exclusion. This
predicate is not fetched native branching or a full decoding/admission result.
Independent read-only finder and skeptic reviews passed with no findings. They
confirmed saturation rather than immediate truncation, the non-vacuous frame
bound, preserved fuel ordering and the explicit distinction between head flags,
initial representation and full entry admission/native execution.

`OffsetChecksInterface.lean` states exact emitted tail/region predicates over
four runtime words with explicit stack order. Signed comparisons and modular
arithmetic are retained; neither predicate alone is whole-reference or entry
admission. Native argument loading, metadata-to-word correspondence and the
separate length/fuel/entry checks remain open.

`OffsetChecks.lean` implements both predicates through the existing Scalar
instruction semantics, with zero-based SWAP indices. General proofs cover every
four-word operand tuple and preserve the entire saved numeric suffix. Selection
V2 frames have explicit input room and capacity proofs; their one-word peak is
conservative for the region sequence. Signed comparisons, subtraction and
multiplication wrap exactly as in the semantic predicates. Controls retain
negative relative offsets, wrapped products, zero extents and boundary refusals.
A concrete `tailRef` control accepts a wrapped negative relative offset from raw
bytes; it uses decidable evaluation without any axioms. This guards against
silently replacing the semantic predicate with a stronger unsigned span check.
The other controls and general proofs use only standard Lean axioms. Runtime
operand loading, metadata correspondence, length64/fuel/other guards, fetched
native branching and whole-entry/Source coverage remain open.
Independent read-only finder and skeptic reviews passed with no findings. Both
checked operand order against actual Scalar semantics, exact signed/modular
agreement, suffix preservation, concrete capacity and the distinction between
semantic reference acceptance and full entry/native execution.

`LengthCheckInterface.lean` specifies dynamic-length admission at the semantic
64-bit limit with suffix/capacity preservation and lazy rejection after the
actual tail and length-prefixed guards. Loading correspondence and all other
entry checks remain separate obligations.

`LengthCheck.lean` reuses the existing bound compiler at `lim+1` and proves
admission iff the runtime length is at most `2^64-1`, preserving the whole
numeric suffix. Its Selection V2 certificate has explicit capacity and input
room. General semantic theorems preserve lazy reference `.revert` after a
passed tail check, and eager bytes/array `.panic` after a present length head.
The latter are semantic model equations, not certificates of native allocation
failure production. Raw-byte controls derive the oversized length from bytes,
including zero-padded offset loading, without a decoded payload premise.
Controls retain maximum accepted length, first rejected length, all-high word,
zero length, short-head-before-panic and fuel-before-panic behavior. Capacity
refusal and an inhabited frame are checked. Factored raw-load lemmas keep these
computations within unchanged recursion/heartbeat limits. Native loading,
branching, actual allocation failures and full entry composition remain open.
Independent read-only finder and skeptic reviews passed with no findings.
They checked the exact limit boundary, saved suffix and non-vacuous frame,
raw-byte derivation and guarded lazy/eager failure ordering, and confirmed
that native allocation/entry correspondence is not claimed.

`AccessBridge/HeadSizeInterface.lean` states the fetched charged CALLDATASIZE
consumer using published P10 input installation. Its all-input numeric result
uses the actual modulo word size, with semantic length agreement kept separate.
It does not claim a fetched native short-head branch or Source adequacy.

`AccessBridge/HeadSize.lean` reuses published P10 `calldatasize_source_input`,
without reproving its fetched opcode or charged execution. It derives the
whole native state and X continuation, then consumes the actual pushed size
in the existing numeric head compiler. For every installed byte input the
numeric result compares its length modulo the word range. An explicit local
representability fact yields the exact semantic short-head predicate; it is
not silently adopted as a Source-input exclusion. An arithmetic wraparound
control demonstrates why that fact cannot be removed. Semantic early revert
retains original fuel ordering. Inhabited native controls preserve protected
memory, saved tail, active words, PC and exact two-gas charge. These are separate
native-size and numeric-head execution layers; a fetched native head-check
branch, general Source authenticity/coverage and full entry composition remain
open. Bridge MCP returned diagnostics_unavailable, so focused serial importing
builds checked these modules instead; no simultaneous server/build or budget
increase was used.
Independent read-only finder and skeptic reviews passed with no findings.
They confirmed the actual P10 pushed value is consumed, modulo conversion and
local representability are explicit, protected-state controls are inhabited,
and the two execution layers and remaining native/Source boundary are clear.

`AccessBridge/MemorySizeExecutionInterface.lean` specifies fetched charged MSIZE
from an initial P6 image, preserving exact bytes, extent and saved stack with
state/continuation accounting. Gas and stack capacity remain explicit; this
is a primitive bridge, not whole compiler/Source adequacy.

`AccessBridge/MemorySizeExecution.lean` composes published P10 `msize_agreement`
with the existing P6 image payload theorem. From initial representation, gas
and stack room it derives the actual fetched reached state, X continuation,
exact observed `32*highWaterWords`, complete saved stack and preserved frame
image. It also retains memory bytes, exact two-gas charge, PC increment and
execution count. The image is proved fieldwise since accounting fields change;
no desired reached state or successful execution is assumed. Inherited charged
contracts keep failures and fuel budgets visible. Controls inhabit either
pipeline, retain two unequal saved words, observe 64 bytes despite reserved
capacity 96, permit arbitrarily enlarged reserves and reject wrong active
extent and short fuel. This completes this primitive linkage only: other
memory/copy/store payloads, general compiler selection and Source/world adequacy
remain open. The physical-write counterexample and all producer boundaries are
unchanged. Bridge diagnostics remained unavailable; focused serial importing
builds checked the implementation after stopping its server.
Independent read-only finder and skeptic reviews passed with no findings.
They confirmed initial-image-derived execution, exact post-image/accounting,
standard word-fit handling, inhabited either-pipeline/unbounded-reserve controls
and preservation of inherited failures and remaining compiler/Source boundaries.

`TailGuardInterface.lean` specifies a single composed numeric length-prefixed
reference guard with exact signed offset, length-limit and modular region
predicates. The runtime size operand is shared explicitly; loading and native
conditional branching remain separate.

`TailGuard.lean` composes the existing offset, length and region programs into
one actual numeric program with shared size input, preserved arbitrary suffix
and explicit one-extra-word capacity. Zero-based SWAP rotation and a duplicated
length retain inputs for the later checks; final ANDs combine their Boolean
flags. The exact semantic `tailRef` result is success with its original wrapped
address/length or `.revert`, under explicit initial operand-to-input facts and
length-prefixed shape. No successful decode/poststate is a premise. These
representation facts are not new global admission restrictions: full native
loading, unbounded metadata coverage and Source-input coverage remain open.
Evaluating pure numeric checks together does not certify native load/failure
ordering. Controls preserve each predicate refusal, noncanonical signed-offset
acceptance, raw zero-filled empty-array success, suffix and stack refusal; the
raw control proves its representation facts directly from bytes. This is a
composed numeric guard/reference result, not fetched native branching, whole
ABI aggregate decoding or full entry dispatch/composition. Existing failure
bytes and all producer boundaries remain unchanged.
Independent read-only finder and skeptic reviews passed with no findings.
They checked actual rotation/DUP/AND execution, shared size, non-vacuous capacity,
signed/modular preservation, exact initial-representation-based reference result
and raw control. They confirmed native load/error ordering and full coverage
are explicitly left open rather than inferred from pure-check conjunction.

`RawTailGuardInterface.lean` specifies deterministic raw-byte operands and the
actual semantic tail condition for the existing guard. Size, base and shape
metadata are unrestricted naturals; no loaded payload/run or representability
premise is supplied by callers. Native operand-loading execution remains open.

`RawTailGuard.lean` derives both words from the actual byte input and proves the
existing numeric guard agrees for every input, pointer, base and shape, without
caller-supplied decoded payload, successful run or load equalities. Subtraction
and product periodicity bridge arbitrary natural byte size and shape metadata
to word operands; no representability bounds or new input exclusion are needed
for these particular modular guards. Length-prefixed references retain the
exact semantic success pair or empty revert. Initial eight-word construction
is an operand specification; actual fetched native load construction and its
failure/gas ordering remain open. Controls use real bytes for a wrapped negative
offset accepted by the reference and cover empty/malformed inputs and a stride
beyond the word range. This does not close aggregate payload decoding, native
branching, Source coverage or entry dispatch/composition.
Published master was adopted with both append-only module-map row sets retained
and generated roots regenerated. Its physical byte-store increment concerns
compiler slices and leaves the pinned native HostWriteControls mismatch intact.
Independent read-only finder and skeptic reviews passed with no findings.
They checked raw load/address derivation, modular identities for unrestricted
metadata, exact length-prefixed reference outcome and real signed-negative
controls. The finder also verified that the master merge retained every row
from both module-map parents. Native execution and full coverage limits remain
explicit and were not inferred from the operand specification.

`AccessBridge/EmptyCopyInterface.lean` states the actual zero-length calldata
copy family with arbitrary source and destination words, explicit initial
stack/gas/capacity and exact reached state/continuation. Nonzero copies and
Source/compiler adequacy remain open.

`AccessBridge/EmptyCopy.lean` proves the actual pinned zero-length CALLDATACOPY
is the identity on shared state for every source and destination word. It
derives the real gate from initial stack/gas/capacity, proves zero expansion
and exact three-gas charge, and uses the existing charged driver and X law to
obtain the complete reached state and continuation. No desired run/poststate
is supplied. P6 frame images and empty-span touch survive the accounting and
stack changes. The certificate inherits all existing charged failure/budget
contracts. Controls inhabit either pipeline and test offset `2^64`, maximal
source, unequal saved words, dirty protected bytes, exact gas/PC/active extent,
insufficient gas and short fuel. Zero length is a proved family case; nonzero
native copy/store preservation, compiler selection and Source/world adequacy
remain open, with the host-writer counterexample unchanged. Bridge diagnostics
remained unavailable; after stopping the server, focused serial builds checked
proofs and controls without budget increases or concurrent Lean jobs.
Independent read-only finder and skeptic reviews passed with no findings.
They checked the actual all-offset identity, derived gate/charge, complete
execution/continuation, connection of the P6 post-image to the same reached
state, and extreme/dirty-byte/refusal controls. Both confirmed the zero-length
family does not imply nonzero physical write or Source/compiler adequacy.

`SelectorMatchInterface.lean` specifies an intrinsic four-byte selector matcher
and exact raw prefix agreement after a complete four-byte prefix. Short-input
classification remains explicit and is not inferred from a padded word match.

`SelectorMatch.lean` emits actual SHR/EQ over the existing numeric execution
framework. It preserves the entire saved suffix and compares high four bytes
against an intrinsic four-byte selector, with explicit Selection V2 capacity.
Raw agreement reuses the published word reader, byte bound and inverse codec;
concatenation/division isolates the prefix exactly without constraints on the
remaining payload. The actual `Source.Glob.selector` fixed-hash bytes are
preserved and the predicate is expressed in Source's comparison direction.
The full-prefix precondition is local: short inputs are separately proved not
to match four-byte Source selectors. Controls show why it is needed: a padded
two-byte input can match numerically while the Source prefix comparison is
false. They also cover raw match/mismatch, all-low-payload variation, empty
input, distinct saved words and an inhabited/capacity-refused frame. No fetched
native load/branch, lookup ordering, collision resolution, receive/fallback,
Source compiler selection or full dispatch/composition is claimed here.
Independent read-only finder and skeptic reviews passed with no findings.
They verified byte order and equal-width injectivity, exact Source selector
bytes/direction, local full-prefix condition and concrete padded collision,
and non-vacuous suffix/capacity controls. Full runtime dispatch boundaries were
confirmed explicit rather than inferred from this numeric predicate.

`SelectorRoutesInterface.lean` states typed first-match selector-local routing
through the existing public compiler, with exact result-cell mutation and
complete machine preservation. Route labels are not ABI bodies or authenticated
Source declarations; raw loading and entry/body composition remain open.

`SelectorRoutes.lean` constructs typed programs over two existing uint locals
and proves the public `Compiler.compile` selects the core family for every
finite selector/label table. It then proves actual emitted IR execution selects
the first matching entry or fallback label, writing only the result local and
preserving the entire remaining machine and saved stack with zero pending
skip. Initial selector-cell representation is the only value input fact; no
desired route, compiled value, successful run or poststate is assumed. Duplicate
selectors retain first-entry priority. Controls use actual public selection,
unequal saved words and protected memory, later-match/fallback, non-noop result
mutation, and a raw malformed selector cell that faults. An empty table does
not read that cell. Route labels and fallback labels are numeric results, not
Source declarations, compiled ABI bodies or Solidity fallback execution.
Calldata-to-selector-local transport, Source table authenticity/precedence,
receive/fallback/payability, native fetched realization and full entry/body
composition remain open. This extends the existing intrinsic compiler and IR;
no replacement dispatcher interpreter or untyped syntax is introduced.
Independent read-only finder and skeptic reviews passed with no findings.
They checked actual public compiler selection, emitted jump/skip behavior and
first-match induction, exact result-cell-only mutation and malformed/empty-table
controls. Both confirmed route/fallback labels are not represented as Source
or ABI dispatch success, and the remaining correspondence boundary is explicit.

`SourceRoutesInterface.lean` specifies ordinary Source lookup to checked route
execution using raw selector bytes, retaining complete-prefix and initial-cell
representation facts. Compile-time labels do not certify declaration bodies.

`SourceRoutes.lean` builds ordinary route tables from actual exposed declarations,
virtual-dispatch body presence and function signatures. It retains Source order
and actual fixed-hash selectors. The table depends only on compile-time global,
contract and label mapping, never calldata or a preselected declaration. Raw
selector comparison reuses `SelectorMatch`; its exported hash-prefix value
lemma avoids repeatedly normalizing serialized hashes and keeps original proof
budgets. Exact lookup matches `Source.Glob.pickFn`, and actual public-compiler
route execution writes that declaration's label while preserving the rest of
the machine and saved stack. Only initial selector-cell representation and a
complete prefix are required, not a successful lookup/run/poststate.
Controls use a typed abstract Source unit with a body-less declaration and two
colliding model selectors in both pipelines. They verify exclusion/order,
match/miss, protected state and actual compiled execution. The model hash is
explicitly synthetic, not a Keccak or deployment/admission test. A short input
selects no ordinary Source function while unguarded numeric routing matches a
padded selector; this pins the required outer length branch. Compile-time labels
need not be injective and are not compiled bodies. Their body association,
getters, receive/fallback/payability, native loading/realization and full Source
entry execution/admission remain open. No Source module or ExtCall constructor
was changed.
Independent read-only finder and skeptic reviews passed with no findings.
They checked input-independent table construction against actual `pickFn`,
virtual-body/signature eligibility and collision order, reused hash-prefix value
proof, and actual public-compiler execution. Both confirmed the synthetic
fixture and short-input mismatch do not certify Keccak, deployment admission,
body execution or full ABI entry behavior.

`PayableRoutesInterface.lean` specifies first-match per-entry value gating.
A matched non-payable row rejects value rather than trying later collisions;
a no-match label remains separate from Solidity special-function execution.

`PayableRoutes.lean` inserts the existing checked value gate inside each
matching selector branch of a typed route table. Public compiler admission and
selection are proved for every table, then actual emitted IR execution derives
the first row's label or terminal `.revert` according to that row's payability
and the initial call value. It never retries a later colliding row after a
rejection, nor checks a nonmatching row's value gate. The no-match label is
written without imposing a global value rule; it is not Solidity fallback
execution. Constructor adapters reuse the existing selector test/result write.
Controls cover zero-value nonpayable success, all nonzero-value rejection,
a later payable match and no-match label for arbitrary value, a payable duplicate
that cannot bypass rejection, protected memory/stack/value and malformed-cell
fault. Only the result cell changes on success, with zero pending skip.
Connecting row flags to Source mutability, native loading/realization, exact
byte-level failure output, special functions and ABI body composition remain
open. Newly adopted master control realization explicitly retains native and
Source/G24 boundaries, so it does not silently discharge these obligations.

Independent read-only finder and skeptic reviews passed with no findings.
Both checked public compiler selection, branch skip lengths, terminal collision
rejection, per-row value checks, protected state and the explicit remaining
Source/native/body boundaries; neither used a Lean server or build.

`SourcePayableInterface.lean` specifies declaration-derived payability and
first ordinary selector-match agreement, with explicit selector-cell and
call-value representation. Source body and special-function execution remain
separate obligations.

`SourcePayable.lean` constructs compile-time route rows from the actual exposed
Source declarations, retaining existing body/signature eligibility, selector
order and `Decl.fnMut` payability. General lookup agrees with `pickFn`; actual
public compiler selection and IR execution derive the first matched label or
terminal rejection. Initial selector-cell and call-value representation remain
explicit. The ordinary Source rejection theorem proves the existing dispatch
halts with empty revert bytes before decoding for a matched nonpayable entry
with nonzero value. Numeric IR `.revert` has no byte-output representation, so
these endpoints do not claim a native failure-byte correspondence.
Controls use a typed synthetic colliding hash and both pipelines: bodyless
exclusion, actual declaration flags, zero-value acceptance and nonzero rejection,
payable success at
all values, collision cannot bypass rejection, no-match label at all values,
protected state and actual Source empty-revert-byte execution. No-match labels
remain observations, not getter/receive/fallback bodies; labels need not be
injective. Full entry/body association, native realization, aggregate decoding,
short-input dispatch and admission remain open. A costly direct declaration
witness check timed out in MCP; closed signature/payability metadata plus a
case split on the actual lookup avoids declaration equality without a budget
increase or stronger premise.

Independent read-only finder and skeptic reviews passed. Both checked actual
Source flag authenticity, selector order, public selection/execution and the
separate exact Source rejection endpoint. The skeptic's wording correction
clarifies zero-value acceptance versus nonzero rejection; no code findings.
Neither reviewer used a Lean server or build.

`ShortRoutesInterface.lean` specifies a compiled length-local branch before
ordinary selector routing, with explicit length and selector representation.
The short continuation label does not execute receive/fallback bodies.

`ShortRoutes.lean` compiles the missing outer length check through the existing
intrinsic/public compiler. The result local initially contains length, then is
reused for the selected label. Inputs shorter than four bytes reach the short
continuation without selector or value checks; full inputs run the existing
per-entry payable routes. General actual execution preserves every other
machine field and saved stack, with zero pending skip. The Source-linked
execution theorem covers both branches using explicit selector, length and
call-value representation. Separately, `source_short` reuses the existing
four-byte selector theorem to prove actual ordinary `pickFn` is absent for all
short inputs. Length is an unsigned represented word; native size loading and
fetched execution are still open.
Controls cover all represented sizes below four, concrete sizes zero through
three, exactly four with zero/nonzero value, a three-byte padded-selector
collision fixed by the guard, the unguarded counterexample, actual Source
ordinary exclusion, malformed length-cell fault and protected state. The
short label deliberately leaves empty-input receive versus nonempty fallback,
getters, special payability/body execution and full ABI composition open;
no-match/short labels are not executed special bodies. Native failure-byte
correspondence and aggregate decoding remain open. No Source/Core changes or
new untyped framework are introduced.

Independent read-only finder and skeptic reviews passed with no findings.
They checked length-cell reuse, actual branch offsets and compiler selection,
Source short exclusion and both-branch linkage, padded collision controls,
protected state and the explicit native/special/body boundaries. Neither used
a build or Lean server. Unused simp arguments found by the focused build were
removed and the importing consumer rechecked without own warnings.

`SpecialRoutesInterface.lean` specifies empty-input receive preference, fallback
choice, absence rejection and selected special payability. It certifies
continuation routing, not special-body execution or fallback parameter binding.

`SpecialRoutes.lean` emits the empty-input branch, preferring receive when
present, otherwise fallback, and selecting fallback for nonempty input. Missing
special entries emit rejection; selected entries run the existing value gate
before writing a continuation label. General public compiler admission and
selection and actual emitted IR execution preserve the whole saved machine
apart from the result/length cell, with zero pending skip. Compile-time rows
map actual `Env.special` declarations and `Decl.specialPayable`; general Source
lookup and execution transport retain explicit length representation. These
are special-path continuations: integration after ordinary/getter misses is
not yet compiled here. Independent actual Source theorems prove absence and
nonpayable refusal produce empty revert bytes before body lookup, with ordinary
and getter misses explicit. IR rejection does not encode bytes, so native
byte correspondence is not inferred.
Controls cover arbitrary-value receive preference, absent receive fallback,
nonempty nonpayable refusal, empty nonpayable refusal without receive, total
absence, all-value payable fallback, actual declaration-derived flags, actual
Source absence/refusal bytes, malformed length and protected saved state. No
special body execution or parameterized fallback input/output transport is
claimed; getters, native realization, aggregate decoding and full ABI body
composition remain open. A bounded MCP scratch attempt timed out; its workers
were stopped before clean per-file diagnostics, without a budget increase.

Independent read-only finder and skeptic reviews passed with no findings.
Both checked actual branch selection/execution, declaration-derived special
flags, Source rejection premises and exact saved state; neither used a build
or Lean server. They confirmed Source-selected rows still use machine call
value in the IR outcome and do not certify successful Source body execution.
Unused simp arguments were removed after focused compilation and the importing
consumer was rechecked.

`EntryRoutesInterface.lean` specifies one compiled continuation path: short
inputs use special selection, full inputs prefer the first ordinary match,
and ordinary misses use special selection. Getter/body integration is open.

`EntryRoutes.lean` composes one typed continuation tree: short inputs enter
special selection; full inputs try ordinary rows in order, then enter special
selection on a miss. Selected ordinary value refusal is terminal, even when a
payable fallback or later collision exists. Length/result cell reuse leaves
original state intact for special selection on a miss. General admission,
public compiler selection and actual IR execution prove exact success state
and zero pending skip, with no supplied body run or poststate. Additive branch
adapters reuse the existing PayableRoutes proofs; no old implementation or
framework is replaced. Option-valued Source ordinary lookup is recovered from
the existing general default-valued theorem at two distinct defaults, so
absence stays distinct without relying on unique labels or redoing selector
proofs. Existing declaration-derived special rows are reused.
Controls cover arbitrary-value empty receive, short nonempty fallback including
a padded collision, full ordinary zero-value acceptance, terminal nonzero
refusal despite payable fallback/later collision, full misses, total absence,
equal ordinary/fallback labels, malformed length and protected saved state.
This remains continuation dispatch. Getter precedence must be compiled before
special selection on an ordinary miss; this module does not claim the whole
Source dispatch when getters exist. Native selector/size loading, native byte
failure correspondence, decoding/argument binding, parameterized fallback
input/output and successful ABI body execution/composition remain open.

Independent read-only finder and skeptic reviews passed with no findings.
They checked one actual selected tree, original length/state on misses,
terminal collision/value refusal, exact joins and noninjective-label option
recovery. Both confirmed the getter/native/body/binding boundaries; neither
used a build or Lean server. Focused importing-consumer compilation passed
without warnings in the changed modules.

`GetterRoutesInterface.lean` specifies actual Source ordinary/getter/special
continuation precedence through the existing EntryRoutes compiler. Getter
argument decoding, storage reads and output/body execution remain separate.

`GetterRoutes.lean` appends actual `Env.getters` rows to actual ordinary rows,
then uses the existing EntryRoutes tree for special selection on a miss. Getter
rows use the existing fixed-hash selector and are nonpayable. General lookup
proves ordinary-before-getter precedence against actual `pickFn`/`pickGetter`;
short-input getter absence reuses the four-byte selector theorem. The exported
actual public-compiler execution theorem covers every represented input length
and produces exactly the Source ordinary/getter/special row outcome, preserving
all machine state except the result cell and zero pending skip. Selector/length
representation is explicit; the outcome uses machine call value and makes no
silent claim equating it with a Source frame. Actual Source getter value refusal
is separately proved to return empty revert bytes before argument/storage work.
Controls use typed Source public uint variables, a payable ordinary function
and fallback, and a synthetic colliding hash on both pipelines. They cover
ordinary priority despite getter collision, first-getter order/zero acceptance,
nonzero rejection without fallback retry, short padded inputs/full misses to
fallback, exact Source getter refusal bytes and protected saved state. The hash
is not Keccak/solc evidence. Getter argument/head/type checks, storage reads and
return encoding, general ABI decoding/argument binding and successful body
execution remain open; labels remain observations, not compiled ABI bodies.
Native loading/fetched execution and failure-byte correspondence remain open.

Independent read-only finder and skeptic reviews passed with no findings.
They checked actual getter eligibility/order, ordinary/getter/special
precedence for short/full inputs, public compiler execution, Source rejection
bytes, synthetic controls and machine-versus-frame value/body boundaries.
Neither used a build or Lean server. The focused consumer was rechecked after
removing its single unused simp argument and has no changed-module warnings.

`DispatchRefusalInterface.lean` specifies exact routing-refusal classification
and empty Source revert bytes, with machine/frame value representation explicit.
It does not classify later decoder or body failures as routing refusals.

`DispatchRefusal.lean` classifies the actual continuation dispatch refusal:
nonpayable ordinary entries/getters/special entries receiving nonzero value,
or absence of any entry. With selector/length representation and explicit
machine-to-Source call-value equality, rejection of the actual publicly selected
compiled code is equivalent to this Source-derived predicate. A general Source
theorem proves each such refusal halts with exactly empty revert bytes before
later argument/storage/body work. Ordinary signature eligibility and nonempty
input are derived from actual `pickFn`; they are not extra premises. Existing
Source rejection theorems and actual getter compiler execution are reused.
The classifier is label-independent and does not assert native byte encoding.
Controls instantiate ordinary/getter/special/absent combinations on both
pipelines with a typed bool-parameter function, public uint and nonpayable
fallback. Nonzero calls reject in actual IR and actual Source; zero-value present
routes are not rejected by routing. A separate zero-value truncated-head control
has routing refusal false while actual Source still reverts with empty bytes.
This pins the exclusion of later decoder/body failures from the classification;
it is not a claimed completeness theorem for all Source reverts. The fixed hash
is synthetic, and native execution, aggregate decoding, successful ABI body
execution/binding and full entry composition remain open.

Independent read-only finder and skeptic reviews passed with no findings.
They checked explicit machine/frame value alignment, derived ordinary
eligibility, actual selected compiler code, label independence and one-way
Source rejection correspondence. Both verified the later-head-failure negative
control and rejected any reading as completeness for all Source reverts; neither
used a build or Lean server. Focused compilation has no changed-module warnings.

`HeadGateInterface.lean` specifies a typed/public compiler head-span guard
with exact reject/continue behavior, retaining unbounded semantic head extents.
Passing this initial check does not certify argument decoding or body execution.

`HeadGate.lean` implements the selector-inclusive ABI head-span guard as an
intrinsic program selected by the existing public compiler. Representable
extents compile to size comparison and conditional revert before writing a
continuation label; extents at least the word modulus emit unconditional revert.
General execution preserves all machine state except the result cell on
success, with saved stack and zero pending skip. Rejection is equivalent to
represented size below the full semantic extent. Its transport to the existing
ABI-entry early-failure theorem reuses `HeadCheck.early_revert`; no immediate
truncation or narrower input admission is introduced. Input-size loading and
native byte realization remain separate.
Controls cover empty and bool signatures, mixed static tuple/dynamic aggregate
heads, exact boundaries, all represented sizes against huge metadata heads,
and a wraparound counterexample (a huge extent has low word four yet rejects
size four). They also cover malformed size cells, fuel-zero semantic head
failure and protected state. Passing the emitted head gate still permits the
existing dirty-bool decoder failure; that semantic counterexample reuses its
previous proof. This guard does not certify whole decoding, typed argument
construction, selected-signature/body integration, native failure bytes or full
entry composition.

Independent read-only finder and skeptic reviews passed with no findings.
They checked actual compiler selection, operand order/equality, full-extent
oversized rejection, exact saved state and the one-way semantic failure
transport. Both confirmed the dirty-bool control prevents a full-decoding
interpretation; neither used a build or Lean server. Focused compilation has
no warnings in the changed modules.

`UnsignedGateInterface.lean` specifies actual public-compiler word validation
against an unbounded unsigned bound; wide bounds are not truncated. Raw loading
and full argument decoding remain explicit separate obligations.

`UnsignedGate.lean` emits actual typed/public-compiler unsigned word guards.
A represented bound uses a conditional revert; a bound at least the word modulus
writes the continuation directly, preserving all represented words without
truncating the bound. General admission/selection/execution preserves the input
local, full saved stack and all machine state except the result cell, with zero
pending skip. Exact rejection iff covers arbitrary natural bounds. For uint
widths (including address), bool and enum cardinality, raw-word representation
connects actual compiled rejection iff the existing positive-fuel lazy scalar
ABI decoder rejects. No decoded value or successful run is supplied. Separate
failure transports preserve the semantic `.revert` class. Span/head checks,
native loading/byte failure encoding, signed/fixed-byte compiler guards and
full argument decoding remain open.
Controls cover bool/uint8/address boundaries and dirty high bits, enum limits
and zero cardinality, all uint256 words, oversized bounds accepting every word,
and a wide-bound wrap counterexample. Raw unaligned prefixed inputs exercise
actual bool/enum/uint8 decoder failures and successful uint8 value derivation.
Empty raw access pads zero and passes bool range validation, while enclosing ABI
entry still rejects its short head; no span or admission narrowing is inferred.
Malformed input-cell and preserved-state controls are retained. Existing numeric
validators remain the implementation for their published certificates; these
modules add intrinsic compiler guard execution rather than replace them.

Independent read-only finder and skeptic reviews passed with no findings.
They checked strict comparison/zero/wide bounds, actual public selection and
preserved input/state, exact positive-fuel raw decoder iff and the empty-word
versus whole-entry distinction. Neither used a build or Lean server. A single
unused simp argument was removed and the importing consumer rechecked without
changed-module warnings.

`SignedGateInterface.lean` specifies actual public-compiler signed word cleanup
validation for every semantic width, preserving accepted sign-extended words.
Raw loading, native execution and full decoding remain separate.

`SignedGate.lean` implements signed cleanup validation through the existing
intrinsic/public compiler. A small unsigned range accepts nonnegative values;
the other branch accepts correctly sign-extended negative words. If the low
bound reaches the word modulus, the program accepts every represented word
without truncating a bound. Exact actual execution agrees with `Kind.int.valid`
for every natural width, preserves the input word and all saved state except
the result cell, and finishes with zero pending skip. A comparison adapter
reuses the existing unsigned condition; prior implementations are unchanged.
Raw-word representation connects compiled rejection iff the positive-fuel
existing signed scalar ABI decoder rejects, without a supplied decoded value
or run. Native loading, span/head checks and failure-byte realization remain
separate; existing numeric signed validators and their certificates remain.
Controls cover both int8 edges and adjacent dirty values, zero/one widths as
specified by the existing semantics, every represented word at widths 256 and
257, a wide-bound truncation counterexample, prefixed unaligned dirty/valid
negative raw words, malformed input and protected saved state. Raw successful
negative value derivation is explicit. Full argument construction, aggregate
decoding, fixed-byte compiler guards, body integration and full entry composition
remain open; these are word validators, not full ABI execution.

Independent read-only finder and skeptic reviews passed with no findings.
They checked signed endpoints, zero/wide-width semantics, actual emitted
comparison/branch joins and public selection, raw decoder iff and unchanged
valid negative words/saved state. Neither used a build or Lean server. Focused
compilation has no warnings in the changed modules.

`BytesGateInterface.lean` specifies actual fixed-byte padding validation;
`WordGateInterface.lean` unifies actual compiler validation for every existing
ABI word kind. Input loading and aggregate/body execution remain separate.

`BytesGate.lean` emits actual fixed-byte padding checks using the existing
intrinsic bitwise compiler. The mask is representable for every semantic size;
the standard mask/modulus identity already used by the numeric validator links
emitted execution to `Kind.fixedBytes.valid`. Input words and saved machine
state remain unchanged except the continuation/result cell, with zero pending
skip. Size zero and sizes at/above the full word retain their existing semantic
behavior, without a new admission restriction or input cleanup.
`WordGate.lean` delegates every existing ABI word kind to the proved unsigned,
signed or fixed-byte family. It exports general public compiler selection,
exact actual execution, rejection iff semantic validity is false, and raw
positive-fuel scalar decoder rejection equivalence for all kinds. No decoded
payload or successful run is supplied. This closes primitive word validation
at the intrinsic compiler boundary; native loading/byte failure transport,
aggregate decoding, head/span/signature integration, typed argument construction
and successful ABI body/full-entry execution remain separate obligations.
Unified controls exercise accepted and rejected uint, signed, bool, fixed-byte
and enum inputs, bytes0/1/31 boundaries, all words at full and oversized byte
sizes, prefixed unaligned padding failure and successful value derivation,
malformed cells and protected saved state. Existing numeric validators and
certificates are unchanged; their mask arithmetic lemma is reused.

Independent read-only finder and skeptic reviews passed with no findings.
They checked mask representability/saturating sizes, actual compiler selection
and saved state, exhaustive kind delegation and the positive-fuel raw scalar
correspondence. Both confirmed the primitive-only boundary and meaningful
unified controls; neither used a build or Lean server. Focused compilation has
no warnings in the changed modules.

`SingleWordGateInterface.lean` specifies sequential head/primitive validation
for one value parameter, actual entry-rejection agreement and explicit raw
representation/fuel boundaries. Native loading and aggregates remain separate.

`SingleWordGate.lean` now selects a typed head-guard block followed by the
existing all-kind primitive validator through the public compiler. General
execution preserves the input word and every machine component except the
continuation/result local, with zero pending skip. The intermediate and final
writes to that local are identical. Short heads reject before inspecting the
word cell. For one `.value` primitive parameter, represented raw word at byte
4 and represented input size imply rejection iff the actual entry decoder
returns `.revert` at fuel `fuel + 2`. The successful semantic result is a typed
word constructed directly from the byte load and its validity proof; no decoded
payload, desired execution or poststate is assumed. The explicit two-level
fuel requirement is retained: full heads at fuel zero/one return `.fuel`,
whereas short heads reject even at zero fuel.

Controls execute actual selected artifacts for a nonzero arbitrary selector
and trailing bytes, dirty bool input, a short head with malformed word memory,
a full head with malformed word memory, insufficient decoder fuel and protected
input/heap/storage/balance/saved stack. A direct whole-program fault reduction
hit the existing heartbeat bound; the final proof instead composes the proved
head execution and small unsigned condition code. No budget was raised.
Independent read-only finder and skeptic found no semantic issues in compiler
selection, exact state, raw value derivation or failure/fuel ordering; their
requested final validation, scoped axiom guards and implementation description
were completed. Scoped reports use only standard axioms.

This increment covers validation and semantic typed decoding of one primitive
value parameter. Native byte loading, argument materialization in the compiler,
aggregate/multiple parameters, dispatch-to-body linkage, exact native failure
bytes and whole G40 composition remain open. G46.02 general memory/calldata
correspondence and the physical writer counterexample are unchanged. Full
assignment final gates and fixture replay remain pending; shared doc-path and
axiom-inventory failures from previous checkpoints remain outside this lane.

`UIntBindingInterface.lean` specifies actual compiler validation followed by
binding a typed uint parameter local, exact frame state and raw entry rejection.
Native loading and full Source/body correspondence remain separate.

`UIntBinding.lean` now selects a typed program that performs singleton uint
head/word validation and declares the parameter with the existing `declLocal`
compiler path. For every semantic uint bit width, execution either rejects
exactly at the existing checks or extends the typed frame with the preserved
raw word. The continuation cell and new parameter cell are the only writes;
saved stack, input word, storage, balance and all other machine fields remain
as stated by the exact execution result. `decoded_and_bound` constructs the
semantic typed word from bytes at offset 4 and proves its equality to the
actual newly declared local identified through `cellOf`. No decoded payload,
desired run or poststate is a premise. Raw rejection agreement retains the
explicit represented word/size and `fuel + 2` boundaries.

Controls cover raw uint8 value 255 after an arbitrary nonzero selector with
trailing bytes, dirty high bits (256), zero-width acceptance/rejection, general
full and oversized widths, a short head, insufficient decoder fuel and exact
protected state. A separately selected compiled body reads the new typed local
and writes the continuation cell; this exercises local usability without
claiming whole Source-body linkage. Independent read-only finder and skeptic
reviews found no semantic issues. Focused compilation and per-file diagnostics
passed; individual axiom guards record only standard axioms.

This supplies intrinsic singleton uint argument binding. Boolean/signed and
aggregate bindings, native loading/frame realization, general argument and
signature pipeline composition, Source-body correspondence and complete G40
remain open. G46.02 and the physical writer counterexample are unchanged. The
shared doc-path and central axiom-inventory failures remain outside lane
ownership, and the full assignment gates and fixture replay remain pending.

`UIntBindingBodyInterface.lean` specifies one public compilation of validation,
uint binding and an existing core-admitted typed body, with exact ordered
execution. Body failures remain distinct from decoder rejection obligations.

`UIntBindingBody.lean` selects one typed compiler program containing validation,
uint parameter declaration and the body. Its supported body family is the
existing core classifier at the extended uint frame. Both the whole program
and body are selected through the public compiler; no target run or body result
is a premise. Exact execution checks the head, then word validity, then runs
the actual selected body on the proved bound state. It retains the complete
body outcome, rather than assuming body success. Raw semantic success at
`fuel + 2` derives the typed word from bytes and identifies the same new local
that the body reads. A short head prevents the word read and body, even if the
word cell is malformed.

Controls select and execute the complete program with a context-growing body
that reads raw 255, performs the compiler checked increment and stores 256 in
a new local. The arithmetic control reuses the existing `add_tail` proof.
An actual reverting body after successful raw decoding demonstrates why whole
program rejection cannot imply decoder rejection. Dirty input and short heads
stop body execution; semantic low-fuel controls, arbitrary selector/trailing
bytes and exact saved state remain explicit. Direct control reduction and
bounded automation timed out during development; factoring the actual checked
code and reusing its proof resolves checking without raising budgets. Focused
compilation, final per-file checks and standard-only scoped axiom guards pass.
Independent read-only finder and skeptic reviews found no semantic issues.

This composes singleton uint validation/binding with supported intrinsic typed
bodies. It does not supply Source body/label association, general profile
admission, native loading/frame realization, other argument families,
aggregate decoding, full dispatch/entry composition or physical failure bytes.
Those G40 obligations, G46.02, the writer counterexample, fixture replay and
full assignment gates remain open. Published master was adopted before this
increment; prior checkpoint evidence is retained without relabeling failures.

`BoolBindingInterface.lean` specifies validation before typed Boolean local
binding, exact compiler execution and raw entry rejection. Native loading
and general Source/body adequacy remain separate.

`BoolBinding.lean` selects a typed program that validates a singleton Boolean
entry and declares a `.bool` parameter through the existing compiler. The
initializer compares the raw word to one only after the existing exact
validator succeeds. `validated_word` derives zero-or-one from semantic
validity and proves the emitted Boolean encoding preserves that accepted raw
bit. Dirty values are rejected before conversion. Execution changes only the
continuation and fresh Boolean local, retaining the input word and remaining
machine state. Raw semantic decoding constructs the typed word from bytes and
identifies it with the actual new local; rejection agreement retains explicit
word/size representation and `fuel + 2`.

Controls bind both false and true after arbitrary selectors with trailing
bytes. Dirty raw two would convert to false in isolation but the actual
validated program rejects it; short heads reject before malformed word access.
A separately selected compiled typed branch reads the Boolean local and
writes different results for true and false. Low semantic fuel and protected
input/storage/balance/saved stack remain explicit. Per-file diagnostics and
focused compilation pass, with individually scoped standard-only axiom guards.
Independent read-only finder and skeptic reviews found no semantic issues.

This closes intrinsic singleton Boolean binding only. Successful whole Boolean
body composition, signed/aggregate binding, native byte loading/frame
realization, general Source/profile/body association, full dispatch/entry
composition and physical failure bytes remain open. G46.02, its physical writer
counterexample, fixture replay and full assignment gates are unchanged. The
existing shared metadata gate failures remain outside this lane.

`BoolBindingBodyInterface.lean` specifies one public compilation of Boolean
validation, typed binding and a core-admitted body, preserving ordered failures
and the actual body outcome. Native/Source adequacy remains separate.

`BoolBindingBody.lean` selects one typed program containing the exact Boolean
head/word validator, typed parameter declaration and body. The body family is
the existing core classifier at the extended Boolean frame. Whole and body
artifacts are both selected through the public compiler, with exact code
factorization and execution. No target run or body result is assumed. Head and
word rejection stop execution; successful validation/binding runs the actual
body on the proved state, retaining its entire outcome. Raw semantic success
at `fuel + 2` constructs the typed bit from bytes and identifies the actual
argument local that the body reads. Short input prevents both malformed word
access and body execution.

Controls execute the complete selected program with a context-growing typed
negation body for true and false inputs, writing the opposite bit into a fresh
local and preserving the argument and saved state. A real reverting body after
successful decoding distinguishes body failure from decoder rejection. Dirty
two, short malformed input, low semantic fuel, arbitrary selectors/trailing
bytes and protected storage/balance/stack are explicit controls. Focused builds,
per-file diagnostics and standard-only scoped axiom guards pass. Independent
read-only finder and skeptic reviews found no semantic issues.

This composes singleton Boolean validation/binding with supported intrinsic
bodies. Source body/label association, native loading/frame realization, signed
and aggregate bindings, multiparameter decoding, full profile/dispatch-entry
composition and physical failure bytes remain open. G46.02, its writer
counterexample, fixture replay and full assignment gates remain pending.
Published master was adopted before this increment; prior failure evidence is
retained rather than relabeled.

`ValueCheckedBodiesInterface.lean` specifies value checking before uint/Boolean
decoding, binding and typed body execution, including early rejection without
any calldata-local representation premise.

`ValueCheckedBodies.lean` composes the existing `ValueGateBody` with the proved
uint and Boolean entry/body programs through the same public compiler. Both
families export actual selection, ordered execution and raw typed-value/body
agreement. Execution checks payability/value before the head, primitive word,
parameter declaration and body. Early rejection quantifies arbitrary machine
memory with no word/size representation facts, so it prevents all calldata-local
reads. Allowed calls retain the existing raw decoding acceptance and the entire
body outcome. Raw word/local agreement keeps explicit representation and
`fuel + 2`; no decoded payload, target run or body result is assumed.

Controls execute the combined artifacts for payable entries at every represented
value, zero-value non-payable entries and nonzero non-payable entries with all
locals malformed. Passing the value check still rejects dirty uint high bits
and dirty Boolean two. Real typed bodies copy the uint argument or branch on
the Boolean argument, while an actual reverting body remains rejected after
successful decoding. Exact input/argument/other-cell, storage, balance, callvalue
and saved-stack observations are retained. Focused builds, per-file diagnostics
and individual standard-only axiom guards pass. Independent read-only finder
and skeptic reviews found no semantic issues.

Payability remains an explicit flag; existing `SourcePayable` supplies Source
metadata flags, but this increment does not establish Source declaration,
signature or body association. Native loading/frame realization, signed and
aggregate bindings, multiparameter decoding, full profile/dispatch-entry
composition and physical failure bytes remain open. G46.02, the writer
counterexample, fixture replay and full assignment gates remain pending.

`SignedBindingInterface.lean` specifies actual signed validation followed by
typed `.int` parameter binding with exact word/state and raw entry agreement.
The existing typed `toInt` cast preserves the accepted representation.

`SignedBinding.lean` selects a typed program that validates a singleton signed
entry and declares an `.int` parameter using the existing `UnOp.toInt`. The
compiler cast preserves bits; no new conversion or cleanup is introduced.
Exact signed validation precedes the declaration, retaining accepted sign
extension and rejection of dirty words for all semantic widths. General
execution preserves the input word and every machine component except the
continuation and fresh parameter cells. Raw decoding constructs the typed
word directly from bytes, identifies the actual `.int` local and relates its
signed reading to `Semantics.AbiEntry.toInt`, with explicit representation and
`fuel + 2`. No decoded payload, desired run or poststate is assumed.

Controls exercise signed-8 positive/negative endpoints and adjacent dirty
encodings, zero/full/wide metadata without truncation, raw sign-extended -128
after an arbitrary selector with trailing bytes and nonzero free pointer,
short malformed input and insufficient semantic fuel. A separately selected
compiled signed comparison reads the new local and distinguishes negative
from positive. Exact saved input/storage/balance/stack observations remain
explicit. Focused builds, per-file diagnostics and individually scoped
standard-only axiom guards pass. Independent read-only finder and skeptic
reviews found no semantic issues.

This supplies intrinsic singleton signed binding. Whole signed body/value
composition, aggregate and multiparameter decoding/binding, native loading/frame
realization, Source declaration/body/profile association, full dispatch-entry
composition and physical failure bytes remain open. G46.02, the writer
counterexample, fixture replay and full assignment gates remain pending.
Published master was adopted before this increment; existing evidence remains
separate from new checkpoint outcomes.

`SignedEntryBodyInterface.lean` specifies actual value-checked signed decoding,
typed binding and core-admitted body execution with exact ordered outcomes.
Early value rejection needs no calldata-local representation facts.

`SignedEntryBody.lean` selects a single typed program containing value checking,
signed head/word validation, the existing bit-preserving `.int` declaration and
an existing core-admitted body. Binding/body and complete artifacts are selected
through the public compiler. Exact execution preserves value-before-head-before-
validation ordering and then runs the actual body on the proved bound state,
retaining its whole outcome. Early non-payable rejection needs no calldata-local
representation facts. Raw semantic success constructs the typed word from bytes,
identifies the actual local and signed reading, and keeps `fuel + 2` explicit.
No decoded payload, desired execution or body result is supplied as a premise.

Controls execute the complete program at every represented payable value for
negative and positive signed bytes, allocating a Boolean sign result from the
new `.int` local. Zero-value non-payable success, nonzero-value rejection before
all malformed locals, strict dirty-word rejection, short-input rejection before
word/body access, raw typed-value agreement and low semantic fuel are explicit.
An actual reverting body after successful decoding distinguishes body failure
from decoder rejection. Saved input/argument/storage/balance/stack observations
are retained. The short control exercises the complete value-checked artifact.
Focused builds, final per-file diagnostics and standard-only scoped axiom guards
pass. Independent read-only finder and skeptic reviews found no semantic issues.

This supplies supported singleton signed value/entry/body composition. Payability
remains an explicit flag; Source signature/declaration/body association, aggregate
and multiparameter decoding/binding, native loading/frame realization, general
profile/dispatch-entry composition and physical failure bytes remain open.
G46.02, its writer counterexample, fixture replay and full assignment gates
remain pending.

`WordCarrierBindingInterface.lean` specifies public compiler selection and exact
singleton primitive validation followed by declaration of the existing typed
uint carrier, including enum and fixed-bytes words. The carrier stores raw
accepted bits; it does not replace typed Boolean/signed binding or authenticate
Source type erasure. Raw semantic failure agreement retains `fuel + 2` and
explicit word/size loading obligations. Native loading and general entry
composition remain open.

`WordCarrierBinding.lean` extends the existing singleton head/word gate with
`UIntBinding.parameter` and the same typed declaration and machine carrier.
Public compiler selection, exact execution and raw semantic success/failure
agreement hold for every primitive kind and semantic metadata value. The uint
specialization is definitionally the existing binder. The fresh local stores
the validated raw bits without cleanup; Boolean and signed Source locals still
use their distinct bindings. No decoded payload, desired run or poststate is
assumed. Exact success changes only the continuation and fresh argument cells;
short heads reject before any word-cell representation fact is needed.

Controls cover raw enum values at and below the cardinality, fixed-bytes data
with clean and dirty right padding, arbitrary selector and trailing bytes,
nonzero free pointer, empty enum and zero-byte boundaries, full/wide bytes
metadata, and all words for enum cardinalities at least the word modulus.
They retain low semantic fuel, malformed-word short input, exact saved state
and an actually selected compiled read of the new carrier. Per-file diagnostics,
focused importing-consumer build and scoped standard-only axiom guards pass.
This is raw carrier binding, not Source signature erasure or whole body linkage.
Independent read-only finder and skeptic reviews found no semantic issues.
Checkpoint outcomes accompany the sealed handoff. Native loading,
aggregate/multiparameter decoding/binding, Source
signature/body/profile association, full dispatch-entry composition and exact
physical failure bytes remain open, as do G46.02 and fixture replay.

`WordCarrierEntryBodyInterface.lean` specifies actual compiler selection and
ordered value/head/primitive validation, raw carrier binding and body execution.
The body is admitted by the existing core classifier; its run and result are
not premises. Early non-payable rejection needs no local representation facts.
The signature retains explicit raw loading and Source/body-linkage boundaries.


`WordCarrierEntryBody.lean` selects one typed program that composes the existing
value guard, primitive head/word validation, unchanged raw uint declaration and
an existing core-admitted body. Both whole and body artifacts are selected by
the public compiler. Exact execution orders value, head and word failure before
binding/body execution and retains the body's complete actual outcome. No body
run/result is assumed. Raw success constructs the indexed semantic word from
bytes, identifies the actual carrier local and connects the whole artifact to
the actual selected body at that bound state, retaining `fuel + 2` and explicit
word/size representation. Early value rejection needs no local facts; short
heads preempt malformed word/body access. All primitive metadata remains exact.

Controls run an actual body that compares the new carrier with two and allocates
a Boolean result. Enum values two and one produce different results; clean
fixed-bytes input executes the same body. Payable values range over all words;
zero non-payable success, arbitrary-machine nonzero rejection for every kind,
out-of-range enum and dirty padding, raw typed-value/body agreement, low fuel,
short malformed input and saved machine state are explicit. Wide byte metadata
preserves the decoder's accepted case and executes the body on the same bytes
that a narrow validator rejects. A reverting body after successful decoding
prevents confusing body failure with decoder rejection. Per-file diagnostics,
focused importing-consumer build and scoped standard-only axiom guards pass.

This supplies supported raw singleton carrier value/entry/body composition.
It does not authenticate Source type erasure, signature/body association or the
payability flag, and keeps the existing typed Boolean/signed bindings distinct.
Native loading/frame realization, aggregate/multiparameter decoding, general
Source/profile/dispatch composition and physical failure bytes remain open.
G46.02, fixture replay and full assignment gates remain pending. Independent
read-only finder and skeptic reviews found no semantic issues. Checkpoint
results accompany the sealed handoff.

`SelectorGateBodyInterface.lean` specifies actual public compiler selection and
execution of a selector guard on an arbitrary intrinsic uint local followed by
an existing core-admitted body. Distinct selector/argument/length cells can be
represented without changing the decoder framework. The contract is a single
match/reject continuation, retaining selector loading, short routing and Source
table/body authenticity as separate obligations; no body run/result is assumed.


`SelectorGateBody.lean` compiles a selector equality requirement at an arbitrary
intrinsic uint local before an actual core-admitted continuation. Whole and body
artifacts are selected by the public compiler. The checked prefix leaves the
entire machine and saved stack unchanged on a match; a miss rejects before any
continuation-local facts or body execution. The selector comparison compilation
reuses `SelectorRoutes.condition_code`; the Source predicate adapter reuses
`SourceRoutes.predicate` with its explicit four-byte length condition. Source
signature/body association and selector loading are not inferred.

A three-local control adds a distinct outer selector through existing `Prog.wk`
to the proved primitive entry/body program. Its actual compiled entry code is
definitionally identical to the existing code at the shifted base, avoiding a
copied decoder or compiler. Raw-byte selector match executes value/head/enum
validation, carrier binding and a Boolean-producing body. Miss, malformed-word
short head, dirty enum, non-payable value, raw typed-value/body agreement and
saved state are checked. A matching reverting body distinguishes selector
acceptance from body success. Source match/miss controls use the published model
hash fixture; they make no native Keccak or Source body-authenticity claim.

Focused compilation and scoped standard-only axiom guards pass. Proof repair
used bounded bridge trials; timeouts and diagnostic recovery are retained in the
handoff. A lingering diagnostic worker overlapped the focused build after its
stop request failed; the owned container was restarted after build completion,
and subsequent validation uses verified shutdown before building. No proof
budget or resource limit changed. This is a single-match/reject continuation;
short receive/fallback routing, Source-authenticated dispatch trees, authenticated Source
association, native loaders, aggregate decoding and complete G40 remain open.

Independent read-only finder and skeptic reviews found no semantic issues.
Both retain the validation-process incident and require the final checkpoint
after verified diagnostic shutdown; its exact commands and outcomes are sealed.
Final guarded per-file diagnostics report zero errors.

`SelectorBranchesInterface.lean` specifies actual public compiler selection of
both typed branches and exact selector dispatch including the compiler join.
The matched branch retains its trailing jump over the miss branch; no normal
return, desired body execution or poststate is assumed. Represented-input join
removal is supplied by `CoreJoin` below; Source association, short special
routing and native loading remain separate.


`SelectorBranches.lean` selects the actual typed conditional, both branch
artifacts and the joined output fragment through the existing public compiler.
Exact dispatch reuses the proved selector test at the chosen local. The match
executes the selected left code followed by the compiler's jump over the right
code; a miss executes the right code directly. The real left outcome feeds that
join, preserving its skip instead of assuming a normal return. This certificate
retains the join; `CoreJoin` below removes it for represented core inputs within
the existing resource bound. No body run/poststate or normal-return premise
appears in the certificate.

Controls weaken the existing primitive entry/body program with a distinct
selector local, retaining definitionally identical decoder code at the shifted
base. Both branches and the whole are publicly selected. The matched raw enum
entry validates, binds and allocates its Boolean result, then provably skips the
miss continuation. A miss executes a different value-checked write. Dirty
matched input reverts even though the miss branch would succeed, ruling out
fallthrough after validation failure. Non-payable miss rejection, malformed
unused entry locals, raw typed-value agreement, distinct branch writes and
saved state are explicit. These are represented-local compiler controls; the
miss continuation does not authenticate Source fallback declarations/parameters.

Focused compilation and scoped standard-only axiom guards pass. Repairs and
bounded bridge trial timeouts remain in the handoff. Diagnostic containers are
restarted and worker absence verified before builds; no concurrent diagnostic
worker/build is claimed for this checkpoint. Source-authenticated dispatch trees, native
construction of represented inputs, receive/fallback Source association, loaders, aggregate
input decoding and full G40/G46.02 remain open, as do fixture replay and final
assignment gates.

Independent read-only finder and skeptic reviews found no semantic issues.
Final guarded per-file diagnostics report zero errors; exact checkpoint gates
and retained failures accompany the sealed handoff.

`CoreJoinInterface.lean` specifies actual compiler join removal from an existing
represented typed input and the unchanged compiler allocation bound. It assumes
neither a normal return nor a body execution/result. Source/native construction
of that input representation remains separate; earlier arbitrary-machine exact
join statements remain unchanged.


`CoreJoin.lean` removes the trailing join for every actual core compilation from
an existing `Evm.Sim` input within the unchanged `L + Prog.pushes ≤ Lmax` bound.
The proof reuses `Evm.compile_correct` to derive all actual outcomes: a return
with skip zero, a revert or a fault, including divergence. It supplies no body
run/result or normal-return premise and builds no replacement checker. Public
compiler selection identifies the actual artifact; the branch consequence now
returns the selected body's complete outcome under those existing input facts.
Earlier arbitrary-machine exact-join statements remain unchanged.

Controls construct an actual typed local state and prove its representation,
then select and execute returning, reverting and infinite-loop bodies. The loop
fault is proved from the existing loop semantics and preserved by the join.
Represented selector match and miss execute different writes while retaining
saved state and stack. A raw escaping-jump counterexample shows why the result
is not an unconditional statement about arbitrary instruction lists. These are
intrinsic compiler controls; Source/native construction of represented frames
and full-profile authority are not supplied. Focused compilation and scoped
standard-only axiom guards pass; bounded proof-repair evidence is retained.
Full dispatch/source association, aggregate decoding, native calldata/frame
realization, failure bytes, G46.02 and fixture replay remain open.

Independent read-only finder and skeptic reviews found no semantic issues.
Both confirmed unchanged representation/resource premises, coverage of every
compiler-correctness outcome and nonvacuous divergence/negative controls. Final
guarded diagnostics report zero errors; exact gate outcomes are in the handoff.

`CoreDispatchInterface.lean` specifies finite first-match dispatch over existing
intrinsic bodies with actual core-classifier witnesses. Neither selected target
artifacts nor body executions/results are metadata premises. Whole and target
selection use the public compiler; execution retains the existing represented
input and per-row allocation bounds. Source table/body authenticity, short
special routing and native frame construction remain separate obligations.


`CoreDispatch.lean` constructs finite nested conditionals through the existing
typed compiler. Each row contains an existing intrinsic body, its output context
and actual core-classifier witness; it contains no assumed execution or selected
artifact. The whole route and every body are publicly selected. The execution
proof relates first-match lookup to the complete selected body outcome from the
existing represented input and per-row allocation bounds, reusing `CoreJoin` and
`SelectorBranches`. A miss leaves the original input for the remaining rows;
a match is terminal even if its body reverts. Target equality is proved before
projecting its context-indexed program, retaining intrinsic body/context links.
No replacement interpreter, decoder, compiler or untyped AST is introduced.

Controls reuse the inhabited typed representation and execute differently typed
bodies. They cover a first match with a colliding later row, a later match, no
match, an empty table, a reverting default and terminal first-match failure even
though the colliding body succeeds independently. Allocation bounds and actual
public whole/body selections are proved; saved state and stack remain explicit.
Focused compilation and scoped standard-only axiom guards pass. Predicate repair
trials and failed attempts are retained in the handoff.

This proves finite dispatch over core bodies from represented inputs. Source
exposed-table/body/pipeline authority, short receive/fallback routing, native
input-frame and selector loading, aggregate input decoding, exact physical
failure bytes and full G40 remain open. The default continuation does not
establish Source fallback declaration or parameter correspondence. G46.02,
fixture replay and full assignment gates remain pending.

Independent read-only finder and skeptic reviews found no semantic issues.
Both confirmed actual whole/body selection, heterogeneous target transport,
terminal first-match behavior and unchanged input/resource premises. Final
guarded diagnostics report zero errors; exact gates accompany the handoff.

`CoreSpecialInterface.lean` specifies actual typed receive/fallback body choice,
including value guards and absent-endpoint rejection. Empty input prefers
receive with fallback when absent; nonempty input uses fallback. The interface
anchors endpoint code to the existing guard/compiler, not supplied body runs.
Source declaration/payability authority and native parameter binding remain open.


`CoreSpecial.lean` compiles receive/fallback choice through `CoreDispatch` on
an intrinsic uint size local. Empty input prefers receive, then fallback;
nonempty input selects fallback. Each present endpoint wraps its existing typed
core body with `ValueGateBody`; absence compiles to actual revert. Public whole
and endpoint selection are proved, as are complete outcome equality and endpoint
allocation counts. The general execution theorem retains the existing input
simulation and allocation bound for the empty-input endpoint. The nonempty
proof needs only the size cell and nonzero size: unused receive representation
and capacity are irrelevant on the actual miss path. Neither theorem assumes a
body run, desired result, poststate or replacement compiler.

Controls build an inhabited typed input with size and an incoming uint local,
then execute receive assignment or fallback bool allocation reading that local.
They cover empty receive preference, absent receive, arbitrary nonempty size,
missing fallback, both endpoints absent, arbitrary value on payable receive,
terminal nonpayable receive despite an independently successful payable fallback,
value refusal before a malformed argument, body revert and saved state/stack.
The complete machine outcomes retain untouched state. These are core target
controls; the size/local binding, Source declarations and payable metadata are
not authenticated by these results. Source fallback calldata parameter binding,
raw fallback output, native dispatch loading and exact physical failure bytes
remain separate G40 obligations, alongside aggregate decoding and whole-profile
composition. G46.02 and ordered G46.03 remain open.

Independent read-only finder and skeptic reviews found no semantic issues in
actual selection, routing, terminal failure, intrinsic typing or retained
resource/input premises. Following heartbeat failures in whole-program control
reduction, proof repair separated code equalities and used existing dispatch and
value-guard execution plus explicit instruction-step simplification. No theorem,
exclusion or heartbeat budget changed. The resulting controls also check in a
scratch diagnostic with a smaller budget. Final per-file diagnostics report zero
errors; focused importing-consumer compilation and nineteen scoped standard-only
axiom guards pass. Failed attempts and checkpoint gate outcomes are retained in
the sealed handoff; this increment does not close the whole lane.
The final skeptic review identified one proof-style issue: an inferred local
execution equality lacked an explicit type. It now has its full input/output
equality type; the statement and premises are unchanged. Finder found no issues.

`HeadCheck.lean` explicitly imports the Selection V2 interface it consumes.
The import correction preserves all statements, proofs and resource bounds.
Independent read-only finder and skeptic reviews confirmed preservation of the
owned sources and generated-root imports; both passed without findings.

`LengthCheck.lean` directly imports the Selection V2 frame interface. Its
numeric `belowCode`, correctness and capacity prerequisites already exist in
published WordValidation; the packet does not require that file's unpublished
signed/fixed-bytes extensions or their transitive imports. LengthCheckInterface,
LengthCheck and LengthCheckControls form the complete new-module packet.

An isolated check compiles the published WordValidation source and those three
packet sources against 36 reused common artifacts whose source hashes match the
published dependency closure. It passes all fourteen packet axiom guards and
actual certificate axiom reports. A negative import check rejects the unpublished
signed validator, confirming that branch-only extensions are unavailable.
This is four explicit source checks, not a fresh rebuild of the entire closure.
Independent read-only finder and skeptic reviews passed without findings.

The emitted loaded-length flag, stack capacity and semantic lazy-revert versus
eager-panic/fuel/head ordering are unchanged. Native loading, guarded runtime
allocation, physical panic bytes and complete entry composition remain open.

`SizeBranchesInterface.lean` specifies short/full input branching over actual
intrinsic core bodies. The threshold is size four; both raw compiler joins and
complete represented body outcomes are retained in the contract. It uses the
existing compiler, core classifier, input simulation and allocation bounds;
no desired run or body result is supplied. Native size loading, Source metadata
and full runtime-entry composition remain open.

`SizeBranches.lean` constructs the intrinsic size-less-than-four conditional and
proves actual public selection of the whole program and both core bodies. The
raw execution theorem retains the compiler's real join and escaping skip. From
the existing input simulation and unchanged left-body allocation bound, the
shared core join proof supplies the complete selected body outcome; no expected
body run or poststate is a premise. Different branch output contexts stay typed.

Controls construct a represented uint input with a saved stack, execute a short
assignment or a full-input bool allocation reading the size, and cover zero,
three, four and the largest word. They also cover a terminal reverting short
body, malformed size-cell fault, unchanged protected state and a raw escaping
skip whose remaining count is retained. Native calldata-size representation and
Source body/signature authority are separate obligations.

The existing core join proof now lives in `CoreJoin/Shared.lean`, retaining its
public names, statements and premises. An unused simp argument is removed;
CoreJoin's existing branch consumers remain available and checked. Its interface
explicitly imports Compiler. This removes selector/decoder imports from the new
size packet without reproducing the join proof or adding another compiler.
The packet's complete unpublished dependency closure is supplied in its handoff.

Independent read-only finder and skeptic reviews passed the new implementation,
controls and proof split without findings. Six final per-file diagnostics and
seventeen new scoped standard-only axiom guards pass. The importing-consumer
build also checks the existing finite-dispatch controls after extraction.
An isolated seven-source packet check passes against published master using 187
source-verified reused common artifacts; both unpublished selector and decoder
helper checks fail as expected. This is not a fresh rebuild of the entire
194-source closure. Repair trials and earlier failed attempts remain in the
handoff. Full G40 Source/native composition, fixture replay, G46.02 and ordered
G46.03 remain open; checkpoint gate results accompany the sealed evidence.

The public eager/lazy transport theorem and its complete statement are preserved
with the original one-step fuel difference and size premise. SourceEntryAgreement
retains its original two-field structure and coverage projection; its exact
record declaration matches the published interface. `of_exact_result` keeps
coverage derivable without adding a premise for record construction. Existing
projection calls and the two-field constructor remain available. These are API
preservation changes; they add no source-to-runtime correspondence claim.

Independent read-only finder and skeptic reviews passed the API restoration
without findings. A compiled compatibility check exercises the original eager/
lazy theorem signature, coverage projection, two-field constructor and exact-
result constructor. Per-file diagnostics pass; the restored theorem, projection,
constructor and source graph controls have standard-only axiom reports. These
checks preserve the public API and do not establish native entry adequacy.
