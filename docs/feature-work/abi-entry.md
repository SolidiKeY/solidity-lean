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
  Source coverage is derived from exact graph agreement, with inhabited graph
  and empty-relation controls. Dispatch helper equalities are bookkeeping and
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
  `Semantics/AbiEntryProofs.eager_cref` directly, without a duplicate wrapper.
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
and doc paths passed. The central axiom inventory still fails: 6553 standard-only
pins, one removed duplicate wrapper and 45 unrecorded changes. Its refresh is
proposed separately, outside lane ownership; no gate pass is claimed. Independent
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
