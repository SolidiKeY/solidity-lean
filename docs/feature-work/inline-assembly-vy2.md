# Inline assembly VY2: physical view preparation

Status: **partial; full lane open**. Assigned base
`0b078cefaf7daad79007b87b72df64eb6936420f`; branch
`codex/solidity-inline-assembly5-20261031/vy2-physical`;
checkout `/workspace/solidity-lean`. No admission row reopened.

## Authorization and ownership

[YQ1–YQ7](../solidity-scope.md#inline-assembly-decisions-2026-10-31)
are approved implementation directions. Existing canonical rethrow is unchanged;
non-memory-safe blocks, compiler-dependent observations and fork exclusions
are not broadened. VY1 syntax/static/word semantics is absent in the validated
tree. No duplicate syntax, prerequisite implementation, compiler rewrite,
external dependency in core, proof-budget increase or source-state refactor
is introduced. G27/V10 and G32/V11 remain owners of compiler agreements.

## Queue accounting

| Item | Implemented preparation | Remaining concrete obligation |
| --- | --- | --- |
| Y04 | Existing HashedLayout slot interpretation; intrinsic field widths; read/update/low/high/unchanged/bounded-word arithmetic; typed canonical codec/region reconstruction; residual bytes and raw slot updates; actual source reset/rollback controls | Further nested/dynamic/mapping/source-path layouts and whole-store codecs, dirty/noncanonical owned bits, derived source view instance and typed writeback, persistent/transient residual journal/reset, VY1 sload/sstore/tload/tstore composition, V10 agreement instance |
| Y05 | Byte operations; both general word roundtrips; snapshot mcopy including overlap; documented object-size/placement contracts and inhabited two-object allocation choices; reserved-area control; exact actual V04b MemOK preservation obligation | Full logical heap-byte view/writeback and V11 agreement; VY1 memory-safe semantics preserving actual MemOK; integrated nondeterministic allocator and full G01 refinement/resource-adequacy amendment; Gate G0 and speed measurements before any source representation change |
| Y06 | Raw byte input, size/word-length premise, zero-padding and copying; approved Fixed hash and congruence; typed universally supplied environment values, blockhash window/blob index semantics; executable hash vectors | Source/Yul builtin integration and corresponding Solidity rows with source/session sharing proofs; raw input bounds in final semantics; fork-aware admission; compiler/source/EVM composition |
| Y09.02 | Lean-only equational preparation table in rule map | Actual VY1 terms/statements and source integration, dl/tm syntax, printers, sound statement/update rules and source-level combinations |
| Backfill A | Reusable typed codec/region/residual and packing laws; endian/width/overlap/zero-padding/unchanged-view controls | Concrete source codec/view composition remains open with the above dependencies; generic laws do not discharge it |
| Backfill B | Scalar V10 obligations, allocation extension, actual V04b preservation sub-obligations, source rollback/reset, calldata/hash/environment vectors | V11 layout agreement instance, residual journaling, instantiated allocation/refinement/preservation and VY1 connection |

Successful sstore/tstore integration must enforce non-static frames as well
as resource success; these pure update laws do not claim a store-step theorem
in a static frame.

No loop/modifier/try/constructor/library Yul combination is claimed. Existing
source and frontend/type/compiler owners are read-only prerequisites. The
present controls combine physical operations and exercise the existing typed
source world; they are not source-level assembly executions.

## Modules, exact premises, proof boundaries

All code is under `Solidity/Yul/Views/`. Byte/slot maps are derived view
functions, not a second source state. `StorageWidth` is a relation on existing
`Source.STy`; codecs return existing `Source.Val`. Source `Storage`, `Heap`,
`ExecState`, `Op`, and the actual `Source.MemOK` are reused.

- `Field.find_save`, `save_low`, `save_high`: any intrinsically bounded field
  value; `Field` carries positive byte width and `offset + width ≤ 32`.
- `Field.find_save_above`, `find_save_below`, `find_save_disjoint`: preserve
  another packed field under explicit disjoint byte-interval inequalities.
  `saveWord`/`findWord` give intrinsically bounded packed updates and roundtrips.
- `Field.save_unchanged`: exact arithmetic reconstruction for any Nat slot;
  `Field.save_lt` additionally assumes the original slot below `256^32`.
- `bytesObject_header`, `bytesObject_payload`, `bytesObject_residual`,
  `bytesObject_unchanged`: concrete length-prefixed byte/string content view,
  under a word-sized length; typed Source.Data/ObjectByte agreement and exact
  unchanged view include arbitrary residual/padding bytes. Typed bytes/string
  decoders have decode-after-encode identity on actual Source.Data constructors;
  encoding is idempotent and an unaligned nonzero-padding witness is included.
  This is an object
  component, not the full logical heap/writeback instance.
- `mload_mstore`, `mstore_mload`: any byte view, natural offset and bounded
  word. Both are general kernel proofs, including exact preservation outside
  the written interval. EVM execution additionally needs valid intervals and
  resource success; these functions do not model allocation failure or gas.
- `Regions.decode_encode`: each actual typed codec supplies its own
  decode-after-encode law; the layout supplies inverse ownership. This does
  not posit hash injectivity or derive packing from a compiler.
- `Regions.unchanged`: a typed family whose encoded owned bytes equal the
  original view; every unowned byte is retained by the residual subtype.
  This is a canonical-view theorem, not a theorem for arbitrary raw owned bits.
- `ScalarStorageObligations`: indexed scalar subset, explicit source path,
  width/codec, read agreement, view existence and unchanged/result-view
  writeback obligations. No instance for an entire source layout is supplied.
- `source_view_rollback`: any projection of the actual typed source state,
  any finite source operations and frame parameters; follows actual
  `Source.rollback_run`. Residuals are not yet journaled by that state.
- `Placement`: actual typed heap contents, non-overlapping addresses
  at/above 128, bounded free pointer, live identity injectivity,
  typed object shapes and ends below the free pointer. Scratch is [0,64),
  pointer word [64,96), zero slot [96,128). Dynamic arrays have length headers;
  static arrays do not; reference members occupy pointer words; bytes/string
  payloads pack and round up to words.
- `AllocationRefines`: for every target observation, a valid placement with
  the **same** source observation. This is the proposed allocation soundness
  component in an isolated extension interface, not a final G01 theorem or a
  discharge of its adequacy/resource obligations. Existing G01 is unchanged.
- `MemoryLayoutObligations`: ordinary-object read-side input contract (with inhabited byte-header/payload
  and actual struct-member read controls) over
  actual typed Data/DataList.nth; explicit reserved-area, canonical scalar and
  pointer, byte/string, dynamic header, array-element and struct-member reads.
  A valid Placement is an explicit input to its realization obligation; MemOK
  alone does not imply finite physical allocation fits. It has no compiler
  instance and does not cover shared-zero-slot references.
- `MemoryWritebackObligations`: nonvacuous view/unchanged-writeback existence,
  exact unchanged result and preservation using the real V04b MemOK (EMOK,
  HeapShaped, HeapInner), all heap typings and initial view. This is only the
  preservation sub-obligation; the separate MemoryLayoutObligations and
  a real implementation are still required by V11.
- `HashInputAgreement`: G27/V10 shares the approved Fixed hash over the
  existing HashedKeccak encoding; its boundedness follows without any collision
  assumption. `InputAgreement` links the actual source Glob Fixed/timestamp,
  transaction origin and frame calldata to the physical inputs. Source fields
  for the other block/tx rows are still absent and must be extended by integration.
- `calldata_zero`, `calldataload_zero`: raw offset at/after input length.
  `calldatasizeWord` requires `CalldataValid`; loads/copies expose no compiler
  code/gas/size observation. Successful steps need `ValidRange`/resources.
- `keccak256_congr`: the same approved `Roadmap.Evm.Fixed` and equal byte
  lists, with no collision-freedom premise. The Fixed bound supplies Word.
- Environment inputs are universally supplied; coinbase/origin are 160-bit
  addresses, others Word. Historical hashes are read only for the previous
  256 blocks; blobhash returns zero outside the transaction list. The source
  Glob/session sharing and fork admission are not yet instantiated.

Administrative source storage distinguishes `none` from `some default`,
although their physical bits can coincide. Original typed storage is therefore
an input to writeback; physical bits alone are not claimed to recover that
administrative distinction. `boolCodec`/`boolBytes` reject byte 2 as a canonical
preparation codec. This is **not** an admitted sstore refusal: dirty-bit
retention/normalization and typed writeback must be resolved in the concrete
composition according to solc and YQ4.

Kernel proof versus executable evidence: all `theorem` controls use ordinary
kernel proofs (no native_decide, new axiom or sorry). Keccak `#guard` vectors
execute compiled code and are reported separately. Pinned solc/EVM replay is
external evidence, not Lean admission or a universal correctness proof.

## Gate G0 and history

No existing indexed syntax/state/value representation changed. No new hot
indexed matcher was introduced; typed constructor elimination uses casesOn
through tactic `cases`. The prior history was inspected before edits:
`21067a47` source intrinsic state, `692a60cc` typed transient roots/transactions,
`91696d61` deletion of the untyped state, `1a78f65f` core/elaborator separation.
Actual MemOK owner history includes `d8af4696` and `8492d267`.
A future residual/state representation change still requires Gate G0 review,
warning and checking-speed measurement; this preparation does not waive it.

## Runtime, recovery and validation

The original VM had a clean `work` checkout at
`2fe1f8932f96be15b00df03ba2cde46f64a87758`. Authorized same-VM recovery fetched
exactly `0b078cefaf7daad79007b87b72df64eb6936420f` (exit 0), verified its parent
is that original HEAD, and created the assigned branch at the pinned base.
The old work branch and caches were preserved. `get_goal` and Lean MCP tools
are not exposed; no second goal was created or reset.

Actual Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. KeySort exited 0, “Build completed successfully
(2 jobs).” before any runtime pass claim. RUNTIME_GATE_PASS is limited to
that prerequisite. Managed Docker cgroup v2 enforces memory.max=12884901888,
memory.swap.max=0, inside enclosing 17179869184 bytes. LEAN_NUM_THREADS=1;
a disk-local wrapper passes -j1 and serializes Lean and clang with one lock.
An alternate untracked TOML also passes -j1 for focused builds. The original
tracked run-lean.sh is used for the full gate. Writer lock is held at the
repository-prescribed path. OS headroom, cgroup current/peak/no-swap, aggregate
RSS and free disk are logged. The first RSS probes failed (container ps absent,
then docker top missing PID column); zero RSS entries from those probes are
invalid, not measurements. The corrected PID/RSS monitor retains actual values.
No simultaneous Lean server/build or second 12 GiB OS reservation.

Focused physical/control closure: 35 jobs, exit 0. Per-file failures (syntax,
elaboration, looping simp, unknown tactic/name and witness projection) are
retained raw and repaired without increasing any proof budget. Headline scoped
axioms are subsets of propext, Quot.sound and Classical.choice. Final outcomes follow below; the earlier failed attempts remain raw evidence.

## Independent reviews

Separate finder and skeptic reviewed read-only, with no Lean server/build.
Confirmed findings fixed: free pointer lower bound; distinct live
placement identities; nonvacuous view/unchanged writeback obligations; restrict
storage codecs to an indexed scalar subset; 160-bit coinbase/origin. Memory
contract narrowed to preservation sub-obligations rather than claiming a full
V11 agreement. Added packed-word boundedness and both word roundtrip proofs.
Pinned assembly.rst explicitly requires no address alignment; removed the
initial overly restrictive alignment obligations and added an unaligned valid
placement witness. Default empty references may use shared zero slot 0x60 and
remain a distinct final V11/refinement obligation, outside ordinary allocated
object placement. Zero-slot empty-object decoder controls do not discharge
that pointer/heap aliasing obligation.
Added nontrivial allocation, dirty bool, endian, width, residual, overlap,
calldata, environment, actual source reset/rollback and combination controls.
Dirty owned bits, residual journaling, full V11 layout/read agreement and
concrete source/correctness composition remain explicitly open.

## Artifacts and final gate record

Evidence directory: `/workspace/vy2-evidence` (raw failures retained).
Original patch: `/workspace/vy2-evidence/vy2-original.patch`.
Bundle: `/workspace/vy2-evidence/vy2.bundle`.
Handoff: `/workspace/vy2-evidence/HANDOFF.md`.
Checksums: `/workspace/vy2-evidence/SHA256SUMS`.
Final revision/gate outcomes are recorded in the external handoff to avoid a
self-referential commit hash. The full lane cannot complete without the
concrete prerequisites and gates listed above.


### Final preparation validation (2026-10-31)

- Final focused closure: `lake -f lakefile.vy2.toml build Solidity.Yul.Views.Agreements Solidity.Yul.Views.ReadControls Solidity.Yul.Views.MemoryControls Solidity.Yul.Views.SourceControls`, 40 jobs, exit 0 (`final-focused-3.log`). The first final attempt failed on a missing explicit `Source.STy` binder annotation; corrected without changing the relation or proof budgets. A new unused simp argument was removed.
- Final registered-tree gate: `./run-lean.sh` in the bounded runtime with `SOLKEY_RULES` set to the frozen local taclet file, exit 0: 996 default jobs, 262 TestSuite jobs, 377 taclets parsed and all 131 read-bearing annotations matched (`final-run-lean.log`). The preceding first full gate also exited 0 (992/262 jobs); it did not include every late registration and is not substituted for the final gate.
- Exact signatures and scoped axioms: `lake env lean --tstack=131072 -j1 /workspace/vy2-evidence/Signatures.lean`, exit 0; 177 public declarations, 89 theorems. Only `propext`, `Quot.sound`, `Classical.choice` occur in their axiom reports. No new axioms, sorry, native_decide or budget increases.
- Lane-owned external scalar vectors: `node tests/yul-views/physical-reference.mjs .lake/soljson/soljson-v0.8.38+commit.1835d247.js /workspace/vy2-evidence/physical-reference.json`, exit 0, legacy and via-IR working, Osaka. Ten vectors per pipeline include dirty uint8 local (raw1193046/clean86), bool local/storage (raw2/clean1), word/byte/copy/calldata/hash/residual controls. These cases show no pipeline difference and do not prove all dirty-bit behavior or frontend support.
- Upstream storage and transient fixtures pass both pipelines. Four upstream memory/calldata/hash/copy fixtures remain blocked in the unchanged reference adapter (host-dependent behavior or missing raw adapter shape); their exit1 reports are preserved. The lane-owned scalar controls do not relabel those failures.
- Peak child cgroup memory 12884901888 bytes; zero swap and OOM kills. Enclosing peak 16744333312 bytes, max17179869184; physical OS headroom remained monitored. Aggregate RSS and disk samples are retained. No second heavy job ran concurrently.
- Final layer/orphan/trust and baseline comparisons are recorded in `static-final.json` and the external handoff. Raw doc-path validation fails on the exact base and this tree with the same 48 missing references; this is a baseline failure, not a passing gate. Markdown comparison and no-new-findings are separate checks.

Final independent finder and skeptic reviews inspected the late byte-object,
read controls, packing and actual source input agreements without Lean/server/build.
Neither found a confirmed defect. Inhabited read controls establish local typed
relations; they do not instantiate MemoryLayoutObligations or full heap composition.
Review records are `finder-review.md` and `skeptic-review.md` in the evidence directory.

The preparation checkpoint leaves every original Y04/Y05/Y06/Y09.02 concrete
closure obligation in the queue above open. No permission question is needed;
missing owner interfaces/instances are dependency obligations, not semantic approvals.


### Canonical scalar codec checkpoint (2026-10-31)

Continues the preparation revision `7e03d333113fcd81e37057132f8f703bf1cf1615`.
`ScalarCodecs` supplies concrete canonical codecs over the existing intrinsically
typed Source.Val: all valid signed/unsigned integer widths, scaled fixed-point
integers, addresses/contracts, bounded enums, underlying UDVTs, bytesN and
external functions. Bool codecs can be placed at any fitting offset.
No source state, storage layout owner, frontend or manifest changed.

Exact additional premises and representation:

- `intField_modulus` uses the actual IntTy validity (byte multiple, 8–256 bits).
  `intPayload_bound` and `read_intPayload` require the real source lo/hi range.
  Negative values add the width modulus; signed reads subtract it at the sign
  threshold. Field offsets must fit. Fixed point reuses this on its scaled
  integer; no claim of solc fixed-point admission follows.
- `fixedBytesCodec` requires the existing positive 1–32 byte source width and
  fitting offset. The packed numeric payload is right-aligned within its field,
  with big-endian bytes, unlike ABI's left-aligned word. General
  `scalar_beValue_bound` and `scalar_beBytes_value` prove the byte bounds/inverse.
- Addresses/contracts are 20 bytes; `enumCodec` requires enumSize≤256 and rejects
  invalid canonical members. UDVTs require a concrete codec for their actual
  declared underlying type. External functions are 24 bytes: address<<32 plus
  four-byte selector. Internal function code offsets remain a separate owner
  obligation, not an invented address codec.
- `ScalarCodec.bytesBE` in ScalarBytes turns each concrete identity into an
  existing ByteCodec with its decode-after-encode proof. The Regions owner/address
  map must still supply actual physical byte order and separation; this does
  not equate low-end storage offsets with increasing byte-memory addresses.
- ScalarControls includes signed8 and signed256 boundaries, unsigned distinction,
  scaled negative fixed, maximum address, nonzero contract/function payloads,
  enum refusal, bytes ordering, actual underlying UDVT and packed signed/bytes/bool
  update with high residual preservation. A signed codec also inhabits the
  existing byte/residual region framework. These are canonical logical-value
  components, not raw dirty-bit writeback or whole-layout instances.

Per-file diagnostics and focused build passed; the external-function inverse
initially needed explicit rewrite normalization (raw third.log exit1 retained).
No theorem premise, expected verdict or budget changed. Focused closure:23 jobs,
exit0. Full registered tree: `./run-lean.sh`, exit0,999 default jobs,262 TestSuite
jobs,131 read-bearing annotations matched. Complete signature/axiom audit:222
public declarations,109 theorems, only the three standard Lean axioms.
The original KeySort/version/resource prerequisites remain unchanged; all heavy
checks serial with -j1 in the same enforced12GiB/no-swap container and monitored
OS/RSS/disk bounds. No simultaneous Lean server/build. New raw logs are under
`/workspace/vy2-evidence/scalar-codecs`.

The unchanged pinned reference helper ran12 scalar vectors per pipeline,
legacy and via-IR, Osaka, optimizer disabled, exit0. Two new external controls
check the packed word0x5566011234ff (signed8=-1, bytes2=0x1234, bool=true,
residual0x5566) and external-function address/selector formula. Existing expected
vectors and execution budgets are unchanged. Kernel inverse laws and these
external witnesses do not prove compiler/layout agreement for all programs.
Earlier upstream adapter failures and exact-base doc failures remain retained.

Independent finder and skeptic reviewed scalar code and external controls
read-only, without Lean/server/build, and found no confirmed defect. Their
requested external layout evidence was added and passed; review records are
in the new evidence subdirectory. Final static/docs comparisons and committed
head/artifact checksums are in HANDOFF.md.

Queue impact: further discharges independent Backfill A concrete canonical
scalar preparation and its connection to residual laws. Every Y04/Y05/Y06/Y09.02
final integration item in the queue remains open. VY1 Syntax/Static/Words files
are absent; no effect AST/state adapter can be connected without inventing that
owner's interface. Actual source values remain range-indexed (for example uint8
cannot contain a dirty larger raw value), so whole writeback needs the agreed
physical/source overlay and owner integration, not silent cleaning in these codecs.
Actual MemOK is available but no assembly preservation instance is proved.
No additional permission or semantic decision is requested.


### Constructive packed aggregates and exact raw replay (2026-10-31)

Continues revision `3fe717a45ff4267cedcf53173a15a06730800314` in the same VM,
branch and pinned-base ancestry. No owner source, state representation, Syntax,
allocator, compiler or manifest changed; original artifacts and failures retained.

`PackedAggregates` constructs canonical **flat scalar-member** storage components.
`PackedMembers D τs` is an intrinsic layout descriptor indexed by actual source
field types; each member supplies an existing scalar codec and its documented
`StorageWidth`. It contains no assumed aggregate inverse. Encoding traverses
actual `Source.DataList`, accepts actual `Data.val` members and fails otherwise.
Decoding constructs actual DataList. Struct decoding returns `Source.Data.struct`;
fixed-array decoding returns `Source.Data.array` with its real declared length
and actual member function. Array conversion inverses are proved, not assumed.
`AggregateData` supplies direct actual Source.Data encode entry points, derives
array length equality from its existing source proof, and rejects reference-only
Data.val inputs rather than dereferencing them without source state. Its typed
roundtrip and unchanged results are proved constructively; output-slot residual
preservation follows from the successful encoder. Actual entry/reference-refusal
controls are inhabited. Both independent reviewers inspected this final addition
without checks and found no confirmed issue.

Packing uses low-end byte coordinates inside storage words. `packedStart_spec`
proves the first fitting offset is forward and cannot cross a word; `endByte`,
`owned_bounds`, `head_tail_disjoint`, and `nextSlot_spec` prove extents, separation
and trailing slot rounding. Struct/array entry uses `base.val*32` for a Word base;
`Fits` requires end≤32*2^256, excluding address wrap. `nextSlot` is a natural end
sentinel, not a claim that an additional object fits in storage. This follows the
pinned storage documentation; memory's word-per-member layout is distinct.

`PackedSlots` constructively serializes actual Word-indexed SlotView values to
low-end bytes and back. `slotsOfBytes_slotBytes` is exact whole-map identity.
The reverse byte identity requires address<32*2^256. Successful supported
encoding has a typed decode-after-encode theorem and always exists for actual
scalar-member DataList. `slot_roundtrip` composes this with the real nonwrapping
bound. `encode_residual` preserves every unowned byte; `slot_residual_byte`
preserves padding and residual bits even within partly owned slots. Canonical
unchanged encoding requires only matching owned bytes; `encode_matches` proves
that condition for constructed outputs, giving constructive idempotence. Gaps
and trailing bytes are unrestricted, not assumed zero.

Controls inhabit a heterogeneous five-field struct and12-element uint24 array,
including slot rollover, internal/trailing nonzero padding, exact decoded source
data, unchanged encoding, invalid enum refusal, and wrapping-extent refusal.
Four explicit slot-word goldens are kernel checked and match two new lane-owned
solc vectors in both pipelines. Nested aggregate members, dynamic arrays/mappings,
hash-region separation, dirty/noncanonical owned bits, full typed store/heap
writeback and whole-state identity remain open. HashedLayout still supplies the
base through `physicalSlot`; its layout/separation and V10 agreement are inputs,
not replaced compiler proofs. Actual V04b MemOK and allocation contracts unchanged.

#### Gate G0 and independent findings

Finder and skeptic both caught indexed matches in the initial aggregate code.
They were replaced with tactic `cases`/casesOn elimination and explicit typed
head/tail recursors; remaining pattern recursion is on Nat. The user was warned
before this normalization refactor. Per-file final aggregate check1.47s versus
1.55s initial match form on this small preparation file; these are recorded
command timings, not a general performance claim. No exemption, proof-budget
increase or shared source rewrite was used. Raw elaboration/normalization failures
remain under `/workspace/vy2-evidence/aggregates-replay`.

The skeptic also caught the initial adapter's invalid storage-root check:
SimpleStateManager does not maintain account storage roots. `reference-first.json`
retains valid return-byte runs but is **superseded for the storage invariant**.
The final adapter observes public putStorage calls on a fresh public machine.
Its declared extra invariant is no attempted writes, including reverted attempts;
it does not infer state from unsupported roots. A real SSTORE control reads back
value1 through public getStorage and requires adapter rejection. Both reviewers
verified these fixes read-only, with no Lean/server/build/tests, and found no
remaining confirmed issue. Final golden/control followups also found none.

#### Exact pinned upstream replay

The lane-owned adapter is closed to exact hashes of four existing pinned files:
calldata_length_read (6 calls), mcopy_overlap (5), keccak256_assembly (1), and
inline_assembly_memory_access (1). It uses public snapshot/parser/vector and
machine/creation/observation APIs; shared reference scripts are unchanged.
Each pipeline retains13 ordered calls plus4 implicit deployments. These sources
have no explicit constructor/failure/storage/log/world-host expectations;
that complete inventory is recorded, not silently ignored. Local `new bytes(5)`
is allocation, not a world-host requirement. Raw calldata (including noncanonical
trailing words) and complete returndata/padding are retained and compared.
No byte vector is converted to scalar args. Unknown shapes/settings, source drift,
missing/reordered observations, wrong deployment/code/failure/bytes/state fail closed.
The unchanged public machine retains exception/log admission and transaction resets.

Final reference exit0: both pipelines, Osaka, optimizer disabled; all four fixtures
working plus14 lane-owned scalar/aggregate vectors per pipeline. Fail-closed
controls exit0:8 positive fixture variants and81 mutations, including actual SSTORE.
Gas100m/step5m and proof/test budgets unchanged. Earlier global adapter exit1 logs
remain original failures; the narrow lane adapter repairs these exact cases without
rewriting that other owner's general harness. Unannotated upstream assembly here
is external evidence only and does not relax YQ7 or establish Lean admission.

#### Gates and full-queue handoff

Final focused closure27 jobs exit0. Complete audit309 public declarations and157
theorem axiom reports, only propext/Quot.sound/Classical.choice. Mandatory KeySort
and actual Lean4.24.0/Lake5.0.0-src+797c613 recorded in versions-keysort.log, exit0,
2 jobs, before this checkpoint's RUNTIME_GATE_PASS prerequisite claim. Full final
wrapper exit0:1003 default jobs,262 TestSuite jobs,131 annotations matched. Static/docs comparisons are in the external handoff and raw
`aggregates-replay/*.exit.json`; no fabricated gate markers.

Backfill A now includes constructive supported aggregate codecs/layouts and their
Word-slot/residual composition, beyond scalar assumed-law interfaces. Backfill B
agreements/allocation/MemOK obligations remain explicit inputs. No fallback residual
journal implementation is claimed: aggregate construction was possible and completed
for the stated supported components. Y04 remains partial for dirty/whole-store and
source effects; Y05 for whole memory/allocator/MemOK; Y06 for actual source/Yul
builtins and rows; Y09.02 for intrinsic terms/notation/printers/calculus composition.
VY1 remains absent; applicable V10/V11 and VY3/VY4/VY5 joint V12/V13/V15/V16 closure
is not imported. Questions=[]; no new human semantic choice is required.


### Disjoint and fixed nested component checkpoint (2026-10-31)

Continues exact revision `5149e2d540ab7b786bbf8ded4b55de8ce98e79d4` on the same
branch, VM and pinned base. Existing codecs/ownership/widths/source values retain
their meanings. No prerequisite owner, AST, Source state, allocator or manifest
changed. New code uses intrinsic existing Data/DataList and actual declaration
indices, with explicit recursor elimination; recursion matches only Nat.
Source history (`21067a47` intrinsic state) and Gate G0 were inspected first;
possible recursive checking cost was announced before implementation. No source
representation refactor, exemption, proof-budget increase or second untyped IR.

`ComponentComposition` proves both directions of the reusable owned-read/decode
frame law via explicit disjointness (including its symmetric form), using actual
successful encoder outputs. `composed_roundtrip`, `composed_residual` and physical
Word-map corollaries retain real outputs and nonwrapping Fits/bounds. Exact
unchanged composition uses both canonical matches; it does not need an invented
disjointness premise when both writes already leave the same view unchanged.
`disjoint_at_nextSlot` and `disjoint_at_roundSlot` derive useful separation from
computed ends, not from a desired final conclusion. Rounding bounds/alignment
and unowned-byte frame laws preserve inter-slot and trailing padding.

`StructArray` constructs fixed arrays of heterogeneous actual Source.Data.struct
contents. Each public Word-based entry starts aligned; each element's computed
end rounds up for its successor. Low-level helpers also accept arbitrary Nat
coordinates and do not assert alignment without that entry condition. Encoder/
decoder contents remain DataList indexed by the declaration's actual field types.
Positive declared length, actual Data.array length equality and total computed
extent≤32*2^256 are explicit at the physical API. Reference-only outer values or
struct elements return none. No reference is silently read as its contents.
Roundtrip, owned bounds, head/tail separation, residual, match transfer and exact
unchanged re-encoding of actual successful physical outputs are proved.

`ArrayStruct` constructs a nontrivial struct containing a fixed scalar array and
an actual heterogeneous struct member. Its schema contains real source field
list equality, positive array length and existing scalar/flat-inner codec inputs;
**no aggregate inverse or whole-store agreement is assumed**. Both parts are
extracted from actual Source.Data, length equality follows the source constructor,
and decoding constructs the actual declaration-indexed object. The fixed array
packs normally; the next aggregate begins at its rounded end. The outer end is
rounded too. Physical roundtrip/residual/unchanged proofs derive canonical owned
matches from actual encodings, then compose the existing byte/Word inverse under
the actual total bound. `castDataFields_back` accounts for declared-index transport.

NestedControls inhabits the real declarations with uint24[12] plus five-field
struct and three distinct heterogeneous structs. Computed extents64/128/192,
slot rollover, nonzero a5 internal/trailing padding, output re-encoding identity,
actual typed decode, reference refusal, checked wrong length, incompatible source
type/length indices and wrapping extent refusal are included. Invalid source
indices remain intrinsically unconstructible; the checked length boundary returns
none rather than manufacturing an ill-typed Data value. Further fixed-nesting
shapes, pointers/source paths, dynamic/mapping/hash separation and dirty owned
bits remain additional work, not newly approved exclusions.

Full5/7-word goldens include every4/6-component slot and an untouched sentinel.
They are **compiled #guard controls**, separate from universal kernel proofs.
The first attempt to calculate padding through the entire encoded view hit the
default recursion-depth limit; it was replaced with kernel residual/bounds proofs
and small ownership checks, without increasing the limit. Other normalization/
induction failures remain raw. A local recursive decision instance did not reduce;
that attempt was replaced with actual per-element extent reasoning. Final per-file
nested controls2.28s, focused31 jobs exit0; no checking-speed claim beyond recorded
command timings.

Two new owned solc methods perform real typed assignments and return all physical
words plus sentinel words, initialized to a5. Fourteen earlier owned vectors retain
their expectations/order; total16 per pipeline now pass. The four original pinned
upstream fixtures still execute13 calls and4 deployments per pipeline in order;
all81 fail-closed controls still pass, including real SSTORE detection. Pinned
solc0.8.38 commit1835d247, Osaka, legacy/via-IR, optimizer disabled,100m gas/5m steps
unchanged. Exact complete raw words match the compiled Lean goldens in both
pipelines. This is external/compiler evidence, not source admission/correspondence.
The old failed shared replay outputs and superseded empty-root claim remain intact.

Independent finder and skeptic reviewed all new areas read-only without Lean/
server/build/tests. No mathematical defect found. Skeptic's two documentation
findings were fixed: qualify low-level alignment and add the previously missing
full-slot goldens. Final followup found no remaining confirmed finding. Records
are `/workspace/vy2-evidence/nested-components/*-review.md`.

Final wrapper exit0:1007 default/262 TestSuite jobs,131 sort annotations matched.
Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613; mandatory KeySort exit0,2 jobs before RUNTIME_GATE_PASS.
Complete signature/axiom audit407 public declarations/213 theorems, only the three
standard axioms. Initial audit extractor dropped '?' suffixes; failed input/output
preserved, corrected extractor and final audit pass. All checks serial -j1 in the
same enforced12GiB/no-swap runtime with OS/RSS/disk monitoring and caches. Final
exact-base static/docs outcomes and exact committed head/artifacts are in HANDOFF.md.

Queue accounting: this advances original Backfill A with concrete disjoint and
fixed nested composition, not an opaque owner agreement. Backfill B actual
journals/instances remain open. Full Y04/Y05/Y06/Y09.02, whole-store/heap/dirty
writeback, actual assembly MemOK, allocator/refinement, V10/V11 instances and
VY1/source/calculus/compiler joint closure remain unfinished. Actual prerequisite
interfaces remain absent in this tree, consistent with the user's published-tree
investigation; no other worker fetched or merged. Goal remains blocked, never
recreated/reset/reactivated. No new human semantic decision; questions=[].

### Canonical typed writeback checkpoint (2026-10-31)

New ScalarWriteback constructs writeback over actual Source.Storage, including a
concrete singleton ScalarStorageObligations instance. A codec, actual path/slot,
StorageWidth proof and available typed default are explicit inputs. Canonical
validation checks decode then re-encode; no assumed inverse/result-view law is
added. On unchanged encoded input the original store is returned, preserving
none versus explicit-default cells. Changed successful inputs write exactly the
selected typed path. Unrelated paths, disjoint component reads and unowned bytes
(including nonzero padding) are preserved under real bounds/separation premises.
The arbitrary residual-map encoder reconstructs an unchanged physical view.

ScalarWorld constructs actual Source.Op.account/transient callbacks over current
storage. Controls inhabit bool fields at slot7 offsets0/1 and transient slot0:
empty/default identity, changed/repeated/disjoint writes, invalid canonical decode,
caller prefix with inner revert, successful child followed by outer revert, and
endTx keeping persistent values while resetting transient storage/journal. These
are source-owned controls, not integration of the still-missing raw residual-slot
journal. No Source representation or compiler was rewritten (history21067a47 read).
Dirty bool2 is explicitly outside canonical preparation; None is unsupported
preparation input, never a Yul no-op/refusal or proof of required dirty semantics.

Nine new ordered pinned-solc observations per pipeline include raw dirty bool2,
nonzero a5 padding, default/changed/disjoint writes and source-frame behavior.
Actual storage/transient layout assertions match slot7/offset0,1 and slot0.
Both legacy/via-IR pass with unchanged100m gas/5m steps. Original16 vectors,
four fixtures/13 calls/four deployments per pipeline and81 controls still pass.
New14 controls reject wrong/missing failure observations; explicit revert must be
reported as revert, never out-of-gas/stack failure. Exact pipeline inventory is
asserted following independent finder/skeptic review. Final reviews have no
remaining finding, without Lean/server/build/test use by reviewers.

Per-file/focused gates pass; initial missing-olean audit failure is preserved,
then complete signature/axiom audit489 declarations/260 theorems passes with only
propext, Quot.sound, Classical.choice. Mandatory wrapper exit0:1010 default jobs,
262 suite jobs,131 sort annotations matched. Actual Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613; mandatory KeySort2 jobs exit0 before RUNTIME_GATE_PASS.
Same12GiB hard/no-swap runtime, serial-j1, OS/RSS/disk monitor and writer lock.
Raw evidence and all earlier failures remain in `/workspace/vy2-evidence/scalar-writeback`.

Backfill A/B advance; full Y04/Y05/Y06 remain partial and concrete Y09.02 blocked.
Whole-store/heap/dirty writeback, raw residual journals, actual assembly MemOK,
allocation refinement, V10/V11 concrete agreements and VY1/source/calculus/compiler
closure remain open. Existing World/memory-call/Bridge prerequisites are present;
missing Yul correctness interfaces are not supplied by those components. Approved
YQ1–YQ7 remain in the scope decision record; no new decision or admission promotion.
Goal remains blocked; get_goal is unavailable and no goal transition is attempted.
Exact final committed head, gates/static comparisons and cumulative artifacts are
recorded in `/workspace/vy2-evidence/HANDOFF.md` (prior versions retained).

### Typed residual companion checkpoint (2026-10-31)

ResidualJournal adds a constructive fixed-domain companion alongside actual
Source.ExecState, without changing Source/World or creating untyped state/IR.
ResidualKey carries bounded address/word and a proof of nonownership in the
supplied persistent/transient ownership family. The journal saves actual old
words; undo/run, repeated-write restoration, unrelated-key preservation and mark
rollback are proved without assumed inverse laws. ResidualCompanion keeps actual
Source.Op lists and separate typed residual write lists; their independent runs
commute. ResidualFrame contains the actual Source.CallFrame and residual mark.
Combined rollback restores both components, including inner revert retaining
caller prefix and child commit remaining undoable by the outer frame. endTx uses
actual source endTx and clears transient residual cells/both journals while
preserving persistent source state and residual cells.

This is a concrete residual mechanics component, **not** a full physical source
representation. Ownership is fixed supplied input, not proved completeness or
hash separation for every source path. Controls register the existing bool slots7
and0, with unowned99/100 and actual typed scalar source operations. No conclusion
about arbitrary other source paths follows. Owned-slot padding/dirty bits, dynamic
ownership, full physical view/writeback adequacy and proper static-mode/source/Yul
execution integration remain open. The nonzero transient165 snapshot is a general
within-transaction witness, not transaction-initial reachability. G0/history review
preceded implementation; only parameter-only families are matched and existing
source representation/history21067a47 is preserved. No checking budget was raised.

New Residual.sol explicitly seeds transient165 within the transaction and checks
five ordered calls per pipeline: nested revert retaining prefix, child commit then
outer revert, persistent read/reset, successful child and next-transaction reset.
Every result checks raw source-owned word, unowned persistent99, transient99,
logical transient flag and untouched100. Exact constructor error/return bytes and
runtime hash are checked. Independent finder/skeptic found a constructor transcript
validation gap; fixed with three mutations per pipeline. Final33 controls assert
exact pipeline inventory and reject dropped/reordered calls, wrong bytes/state,
wrong exception/resource failures and bad deployment. All original16 vectors,
four fixtures/13 calls/four deployments and81 controls per aggregate run remain
unchanged; prior nine writeback calls and14 controls remain passing too. External
solc0.8.38/Osaka legacy/via-IR evidence is separate from kernel proofs and supplies
no compiler correspondence or frontend admission.100m gas/5m steps unchanged.

Per-file diagnostics (CLI fallback; MCP unavailable) and focused33 jobs exit0.
Complete544 public signatures/287 theorem axiom reports pass, only propext,
Quot.sound, Classical.choice. Final full wrapper exit0:1012 default/262 suite jobs,
131 annotations match. Actual Lean4.24.0 commit797c613 and Lake5.0.0-src+797c613;
mandatory KeySort exit0,2 jobs before RUNTIME_GATE_PASS. Strict automatic proof gate
base/head both exit0:491 automatic,61 with step budget,11 refuted,0 manual/pending;
outputs equal. Hard12GiB/no-swap, serial-j1/LEAN_NUM_THREADS=1, writer lock and actual
OS/RSS/disk monitor preserved. Raw failed attempts remain in residual-journal and
scalar-writeback evidence. Independent read-only finder/skeptic reviews used no
Lean/server/build/tests; no remaining confirmed finding after fixes.

Queue: canonical selected-path actual writeback and fixed-domain residual mechanics
advance original Backfills A/B; neither backfill nor any full work item is complete.
Y04 partial: whole-store/dirty values, complete ownership/path/hash layout and
physical/source integration pending. Y05 partial: actual heap/assembly MemOK and
nondeterministic allocation refinement/actual V11 agreement pending. Y06 partial:
existing raw inputs/hash/environment preparation not actual Yul/source admission
or compiler proof. Y09.02 blocked: concrete VY1 source semantics/calculus interface,
notation/printers and full composition absent. V10/V11 agreement instances and
V04b/V12/V13/V15/V16 final dependency obligations remain precise owner inputs;
existing source World, memory-call and Bridge components are present prerequisites,
not substitutes for the missing Yul correctness interfaces. No other branch/owner
was changed or fetched. Goal remains blocked unchanged; get_goal is unavailable;
no create/reset/reactivation/completion or stop transition attempted this turn.
Approved YQ1–YQ7 (scope decision record) unchanged; questions=[]. Exact revisions,
raw gate commands/exits, static/no-new-findings outcomes and absolute versioned
patch/bundle/handoff/checksum paths are in `/workspace/vy2-evidence/HANDOFF.md`.

### Constructive finite typed-path checkpoint (2026-10-31)

FinitePaths extends singleton preparation to a finite heterogeneous collection
over actual Source.Storage. ScalarPath carries the actual path-indexed existing
codec, StorageWidth proof and bounded slot/field. finiteSeparated requires real
pairwise distinct source paths and physical slot/field separation. No aggregate
inverse or result-view law is supplied as a field; the existing scalar codec's
individual inverse remains an input. finiteEncode and finiteWriteback construct
actual encodings/typed changes in order. Kernel laws derive represented-path
views/decoded reads, encode/writeback identity, exact unchanged original-store
identity, re-encoding reconstruction, unrelated cells/reads, bounded unowned-byte
and padding preservation. Writeback permutation/reversal and idempotence are
proved. A failed canonical member anywhere gives None for the entire preparation;
this is unsupported preparation, never Yul refusal/no-op/dirty-bit semantics.

finiteScalarObligations constructs the existing agreement interface for the finite
member subtype. Real default availability and chosen slot/location equality are
explicit inputs, plus actual separation; realization encodes into the caller's
arbitrary residual map. No complete source-path-to-HashedLayout agreement or
aggregate adequacy is assumed. FiniteWorld validates all payloads before producing
actual Source.Op.account/transient updates of CURRENT typed storage. Successful
requests derive actual result/view/unrelated-path/unchanged-store and journal
laws. An unchanged store can still produce a source journal entry; no claim of
unchanged full ExecState or EVM opcode counts follows.

FiniteControls inhabits three real paths with bool and uint16 sharing slot7 at
offsets0/1, plus uint256 in slot8. Controls cover empty versus explicit-default
administrative identity, changed ordered values, reversed agreement, repeated
writeback, unrelated typed value55, nonzero a5 residual/padding, complete word
goldens, failure at the last reversed-list member, duplicate-path separation
refusal, actual source operations and caller-prefix/inner revert/child commit/
outer revert/transaction reset. Heterogeneous actual transient batch controls
prove rollback and all three typed reset defaults. Nonzero transient snapshots
are within-transaction witnesses, not transaction-initial reachability claims.

FiniteResidual derives the residual ownership predicate from actual persistent/
transient finite registrations. Intrinsic residual keys therefore imply slot
exclusion from those collections; concrete finite encoders preserve those entire
unowned slots. FiniteResidualControls connects actual heterogeneous source batches
and these residual keys through the existing actual Source-frame companion,
including changed residual words, nested/outer rollback and reset. This is fixed
REGISTRATION ownership, not completeness over all possible source paths. Owned
padding/dirty-bit journaling, dynamic/mapping/hash region separation and full
physical-source adequacy remain unproved. No Source/World/Heap owner code changed;
G0/history21067a47 reviewed and checking-cost warning preceded the new parameter-
only record/list recursion. No proof/fuel/node/test/gas budget increased.

New Finite.sol observes10 calls per pipeline. Independent expected words follow
bool byte0, uint16 bytes1..2 and next-slot uint256. Both pinned solc0.8.38/Osaka
legacy/via-IR pipelines pass, optimizer disabled,100m gas/5m steps unchanged.
All eight returned values and exact ABI bytes are checked: represented fields,
unrelated typed field/physical word, full residual sentinel and transient flag.
Forward/reverse/repeated/default/dirty2 and inner/outer/transaction controls retain
their original order. Exact constructor exception/bytes/runtime hash, pipeline
inventory and layout labels/slots/offsets/widths are validated.55 fail-closed
mutations include missing/reordered calls/pipelines, wrong results/bytes/state,
resource failures posing as revert, constructor and metadata corruption.
An initial seed-literal length typo failed solc; source/reports and failed control
run are preserved, then corrected to exact32-byte seeds without changing expected
results. This fixture checks residual99 PRESERVATION; changed residual journaling
is covered by earlier Residual.sol and finite kernel controls, not by this fixture.

Original16 physical vectors, four upstream fixtures/13 calls/four deployments per
pipeline, nine writeback and five residual calls remain unchanged and passing.
Their81/14/33 negative controls still pass. External tests are separate from
kernel laws, compiled goldens and actual frontend/compiler correspondence; no
admission/exclusion/manifest promotion or Y09.02 completion follows.

Per-file CLI diagnostics (MCP absent), focused38 jobs,659 exact public signatures/
348 theorem axiom reports pass. Only propext/Quot.sound/Classical.choice; raw failed
attempts retained. Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613; mandatory KeySort exit0 with2 jobs precedes this checkpoint's
RUNTIME_GATE_PASS prerequisite claim. Final required wrapper exit0:1017 default/
262 suite jobs,131 matched sort annotations. Strict automatic gate exact-base/head
exit0 with equal outputs:491 automatic,61 budgeted,11 refuted,0 manual/pending.
Hard aggregate12GiB/no swap, serial-j1/LEAN_NUM_THREADS=1, writer lock and actual
OS/RSS/disk monitoring/caches preserved. Independent read-only finder/skeptic
reviews used no Lean/server/build/tests. Wording clarified scalar versus aggregate
inverse inputs; final reviews have no remaining confirmed findings. Exact static/
trust/docs comparisons, command exits, full committed revision and artifact paths
are in `/workspace/vy2-evidence/finite-paths/HANDOFF.md` and cumulative HANDOFF.md.

Entire queue stays unfinished: Y04 partial (finite canonical preparation only;
whole-store/dirty/dynamic/path/hash agreement open), Y05 partial (actual heap/
MemOK/allocation refinement/V11 instance open), Y06 partial (actual Yul/source/
admission/compiler connection open), Y09.02 blocked (actual producer source/
calculus interface, rules/notation/printers/final composition open). Backfills A/B
both partial. Arbitrary Source.Storage layouts do not supply declared physical
coverage or a representation for raw dirty bits; those cannot be inferred from
this finite collection. Actual World/memory-call/Bridge prerequisites are present,
not substitutes for missing VY1/MemOK/V10/V11/Yul compiler/calculus interfaces and
V12/V13/V15/V16 joint gates. Goal remains blocked unchanged; get_goal unavailable;
no create/reset/reactivation/completion/stop transition. Approved YQ1–YQ7 remain
in the scope record; questions=[]. Prior3417-entry artifacts/manifests and all
older raw failures are preserved under finite-paths/prior-* before refresh.

### Actual selected heap bytes/string checkpoint (2026-10-31)

HeapByteWriteback now decodes physical bytes/string objects into actual
Source.Heap.write at the selected object's original logical identity and exact
declared type. It reuses ByteObjects' existing decoders; no second state/value IR,
opaque writeback/inverse premise, arbitrary decoder cap or owner rewrite. The
original allocated object/get proof and actual valid Placement are explicit inputs.
The selected preparation retains the original length header, so the original
Placement's exact shape remains valid. Changed payloads update the real typed
object; unchanged header/payload returns the WHOLE original heap by proved heap
extensionality. Every other cell, all types, next and boundedness are preserved.
Alias/get laws, decode/encode and exact physical re-encoding preserve residual and
padding bytes. None on header mismatch is unsupported selected preparation, NOT
Yul refusal/no-op or semantics for required raw header/growth cases.

HeapBytePlacement/Composition construct valid placement for actual successful
outputs, retaining original address/shape/free choices and all reserved-area,
capacity, distinctness and separation obligations. Length bounds derive from the
actual Placement's ends/free bound. No alignment requirement added. Same-sized
canonical patches preserve the exact free-pointer and zero words, every other
nonoverlapping object's live region and decoder; the latter retains its real
correct-header premise. Actual Heap.write operations at distinct identities
commute, with concrete writeback calls in both orders. Full allocated padding is
not silently cleaned. No allocation is performed or refinement theorem claimed.

HeapByteMemOK proves transport of ACTUAL owner Source.MemOK for every initial
heap typing H, using existing HeapOK/HeapShaped/HeapInner/LocalsOK laws. Actual
owner definitions are AVAILABLE in Source/State.lean and Source/WellTyped.lean;
there is no Source/Heap.lean module. withSourceHeap updates the actual typed
EMState, retaining locals/world/observations/other state. The selected relation
heapByteStateStep is defined by implemented writeback; heapByteStateStep_preserves
proves the existing PreservesMemOK contract for that relation, not all assembly.
It does not instantiate whole MemoryWritebackObligations or MemoryLayoutObligations.

Controls use actual Heap.alloc for bytes3, string33 and unrelated bytes3. They
inhabit changed/unchanged whole heaps, same-identity bytes/string aliases, actual
source reads through BOTH local alias values at EVERY horizon, actual initial/
output MemOK and two successful state writebacks. Non-UTF8 ff string bytes are
preserved. Other-cell/type/next/bounds, forward/reverse changes, nonzero a5 padding/
gaps, exact reserved words and unaligned placement choices are controlled.
Ordinary allocated empty and31/32/33-byte families prove writeback/unchanged and
exact free/padding boundaries; Fin34 is a finite test family, never a decoder cap.
Shared zero-slot empties remain separate. Initial direct normalization exceeded
default recursion depth; replaced by existing codec/frame proofs, no limit raised.
All raw syntax/inference/normalization failures retained. G0/history21067a47 and
owner invariant interfaces inspected; checking-cost warning preceded the local
helpers. Only parameter-only Bool is matched in new computational selectors.

Pinned HeapBytes.sol adds10 ordered calls/pipeline, with independently specified
18-word ABI-byte envelopes: complete length/payload words, typed bytes/string
alias reads, unrelated object, padding/gaps, exact free/zero words and ordinary
empty/31/32/33 boundaries, plus exact explicit revert and fresh-call observation.
Both solc0.8.38/Osaka legacy/via-IR pass; unchanged100m gas/5m steps and optimizer
disabled. Full return bytes, constructor exception/bytes/runtime hash/length,
pipeline inventory and89 fail-closed mutations pass. Raw header3→4 succeeds in
both pipelines and is EXPLICITLY OPEN in the same-length kernel preparation;
its None does not establish an exclusion/refusal/no-op. Initial free0x80 and the
explicit384/256-byte object/boundary allocations explain observed512/384 pointers;
retained IR/code hashes and exact observations are specific compiler evidence,
not a source allocation discipline or refinement proof.

All earlier16 physical vectors, four upstream fixtures/13 calls/four deployments,
nine writeback, five residual and ten finite calls per pipeline retain order and
expectations; all81/14/33/55 earlier negative controls still pass. Kernel proofs,
compiled golden controls and external compiler/EVM tests remain separate. No
frontend/manifest promotion or Source/Yul/compiler correspondence follows.

Per-file CLI diagnostics (Lean MCP unavailable), focused39 jobs and final full
wrapper exit0:1024 default/262 suite jobs,131 matched annotations. Exact768 public
signatures/413 theorem axiom reports pass with only propext,Quot.sound,
Classical.choice. Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613, mandatory KeySort exit0,2 jobs before RUNTIME_GATE_PASS
prerequisite claim. Strict automatic exact-base/head exit0 and equal outputs.
Same hard aggregate12GiB/no swap, serial-j1/LEAN_NUM_THREADS=1, writer lock and
actual OS/RSS/disk monitor/caches. Independent read-only finder/skeptic reviews
used no Lean/server/build/tests. Their inhabited-state/alias-read control gap was
fixed and re-reviewed; no remaining confirmed findings. Exact commands, static/
trust/docs results, revisions and preserved artifacts: heap-bytes/HANDOFF.md in
`/workspace/vy2-evidence` and cumulative HANDOFF.md.

Full queue remains unfinished. Y05 is PARTIAL: selected ordinary fixed-shape
bytes/string writeback and actual selected-step MemOK are done; complete heap
view/realization, raw header/size changes (even within rounded extent), growth,
shared-zero empties, dirty word/pointer-bearing/nested aggregates, reserved-word
mutation semantics, actual assembly integration and allocator refinement remain
open. MemoryWritebackObligations.realize still quantifies ∀H s, MemOK E H s →∃m,
view s m; MemOK alone gives no EVM placement/capacity bound on arbitrary logical
byte lists. MemoryLayoutObligations.realize receives a valid Placement but still
owes ALL object/word/byte reads, not just selected objects. We neither weaken
those signatures nor fake whole-memory instances. Concrete V11 compiler layout
agreement and full assembly MemOK composition still require actual producer
interfaces. Y04/Y06 and Backfills A/B remain partial; concrete Y09.02 remains
blocked. Existing Source.World/memory-call/Bridge and owner MemOK definitions
are present, not substitutes for missing VY1/source/calculus/compiler and
V10/V11/V12/V13/V15/V16 joint obligations. Goal blocked unchanged; get_goal absent;
no create/reset/reactivation/completion/stop transition. Approved YQ1–YQ7 remain
in scope; questions=[]. Original3540 manifest/artifacts verified and preserved
under heap-bytes/prior-*; older failures/caches retained.

### Bounded size-changing heap checkpoint (2026-10-31)

HeapByteResize adds a SEPARATE actual bytes/string Heap.write implementation.
The existing fixed-length API, guard, controls and signatures are unchanged;
heapByteResize_fixed_compat proves equality on the old same-header domain. The
new guard compares the new header's rounded MemoryShape footprint with the
selected object's ACTUAL input Placement footprint. Existing unbounded decoders
are reused only after this check. No arbitrary decoder/fuel/test cap, cleaning,
Source representation change or opaque inverse/result-view premise. Any new
length fitting that original input footprint is supported, including shrink,
empty and same-rounded-extent growth. None remains unsupported preparation,
never Yul admission/refusal/no-op or a proof of all memory-safe semantics.

HeapByteResizePlacement constructs the actual output Placement: addresses/free
choice retained, only the selected shape updated to decoded length. Actual
Heap.write keeps occupancy, exact declared type/identity, all other cells/types,
next and boundedness. New starts/ends/distinctness/separation derive from old
placement facts and the checked size bound; all other shapes/physical regions
remain original. Source.MemOK transport for every initial H uses the real owner
invariants. Exact successful header/live-byte/read and physical re-encoding laws
are proved. Canonical shrinking encoders retain formerly live tail bytes in the
residual; raw header stores preserve exact reserved/free/zero words. Neighbor
header/payload/decoder laws retain their necessary correct-header premise, not
an assertion that arbitrary raw memory operations were safe. Two-object actual
resizes in both orders and combined actual-state MemOK are controlled.

Controls inhabit raw3→4 growth exposing old padding a5,3→1 and3→0 shrink,
nonUTF8 string33→32, ordinary31→32/33→32/33→64 boundaries, and real source states/
MemOK/alias reads at every horizon. Unrelated cells, neighbors, tail/padding/gaps,
fixed guard failures and exact retained placement choices are checked.32→33 is
an actual beyond-input-footprint None witness. Fin34 only bounds inherited
boundary witnesses; it is not a decoder/model cap. Raw normalization failures
were replaced by explicit header/placement laws with no budget increase.

Important exact limitation: Placement.shape describes current logical shape,
not historical allocated capacity. After3→0, output shape is bytes0 (size32),
address128/free512 retained, and historical_capacity_not_recovered proves that
feeding that minimal output placement to a later header4 request gives None,
even though the original bytes3 footprint was64. This is NOT deallocation or a
Yul refusal. Threading real allocation-capacity/history evidence is still open;
we do not keep a false old shape, invent a second state or weaken typed/placement
obligations. No new human semantic decision is inferred from this interface limit.

New HeapResize.sol imports the frozen HeapBytes.sol unchanged. Twelve new ordered
calls/pipeline observe22 ABI words each: all headers/live payload words, newly
exposed padding, preserved formerly live tails, both typed aliases' lengths/reads,
unrelated object/gaps, exact free/zero words, explicit revert and a fresh call.
All expected bytes specified independently and checked in both pinned solc0.8.38/
Osaka legacy/via-IR pipelines.103 fail-closed mutations require exact constructor/
exception/hash/length/inventory/ABI/value/tail/alias/failure behavior. A raw65-byte
header beyond the selected33-byte object's96-byte footprint ALSO succeeds
externally and remains explicitly OPEN here; its prep None is not an exclusion.
The pool's384-byte allocation and free512 are specific fixture observations,
not a source allocator discipline or allocation refinement proof.

All old physical/upstream/writeback/residual/finite/heap fixtures, deployment/
failure observations, expectations/order and81/14/33/55/89 negative controls
remain unchanged/passing. Parent heap APIs and fixture hashes checked against
33530fa39cd00a0601046c2a2ecab50eb1a8fb93. No fork/observation/premise/target predicate
weakened.100m gas/5m steps/proof/node/test budgets unchanged. Kernel laws and
external compiler/EVM evidence remain separate; no frontend/manifest promotion.

Per-file CLI fallback (no Lean MCP), focused44 jobs and final full wrapper exit0:
1029 default/262 suite jobs,131 matched annotations. Exact859 public signatures/
470 theorem axiom reports pass, only propext/Quot.sound/Classical.choice. Actual
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613;
mandatory KeySort2 jobs exit0 before RUNTIME_GATE_PASS prerequisite claim.
Strict automatic exact-base/head exit0 and equal outputs. Hard aggregate12GiB/
no swap, serial-j1/LEAN_NUM_THREADS=1, actual OS/RSS/disk monitoring/writer lock/
caches retained. G0/history reviewed; only local typed helpers, no owner rewrite.
Independent finder/skeptic reviewed read-only without Lean/server/build/tests;
no confirmed semantic/G0 finding, requested over-capacity control included, final
review clear. Raw failed attempts retained. Exact static/trust/doc comparisons,
commands/exits/full revisions and versioned artifacts: heap-resize/HANDOFF.md in
`/workspace/vy2-evidence` and cumulative HANDOFF.md.

Full queue: Y04/Y05/Y06 and Backfills A/B remain PARTIAL, concrete Y09.02 BLOCKED.
Y05 now includes bounded size changes but still lacks historical capacity,
larger/cross-boundary growth, shared-zero empties, dirty word/pointer/nested
representations, whole-memory realization/owner agreement, full assembly MemOK,
actual source/Yul embedding and allocator refinement. MemoryWritebackObligations,
MemoryLayoutObligations and PreservesMemOK signatures unchanged. Actual owner
MemOK/World/memory-call/Bridge definitions are present, not substitutes for missing
VY1/source/assembly/allocation/V10/V11/compiler/calculus and V12/V13/V15/V16 final
interfaces/gates. Goal remains blocked unchanged; get_goal unavailable; no goal
transition/create/reset/reactivation/completion. Approved YQ1–YQ7 preserved;
questions=[]. Original3666 manifest/artifacts verified and retained under
heap-resize/prior-*; all previous code/raw failures/caches remain.


## Retained ordinary allocation checkpoint (2026-10-31)

Recovery parent `5c108b7ffc4074f40ea5c5bd8a47f755cc7c3c44`; pinned base
`0b078cefaf7daad79007b87b72df64eb6936420f`; assigned branch
`codex/solidity-inline-assembly5-20261031/vy2-physical` in
`/workspace/solidity-lean`. Exact committed head is in the versioned handoff
`/workspace/vy2-evidence/retained-allocation/HANDOFF.md`.

[RetainedAllocation](../../Solidity/Yul/Views/RetainedAllocation.lean) adds a
separate typed witness. RetainedGeometry proves occupancy, address/free identity
and exact current-shape bounds against a supplied actual origin heap/Placement.
It is NOT enough for writeback: RetainedAllocation records inductive lineage
from that initial placement through actual typed Heap.write operations. Initial
allocation-snapshot provenance still must be established by the integrated
allocator; the witness does not prove allocation refinement or a source trace.
Retained capacity means that placement's original shape footprint, never an
address gap/free-pointer guess or all capacity of a custom memory pool.
Constructive output placements retain the real current data shape while using
original full-region ends/separation. No owner representation or existing
Placement/HasMemoryShape/fixed/bounded API or obligation signature changed.

`retainedByte_encode`, `retainedByte_unchanged`, `retainedByte_result_history`,
`retainedByte_result_choices`, `retainedByte_preservation`,
`retainedByte_full_separation`, `retainedByte_other_region`,
`retainedByte_live_view` and `retainedByteState_MemOK` prove actual supported
writes, exact byte/header/residual agreement, whole-heap unchanged identity,
types/next/boundedness/other cells and owner MemOK for EVERY initial typing H.
Real found/type/Placement/lineage/rounded-footprint/separation premises are
explicit in the scoped signatures. No opaque inverse or desired-result law,
new axiom, hash injectivity, false old shape or decoder/fuel cap is assumed.
The unmodified old historical_capacity_not_recovered remains a negative control
for the original minimal API. Prep None still means unsupported preparation,
never Yul refusal/no-op, deallocation or observed compiler behavior.

[Controls](../../Solidity/Yul/Views/RetainedByteControls.lean) inhabit bytes
3→0→4/32 and33→0→64, raw nonUTF8 string33→0→64, both aliases at every horizon,
nonzero retained live tails/padding/gaps, actual reserved/free/zero words, unrelated
cells and two retained regions in both orders. The coherent both-zero physical
prefix is used in both orders; universal disjoint byte-object commutation proves
exact physical equality as well as actual heap-write commutation.
[RetainedHeap.sol](../../tests/yul-views/RetainedHeap.sol) imports the frozen
previous fixtures. Nine ordered calls per pinned legacy/viaIR pipeline compare
complete ABI bytes/values, aliases at observable zero/regrowth stages, original
padding/tails, unrelated objects, free/zero, explicit revert and fresh calls;
all deployment exceptions/bytes/runtime hashes remain checked. The external
forward/reverse case retains the original0x61 string payload, while the kernel
combined case uses the nonUTF8ff/62 prefix: complementary instances, not an
identical golden input or a correspondence proof. Actual combined source state
controls carry four aliases and prove owner MemOK after both regrowth writes. 121 new negative
controls reject dropped/reordered/wrong byte/state/stage/failure/deployment
observations. Every prior reference-report field is identical, with all earlier
81/14/33/55/89/103 controls preserved. This is external compiler/EVM evidence,
NOT kernel source/target correspondence or frontend admission. Gas100m/steps5m,
proof/fuel/node/test limits and fork exclusions unchanged.

Reviews: separate read-only finder and skeptic without Lean/server/build/tests.
Their provenance and inconsistent-intermediate-map findings were addressed with
constructive lineage and the coherent both-zero prefix/physical commutation;
final review results and exact gates/resources/signatures are saved in the
versioned evidence/handoff. An initial proof placeholder-inference failure and
wrong test filename invocation are retained, not passes. G0/speed history read;
no owner state/compiler rewrite, no source representation change. Serial-j1,
LEAN_NUM_THREADS=1, hard aggregate12GiB/no swap, actual OS/RSS/disk monitoring,
writer lock and caches preserved. Global docs still exit1 with exact-base48
findings and zero new findings; zero delta is not a global pass.

Full queue remains unfinished: Y04/Y05/Y06 and Backfills A/B PARTIAL, actual
Y09.02 BLOCKED. Historical extent retention for these ordinary selected objects
is now constructive; whole-store/path/dynamic/hash separation, shared-zero,
larger-than-origin/pool ownership, dirty/pointer/nested memory, whole-memory
realization, exact full MemoryWritebackObligations/MemoryLayoutObligations,
actual Yul/source assembly MemOK and allocation refinement, V10/V11 instances,
Yul compiler/calculus and final joint closure remain. Actual owner MemOK/World/
memory-call/Bridge code exists and is reused, not claimed absent or adequate for
missing VY1/source/assembly/allocation/compiler/calculus interfaces. No worker
fetch/merge, scope promotion, goal reset/reactivation/completion or push. Goal
remains blocked unchanged; get_goal is not exposed. YQ1–YQ7 remain binding;
questions=[]. All3793 prior hashes verified before preserving prior-* snapshots;
versioned patch/bundle/handoff/evidence/checksums retain every older artifact.

Final checkpoint gates: per-file CLI fallback and focused46jobs pass; final
fullwrapper1031default/262suitejobs/131matchedannotations exit0, actual
Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs exit0. Scoped960declarations/
517theorem reports have only propext/Quot.sound/Classical.choice. Both independent
final reviews clear, including four-alias actual-state addition and59/121
inventory assertions. Raw failures and baseline-equal docs exit1 are retained.


## Constructive supported byte-heap realization (2026-10-31)

Continued original Y05/Backfill A/B after reviewed retained checkpoint
`a1536515747bd091aa2254cc154146831122b243` on the same branch/VM.
[ByteHeapRealization](../../Solidity/Yul/Views/ByteHeapRealization.lean)
constructs physical views by a finite List fold over actual typed Heap.get
witnesses, not an untyped state, owner rewrite or assumed inverse. Each entry
contains its actual source id, bytes/string choice, contents and found proof.
`encodeByteHeap_reads`, `encodeByteHeap_reserved`, `encodeByteHeap_residual`,
`encodeByteHeap_unchanged` and `encodeByteHeap_realizes` derive exact reads,
reserved words and arbitrary residual/padding preservation. All lengths/bounds
come from the valid actual Placement. List coverage and distinct ids are real
explicit premises; no artificial size/fuel limit. `encodeByteHeap_source_word`
and `encodeByteHeap_source_byte` prove ALL actual ObjectWord/ObjectByte reads
for a heap covered by those entries. This is bytes/string-only ordinary support,
not the universal MemoryLayoutObligations/MemoryWritebackObligations instance or
a changed source/calculus coverage predicate. Existing obligation signatures
remain unchanged.

[Controls](../../Solidity/Yul/Views/ByteHeapRealizationControls.lean) construct
all three heterogeneous objects of actual byteHeap, exact bytePhysical equality,
whole supported-view unchanged identity and coverage. Missing-string coverage
and wrong bytes/string type are negative controls. The same construction covers
the actual two-region retained/regrown heap, with its real output Placement and
RetainedAllocation lineage, exact reads/unchanged/reserved/padding. Existing
pinned compiler fixtures already compare this original three-object physical
layout; no external test is a kernel correspondence proof. No fixture/driver/
expectation changed in this checkpoint. Previous both-pipeline observations and
121new negative controls remain applicable unchanged.

[Y05/realize-capacity] Exact obstruction, not a semantic exclusion:
`oversized_actual_MemOK` proves actual owner MemOK for a source heap allocated
with List.replicate (2^256) bytes. `oversized_no_ordinary_placement` proves that
heap has NO ordinary Placement, using the existing documented byte-layout bound.
Thus an implication from arbitrary owner MemOK to existence of this ordinary
EVM placement is false. This does NOT refute MemoryLayoutObligations.realize
(which already takes a valid placement), nor every possible relation satisfying
MemoryWritebackObligations.realize; it blocks silently realizing ALL MemOK states
via ordinary placements without further concrete source/allocation reasoning.
No contract/premise was weakened, new resource bound/refusal introduced, or human
choice assumed. Initial allocation/refinement and full realization remain open.

Initial failed proof/control outputs retained, including the mistaken NEW
padding offset416 (actually c payload), corrected to419 using the actual view.
No old expected verdict changed. G0 uses parameter-only List recursion, not a
new indexed Data match. Independent finder/skeptic read-only reviews, final gates,
exact committed SHA/signatures/resources and artifacts are recorded in
`/workspace/vy2-evidence/heap-realization/HANDOFF.md`; cumulative artifacts remain
under `/workspace/vy2-evidence`. Full queue still Y04/Y05/Y06 and Backfills A/B
PARTIAL, concrete Y09.02 BLOCKED; dirty/dynamic/pointer/hash/whole-memory/source/
assembly/allocator/V10/V11/compiler/calculus/final closure obligations unfulfilled.
Actual owner interfaces are available and reused. Goal remains blocked unchanged;
YQ1–YQ7 approved, no promotion, push/merge or owner takeover; questions=[].

Final supported-view validation: per-file/focused48jobs, fullwrapper1033default/
262suitejobs/131matchedannotations, actual Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort2jobs exit0. Scoped999declarations/543theorem reports standard axioms only;
layers224core/0elaboratorreach, orphans1048reachable/0orphan, trust1063sources/
246inventoriedsites/0findings, strict491automatic/61budgeted/11refuted/0pending
pass. Global docs exit1 same48findings; markdown base1/head1/new0. No preceding
fixture/API/owner source changed. Separate read-only reviews cover final
retained/oversized controls and exact scope. Every raw failed attempt retained.


## Mixed ordinary aggregate/pointer views (2026-10-31)

Continued ORIGINAL Y05/Backfill A/B from clean
`2b1079eb79ea40d804172f64df0104985a11e984`, pinned base
`0b078cefaf7daad79007b87b72df64eb6936420f`, assigned branch/VM unchanged.
Exact committed head and gates are in `/workspace/vy2-evidence/mixed-heap/HANDOFF.md`.
New lane modules [AggregateMemoryWords](../../Solidity/Yul/Views/AggregateMemoryWords.lean),
[AggregateMemoryObjects](../../Solidity/Yul/Views/AggregateMemoryObjects.lean),
[MemoryImages](../../Solidity/Yul/Views/MemoryImages.lean),
[MixedHeapView](../../Solidity/Yul/Views/MixedHeapView.lean) and
[MixedMemoryMemOK](../../Solidity/Yul/Views/MixedMemoryMemOK.lean) construct
ordinary word-per-member structs, static arrays without headers and dynamic
arrays with length headers, alongside existing bytes/string images.

MemoryElement scalar words use the existing Source.Val.word; pointer words
require actual child heap typing and memShape compatibility. Addresses and
array header ranges derive from real typed contents, valid Placement ends and
its bounded free word. Child contents are SEPARATE heap objects; aliases share
the same pointer, never inline nested copies. MemoryFields/MemoryObjectWords
are intrinsic constructor serialization witnesses about actual Data/DataList,
not a second state, AST or untyped intermediate. No assumed inverse/read or
preservation theorem is a structure field. Word-list and heap-entry recursion
is parameter-only; indexed images use explicit constructor eliminators, not
new equation-compiled indexed matches. G0/speed history reviewed, owner source
representations untouched; control check3.5seconds then3.8seconds with actual
Env declarations (not a general performance claim). No proof/fuel/node budget
raised; initial deep nested evaluation replaced with compositional read laws.

wordList_read/residual/unchanged, MemoryObjectWords.read/fits,
MemoryImage.encode_reads/fits/reads_congr/unchanged/source_word/source_byte,
encodeMixedHeap_reads/reserved/residual/unchanged/source_word/source_byte prove
exact physical and actual source-layout agreement with explicit typed snapshot,
finite distinct coverage, valid placement and canonical element premises.
MemoryElement.refOK, MemoryFields.dataOK/allVal and actual mixedHeap owner
invariants derive DataOK/Top/Inner from constructors. These remain supported
read/view components, not universal realization/writeback or dirty-word cleanup.
Standalone Data.val roots have NO existing HasMemoryShape constructor;
no_value_memory_shape records that exact boundary without inventing a shape,
new exclusion or altered API. Scalar/pointer MEMBERS are implemented. Dirty
owned words, shared zero-slot empties, unsupported representations and full
source/Yul/compiler/allocator/calculus closure remain original open work.

[Controls](../../Solidity/Yul/Views/MixedHeapControls.lean) inhabit actual Env
Box declarations and a six-object typed Heap: bytes child, nonUTF8 string,
uint256[2], heterogeneous bool/uint/two aliased bytes pointers/dynamic-array
pointer struct, dynamic bytes-pointer array with two aliases to the same child,
and unrelated bytes. Exact word/header/pointer/padding/free/zero, physical
struct→array→child chain, actual initial owner MemOK and source local bytes/string
alias reads at EVERY horizon are proved. Missing/wrong-shape ownership,
wrong pointer bits/member type are negative controls; legal bytes/string child
shape alias is positive. Physical nested-chain reads are NOT a source Expr/Yul
execution/composition theorem. Actual observed free1888 has a valid alternate
Placement and actual source-word preservation; kernel initial free1664 is a
separate valid choice. No silent allocation normalization/refinement assertion.

[MixedHeap.sol](../../tests/yul-views/MixedHeap.sol) reserves1536bytes BEFORE
named uint[2]/Box return defaults; these temporary defaults add64+160bytes.
The observed pre-output free word is exactly128+1536+224=1888; output storage
is allocated later. Proper bytes ABI envelope and ALL40payload words are
independently specified, including pointers, headers, six gap words, aliases,
child/scalar writes in both orders, retarget to nonUTF8 string child, explicit
revert and fresh calls. Both pinned solc0.8.38/Osaka pipelines pass8ordered calls
and157negative controls (77mutations per pipeline+3inventory), fixed inventory
assertions. All previous report fields/168calls and prior controls remain
unchanged; no shared helper, gas100m/steps5m, fork exclusion or old expectation
modified. Initial draft raw report is BROKEN in both pipelines due named-return
allocation order; raw source/report/log retained, fixture source corrected;
not relabeled pass. This evidence is external-only, not frontend admission or
kernel compiler/source correspondence. Rule-map rows are Lean-only per YQ5.

Independent finder/skeptic read-only reviews (no Lean/server/build/tests) found
no confirmed mathematical/G0/fixture defect; stale reference comment fixed.
Final exact gates/signatures/resources/reviews and checkpoint artifacts are in
mixed-heap/HANDOFF.md. Full Y04/Y05/Y06 and Backfills A/B remain PARTIAL,
Y09.02 BLOCKED. Whole-store/path/hash/dynamic/dirty ownership, universal memory/
writeback, allocator provenance/refinement, shared-zero/nested source execution,
V10/V11 instances and actual VY1/source/compiler/calculus/final closure remain.
Owner MemOK/World/ContractWorld/Bridge interfaces ARE available, not adequacy.
The oversized_actual_MemOK/no_ordinary_placement boundary is unchanged: it
refutes only unqualified owner-MemOK→ordinary-Placement inference, not existing
placement-parameterized MemoryLayout.realize, arbitrary MemoryWriteback relations
or a proved reachable execution. No capacity premise/semantic choice assumed.
YQ1–YQ7 and manifest statuses unchanged. Goal blocked unchanged, get_goal absent,
no goal transition/new VM/thread/model/worker merge/push/owner repair; questions=[].

Final mixed checkpoint validation: per-file CLI/focused47jobs/fullwrapper1039
+262jobs/131matchedannotations exit0; actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs exit0. Scoped1106declarations/600theorem reports standard axioms.
Layers230core/0elaboratorreach,1054reachable/0orphan, trust1069sources/246sites/
0findings, strict491automatic/61budgeted/11refuted/0pending pass. Raw docs exit1
same48findings, markdown base1/head1/new0. Final independent reviews clear.


## Concrete selected array and pointer writeback (2026-10-31)

Continued original Y05/Backfill A/B AFTER reviewed/gated mixed-view commit
`3cd014adf657cdc84f697f165720d5744844f70e`. New
[StaticUintMemory](../../Solidity/Yul/Views/StaticUintMemory.lean) constructs
uint256 values from ALL256bits, static arrays at their declared length and exact
physical decoders. uintValueOfWord_word, decodeStaticUint_encode/reencode,
staticUintWriteback_encode/unchanged/other/types, staticUintWrittenPlacement,
staticUintState_MemOK/unchanged and staticUint_word_fits prove constructive
roundtrip, whole heap/state unchanged identity, actual typed Heap.write,
unrelated cells/types/next/boundedness and original address/shape/free choices.
EVERY initial owner typing H is preserved; no inverse/preservation law is assumed.
Valid original found array/Placement supplies length/word bounds, not an added
cap. Full-width uint256 has no discarded dirty high bits; this does NOT provide
narrow dirty-word cleanup or resolve YQ4 for other types.

[PointerMemory](../../Solidity/Yul/Views/PointerMemory.lean) searches a finite
set of actual typed MixedHeapEntry witnesses. Candidate shape and EXACT raw
address must match; no gap/free-pointer inference. Successful decoding proves
actual RefOK and ElementWord raw-bit agreement. Complete supported coverage and
Placement.distinct give decodeMemoryPointer_encode, not an assumed inverse.
The candidate list is explicit; incomplete lists do NOT imply absence of a real
child. pointerStateWriteback composes with ACTUAL Source.writeLoc and exposes
its full Except/state result; real owner MemOK for EVERY initial H is preserved
through successes AND source errors. structPointerWriteback reads the actual
physical member word with real found-struct/declared Fin-index/type premises;
structPointer_word_fits derives its word window bounds. It is SELECTED-FIELD
writeback: it does not decode other simultaneously changed struct fields or
claim generic target progress/all-block safety. None is unsupported preparation,
not Yul refusal/no-op/deallocation; shared-zero/interior/unrepresented/dirty
pointer cases remain original open obligations. Existing owner and full memory
obligation signatures are unchanged.

[Controls](../../Solidity/Yul/Views/WordWritebackControls.lean) use the actual
mixed Env/Heap: array7,9→7,42, unchanged whole state, full2^256-1 value, two array
aliases/actual Source.readLoc, retarget a bytes member to a real string child,
actual member reads and bytesOfRV at EVERY horizon, unchanged pointer source
step, invalid129/wrong-type/shared-zero96/missing-coverage preparation controls,
reserved/free/zero/padding/other roots. Concrete array→physical-pointer and
pointer→array source state steps agree, with actual all-H owner MemOK;
mstore_disjoint_commute proves exact whole physical equality of both orders.
No full source Expr/Yul/compiler correspondence is inferred.

[WordWriteback.sol](../../tests/yul-views/WordWriteback.sol) imports the frozen
MixedHeap.sol. Six ordered calls per pinned legacy/viaIR pipeline compare ALL42
ABIwords/bytes for pointer+scalar orders, maximum uint256, explicit revert and
fresh state.73mutations per pipeline+3inventory=149negative controls have fixed
asserted counts. All old complete report fields/184calls are identical; new
cumulative196calls. Gas100m/steps5m, compiler/fork pins, all prior fixtures and
expected observations remain unchanged. Compiler/EVM evidence is separate from
kernel/source/target/Yul admission proof. Scope is canonical supported parts;
no promotion or exclusion change. Exact signatures/axioms, commands/exits,
reviews/resources/head/artifacts are saved under
`/workspace/vy2-evidence/static-uint/HANDOFF.md` and cumulative handoff.

Full work/backfill accounting remains Y04/Y05/Y06 and A/B PARTIAL, concrete
Y09.02 BLOCKED. Still open: whole-store/path/hash/dynamic/dirty ownership,
generic dynamic/struct/all-fields and whole-memory writeback/realization,
shared-zero/interior/pointer/nested source semantics, allocator provenance/
refinement, V10/V11 agreement instances and actual VY1/source/compiler/calculus/
final joint closure. Owner MemOK/World/ContractWorld/Bridge are available and
reused, not substitutes for missing actual Yul adequacy. Oversized MemOK/no-
ordinary-Placement counterexample retains its EXACT earlier boundary; no new
capacity premise/refusal or reachable-allocation claim. Goal remains blocked
unchanged, get_goal absent, no transition/new VM/thread/model/worker merge/push;
YQ1–YQ7 preserved; questions=[]. Original3988manifest/prior artifacts and every
failed attempt, including initial mixed fixture/proofs/lock probes, are retained.

Final selected-word validation: per-file/focused50jobs/fullwrapper1042default+
262suitejobs/131matchedannotations exit0; actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs exit0. Scoped1188declarations/652theorem reports standard axioms only.
Layers233core/0elaboratorreach,1057reachable/0orphan, trust1072sources/246sites/
0findings, strict491automatic/61budgeted/11refuted/0pending pass. Global docs
ACTUAL exit1 with same48exact-base findings/zero delta; markdown base1/head1/new0.
Both independent final reviews clear. Complete external196calls preserve ALL
preceding fields, and all81/14/33/55/89/103/121/157/149negative suites pass.


## Dynamic full-width array writeback (2026-10-31)

New [DynamicUintMemory](../../Solidity/Yul/Views/DynamicUintMemory.lean) decodes
actual Source.Data dynamic uint256 arrays from their length word and all element
words, without a decoder/fuel/size cap. Constructive encode/decode and exact raw
re-encode laws preserve every byte, including residual/tail bytes. Fixed-length
writeback keeps its header guard and proves unchanged WHOLE heap/state identity,
valid same-shape Placement and actual all-initial-H owner MemOK. Real found data
and Placement derive length/window bounds. Full-width words retain all256bits.

[RetainedDynamicUint](../../Solidity/Yul/Views/RetainedDynamicUint.lean) adds a
separate size-changing component, using the existing actual RetainedAllocation
lineage and original full owned extent. It constructs the new current shape,
valid Placement and retained history; proves types/next/boundedness, unrelated
cells, original address/free choices, other shapes and full other-region bytes.
No capacity is inferred from gaps/free pointers; shrink does not erase tails.
Compatibility with fixed-length successes is proved. None is unsupported
preparation, never Yul refusal/no-op/deallocation or a compiler verdict. Owner
representations, Placement and all full memory obligation signatures are intact.

[Controls](../../Solidity/Yul/Views/DynamicUintControls.lean) inhabit actual
heterogeneous source heaps with two full-width arrays, unrelated bytes and a
static array containing two aliases to the first dynamic array. They cover
unchanged identity,3→0→3, retained maximum-word tails/nonzero gaps, old fixed API
negative regrowth and beyond-original-extent preparation, actual all-H MemOK,
real Source.lengthOf/readLoc/nested reads, actual evalE alias lengths at EVERY
horizon≥2 and exact timeouts at0/1, and disjoint source/physical update orders.
wordList_inside/disjoint_commute and dynamicUint_disjoint_commute prove whole
physical equality from actual separated windows, not assumed result equality.

[DynamicUint.sol](../../tests/yul-views/DynamicUint.sol) and its lane-owned
strict adapter compare complete34-word ABI envelopes for9ordered calls per
pinned legacy/viaIR pipeline: initial, all-element changes/maxword, zero shrink,
partial/full retained-tail regrowth, both disjoint orders, revert and fresh call.
The153negative controls discriminate missing/reordered calls, lengths/pointers/
words/aliases/tails/free/zero/other objects, bytes and deployment failures.
All preceding report fields and196calls remain EXACTLY identical; cumulative214.
Compiler/EVM evidence is separate from kernel/source/compiler/Yul correctness.
Evidence and exact signatures/axioms/gates/reviews are versioned at
`/workspace/vy2-evidence/dynamic-uint/`; prior4243hashes verified before writes.

Queue remains Y04/Y05/Y06 and BackfillA/B PARTIAL, concreteY09.02 BLOCKED.
Dynamic full-width supported preparation is not universal aggregate/writeback,
whole memory/dirty/narrow/shared-zero/interior/dynamic ownership, full-store/path/
hash, allocator provenance/refinement, V10/V11 agreement instances or actual
VY1/source/compiler/calculus/joint closure. Existing owner MemOK/World/Bridge
interfaces are available and reused. Original oversized-MemOK counterexample
boundary, YQ1–YQ7 and exclusions are unchanged. Persistent goal remains BLOCKED
unchanged; no goal tool exposed, no transition made. No new semantic question.

Dynamic checkpoint validation: focused53jobs/fullwrapper1045default+262suite/
131matchedannotations exit0. Actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort
2jobs exit0. Scoped1271declarations/701theorems have standard axioms only.
Layers236core/0elaboratorreach,1060reachable/0orphans, trust1075sources/246sites/
0findings, strict491automatic/61budgeted/11refuted/0pending pass. Docs ACTUAL
exit1 with same48missing/37ambiguous exact-base references; zero-delta comparison
passes, markdownbase1/head1/new0. Both independent read-only reviews found no
confirmed defects; corrected an adapter comment about local defaults. Initial
proof/summary-parser failures retained (parser fixes only, not altered verdicts).
Code commit f765cde0344fb4199b439e96b157aff6307c04d1. Serial-j1/12GiB/no-swap/
writer lock/caches retained; no owner representation or budget change. Versioned
handoff records exact signatures, resources and gates.


## Simultaneous heterogeneous struct writeback (2026-10-31)

[AggregateWriteback](../../Solidity/Yul/Views/AggregateWriteback.lean) decodes
ALL declared members of an actual Source.DataList using parameter-only List
recursion. Supported member types are canonical bool, full-width uint256 and
actual owned memory references. OrdinaryMemberType is an explicit component
type list, NOT a residual Yul fragment or substitute for original coverage.
uintValueOfWord_inverse covers every actual typed uint256, not only literals.
Pointer decoding reuses real typed child candidates; members remain pointer
words and children separate, including aliases. No opaque inverse/preservation/
read law is accepted as a structure field. No second source state/AST/IR exists.

Derived laws: per-member actual RefOK/MemoryElement; typed DataListOK, actual
MemoryFields/read representation from successful decoding; encode/decode with
real supported types, owned source images and candidate coverage; exact whole
ByteView re-encoding; actual ObjectWord reads; declared-size/full other-region/
reserved-word preservation. Actual Heap.write constructs output Placement
with original address/shape/free and preserves every other cell/types/next/
boundedness. Unchanged WHOLE heap/state identity is proved. structStateWriteback
runs actual Source.heapPut and returns its ENTIRE Except/state result. Its
MemOK theorem preserves EVERY original H on both successes AND source errors,
using all actual owner EMOK/HeapShaped/HeapInner conjuncts. Missing/wrong-type
source roots are not silently turned into successful writes.

[Controls](../../Solidity/Yul/Views/AggregateWritebackControls.lean) change a
real Box bool/maximum uint/two bytes pointers simultaneously; both pointers
retarget a real nonUTF8 string child, retain the dynamic-array member, and actual
Source.readLoc→bytesOfRV observes both aliases at EVERY horizon. A following
actual child Heap.write is seen by both aliases and preserves all-H MemOK.
Controls include unchanged whole state, same-shape Placement, all other roots,
nonzero gaps/free/zero words, invalid129/missing-owned candidates and canonical
bool2 preparation failure, plus actual Source.heapPut type-error/state behavior.
None means unsupported preparation; no original dirty/bool/shared-zero/interior
case is silently cleaned, refused at admission or assigned no-op semantics.

[AggregateWriteback.sol](../../tests/yul-views/AggregateWriteback.sol) imports
the unchanged MixedHeap fixture and independently checks complete42-word ABI
observations for6orderedcalls per pinned legacy/viaIR pipeline: initial, all
fields, reversed order, shared-child update, revert and fresh call.153strict
mutations discriminate pointer/header/offset/bool/maxword/child/alias/other/
padding/free/zero/bytes/failure/deployment/inventory changes. All previous214
calls and report fields are EXACTLY identical; cumulative226. External finite
compiler/EVM evidence remains separate from source/Yul/compiler correspondence.
Exact receipts/signatures/axioms/reviews/gates are versioned under
`/workspace/vy2-evidence/aggregate-writeback/`.

Full Y04/Y05/Y06 and BackfillA/B remain PARTIAL; actual Y09.02 BLOCKED. Generic
all-member supported structs improve component coverage, not universal narrow/
dirty/shared-zero/interior/pointer/dynamic object/whole memory/storage/hash/
allocator provenance/refinement/source/compiler/calculus closure or concrete
V10/V11 agreement instances. Actual available owner interfaces are reused;
missing Yul producer adequacy is not assumed. Original oversized-MemOK boundary,
YQ1–YQ7, exclusions and full obligation signatures are unchanged. Goal BLOCKED
unchanged; no goal tool/transition or new semantic question. Initial proof and
default-heartbeat timeout logs are retained; compositional proofs replace the
expensive image reduction without raising any budget.

Aggregate checkpoint validation: per-file/focused55jobs/fullwrapper1047default+
262suite/131matchedannotations exit0; scoped1325declarations/740theorem reports
standard axioms only. Layers238core/0elaboratorreach,1062reachable/0orphan, trust
1077sources/246sites/0findings and strict491automatic/61budgeted/11refuted/0pending
pass. Real Lean4.24.0/Lake5.0.0-src+797c613 and passing2jobKeySort recorded in the
preceding same-runtime checkpoint. Docs ACTUAL exit1 with identical48missing+
37ambiguous base references; zero delta comparison passes; markdownbase1/head1/
new0. Both independent read-only reviews clear. Complete226orderedcalls retain
every preceding field; all old suites plus153aggregate negatives pass.

The1.528s exploratory proof/reference overlap is explicitly recorded in evidence,
not a claim of perfectly serial exploration; failed proof log retained. No
concurrent Lean processes/MCP/server, resource event or budget increase; final
affected/full/scoped gates serial. Writer lock/12GiB/no-swap/caches preserved.
This checkpoint follows committed dynamic-array validation1c85e49f68b71d0548c4f6bd91b7a710269f0e8a;
final full SHA/patch/bundle/resources/checksums are in the versioned handoff.


## Canonical array element families (2026-10-31)

[MemberArray](../../Solidity/Yul/Views/MemberArray.lean) constructs fixed and
header-preserving dynamic actual Source.Data arrays using the existing typed
canonical bool/fulluint256/owned-reference decoder. Recursion is on ordinary
Nat length, no size/fuel cap; all elements are actual Source.Val, references
remain pointer cells to separately owned children. OrdinaryMemberType retains
its explicit limited component meaning, not a renamed Yul coverage fragment.
Successful decoding DERIVES MemoryElement for every index, DataOK/Inner, real
MemoryObjectWords; candidate coverage/supported type and actual encoded words
prove decode-after-encode. Arbitrary input raw reencoding is exact whole
ByteView identity. Valid actual found data/Placement derives length/word-window
bounds, output same-shape Placement, unrelated cells/types/next/boundedness and
other real regions/reserved/free/zero preservation. No inverse/read/safety/
placement result is an assumed structure field.

Heap writeback preserves unchanged WHOLE heap; state wrapper runs complete
actual Source.heapPut Except/state, including wrong-type errors and EVERY
initial H owner MemOK. Unchanged whole state includes .ok() and exact initial
state, with real found/read/coverage/support premises. Fixed header guards,
existing codecs/owner/full obligation signatures are unchanged. Dirty2 bool,
narrow/noncanonical/shared-zero/interior/missing-candidate cases remain original
unfinished semantics; None is unsupported preparation, never Yul refusal/no-op/
deallocation or compiler behavior. Header-preserving arrays do not yet discharge
retained-capacity size changes or universal dynamic/whole-memory writeback.

[Controls](../../Solidity/Yul/Views/MemberArrayControls.lean) inhabit actual bool
and pointer-array heaps: all bool elements change; both static array references
retarget the same real dynamicuint child; nested length/read behavior and child
update are observed through both aliases; generic source/physical disjoint orders
agree. Dynamic bytes-pointer array retargets both children to a real nonUTF8
string; actual Source readLoc→bytesOfRV works at every horizon. Original H,
unchanged whole state, source type-error/state, missing candidates/dirty bool,
unrelated roots/nonzero gaps/reserved/free/zero are controlled.

[MemberArrays.sol](../../tests/yul-views/MemberArrays.sol) independently checks
all58ABIwords/bytes for6orderedcalls per pinned legacy/viaIR pipeline: initial,
all fixed/dynamic bool/pointer updates, reverse order, shared-child update,
revert/fresh. Explicit1792pool precedes96+64static defaults; observed free2080
before output allocation.183strict negative controls discriminate every old
observation index, aliases/pointers/headers/bytes/status/deployment/inventory.
All previous226calls/report fields are identical; cumulative238. External finite
observations are separate from kernel/source/compiler/allocator adequacy.
Initial malformed33byte fixture literal and proof/default-heartbeat failures are
retained; corrected implementation/proof structure, not expected observations
or budgets. Versioned evidence `/workspace/vy2-evidence/member-arrays/`.

Full Y04/Y05/Y06 and both backfills PARTIAL; actual Y09.02 and final producer/
compiler/calculus closure remain open. Canonical array components do not solve
whole-store/path/hash/dirty ownership, universal memory/shared-zero/interior/
allocator provenance/refinement or concrete V10/V11 agreement instances. Actual
owner MemOK/World/Bridge available and reused; missing Yul adequacy not assumed.
Original oversized-MemOK boundary and YQ1–YQ7/exclusions preserved. Original
persistent goal BLOCKED unchanged, get_goal absent, no goal transition or new
semantic decision. All4444previous hashes verified before writes; prior versions
and raw failures preserved. Future checks are strictly serialized.

Array-family checkpoint gates: per-file/focused56jobs/fullwrapper1049default+
262suite/131annotations exit0. Actual Lean4.24.0/Lake5.0.0-src+797c613, KeySort
2jobs exit0. Scoped1407declarations/783theorems standard axioms only. Trust/
strict/layers/orphans and all prior negative suites plus183new controls pass.
Global docs ACTUAL exit1, identical48missing/37ambiguous base lines; zero delta
comparison passes, markdownbase1/head1/new0. Both independent read-only reviews
clear. Serial-j1/12GiB/no-swap/writer lock/monitor/caches retained; no overlap
in this recovery. Complete commands/signatures/reviews/resources/committed SHA
and artifacts are in the versioned handoff. Full original queue remains open.


## Retained array element-family resizing (2026-10-31)

[RetainedMemberArray](../../Solidity/Yul/Views/RetainedMemberArray.lean) adds
actual dynamic bool/u256/owned-reference array resizing bounded ONLY by a real
original Placement extent and existing typed RetainedAllocation lineage.
Current shape always describes new data; original ownership/history preserves
full original region separation, addresses/free and all other shapes. Successful
decode DERIVES actual values/typed Heap.write/output Placement+history, not an
opaque result or inverse premise. Other cells/types/next/boundedness, actual
whole-state unchanged, raw ByteView reencode/tails/other original regions are
proved. Full Source.heapPut Except/state and EVERY original H owner MemOK cover
success and actual source errors. The prior header-preserving guard is intact.

[Controls](../../Solidity/Yul/Views/RetainedMemberControls.lean) inhabit actual
reference2→0→2 and bool3→0→3 allocated arrays. Raw header changes retain live/dead
tails; decoded pointers use concrete owned child candidates, real source alias
reads see both retained children at every horizon. Initial and all-H owner
MemOK, exact current0shape/history, bool aliases/length/member reads, old guard
negative regrowth, beyond-original-capacity preparation, actual source type
error, disjoint typed/physical writes and reserved/free/zero/nonzero gap controls
are retained. decodeArrayMembers_of_decodes composes actual successful per-cell
decoder evaluations; controls derive these from concrete raw loads and typed
candidates, never assume a generic inverse/read agreement.

[RetainedMemberArrays.sol](../../tests/yul-views/RetainedMemberArrays.sol) checks
complete58ABIword envelopes/bytes for8orderedcalls per pinned pipeline: initial,
zero shrink, full/partial/reversed regrowth, retargeted shared-child update,
revert/fresh. Raw tail words remain observed even when logical length0; guarded
absent logical elements yield explicitly expected0, never dropped observations.
195strict negative controls discriminate headers/tails/aliases/deployment/order/
bytes/status. All preceding238reportfields/calls exactly identical; total254.
Initial viaIR fixture extra alias locals caused a32byte spill/shift; raw broken
source/report preserved. Simplified locals rather than changing independently
specified expected words2080FMP/pointers or budgets. This finite fixture does
NOT prove nondeterministic allocation refinement or erase pipeline differences.
Kernel source bool aliases and separate real child aliases remain explicit.

Retained snapshot provenance is NOT a reachable allocator theorem. Shared-zero/
interior/beyond-proven-extent/noncanonical/dirty/narrow/generic nested ownership
and universal memory/store/source/compiler/calculus closure remain original
unfinished obligations. None is unsupported preparation, not a Yul refusal,
no-op, deallocation or compiler outcome. Existing owner/full obligation/API
signatures, oversized-MemOK boundary and YQ1–YQ7 preserved. Y04/Y05/Y06 and A/B
PARTIAL; concreteY09.02 BLOCKED. Goal BLOCKED unchanged; no get_goal tool/goal
transition/worker integration or new semantic question. Evidence
`/workspace/vy2-evidence/retained-members/` retains proofs/reviews/raw failures/
exact signatures/gates and full queue handoff. This follows array checkpoint
`ebcdee018556551d87c20a82140282e262f7bed0`, not whole-lane completion.

Retained-family final checks: per-file/focused58jobs/fullwrapper1051default+
262suite/131annotations exit0; scoped1468declarations/815theorem reports standard
axioms only. Layers242core/0elaboratorreach,1066reachable/0orphan, trust1081sources/
246sites/0findings; strict491automatic/61budgeted/11refuted/0pending pass. Full
254calls and all preceding suites plus183/195new negatives pass, prior report
fields exactly identical. Docs ACTUAL exit1 same48missing/37ambiguous base lines,
zero delta separatePASS; markdownbase1/head1/new0. Both independent read-only
reviews clear. Real Lean4.24.0/Lake5.0.0-src+797c613 and2jobKeySort0 saved in
preceding same-runtime checkpoint. All current heavy job intervals serial;
previous1.528s recovery overlap preserved. Writer lock/hard12GiB/no-swap/caches/
OS+aggregateRSS monitoring retained. Full original lane and both backfills stay
unfinished; no goal transition, premise/exclusion or owner representation change.


## Canonical scalar memory extension (2026-10-31)

Before proof design, pinned solc0.8.38 Osaka legacy/viaIR
[MemoryScalarWords](../../tests/yul-views/MemoryScalarWords.sol) checks signed8/24
min/-1/0/max, uint8/24, address/contract/enum, bytes3/31. Signed MEMORY words are
sign extended, uint/address/enum right aligned, bytesN LEFT aligned; matches
actual Source.Val.word and differs from storage bytesN payload alignment. Full
16word ABI/status/deployment audit retained under
`/workspace/vy2-evidence/memory-scalars/`. Initial address-checksum syntax error
preserved; source literal syntax fixed, independently specified values unchanged.

[MemoryScalarCodec](../../Solidity/Yul/Views/MemoryScalarCodec.lean) constructs
actual typed canonical scalar candidates, validates their ENTIRE Source.Val.word
against input, proves decode-after-encode and exact successful raw reencode,
RefOK for every H. Signed/unsigned integer widths, bool, address/contract,
bytesN1..32 and enum supported. bytesN inversion uses actual byte/numeric laws,
not storage alignment. Enum completeness has REAL premise enumSize≤2^256 for an
arbitrary Layout (valid solc enums are≤256); otherwise word wrapping is not
injective. This component premise does not weaken any whole obligation or
introduce an admission exclusion. Fixed-point/UDVT/function cases remain open.

[CanonicalMemory](../../Solidity/Yul/Views/CanonicalMemory.lean) is a parallel
adapter: original decodeMemoryMember/OrdinaryMemberType and ALL original array/
struct/retained APIs/controls remain byte-identical. New concrete canonical
decoder falls back to existing owned-pointer decoder; soundness and supported
roundtrip DERIVE actual MemoryElement/RefOK. Callback Nat/List folds have no
assumed law fields; proved equality when instantiated with legacy decoder.
Canonical instances prove actual typed arrays/DataList from successful reads;
full heap/state unchanged, output Placement/other cells/types/next/boundedness,
raw byte reencode and complete Source.heapPut Except/state/every original H
owner MemOK use existing concrete machinery. No untyped AST/state/IR, opaque
inverse/read/safety/Placement premise or proof budget increase.

[CanonicalRetained](../../Solidity/Yul/Views/CanonicalRetained.lean) connects
those actual decoded scalar arrays to original typed retained allocation history
and actual Heap.write/heapPut, exact current shape/output Placement/history,
other cells/types/next/boundedness, all-initial-H MemOK including source errors,
encode/unchanged laws. Capacity is real original extent; existing raw/reserved/
region/placement laws reused. No gap/free inferred ownership or allocator theorem.
[Controls](../../Solidity/Yul/Views/MemoryScalarControls.lean) inhabit actual
ScalarBox/array/bytes heaps and owner MemOK: signed/address/bytes3 struct updates,
all-element signed arrays/aliases/disjoint orders, unchanged whole state, bytes3
2→0→2 retained tails/shape/history/alias length reads, source error, narrow dirty/
wrong bytesN alignment controls, enum/contract/u24 boundaries and old pointer
behavior. None is unsupported CANONICAL preparation, never Yul refusal/no-op/
deallocation/cleaning semantics. Dirty high bits remain original open transport.

[ScalarMemoryOps](../../tests/yul-views/ScalarMemoryOps.sol) independently checks
complete38word envelopes for fixed/dynamic scalar arrays, structs, both update
orders, zero/partial/full regrowth, repeated reads/other roots/padding/free/zero,
revert/fresh in both pipelines.The external fixture repeats reads through b, not an independent alias; actual
two-alias evidence above is kernel-side.99scalar audit +155operation strict negatives;
all preceding254report fields/calls identical, cumulative282. Compiler/EVM finite
observations remain separate from kernel/source/compiler/allocator adequacy.
Original oversized-MemOK boundary, YQ1–YQ7/exclusions and whole obligations
unchanged. Y04/Y05/Y06 and both backfills PARTIAL, concreteY09.02 BLOCKED;
whole-store/memory/dirty/sharedzero/interior/allocator/V10/V11/source/compiler/
calculus/joint closure still mandatory. Goal BLOCKED unchanged, get_goal absent,
no goal transition/new semantic question/owner edit or unpublished integration.

Canonical scalar checkpoint validation: per-file/focused68jobs/fullwrapper
1055default+262suite/131annotations exit0; actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs0. Scoped1598declarations/880theorem reports standard axioms only.
Strict/trust/layers/orphans and all old suites plus99/155new negatives pass.
Docs ACTUAL exit1, identical48missing/37ambiguous base lines, zero delta separate
PASS; markdownbase1/head1/new0. Independent finder clear; skeptic scope finding
fixed (external repeats b reads, real alias evidence kernel-side) and follow-up
clear. Source/owner/old decoder APIs unchanged, no budgets raised. Serial-j1/
12GiB/no-swap/writer lock/monitor/caches maintained. Versioned handoff records
exact signatures/resources/commands/committed SHA. Full original lane remains open.


## Canonical compatibility and genuine aliases (2026-10-31)

[CanonicalCompatibility](../../Solidity/Yul/Views/CanonicalCompatibility.lean)
proves exact ALL-RAW-input equality of the canonical extension with old component
APIs on their original supported types. Member, array/field folds, heap/state
struct/array operations and retained heap/state operations preserve the entire
Option/Except/state result: dirty bool None, missing/invalid owned pointers,
header/capacity failures and source errors are not dropped. Real old type/field
support premises remain explicit, no new fragment predicate or full Yul coverage
claim. No old definition or signature changed.

[CanonicalAliasControls](../../Solidity/Yul/Views/CanonicalAliasControls.lean)
executes real Source.locals→indexLoc→readLoc paths through both typed aliases,
including after canonical bytes3 array shrink/regrowth and a subsequent typed
update seen by BOTH aliases; all original H owner MemOK follows actual heapPut.
An index through the other alias after length0 yields the exact source
Panic(.index) bytes/state. Old bool/u256/pointer all-raw equality, capacity/None
and full-result examples instantiate the generic compatibility proofs.

[ScalarMemoryAlias](../../tests/yul-views/ScalarMemoryAlias.sol) now supplies
GENUINE independent aliases (unlike the prior fixture's repeated b reads):
write through b and observe a/b for bytes3, signed8 and address arrays, retained
header shrink/regrowth/tails and further aliased update, explicit revert,
nonempty Panic(0x32) and fresh-call observation. Complete12word success ABIs and
all36Panic bytes/status are compared in order for7calls/pipeline;137strict
mutations include wrong panic code/data/status, alias bit/sign/alignment,
missing/reordered vectors/deployment and attempted storage writes. All preceding
282reportfields/calls exactly identical; cumulative296.

The shared replayBytecode empty-revert scalar profile is unchanged. A narrow
exact-fixture adapter uses public machine/observation/creationObservation and
existing storage-write observer, preserving original100m gas/5m step limits,
transaction resets, log/unknown-host refusal and all return bytes. Zero attempted
storage writes are checked after deployment/every call. This is NOT a new
general host harness, VY5 composition takeover or source/compiler adequacy.
Compiler/runtime pins, prior fixture/goldens/budgets and all original obligations
are intact. Initial skeptic evidence-scope finding remains recorded as fixed;
this separate regression adds actual external alias evidence without relabeling
old repeated reads. Y04/Y05/Y06 and both backfills PARTIAL; Y09.02 concrete and
full allocator/source/compiler/calculus/joint closure remain open. Goal BLOCKED
unchanged; no new semantic decision, unpublished integration or owner rewrite.
Versioned evidence `/workspace/vy2-evidence/canonical-aliases/`.

Final validation: focused70jobs/full1057default+262TestSuite/131annotations exit0;1623public declarations/899scoped theorem reports standard axioms only. All16negative suites pass, including137genuine-alias mutations. Separate finder/skeptic read-only reviews clear; old evidence-scope finding remains fixed/recorded. Global docs exit1 remains identical48missing/37ambiguous exact-base debt, zero delta separately; not a global pass. Serial12GiB/no-swap checks, caches and raw failures retained. No original full obligation or goal status changed.


## Joint ordinary-memory writeback (2026-10-31)

Original Y05/BackfillA/B productive continuation from
`fb44149b4c168c7a15b655a5ffd02e556d0100a0`; frozen base
`0b078cefaf7daad79007b87b72df64eb6936420f`, same assigned branch/VM.
Approved YQ1–YQ7 in solidity-scope remain binding. No owner representation,
Placement/Source.Val.word/whole-obligation/API/codec/guard/expected old fixture
change, new exclusion, producer integration, goal transition or raised budget.
Full goal stays BLOCKED, get_goal read absent; no other goal tool used.

MemoryTransport constructs intrinsic image and actual MixedHeapEntry transport
through same-type Heap.write: written contents replaced, unchanged children keep
transported images, IDs/types/addresses and owned coverage preserved. Pointer,
canonical member/field/array decoder equality holds for ALL raw inputs, including
None. This proves candidate stability, not an assumed inverse/read agreement.
GateG0/history inspected: no Source/state/AST change, parameter-only ordinary
recursion and constructor eliminators. Modest additional checking cost warned;
per-file cost recorded, recursion/heartbeat failures retained then fixed by
factoring small explicit source/header equalities, never raising limits.

JointMemory decodes simultaneous declared fields and fixed/header-preserving
dynamic array contents from ONE snapshot and executes actual two heapPut binds.
General two-order COMPLETE result equality requires both actual original root
types and distinct roots; no equality claimed for arbitrary failure order.
Every original H owner MemOK is preserved even on complete first/second source
errors; second type error retains successful caller-prefix state. Unchanged
WHOLE state, cells/types/next/boundedness/locals/world preservation derived from
real owner operations. JointPlacement constructs both output placements and
refreshes typed images/coverage/pointers after EACH write, with concrete
struct/array instance. JointSequential equates snapshot joint writeback to the
second concrete decoder after the actual first write/refreshed candidates,
including None and complete second error results. Actual first found/decode and
intrinsic constructor-image premises are explicit; no opaque result law.

JointRetained derives original-capacity changes from actual RetainedAllocation,
constructing current exact shape, full-region bounds/separation and two-write
lineage. JointRetainedControls inhabits scalar struct+bytes3 array2→0→2 with
full refreshed coverage, real alias locals/indexLoc/readLoc/Panic and every-H
MemOK, plus actual initial owner MemOK. JointMemoryControls combines changed
heterogeneous pointer fields and pointer-array elements, both orders, true
array aliases and shared children at every horizon, unrelated roots, type-error
prefix and nonzero padding/gaps/reserved/free/zero preservation. JointRaw uses
actual successful typed decode plus real Placement length bound to prove exact
joint raw re-encoding over the original snapshot/residual bytes, no cleaning.
All exact signatures/premises and scoped axioms saved in joint-memory/ evidence.

Pinned solc0.8.38/Osaka legacy+viaIR JointMemory fixture uses actual x/y struct
and c/d array aliases, retargets pointer words to a real other array, updates all
array words, unchanged other objects, maxword/sign/bytesN alignment,
shrink/regrow, Panic0x32/empty revert/fresh calls. Initial legacy stack-too-deep
failure retained; fixture-only local reduction preserved golden values/settings.
Skeptic CONFIRMED evidence gap: initial four cases had identical outputs and no
actual calldata receipts. Fixed by34word outputs,777/888 nonshrink sentinels
versus actual0/0shrink, returned order/regrow flags and exact actual calldata
recorded/validated against pinned selectors. Six first-four swaps/every-call
calldata corruption plus raw-root/pointer/tail/revert/storage/deployment/budget
mutations guard the fix. Pre-review source/report/raw failures retained; finder
acknowledged missing the first gap; independent follow-ups clear. No old296
report fields or fixture expectations changed. Cumulative310 ordered calls;
external tests are NOT kernel/source/compiler/whole-memory adequacy.

Entire original Y04/Y05/Y06 and BackfillA/B PARTIAL, concrete Y09.02 BLOCKED.
Whole-store/path/hash/dynamic/dirty ownership, universal memory/writeback,
shared-zero/interior/dirty/narrow/unhandled representations, reachable allocator
provenance/refinement, exact V10/V11 agreements and actual VY1/source/compiler/
calculus/notation/printer/final-joint closure remain open. Existing owner MemOK,
World/ContractWorld/memory-call/Bridge are AVAILABLE, not Yul adequacy. Original
oversized-MemOK counterexample retains ONLY its documented unqualified ordinary
Placement boundary; no reachable allocator/resource/profile choice inferred.
Queues NOT exhausted; no new human semantic question established. Checkpoint
patch/bundle/handoff/gates/raw resources/checksums versioned at absolute
`/workspace/vy2-evidence/joint-memory/`; cumulative artifacts retain old versions.

Final checkpoint gates: focused79jobs, full wrapper1065default/262TestSuite/131annotations exit0; actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs0;1718public declarations/961scoped theorem reports standard axioms only. All17negative suites pass including213joint mutations. Layers/orphans/trust/strict/markdown0. Initial five lane short-path doc findings fixed; final globaldocs STILL exit1 same48missing/37ambiguous exact-base debt, zero delta separatePASS. Raw proof, recursion/heartbeat, compiler stack, test-inventory and doc failures retained. Separate final finder/skeptic reviews clear after confirmed external gap fix; full original queue/goal unchanged.


## Finite owned memory inventory (2026-11-01)

Continuation from `30e61d054c2096e949f0a4a7274a6efc7283703a`, frozen base
`0b078cefaf7daad79007b87b72df64eb6936420f`, same assigned branch/VM.
YQ1–YQ7 decision record remains binding. No owner representation/API/Placement/
Source.Val.word/MemoryWritebackObligations/MemoryLayoutObligations/PreservesMemOK
change, source-branch integration, exclusion/admission promotion, goal action,
new VM/thread/model or budget increase. get_goal and Lean MCP read/diagnostics
remain unexposed; goal BLOCKED unchanged, bounded per-fileCLI fallback used.

InventoryObject/ObjectLaws reuse actual canonical scalar/pointer member and
field folds plus unbounded byte/string codecs. Actual indexed Source.Data,
HasMemoryShape and constructor MemoryImage are returned; no inverse/read/safety
law fields. Static array word bound is derived from actual Placement and found
data; dynamic length is the real 256bit header. No new arbitrary heap/list/node/
fuel/size/address cap. Ordinary type syntax elimination and parameter recursion
respect G0; Source.State speed history21067a47 inspected and modest additional
checking cost warned. No indexed AST/state refactor or duplicate untyped IR.

OwnedInventory traverses an ACTUAL finite owned candidate list, retaining every
candidate/duplicate and its exact declared type. CoversMixedHeap establishes
completeness; each owned ID is proved below actual Heap.next using boundedness.
Concrete codecs construct decoded typed data/shape/images and guard ONLY real
original allocated extent. Structural recursion executes real Source.heapPut;
InventoryRealization separately packages existing actual Heap/Placement/images
and constructive retained lineage, never an alternative source semantics.
Every step derives type/next preservation, refreshed written contents/unchanged
children, coverage, pointer metadata/decoder stability, placement addresses/free
and exact current-vs-original shapes. Complete snapshot-to-current-sequential
preparation/source agreement includes None; no entrypoint assumes generic
inverse/read/decoder agreement. The internal induction agreement premise is
instantiated by actual refresh facts at every step. None is unsupported
preparation with NO source/Yul outcome, no-op, rollback or deallocation meaning.

Generic real source execution preserves complete first/late error results and
every ORIGINAL H owner MemOK from actual DataOK, supplied concretely by images
for decoded inventories. Well-owned actual inventory has no root-type error;
wrong-current-source controls exercise the general source program separately.
Distinct actual IDs justify arbitrary List.Perm source-result equality; pointer
aliases are not distinct objects. Repeated SAME decoded candidate is a real
idempotent shared-object write, no silent filtering; differing same-root values
are NOT claimed commutative. Whole-state unchanged is proved from actual complete
supported types, constructor images and unchanged image reads, not assumed
inverse laws. InventoryView derives final complete mixed raw view, exact every
word/byte read and reserved/free/zero/gap/padding/tail preservation. Canonical
success reencoding equals the ENTIRE original snapshot. No dirty-bit cleanup
or canonical-only language admission is inferred.

Controls use the actual six-root heterogeneous heap (bytes, raw string, static
scalar array, struct with aliased pointer fields, dynamic reference array and
unrelated bytes). They prove actual decoder success, all-H MemOK with an
inhabited original typing, whole unchanged state, reverse permutation, exact
Source.locals/indexLoc/readLoc/bytes reads through two aliases at every horizon,
Panic, current shape/history/coverage, complete multi-root zero→regrowth,
repeated candidate and actual late type error retaining successful caller prefix.
Initial direct normalization hit200000heartbeat/recursion limits; raw failures
retained and observations factored through explicit typed heap/source-run laws,
no raised budget or weakened expected result. Generic modules check in under a
second; concrete six-root decoder controls about22s, aliases about11s, retained
controls about20s, recorded separately from cached full gates.

Pinned solc0.8.38/Osaka both pipelines OwnedInventory fixture varies n3/n4/n0,
traverses nested struct/array roots and true shared-child aliases, both orders,
retained shrink/regrowth, unrelated cells/free/zero, full dynamic ABI/calldata,
late Panic0x32, explicit empty revert and fresh calls. Reverse order correctly
changes last SHARED child write; no false same-root commutation expectation.
Independent goldens include ALL7words/root and full ABI envelope;241consistent
word+byte corruptions plus order/calldata/alias/pointer/root/count/coverage/
revert/status/deployment/attempted-storage/budget mutants,677total, pass. All
preceding310report fields/expected verdicts remain EXACTLY identical;330ordered
calls total. Compiler/archive/fork/lock pins and100m gas/5m step unchanged.
These finite EVM observations are NOT kernel source/compiler/whole-memory or
reachable-allocator correspondence; compiler default shared-zero intermediates
are not claimed represented merely because fixture execution succeeds.

Y04/Y05/Y06 and BackfillA/B remain PARTIAL; concrete Y09.02 BLOCKED. Universal
store/path/hash/dynamic/dirty ownership, memory/writeback/shared-zero/interior/
unhandled scalar/nested representations, reachable allocation/provenance/
refinement, exact V10/V11 agreements and actual VY1/source/compiler/calculus/
notation/printer/final-joint closure remain original open obligations. Actual
owner MemOK/World/ContractWorld/memory-call/Bridge are AVAILABLE, not substitutes
for missing Yul adequacy. Original oversized-MemOK counterexample boundary is
unchanged; no semantic/resource/profile exclusion or capacity premise approved
by inference. Queues NOT exhausted; no new semantic question established.
Versioned exact signatures/gates/reviews/resources/patch/bundle/handoff/checksums:
`/workspace/vy2-evidence/owned-inventory/`; cumulative original artifacts and all
prior receipts/raw failures/manifests preserved.

Final checkpoint gates: per-file and focused93jobs0; full policywrapper1079default/262TestSuite/131annotations0. Actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs0.1857public declarations/1059scoped theorem reports standard axioms only. All18negative suites pass, including677inventory mutations. Layers/orphans/trust/strict/markdown0. Globaldocs ACTUAL exit1 SAME48missing/37ambiguous exact-base debt, zero delta separate0, not a global pass. Independent finder/skeptic final reviews clear after restored observations and inhabited retained/error controls. Raw failed proofs/limits retained; original whole-lane obligations/blocked goal unchanged.


## Computed ordinary heap inventory (2026-11-01)

Parent checkpoint `c99b868a5e6159637f167cdd3afb777d5110868d`; pinned base and assigned branch unchanged. This is original Y05/Backfill A/B preparation, not full Y05 or lane completion. YQ1–YQ7 remain authoritative. No owner representation, existing guard, Placement, full obligation or manifest admission change.

`HeapImagePreparation` constructs actual intrinsic MemoryImage from actual Data/Val and a valid Placement. Scalar words are exactly Val.word; pointer words require actual heap type and compatible memShape. Fin traversal uses actual array length; fields recurse over declared member types. Array and byte bounds derive from real found data/Placement, with no new size/fuel/root cap. No supplied inverse/read/safety/coverage/output-law fields or alternative state.

`HeapEnumeration` scans exactly `List.range h.next`. Every successful entry retains exact ID/type/data/found lookup and computed image. Separate lists account for sparse holes and occupied unsupported cells. `HeapEnumerationLaws` proves exact partition/exclusivity, unique IDs, complete successful coverage, and exact nonempty whole-preparation error lists. Unsupported occupied cells are never silently skipped and promoted to coverage. The actual bounded heap rules out occupied cells beyond next. Constructor completeness is proved against the existing MemoryImage relation, in both directions of the no-unsupported characterization.

`HeapPreparationMemOK.ownerMemOK_prepares_inventory` is the stronger source entrypoint: actual owner MemOK for any initial H, valid current Placement and explicit per-declared-type InventoryTypeSupported suffice to construct preparation. It derives bare fields/elements and typed child ownership from actual owner invariants. No image inventory, image-existence, completeness, inverse or safety law is supplied by the caller. This canonical family premise does not redefine whole-memory support or language admission.

`EnumeratedMemory` connects the generated inventory to real Source.heapPut/Heap.write, actual dependent Placement/image/coverage/retained-history refresh after every write, all-initial-H MemOK and snapshot/sequential agreement including None. Successful views reencode the complete raw snapshot, preserving residual/padding/tail/gaps; reserved/free/zero preservation retains its real ReservedOK premise. The direct ownerMemory_unchanged theorem derives whole source-state identity without manually supplied entries or coverage. Full success/error Source results remain those of the existing concrete runner; valid owned same-typed inventories succeed, while the original generic first/late error controls remain intact. Outer enumeration errors and inner decoder None mean unsupported preparation, never Yul/source refusal, no-op, cleaning, rollback or deallocation.

Controls compute six mixed roots, duplicate child aliases, whole-state identity, changed bytes/raw strings/scalars/struct/references, current zero-shape preparation, empty and sparse heaps, exact missing/unsupported IDs, wrong/missing child/inline-reference and dirty-snapshot/real-extent boundaries. A sparse actual source heap reconstructs inventories for shrink-to-zero then in-capacity regrowth, retains original64-byte ownership/current0/4-byte shapes and raw tail, and proves both bytes/string aliases at every horizon plus every-H owner MemOK. Existing six-root/order/late-error/regrowth controls and every expected external observation remain unchanged. An exploratory six-root monolithic regrowth proof reached original heartbeat/recursion limits; raw failures and source snapshot are retained, and the inhabited sparse composition factors the proof without increasing budgets. It does not claim a new six-root regrowth equality that has not been proved.

Read-only finder and skeptic reviews are required; final receipts and exact signatures/axioms/gates live in `/workspace/vy2-evidence/heap-enumeration`. Kernel proofs and unchanged pinned330-call external regression evidence are separate; enumeration itself is preparation over actual typed source cells, not new compiler behavior or correspondence.

Queue accounting: Y04, Y05, Y06 and Backfill A/B remain partial; concrete Y09.02 is blocked. Whole store/path/hash/dynamic ownership and residual-journal closure, dirty/shared-zero/interior and remaining memory representations, reachable allocator/provenance/refinement, concrete V10/V11 agreement instances and actual VY1/source/compiler/calculus notation/printer/final joint closure remain open. Actual owner MemOK/World/ContractWorld/memory-call/Bridge are available, not assembly adequacy. The oversized owner-MemOK/no-ordinary-Placement counterexample keeps its exact earlier boundary. No new semantic question or authorization is inferred. The original goal remains BLOCKED unchanged; get_goal read is not exposed, no goal action was taken.

Final computed-inventory gates: Lean4.24.0/Lake5.0.0-src+797c613; required KeySort2jobs exit0; focused103jobs and full1089default/262TestSuite/131annotations exit0; 1963 declaration signatures and1132 standard-only theorem axiom reports. All330 ordered pinned legacy/viaIR calls and every prior report field remain byte-identical; all18 negative suites pass. Structural/strict/trust/Markdown checks pass. Global docs remains actual exit1 with exact-base48missing/37ambiguous findings and zero delta separately. Separate final read-only finder/skeptic reviews clear. No raised proof/resource/test budget. One1.111-second diagnostic-launcher overlap is retained in resource evidence; the existing private Lean flock serialized Lean execution, and later launchers were explicitly awaited. All prior failures/caches/artifacts preserved.


## Packed-slot complement journaling (2026-11-01)

Parent checkpoint dde021c447f60bde1ca81392d055c5b1cba17717, assigned branch and frozen base unchanged. This advances original Y04/Backfill A/B. It does not complete Y04 or the full lane, promote admission, change YQ1–YQ7 or replace HashedLayout/compiler owners. Source/World/Storage/Heap, existing ResidualKey/registeredOwnership/journal APIs, canonical codecs/guards and original whole obligations remain unchanged. Gate G0/history21067a47 reviewed before edits; new constructor/parameter-only operations are outside owner state representation. Per-file timings and raw failures retained.

PackedResidualMask derives byte ownership directly from actual typed ScalarPath slot/Field offset/width registrations. All8 bits of each registered byte are owned. Remaining bytes/high bits may be arbitrary/nonzero; dirty bits inside canonical owned fields are NOT silently cleaned or reclassified as residual. Universal Field.lowByte_of_find proves exact owned-byte equality from payload equality. PackedResidualCodec.finiteEncode_fromComplement proves fields plus computed complement reconstruct the ENTIRE supplied SlotView, with real finiteSeparated and actual read-view premises. packedStoreWriteback decodes ALL fields, preserves the input actual Storage and administrative none/explicit-default distinction on unchanged values, and returns the exact same snapshot's complement. Successful decode gives full reencoding and unselected-path preservation, not just equal projections.

PackedResidualPlan selects ALL registrations at the requested slot, validates concrete canonical fields before producing one plan, and couples the actual Source.Op with its complementary residual word from the SAME bank/account/slot/raw request. Generated metadata identity is proved; there is no supplied inverse/view/read/safety/output theorem field. Optional executable separation validation catches overlapping fields/duplicate paths; it is not evidence of HashedLayout agreement. Wrong supplied layout controls discriminate ownership rather than pretend that agreement is inferred. Existing whole-slot ownership remains unchanged.

The new complement carrier instantiates the EXISTING ResidualCompanion/ResidualJournal in a separate carrier domain: complementCarrierOwnership=False permits carrier keys, NOT a statement that source slots are unowned. Carrier words are never treated as full raw-slot residuals. PackedComplementValid is the concrete representation invariant: actual registered owned bytes are zero in BOTH live carrier words and saved undo entries. Initialization and every paired plan derive masking. Undo/rollback/commit/endTx preservation is proved using real journals. This does not weaken registeredOwnership or allow an old registered-owned slot to be an unowned ResidualKey under that old ownership contract. No second untyped Source state or IR is introduced.

PackedResidualWorld derives persistent/transient actual typed source views and FULL raw slot readback from actual writes plus journaled complement, with real separation. Nonselected paths and their administrative cells, other banks/accounts/complement keys are preserved. Exact whole administrative identity belongs only to the pure unchanged preparation theorem; changed selected values use the actual typed writeback. runPackedSlots derives both operation lists from the SAME validated plans; actual paired undo marks restore caller prefix after child rollback, and successful child entries remain undoable by enclosing rollback. Repeated same-slot order is observably distinguished. EndTx keeps persistent logical fields AND complement; transient logical defaults and complement become zero, with the REAL individual-codec default-zero premise discharged by concrete registrations. No assumed full-view law is substituted for this composition.

PackedResidualSource and PackedResidualFrame call ACTUAL Source.applyOp. Static writes (even unchanged) yield its exact empty revert and preserve source/residual. Nonstatic success updates source and residual together; actual locals/heap/events/logs are preserved and every original H owner MemOK follows conjunct-by-conjunct. preparePackedFrame binds the account to F.this, and packedFrameWrite? composes that computed preparation with source execution, mask preservation and full raw persistent/transient reencoding, without a source/result adequacy premise. Unsupported canonical preparation None is NOT a Source/Yul error/no-op/deallocation. Static invalid canonical input still has no preparation result; this is not full admitted assembly semantics.

PackedResidualWriteback separately supplies whole-companion unchanged ADMINISTRATIVE writeback identity when logical fields AND complement match. Actual source execution remains packedSourceStep/packedFrameWrite?: it still appends undo history and refuses static writes. PackedResidualWritebackSound proves full raw reencoding for BOTH the identity and changed preparation branches. No claim equates the pure identity shortcut with an actual journaled source operation.

Inhabited controls use same-slot bool/u16/bytes3/address (26owned bytes,6arbitrary padding bytes), an unselected next-slot path, typed unwritten and explicit-default stores, nonzero complement, persistent/transient same numeric slot7, distinct-account isolation, repeated/reversed writes, caller-prefix child rollback/outer rollback after child commit and complete transaction reset. Malformed bool2 is None only at preparation; overlap, wrong-layout, owned-byte boundary and erased-padding controls discriminate failures. Actual nonempty Source.Env mixed-field registrations now instantiate Source.applyOp success/static refusal, current-frame binding, every-H AND inhabited MemOK, exact field/raw readback, source caller/child sequence and concrete rollback. Earlier empty-registry applyOp controls remain supplementary, not the sole source witness.

External fixture PackedResidual.sol adds18 ordered calls per pinned pipeline with independently specified complete13word ABI/status/state/calldata receipts: slot7persistent/transient isolation, rawA/rawB order, retained a5/5a padding under typed writes, typed values/bytes alignment, inner/outer revert, fresh-call transient reset, unauthorized child revert, dirty raw bool2/logicaltrue and staticcall failure. All330 previous report fields/observations remain exact; new total366calls. This is finite compiler/EVM evidence, NOT Lean compiler/whole-store/target correspondence. Compiler/source/archive/fork pins and100m-gas/5mstep budgets stay unchanged. New fixture's initial legacy stack-too-deep failure is retained; equivalent13word fixed-array ABI return construction fixed it without optimizer/budget changes.

Independent read-only finder/skeptic reviews found one confirmed strict-validator gap: paired hash/size deletions could pass equality. Fixed mandatory64hex hashes/positive safe runtime size and paired-deletion mutants. Expected encoded-call metadata was replaced/supplemented by actual calldata receipts from exact bytes sent to public machine.call. Shared scripts/evm-reference and VY5 harness untouched. Final new suite503negative controls includes394 consistent rawABI/value word mutations; old18suites retained. Initial proof/fixture/checker evidence is preserved, no raised budgets/new axioms/sorry/admit. Final review and gate receipts/signatures/resources live under /workspace/vy2-evidence/packed-residual.

Full queue: Y04/Y05/Y06 and Backfill A/B PARTIAL; actual Y09.02 blocked. Remaining whole store/path/hash/dynamic ownership, changes to ownership domains, dirty/noncanonical/shared-zero/interior/remaining representations, universal memory/writeback, reachable allocator provenance/refinement, actual V10/V11 agreements, Y06 source bindings, VY1 source/assembly MemOK and notation/printer/compiler/calculus/final joint closure remain mandatory. Available owner MemOK/World/ContractWorld/memory-call/Bridge and published general memory-loop compiler components are not Yul adequacy. The user-audited published master5f6a75b6038371a3917dbe08b660d5f2d1207c58 still lacks Yul exports; no unpublished branch imported. Original goal BLOCKED unchanged; get_goal read absent/no goal action. No genuine new human semantic decision; questions=[]. Historical global docs failure and prior resource/launcher events remain retained, zero delta is not a global pass.

Final packed-complement validation: Lean4.24.0/Lake5.0.0-src+797c613; required KeySort2jobs exit0; focused62jobs and full1101default/262TestSuite/131annotations exit0;2156declaration signatures/1238standard-only theorem axiom reports. All366ordered external calls pass, every prior330call report field unchanged,19negative suites including503new mutations pass. Layer/orphan/strict/trust/Markdown gates exit0. Global docs remains ACTUAL exit1 with48missing/37ambiguous findings, byte-identical pinned-base logSHA25601fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a; zero delta separate. Final finder/skeptic reviews clear after hash/calldata and wording fixes. The generic nonzero transient complement control starts from an arbitrary within-transaction snapshot, not a proved fresh-transaction reachable initial state; external fresh-call/reset observations are separate. All raw failures and previous artifacts retained; no budget raised.


## Computed word-layout registrations (2026-11-01)

Checkpoint only: Y04/Backfill A/B remain partial; Y05/Y06 remain partial and
concrete Y09.02 remains blocked. The original goal stays blocked unchanged.
Authorization remains the recorded YQ1–YQ7 decisions, not the old proposal's
pending wording. No admission/manifest change or compiler-owner replacement.

New lane modules LocatedHash, FullWordLayout, LocatedRegistration,
LocatedSeparation, LocatedInventory, LocatedControls and LocatedSource derive
canonical uint256 registrations from actual E.rootTy, storage structFields,
E.cellTy and Storage.STy.locate. FullWordLayout's checker follows the actual
finite owner tree with no new fuel bound. Mapping keys must be actual bounded
uint256 values; translation uses Source.wordBytes and an exact Source.keyStep
control. Wrong root/type/path, structural dynamic bounds and oversized keys
produce precise preparation errors, never Yul refusal/no-op semantics.

fixedLayoutHash is Fixed.keccak applied to the actual Storage.encode byte list.
Byte bounds and UInt8 roundtrip are proved, as is lossless preimage encoding
under the owner's real Pre.Words condition. The real-keccak specialization
uses the actual Fixed keccak contract; region transport retains EXACT existing
per-run RegionsDisjoint, never global hash injectivity. Nested mapping/array
controls prove the exact two hash inputs and their word bounds.

Computed finite inventories derive slots, locations, u256 defaults, codec and
width obligations. Owner locate_bounded/located_word_inj derive bounds and
separation, using tree.Fits, root size, L/R bounds, original per-run region
conditions and executable distinct-path/distinct-symbolic-location checks.
Different source paths alone do not imply distinct slots. The finite obligation
adapter uses Classical.choose only to label an existing mapped registration;
actual preparation/registration/writeback remain executable. No inverse/read/
result-view/adequacy law is supplied by a caller. Existing finite codec laws
then derive encode/writeback identity with the exact original store retained.

The actual nonempty Source.Env contains a struct root, full-word mapping,
dynamic array and nested mapping/array. Inhabited checked controls cover those
paths, malformed inputs and aliases. Computed mapping registration feeds the
existing real typed source operations and complementary journal: value777,
full raw readback, caller-prefix child rollback, successful child followed by
outer rollback, persistent survival and transient reset are kernel proved.
The existing Source.keyStep provenance is exact; these ExecState controls do
not prove a new Source.eval binding/runtime-index correspondence. The transient
companion uses the same registry deliberately, not an inferred Solidity
transient declaration-layout agreement.

Boundary: HashedLayout is WORD GRANULARITY, not Solidity packed layout. Root0
and the supplied owner layout are explicit inputs, not inferred arbitrary
contract declaration placement. Dynamic locate uses the owner's lmax structural
bound, not the current logical array length. Whole HashedLayout/path ownership,
solc packed inference, narrow/dirty owned fields, bytes/string keys, arbitrary
hash collisions/dynamic ownership and concrete V10 agreement remain open.
No existing codec, source/heap/world definition, whole-obligation signature,
expected result or proof/test/resource budget changed.

Separate read-only finder and skeptic reviews found no defects, including the
finite-inventory delta; neither ran Lean/server/build/tests. Their scope limits
above are retained. Focused/per-file/full/import/scoped-signature and standard
axiom results, exact commands/exits and raw intermediate failures are packaged
under /workspace/vy2-evidence/hashed-registrations. Prior 366 ordered pinned
legacy/viaIR calls and all report fields are retained unchanged; no new external
source/compiler correspondence is inferred from kernel preparation controls.

Remaining full queue: Y04 whole derived persistent/transient/path/hash/dynamic
ownership/writeback; Y05 all memory/dirty/shared-zero/interior forms and reachable
allocation provenance/refinement plus actual assembly MemOK; Y06 input/environment
source bindings; Y09.02 actual syntax/calculus/notation/printers/source/compiler
composition and final joint gates. Existing owner MemOK/World/ContractWorld/
memory-call/Bridge components are available, but not Yul adequacy. Concrete
VY1/source and V10/V11/compiler agreements remain unresolved. Both backfill
queues remain partial. A finite canonical instance does not complete the lane.


Validation for computed registrations: per-file focused checks and
`lake -f lakefile.vy2.toml build Solidity.Yul.Views.LocatedSource` exit0;
`./run-lean.sh` exit0 (1108 default/262 TestSuite jobs,131 annotations);
Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs exit0. Scoped audit checks
2239 declarations/1282 theorem signatures:1236 standard-axiom reports and46
axiom-free theorems. Strict/trust/layers/orphans and19 existing negative suites
exit0. Actual global docs exit1 is byte-identical to pinned-base debt
(48missing/37ambiguous); separate markdown delta is zero. Exact raw commands,
exits, failed proof/build attempts and final resource report are in the
versioned HANDOFF. No new external observations replace the retained366 calls.


### General checked-path hash provenance

After source checkpoint ef13e7a08ad8ecb73ec2945ef3aaa3e0464bbcd3,
LocatedProvenance derives every preimage's Pre.Words from successful actual
sourceLayoutSteps translation, actual Storage.STy.locate and bounded modulo-word
parent slots. Structural induction covers struct/static-array offsets, dynamic
arrays and nested mappings. No word-bound witness is supplied by callers.
LocatedInventoryPreimages_words lifts this to arbitrary finite checked
inventories; locatedInventory_regions_bytes transports EXACT original per-run
regions directly to the actual Fixed byte inputs. locatedInventoryByteObligations
then constructs the same finite source-storage instance without a supplied
location/slot/default/inverse/readback law or extra preimage premise.
Independent read-only finder/skeptic reviews again found no findings. Remaining
full queue, root0/word-granular/canonical boundaries and blocked goal are unchanged.
Final commands/exits/signatures/resources and both source heads are recorded in
the versioned evidence handoff. These are two reviewed preparation checkpoints,
not final Y04 or full assignment completion.


General-provenance final gates: focused78jobs/full wrapper1109default+262suite/
131annotations exit0; scoped2249declarations/1289theorems (1241 standard-only
reports,48axiom-free), no new axiom. Trust1139sources/0findings, strict/layers/
orphans/markdown delta pass. Actual global docs remains the retained exit1;
no unchanged failed gate rerun. Raw provenance elimination failures are retained.


## Declaration-derived packed registrations (2026-11-01)

Original Y04/Backfill A/B preparation, not lane completion. YQ1–YQ7 stay
approved as recorded in solidity-scope.md; no admission/exclusion/owner contract
change. Source checkpoint parent:00293e3a0d368d5ffa055385f4c7887a8e45b040.

DeclarationScalars selects existing exact StorageWidth/ScalarCodec instances
from ACTUAL source scalar types: bool, signed/unsigned integers, fixed-point,
address/contract, bytesN, valid enum and external function. Unsupported UDVT/
reference preparation is not a Yul refusal/cleaning/no-op. No assumed inverse
is supplied: existing concrete codecs prove their own inverses. DeclarationPacking
traverses actual E.rootTy/structFields in declaration order and checks E.cellTy
at every generated Source.SPath. All widths, low-byte offsets and slot advances
use the EXISTING packedStart planner; no duplicate packing algorithm or untyped
IR/state. Each slot has its real nonwrapping word bound, derived by checked
arithmetic. Root base is an explicit input, not inferred global contract layout.

packDeclarationFields_spec universally derives start/end bounds, increasing
actual field paths and finiteSeparated from successful computation, not caller
slot/offset/default/inverse/readback/separation laws. Exact-full-slot and spill
follow planner progression; rounding yields the struct end/next start boundary.
No word-granular HashedLayout definition is changed or reinterpreted as packing.

The actual nonempty struct/root control contains bool/u16/bytes3/address,
u256, u8+bytes31 and a trailing u16. Computed coordinates are
(0,0,1),(0,1,2),(0,3,3),(0,6,20),(1,0,32),(2,0,1),(2,1,31),(3,0,2).
The first slot leaves six residual bytes; u256 spills; u8+bytes31 exactly fill
a slot; final byte98 rounds to slot4. The computed registry feeds existing
actual Source.applyOp/current-frame preparation, every-H actual owner MemOK,
complete raw reencoding and paired source/complement journals. Controls cover
unselected paths, separate accounts/banks, nonzero padding, actual static empty
revert, caller-prefix rollback, committed child/enclosing rollback and endTx
persistent survival/transient reset. Pure unchanged preparation preserves whole
administrative storage, including empty versus explicit-default cells; it is
not journaled execution. An initial new transient-cell control incorrectly
expected explicit false: corrected to the actual retained None/default-read
behavior, with the failing raw check retained. Existing observations unchanged.

DeclarationBoundary derives a supported fixed scalar array plus inner scalar
struct component directly from actual outer/inner declarations and automatically
selected codecs. It reuses repeatedMembers/endByte/roundSlot and existing
component disjoint/encode/decode laws. The inhabited uint24[12]/inner mixed
struct at base4 has live array end166, next start192, inner live end218 and
aggregate end224. Skipped array padding is preserved. IMPORTANT: these are
Nat ByteView component laws with actual typed DataLists, not a whole nested
Source.Data/Storage writeback instance, arbitrary root assignment or physical
nonwrapping theorem. Physical serialization still needs its real range premises.
Zero-length/other aggregate shapes remain original preparation work; this
supported shape is not a language/profile limit or arbitrary traversal cap.

New external DeclarationPacking.sol controls independently compare exact solc
0.8.38/Osaka legacy/viaIR struct/array field offsets and complete eight-word
observations, including spills, bytes31/storage alignment, array padding,
distinct forward/reverse values, unrelated marker, full Error("packing") bytes
and fresh read after revert. Fourteen new ordered calls bring the cumulative
report to380. ALL preceding366 call fields remain byte-for-byte unchanged;
reference-preservation.json proves the old field-byte prefix and values match.
This is finite external evidence, separate from universal kernel/source/compiler
adequacy. Gas100m/steps5m/optimizer disabled/runs200/fork/compiler/source/archive
pins unchanged. The first new fixture checksum-literal compile failure is
retained. No host errors/logs are silently accepted by the public reference APIs.

Independent read-only finder and skeptic reviews found no source defect and
both found missing mutation-count guards in the new external test. FIXED with
108mutants per pipeline,96complete-word mutants and219total negatives, all
asserted. Final reviews clear; no reviewer Lean/server/build/tests or edits.
All old19negative suites remain required. Raw attempts, exact commands/exits,
resources, signatures and cumulative artifacts: /workspace/vy2-evidence/declaration-packing.

Full queue stays open: Y04 whole storage/path/hash/dynamic ownership and final
packing/V10 agreement; Y05 universal memory/shared-zero/interior/dirty forms,
reachable allocation refinement and actual assembly MemOK; Y06 actual source
input/environment bindings; Y09.02 actual VY1/source calculus/notation/printers/
compiler/joint closure; concrete V10/V11 agreements and both backfills. Existing
owner MemOK/World/ContractWorld/memory-call/Bridge are available, not Yul adequacy.
Original goal remains BLOCKED unchanged; get_goal read unavailable, no mutation.
No new human semantic decision established. Full lane is not complete.


Final declaration checkpoint gates: Lean4.24.0/Lake5.0.0-src+797c613;
KeySort2jobs exit0; focused70jobs and full wrapper1116default/262TestSuite/
131annotations exit0. Scoped2323declarations/1326theorems:1278 standard-only
reports and48axiom-free. Strict/trust(1146sources,0findings)/layers/orphans/
markdown delta exit0. All19old negative suites and the new219mutation suite
pass; actual cumulative report380calls, old366field bytes unchanged. Global
docs ACTUAL exit1,48missing/37ambiguous, byte-identical exact-base debt; zero
delta is separate. Failed recursion/decidability/type and fixture checksum
attempts remain saved; proofs repaired structurally without budget changes.


### Inhabited declaration-state MemOK follow-up

After source checkpoint d0dc0b421c46e103b32b851e42be8d451ff285ad,
decl_initial_MemOK explicitly supplies every actual owner empty-state conjunct;
decl_written_inhabited_MemOK instantiates the every-H source-step theorem with
that concrete initial heap typing. No renamed predicate, assumed desired result,
additional safety premise or owner-state change. Both read-only reviews clear.
Affected/per-file/full/signature checks in the same versioned handoff cover the
final source tree; original full-lane/goal blockers are unchanged.


MemOK follow-up final gates: per-file/focused/full wrapper exit0; unchanged
1116default/262TestSuite/131annotations. Scoped2325declarations/1328theorems:
1280standard-only reports,48axiom-free. Trust0findings. Existing pinned external
observations/tests unchanged by the proof-only addition. Original full-lane
obligations and global docs exit1 remain open, not promoted to passing.


## Nested declared source registry and writeback (2026-11-01)

Original Y04/Backfill A/B continuation, full lane PARTIAL and original goal
BLOCKED unchanged. Parent:a6f77acb3048e20d05b88836f81d59e9017516b8. YQ1–YQ7
remain approved as recorded earlier; no admission/manifest/exclusion change.

The existing declaration packing implementation is factored into ONE
packDeclarationPaths traversal accepting an actual Source.SPath constructor.
The old packDeclarationFields API/guards and theorem signature are preserved
as its exact flat specialization. No second planner/source state/untyped IR.
The generic path proof derives monotone live spans, finite separation under a
proved concrete path-constructor injection, and actual declared index bounds.
An exact ordered path-list theorem proves no omitted/extra elements. Extent
proofs identify the computed end with existing PackedMembers/repeatedMembers,
not a caller-supplied equality. Every output field constructs its actual Word
slot with its original nonwrapping check; rounded total physical extent is
proved within the real word-coordinate domain, without an arbitrary size cap.

NestedDeclaration consumes the existing actual DeclaredArrayStruct lookup
certificate. prepareNestedDeclaration builds ALL paths [.field0,.index i] for
the actual fixed count and [.field1,.field j] for actual ordered inner fields,
checking E.cellTy at every path and choosing existing exact scalar codecs.
Their explicit Source path constructors are proved injective/cross-distinct.
Alignment, separation, index coverage, exact component ends and physical bounds
are derived from actual successful operations. Source storage references remain
references; no nested Source.Data contents are relabeled or owner types changed.

NestedDeclarationSource derives canonical actual Source.Storage snapshot
writeback, full raw-map reencoding with exact computed complement, unchanged
WHOLE administrative store and unselected-path preservation. No assumed final
inverse/view/readback/safety law fields. Actual frame preparation/applyOp uses
the computed registry with derived separation; successful persistent/transient
steps reconstruct the entire supplied word. Every ORIGINAL H owner MemOK is
transported across complete real source results, retaining static refusal.
Canonical preparation failure remains None/error of preparation, NOT a Yul
refusal/no-op/deallocation/cleaning semantics. Dirty owned bytes remain open.

The inhabited uint24[12]/mixed inner struct now yields16 ACTUAL typed source
registrations at base4:10array elements in slot4,2in slot5 and bool/u16/bytes3/
address in slot6. Exact owned masks are30/6/26bytes, preserving the2/26/6
nonzero residual bytes. Array live end166, inner start192, inner live end218,
rounded end224 agree with prior derived components. Controls cover exact paths,
wrong-path/overflow/invalid canonical bool preparation and exclusion of index12
from the generated registry. The physical bound is real, not a decoder cap.

Three actual Source.applyOp/frame steps populate the nested cells and exact
complement from the SAME raw words. NestedDeclarationComposition proves equality
of the COMPLETE Source.Storage result with pure snapshot writeback, using real
finiteWriteback append/input laws and actual selected-slot source steps. Full
map reencoding follows by rewriting that equality, not matching a few return
words or assuming source adequacy. Actual Source.readLoc keeps the parent as a
storRef; two real storage-reference locals use indexLoc/readLoc to observe1/12.
The actual fixed-array index12 path gives the original36byte Panic(0x32).
Initial/postwrite/alias/child actual owner MemOK are inhabited; every-H transport
is retained. This is finite supported source-path closure, not a Yul compiler
or whole arbitrary heap/store theorem.

Paired actual source/residual sequence equality underlies caller-prefix child
rollback and committed-child/enclosing rollback. Controls preserve unselected
paths, other accounts/banks, exact raw words, arbitrary residual padding and
persistent state across endTx. Full transient raw reset derives actual zero
defaults from an executable individual-codec check, not a supplied view law.
Repeated same-slot orders have distinguishable final words. Transient reuse
of this registry is an explicit companion adapter, not independently inferred
Solidity transient declarations/layout.

One first journal proof exceeded the UNCHANGED200000 heartbeat limit while
comparing expanded worlds. Raw failure retained. Universal actual-op bank and
complement preservation plus exact request equations replace that reduction;
repaired generic/closure checks are small, with no raised heartbeat/recursion/
fuel/node/test/resource budget. G0/history reviewed and performance warning
issued before factoring; old Source/Heap/World/compiler definitions unchanged.
No indexed source value/state is matched through a new untyped representation.

Both independent read-only finder/skeptic source and reset-delta reviews clear;
no reviewer Lean/server/build/tests/edits. Existing380 ordered pinned legacy/
viaIR observations are retained BYTE IDENTICALLY at audited reportSHA256
214fff4f136569a4b3350212fd66e577269573674b2ab05ebe5a0a9a39200a54.
No new external expectations/calls/profile changes. The new kernel slot4/5/6
constants are independently compared to both existing writeForward receipts;
this remains finite external evidence, not source/compiler correspondence.
All prior observations, pins, gas100million/steps5million and old negative
inventories remain binding. Exact commands/exits, raw failures, signatures,
resources/reviews/artifacts: /workspace/vy2-evidence/nested-declarations.

Full queue remains unfinished: arbitrary-root/global packing and dynamic/hash/
dirty ownership/writeback, broader memory/shared-zero/interior representations,
reachable allocation provenance/refinement, concrete V10/V11 agreements, Y06
actual source/environment inputs and VY1/source/assembly MemOK/Y09.02 notation/
printers/calculus/compiler/joint closure. Existing owner MemOK/World/Bridge are
available, not Yul adequacy. Supported positive fixed-array/scalar-struct shape
is not a language exclusion or recursive traversal cap. Whole nested Source.Data
realization and arbitrary declarations remain open. Questions=[]; no new human
semantic choice established. Both original backfill queues remain partial.


### Actual paired physical-map closure

NestedDeclarationFinal additionally proves equality of the ENTIRE actual
persistent residual map (all Word coordinates) with the concrete pure snapshot
complement, using actual paired sequence, validated requests and real key writes.
Combined with complete Source.Storage equality, actual source PLUS actual
journal reconstructs the whole supplied physical snapshot, including untouched
slots. No residual/result-view/adequacy equality is supplied by a caller.
Computed individual defaults of all16registrations also yield full transient
raw reset at EVERY physical word. This remains the supported canonical nested
component; arbitrary declaration/dirty/dynamic/compiler closure is unfinished.
Raw metavariable-search heartbeat failures retained; explicit residual/key
normalization repairs them under the unchanged200000 limit. Prior scoped-audit
namespace-collector failure is preserved separately and repaired by tracking
actual namespaces, not by dropping declarations.


Final nested gates: actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs
exit0; focused82jobs/full wrapper1128default/262TestSuite/131annotations exit0.
Scoped2450declarations/1415theorems: 1365standard-only reports,
50axiom-free. Strict/trust(1158sources,0findings)/layers/orphans/markdown delta
pass. All20unchanged reference negative suites pass. Global docs remains ACTUAL
exit1 with byte-identical48missing/37ambiguous exact-base debt; zero delta is
separate. Namespace-audit and proof-budget failures retained, repaired gates
recorded separately. Original full-lane/goal obligations stay open.


## Recursive fixed declaration paths (2026-11-01)

Original Y04/Backfill A/B continuation; full assignment PARTIAL and original
goal BLOCKED unchanged. Parent271736f27513a98a9c11e863ca9c121bf4fb3e76,
assigned branch and pinned base unchanged. YQ1–YQ7 remain approved as recorded
in [scope](../solidity-scope.md); no admission/exclusion/owner API changes.

[FixedDeclaration](../../Solidity/Yul/Views/FixedDeclaration.lean) is a finite
intrinsic certificate indexed by ACTUAL Source.STy. Scalar support comes from
existing declarationScalar?, array counts are the actual positive declared
counts, and each struct carries actual E.structFields equality in declaration
order. These are finite metadata/constructor facts, not supplied final layout,
separation/default/inverse/readback/safety laws. Cyclic metadata is not claimed
total. No depth/fuel/node/address cap or duplicate state/AST is introduced.
Root assignment remains supplied explicitly and checked against E.rootTy.

[FixedDeclarationPack](../../Solidity/Yul/Views/FixedDeclarationPack.lean)
reuses ONE packDeclarationPaths scalar traversal and existing roundSlot at
aggregate entry AND exit. Actual E.cellTy guards and Word slot bounds remain.
[Spec](../../Solidity/Yul/Views/FixedDeclarationSpec.lean),
[Paths](../../Solidity/Yul/Views/FixedDeclarationPaths.lean) and
[Extent](../../Solidity/Yul/Views/FixedDeclarationExtent.lean) prove by structural
recursion: successful traversal has finiteSeparated registrations, exact full
leaf-path enumeration without duplicates/skips, subtree path injection and
cross-separation, scalar spans and exact recursive endByte. Checked Word base
implies nonwrapping end at most2^256*32. Source.pathTy is structural and does
not check fixed-array index bounds: declared enumeration DOES, rather than
changing owner semantics. Original flat/nested APIs and guards remain intact.

[Checked/source](../../Solidity/Yul/Views/FixedDeclarationSource.lean) stores
actual computation evidence and derives canonical whole Source.Storage
writeback, unchanged administrative none-versus-explicit-default identity,
selected view/unselected-cell preservation and full snapshot reencoding with
complement from that SAME raw snapshot. Actual source frame/applyOp wrappers
retain full error/static behavior, bank/raw-word reconstruction and
EVERY-original-H owner MemOK transport. None is unsupported preparation, never
Yul refusal/no-op/cleaning/deallocation. Dirty OWNED payloads remain open.

Inhabited actual declarations Inner[2][2] plus uint128[3] at base8 produce
11typed leaves: four bool/u16 struct slots8–11, exact-full two-element slot12,
spill slot13, end14*32. Controls cover three aggregate levels, nonzero29-byte
struct padding and16-byte trailing padding, complete/no-extra paths, malformed
root/cell/overflow and canonical-bool failure. Actual six-source-operation
storage is proved equal to pure complete snapshot decoding. Actual paired
residual map equality holds at EVERY Word, including untouched slots; together
these give complete physical snapshot reconstruction from the ACTUAL source
and journal. Actual two local storRef aliases use indexLoc/readLoc to observe
1/3 and preserve exact Panic0x32 on index3. Initial/postwrite/alias/child owner
MemOK are inhabited; every-H transport, caller-prefix rollback,
committed-child/enclosing rollback, same-slot order, distinct account/bank
isolation, actual static empty-revert and full transient raw reset are proved.
Transient companion reuse is not inferred Solidity transient declaration layout.

Pinned solc0.8.38 commit1835d247/Osaka legacy and viaIR fixture
[RecursiveDeclaration.sol](../../tests/yul-views/RecursiveDeclaration.sol)
independently checks declared nested coordinates, six COMPLETE raw words,
three untouched sentinels, all11logical scalar reads, both distinct write
orders, complete100-byte Error("recursive") and postfailure fresh read.
New14ordered calls and369mutation controls pass; all previous380call/report
fields remain preserved. These are finite external observations, not universal
kernel source/compiler/target correspondence. Original100m gas/5m steps and
all proof/heartbeat/recursion budgets remain unchanged.

G0 and git speed history reviewed before additions; owner representations and
whole obligation signatures unchanged. Performance warning issued. Initial
whole-tree concrete normalization hit default200000heartbeats; smaller witness
alone did not repair it. Raw failures retained. Constant eliminator motive plus
explicit checked component-success equations repair proof structure; final
inhabited control checks in3.5s without any budget increase or native oracle.
Failed unsupported primitive-recursor codegen probe also retained. All heavy
checks serial/private lock/12GiB-no-swap with aggregateRSS/OS/disk monitoring;
prior launcher overlaps remain historical and are not erased.

Evidence:/workspace/vy2-evidence/recursive-fixed. Final review/gate receipts and
exact exported head are recorded in its HANDOFF.md and cumulative root
HANDOFF.md/SHA256SUMS after checks. Global docs remains actual exit1 with
byte-identical pinned-base48missing/37ambiguous findings; zero delta is
separate evidence, never a global pass.

Full queue remains open: Y04 whole persistent/transient storage/path/hash/
dynamic/global-root ownership and dirty-bit semantics; Y05 broader dirty/
shared-zero/interior forms, whole memory/writeback/allocator provenance and
refinement; Y06 actual source inputs/environment bindings; concrete V10/V11
agreements; VY1 source execution/assembly MemOK; Y09.02 actual calculus,
notation/printers/compiler/final joint closure. Backfill A/B remain partial.
Available owner MemOK/World/ContractWorld/memory-call/Bridge are not assembly
adequacy. Published5f6a75b6038371a3917dbe08b660d5f2d1207c58 still lacks Yul
exports per audited immutable tree; no unpublished producer work imported.
No genuine new semantic decision; questions=[]. get_goal read/Lean MCP absent;
no goal action taken and original goal remains BLOCKED unchanged.


Final recursive checkpoint gates: actual Lean4.24.0/Lake5.0.0-src+797c613;
KeySort2jobs exit0; policy full wrapper1142default/262TestSuite/131annotations
exit0. All2636public declaration signatures/1516theorem reports checked:
1465standard-only and51axiom-free, none missing/unexpected. All21negative suites
pass, including new369controls. Strict491automatic/61budgeted/11refuted/0pending,
trust1172sources/246inventoried sites/0findings, layers333core/0elaborator reach,
orphans1157reachable/0orphans, markdown base1/current1/new0. Exact global docs
exit1 remains byte-identical48missing/37ambiguous; baseline comparison delta0
is separate. Independent final finder and skeptic reviews both clear, neither
ran Lean/server/build/tests or edited. Final cumulative394call report preserves
ALL380preceding fields; SHA256
043cad397185d2d97bb423febfe43c89c130548933351902e873d3cd8a9464cb.
Full original goal and queues remain unfinished/BLOCKED as stated above.


### Actual metadata typing follow-up

Reviewed recursive checkpoint committed atb9dc71b38fa597d7b38a0ee4f2f32ce4c6dcf9ea; immutable export under
/workspace/vy2-evidence/recursive-fixed/checkpoint-1 preserves its patch/bundle,
handoff and checksums before this follow-up. Continued original Backfill A/B:
[FixedDeclarationTyping](../../Solidity/Yul/Views/FixedDeclarationTyping.lean)
proves every generated leaf has actual E.pathTy.isSome from the checked root
and recursive declaration metadata. The field induction's exact indexed type
premise is DERIVED from actual E.structFields in the struct branch; no external
read/inverse/final-safety premise is added. This is path EXISTENCE; exact actual
bool/u16/u128 types are inhabited separately, not an overclaimed universal
exact-type equality. Owner structural index typing remains unchanged, while
registry bounds follow declared enumeration. Missing-field pathTy=None and
cellTy tuple fallback cannot enter the computed leaf inventory. Wrong-root
scalar-vs-struct guard is also retained. Old APIs/signatures unchanged; no new
compiler behavior, so394external report fields remain unchanged. Independent
finder/skeptic read-only follow-up reviews both clear; neither ran checks or
edited. Final affected/import/signature gates recorded in versioned receipts.
Full original obligations and blocked goal remain unchanged.


Final metadata follow-up: per-file Typing/TypingControls and focused98jobs exit0;
policy wrapper1144default/262TestSuite/131annotations exit0. Complete final
signature/axiom audit2647declarations/1526theorems:
1475standard-only/51axiom-free, none missing/unexpected. Final strict,
trust1174sources/246sites/0findings, layers335core/0elaborator reach,
orphans1159reachable/0orphans and markdown new0 pass. Final globaldocs ACTUAL
exit1 byte-identical base48missing/37ambiguous, cmp exit0/delta0 separately.
Unchanged394call reference and21negative-suite receipts retained; no new external
behavior introduced by typing lemmas. Both independent follow-up reviews clear.
No owner/representation/guard/whole obligation signature change, budget increase,
new axiom or goal action. Final full HEAD/patch/bundle/checksums in absolute
/workspace/vy2-evidence/recursive-fixed/HANDOFF.md and cumulative handoff.


## Ordered ordinary root declarations (2026-11-01)

Original Y04/Backfill A/B continuation; full assignment remains PARTIAL and
original goal BLOCKED unchanged. Parent4840cc9e746bae7fcfa814edbef0b487aca87aaa,
assigned branch/base unchanged. Existing6165artifact hashes verified BEFORE
edits; prior mutable exports/manifests and raw failures preserved. YQ1–YQ7
remain recorded in [scope](../solidity-scope.md); no promotion of admission or
manifest coverage, no owner source/compiler/world/heap rewrite.

[RootDeclarations](../../Solidity/Yul/Views/RootDeclarations.lean) carries
intrinsic existing FixedDeclaration certificates indexed by root name/type
pairs. It threads ONE byte cursor through actual ordered roots and calls the
existing FixedDeclaration.pack/ONE packDeclarationPaths scalar algorithm.
Adjacent scalar roots share available bytes; fixed aggregates retain entry
AND exit slot rounding. No second scalar planner, untyped state/AST or new
fuel/depth/root/node/address limit. Explicit constant-motive constructor
eliminators satisfy G0. Local pack_cons avoids recursive symbolic simp loops.

Metadata adapter: ordinaryRootNames filters ACTUAL Env.decls order by exact
scope/bank and ordinary mutable state-variable constructor (no constant or
immutable storage slot). It checks exact complete selected names, distinct
selected roots and each actual E.rootTy against the typed certificate. It does
not silently skip an unsupported ordinary type: omitting it fails metadataOrder.
Source.Syn.collect/decls preserve source order (Source/Decls); frontend
SolcJson/Contract's vars filter also preserves list order, but compiler roots
and deployment immutables are NOT rewritten. Source.Env.rootTy/structFields
provide logical types, not a flattened inherited physical root order or initial
origin. Scope, bank and Word origin remain explicit; C3/base/active-contract
layout/custom-origin and global compiler agreements are original open inputs.
Storage.HashedLayout remains its documented WORD-GRANULAR owner model.

[Spec](../../Solidity/Yul/Views/RootDeclarationSpec.lean),
[Checked](../../Solidity/Yul/Views/RootDeclarationChecked.lean) and
[Typing](../../Solidity/Yul/Views/RootDeclarationTyping.lean) derive complete
leaf enumeration, prefix/root injection and cross-root separation, exact
scalar spans/endByte, no duplicates, real pathTy presence and nonwrapping
Word geometry from checked computations and real distinct declarations. No
caller supplies final layout/separation/default/inverse/readback/safety laws.

A malformed-metadata investigation found that selected-bank Nodup alone misses
same-ID declarations across banks/constness: owner declOf chooses FIRST by
kind/scope/name. The preserved pre-fix counterexample passed preparation while
actual transientRoot selected the other bank. The final checker computes
ALL state-variable IDs in the selected scope (both banks, all constness,
including malformed nodes) and rejects duplicateDeclarations. This is checked
metadata preparation, not a new Solidity admission exclusion or semantic
premise. [Metadata](../../Solidity/Yul/Views/RootDeclarationMetadata.lean)
PROVES unique first lookup, actual ordinary mutability/bank and every generated
leaf's Source.transientRoot agreement. Concrete cross-bank, immutable/plain
and malformed-node duplicates reject; distinct scopes still accept. This
component does not validate arbitrary malformed Source syntax or prove source
program reachability. Original root/FixedDeclaration APIs remain intact.

[Source](../../Solidity/Yul/Views/RootDeclarationSource.lean) reuses concrete
canonical Source.Storage writeback with complement from the SAME raw snapshot:
whole administrative unchanged identity (none versus explicit default),
unselected cells, result view and complete reencoding. Actual current-frame
Source.applyOp, journal/rollback/reset/MemOK operations remain owner operations.
[Composition](../../Solidity/Yul/Views/RootDeclarationComposition.lean) equates
COMPLETE pure storage decoding with seven actual source operations;
[Final](../../Solidity/Yul/Views/RootDeclarationFinal.lean) equates ACTUAL
residual journal maps at EVERY Word. Together they reconstruct the entire
physical snapshot from actual source AND actual residual, not projections.

[Readback](../../Solidity/Yul/Views/RootDeclarationReadback.lean) then derives
actual Source.readCell result/state and encoded physical field payload for
every represented leaf. The generic helper states a real finiteView premise;
concrete persistent and declaration-derived transient instances derive it from
actual executed snapshots, not supplied final read adequacy. The owner
Hoare.run_bind/getter equations retain complete state/result behavior. Source
readLoc/indexLoc local alias controls preserve child REFERENCES, separately
read the real scalar member, and preserve exact Panic0x32. They do not claim
a fully chained source-expression alias/member or compiler theorem.

Inhabited scope: adjacent uint8/uint248 exactly fill slot0; bool at1 then
Inner[2] aligns2–3; uint248 at4 followed by uint16 spills5; marker owns6;
raw unowned slot7=999. Derived10persistent leaves plus a SEPARATE actual
uint16 transient declaration at transient slot0. Complete field/path/root
coverage, masks, missing/mistyped/duplicate/incomplete/overflow/dirty-bool
preparation controls are inhabited. Every-original-H owner MemOK and real
initial/postwrite/alias/child instances, selected/unselected/account/bank
preservation, caller-prefix and committed-child outer rollback, same-slot
order, static empty revert and full transient RAW reset are proved.

[Initial](../../Solidity/Yul/Views/RootDeclarationInitial.lean) aligns typed
initial marker55 and complementary padding with constructor OBSERVATIONS at
slots0–7. Unobserved slots8+ retain arbitrary supplied residual words (0xee… in
this witness), whereas the fresh EVM constructor leaves them zero. The kernel
proves COMPLETE reconstruction of the SUPPLIED initial snapshot, not of the
entire EVM constructor store; no full constructor reachability/correspondence
is inferred. It also proves every-Word persistent residual/padding preservation
across updates, marker administrative identity,
zero transaction-entry transient source/residual and pure reverse-field store
agreement. Administrative pure writeback is distinct from actual source writes,
which retain journals/static effects even when values are unchanged. Witnesses
are actual typed owner states; constructor/program reachability is not inferred.

Pinned [RootSequence.sol](../../tests/yul-views/RootSequence.sol), solc0.8.38
commit1835d247/Osaka, optimizer off, legacy/viaIR: independent20-word goldens
cover eight FULL raw slots including residual sentinel, all10logical fields,
typed+raw transient words, true storage aliases, distinguishable forward/reverse
orders, complete100-byte Error("root layout"), rollback and fresh transaction
reads/reset. New14ordered calls and381fail-closed mutants (240coherent ABI
word mutations plus layout/bank/order/error/budget controls) pass. Every prior
394observation/report field remains unchanged. No original100m gas/5m-step or
proof/heartbeat/recursion/test budget changed. External finite observations
remain separate from kernel source/compiler/target adequacy.

G0/history/build policies inspected; checking-cost warning issued. Independent
finder caught three indexed equation matches: fixed with explicit eliminators.
Default recursion/heartbeat/simp-loop diagnostics retained; proof factoring,
exact numeral equivalence and existing source-step equations repair them with
unchanged budgets. The independently confirmed cross-bank identity gap is
fixed by checked actual identities plus a proved lookup/bank theorem; pre-fix
source and passing witness retained honestly. No axiom/sorry/admit/native oracle,
owner representation change or raised budget. Heavy work serial/private Lean
lock, LEAN_NUM_THREADS=1/Lean-j1, existing aggregate12GiB/no-swap/OS+RSS+disk
monitoring and writer lock. No new executor, goal action, worker import or push.

Full queue remains open: Y04 arbitrary inherited/global/dynamic/mapping/hash
ownership and dirty-owned transport; Y05 dirty/shared-zero/interior/remaining
memory forms, whole memory/writeback and reachable allocation refinement;
Y06 source/environment bindings; concrete V10/V11 agreements; actual VY1
source execution/assembly MemOK; Y09.02 calculus/notation/printers and final
source/compiler/joint closure. Backfill A/B partial. Existing MemOK/World/
ContractWorld/memory-call/Bridge are available, not assembly adequacy. Published
5f6a75b6038371a3917dbe08b660d5f2d1207c58 still lacks Yul exports per audit;
no unpublished producers imported. get_goal read/Lean MCP absent; original
goal BLOCKED unchanged. Questions=[]. Final gates/reviews/head/artifacts in
/workspace/vy2-evidence/root-sequence/HANDOFF.md. Global docs remains ACTUAL
exit1 with pinned-base equal48missing/37ambiguous; zero delta is separate.


Final ordered-root gates: actual Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort2jobs exit0; final affected114jobs and policy wrapper1160default/
262TestSuite/131annotations exit0. Full signature/axiom audit2859
declarations/1638theorems: 1584standard-only/54axiom-free,
none missing/unexpected. Strict491automatic/61budgeted/11refuted/0pending;
trust1190sources/246sites/0findings; layers351core/0elaborator reach;
orphans1175reachable/0orphans; markdown base1/head1/new0. Global docs ACTUAL
exit1 same48missing/37ambiguous, byte-identical pinned base SHA256
01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a;
cmp exit0/zero delta is SEPARATE. All22negative families pass, new381controls.
Cumulative408call report SHA25635140bee16f8a94c2b5c2ac355a35cd4aef313e10a595bf2c846a180c3138502; all394preceding fields identical.

Separate final read-only finder/skeptic reviews clear after recorded fixes:
G0 eliminators, actual declaration identity/bank proof and constructor evidence
scope wording (observed0–7 versus arbitrary residual8+). Neither reviewer ran
Lean/server/build/tests or edited. All raw recursion/heartbeat/simp/type/monad
failures retained; no budget increase or new axiom. Original full lane/goal
remains PARTIAL/BLOCKED and all remaining obligations above stay mandatory.


### Precise inheritance and origin inputs

Post-checkpoint owner inspection confirms these are AVAILABLE metadata, not
absent whole lanes: Source.Env.linearize returns Option(List String) using
owner declaration-count-derived fuel; Source.Syn.contract carries optional
layout-at expression/inheritance syntax; frontend Contract reads actual
linearizedBaseContracts metadata. The present adapter does not prove the
flattened inherited/active-contract root-order bridge or evaluate that expression
to an agreed Word origin. Those ORIGINAL integration/derivation obligations
remain open; no generic assumed order/origin adequacy witness was substituted.
No producer/owner branch import or source-definition rewrite occurred. Exact
symbols/boundaries in root-sequence/owner-order-origin-inspection.json.


### Inherited active-contract roots (2026-11-01)

Original Y04/Backfill A/B progress; full lane remains PARTIAL and original goal
BLOCKED unchanged. YQ1–YQ7 unchanged. Actual pinned solc documentation requires
base-ward-first C3, allows cross-contract scalar packing, aligns aggregates at
entry/exit, and keeps transient and persistent layout independent.

InheritedDeclarations uses ACTUAL Source.Env.linearize, reversed; no second C3
or scalar planner. The computed hierarchy checks unique global contract/interface
identities, owner basesOK, actual declared active/ancestor nodes, no repeated
lineage members and closure under actual direct bases. Those are finite metadata
checks, not supplied final layout/inverse/safety laws. Every descendant scope's
ordinary roots are concatenated in reverse C3; declaration order within each
scope follows actual Env.decls. PRIVATE base storage is included, unlike visible
name lookup. Constants/immutables are filtered as before. Qualified DeclName
identities and all same-scope stateVar IDs across BOTH banks/constness/malformed
nodes are checked to preserve ACTUAL first declOf and transientRoot selection.
Missing/incomplete/wrong-order/wrong-bank/cross-identity metadata cannot silently
become a complete registry. Existing owner C3 fuel/budgets unchanged.

Existing RootDeclarations/FixedDeclaration and ONE packDeclarationPaths thread
one byte cursor across contracts. Computed success derives complete root/leaf
coverage, path uniqueness/cross-contract separation, exact end/nonwrap and actual
pathTy/bank agreement. Existing Source.Storage, Source.applyOp/current-frame and
paired residual journal operations yield complete source-store equality and
whole residual FUNCTION equality, hence full raw supplied-snapshot reconstruction.
Pure unchanged administrative identity retains none versus explicit default.
Actual Source reads, two storRef aliases, member/index errors, every-original-H
MemOK, inhabited initial/written MemOK, static refusal, caller-prefix child rollback,
committed-child enclosing rollback, account/bank isolation and full transient
logical+residual reset are instantiated for the computed diamond registry.

Diamond D is B,C; B and C both inherit A. Owner result [D,C,B,A] reverses to
[A,B,C,D]. A's private uint8 and B's uint248 share slot0. C's bool and Inner[2]
force alignment and two nested struct slots; D's uint248 then uint16 demonstrate
spill and nonzero padding, with marker55/unowned999. Separate declared transient
uint16 occupies transient slot0. Complete supplied kernel map has arbitrary0xee
residual at8+, whereas independent compiler constructor observations concern
slots0–7; no entire EVM constructor equality/reachability/correspondence is claimed.

Pinned InheritedSequence.sol independently expects both legacy/viaIR full
20word ABI/raw/logical/bank observations for7 ordered calls per pipeline, private
base getter/setter, actual storage aliases, distinguishable reverse updates,
full100byte Error("inherited"), postfailure reads and unchanged100m gas/5m steps.
AST-derived owner-qualified field inventory and C3 order are checked independently
of storageLayout coordinates.397negative controls include240coherent ABI word
mutations plus wrong root/order/bank/owner/ancestry/revert/limits. The test-only
InheritedLineage.lean additionally runs EXISTING frontend contractLineage on both
pinned compiler ASTs and12 malformed ancestry/order/identity controls. This is
finite owner API testing, NOT a universal frontend-to-source C3 theorem; no
frontend dependency enters Yul physical core.

Origin remains an explicit Word. Source contract layout-at syntax exists; no
physical evaluator/semantic origin agreement is supplied or assumed here.
The checked Source hierarchy bridge does not prove every arbitrary frontend
source unit's metadata wellformedness, inherited constructor execution or global
allocation refinement. HashedLayout remains its owner's WORD-GRANULAR model,
not this packed-layout proof. Dirty owned fields, dynamic/mapping/hash/global
ownership, remaining memory/shared-zero/interior forms, reachable allocation,
actual V10/V11 agreements, Y06 bindings, VY1/source/assembly MemOK and Y09.02
calculus/notation/printer/compiler/joint closure remain original unfinished work.
Preparation None/errors never become Yul refusal/no-op/deallocation/cleanup.
Owner MemOK/World/ContractWorld/Bridge remain available, not Yul adequacy.

G0/history reviewed; no owner representation change. New typed certificates
reuse existing constant-motive eliminators. Measured per-file/source controls
stay at original budgets. Actual gates, failures, resources, independent reviews,
full head and artifacts: /workspace/vy2-evidence/inherited-roots/HANDOFF.md.
Historical global docs exit1/48missing/37ambiguous stays a FAILURE with pinned-base
zero delta separately verified. No goal mutation, imports of worker branches,
merge/push/PR or semantic decision. Questions=[].


Inherited checkpoint final gates: Lean4.24.0/Lake5.0.0-src+797c613, KeySort2jobs
exit0; focused123jobs/full1170default+262TestSuite/131annotations exit0.
Complete3042signatures/1732theorem reports:1673standard-only/59axiom-free,
no missing/unexpected. Strict491automatic/61budgeted/11refuted/0pending;
trust1200sources/246sites/0findings; layers361core/0elaborator;
imports1185reachable/0orphans. All23cumulative negative suites and pinned frontend
2pipeline/12negative controls pass.422ordered external calls, all408preceding
fields IDENTICAL; SHA2568a67687757bccdb9e08336e96a73373ed7f2ba3e76aeca096bec2f8b61ae381a.
Both separate final read-only finder/skeptic reviews CLEAR, no checks/edits.
Raw audit parser/missing-file failure retained, repaired namespace+mutual handling;
no proof/budget change. Global docs ACTUAL exit1, exact-base byte equality/delta0
separate. Full assignment/goal remains PARTIAL/BLOCKED, all original queue open.


### Computed active layout origin (2026-11-01)

Original Y04/Backfill A/B progress, full lane PARTIAL and original goal BLOCKED
unchanged. Earlier origin-open statements are superseded ONLY for this supported
ordinary current literal-base profile. General expression/global/source/compiler
adequacy remains open. YQ1–YQ7, existing exclusions/guards/owner states unchanged.

LayoutOrigin uses ACTUAL Source.Syn.const and Q.FitsInt uint256, retaining the
exact rational, integral/nonnegative/range facts and Word-to-integer equality.
No modulo256 conversion, fractional truncation, second constant evaluator,
artificial expression/root/depth cap or assumed desired origin law. Numeric,
scientific and integral fractional-spelling literals retain exact owner values;
invalid fractions/out-of-range constants fail preparation. Source.isLiteralBase
is the EXISTING profile guard, and successful active-clause preparation is proved
to preserve actual Source.Syn.excl=none. Compiler accepts40+2 while this existing
Source profile excludes it: both observations preserved, no profile promotion.

prepareActiveOrigin checks actual owner hierarchy/global identity and resolves
ACTUAL Env.declOf contract with qualified file-level active name. Found declaration
membership/kind/scope/name are derived; malformed top/node/name shapes diagnosed.
Only MOST-DERIVED ACTIVE contract's clause is evaluated, not any summed/inherited
base clause. Missing layout defaults0. Transient uses independent0 regardless of
computed persistent origin, after validating the active declaration/clause.
No fabricated interpretation of preparation errors as language refusal/no-op.

ComputedSourceLayout/prepareComputedLayout compose this computed origin with the
existing CheckedInheritedDeclarations/RootDeclarations and ONE scalar packer;
entry signature has NO arbitrary origin Word. Existing explicit-origin APIs and
codec/guard signatures unchanged. Exact metadata/packing/bank/extent/coverage,
nonwrap and raw whole-store reconstruction laws reused. ComputedLayoutPreparation
states only REAL actual hierarchy/metadata/pack equations. Concrete origin_entry_exact
instantiates them and proves the PUBLIC preparation returns the actual checked
layout; it is not a list of assumed inverse/read/safety/final-view obligations.

Actual diamond D:B,C with both inheriting A, D layout at42, yields persistent
leaves at42..48 with adjacent private-base uint8+uint248 sharing42, bool43,
struct array44/45, uint24846, spilled uint1647, marker55 at48; end1568.
The separately declared transient uint16 remains0. All actual typed Source.Storage
snapshot decode/encode, pure unchanged administrative none/default identity,
selected/unselected paths/accounts/banks, actual Source.applyOp/current-frame
sequence, EVERY-original-H MemOK and inhabited initial/postwrite/alias states,
whole residual function equality/full raw reconstruction, caller prefix/child
rollback, committed child/outer rollback, static empty revert, transient logical+
residual reset and alias/readCell/index error controls connect to this computed
origin. Supplied kernel residuals outside observed42–49 are arbitrary0xee;
constructor observations do not imply entire EVM store/reachability/correspondence.

Adversarial controls: absent/duplicate/mismatched active metadata, owner range and
integrality, maxWord exact conversion vs actual full-entry physical-span failure,
profile-preserving arithmetic boundary, standalone base default0, padding and dirty
owned bool43. Finder caught a copied dirty test still at unowned1; fixed to43,
leaving unowned1 fully residual. None remains unsupported preparation, not assembly
refusal/cleanup/deallocation. Dirty owned payload transport remains unfinished.

Pinned OriginSequence.sol independently specifies seven ordered calls per legacy/
viaIR pipeline, complete20word ABI/raw/logical storage/alias/transient observations,
AST numeric42 provenance, independent base-alone0 layouts, full100byte Error("origin"),
postfailure reads/padding/sentinel49.409strict negative controls include240coherent
ABI word corruptions, wrong origin/profile/base/owner/bank/order/revert/limits.
Additional18actual compiler classifications cover defaults, literal42/42.0/0.42e2,
accepted40+2, and fraction/negative/numeric-overflow/span-overflow errors. These are
finite external checks, separate from universal kernel/source/compiler adequacy.
Compiler0.8.38/Osaka/source/archive pins,100m gas/5m steps/all original budgets
unchanged; all older report fields and observations retained.

G0/history reviewed; no owner representation refactor. Direct whole-record
normalization exceeded existing200000 heartbeats; retained raw exits and repaired
with generic staged monadic/dependent-if computation equations, concretely supplied
by actual metadata and already-proved pack result (about6s), no budget change.
All prior failed attempts/caches/evidence preserved. get_goal read/Lean MCP absent;
no goal mutation. Required gates/reviews/full head/artifacts in
/workspace/vy2-evidence/layout-origin/HANDOFF.md. Global docs remains ACTUAL exit1
with exact-base48missing/37ambiguous and zero delta separately.

Whole path/hash/dynamic/dirty ownership, remaining memory/shared-zero/interior
forms, reachable allocation/refinement, whole actual memory/store source closure,
V10/V11 agreement instances, Y06 bindings and actual VY1/source/assembly MemOK,
Y09.02 rules/notation/printers/compiler/joint closure remain ORIGINAL unfinished
work. Owner MemOK/World/ContractWorld/Bridge available, not Yul adequacy. No worker
imports/push/merge/PR, new semantic decision or exclusion. Questions=[].


Computed-origin final gates: actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs exit0; focused134jobs/full1181default+262TestSuite/131annotations
exit0. Complete3243signatures/1837theorem reports:1773standard-only/64axiom-free,
no missing/unexpected. Strict491automatic/61budgeted/11refuted/0pending;
trust1211sources/246sites/0findings; layers372core/0elaborator reach;
imports1196reachable/0orphans; markdown base1/head1/new0.24cumulative negative
families pass.436ordered external calls and18separate compiler classifications;
all422preceding report fields IDENTICAL. Report SHA256
60ede568e49694225e7781974e0e2836f3c3f8e30c91dc71b0ac8eb40bf3e93e.
Independent final finder/skeptic reviews CLEAR after dirty-owned negative test
moved1→43; neither used Lean/server/build/tests or edited. Actual global docs
exit1 byte-identical pinned-base48missing/37ambiguous, zero delta SEPARATE.
Raw normalization/dependent-if/typing/free-variable proof attempts retained.
No budget increase, axioms or changed expected results. Full lane unfinished.

## Computed dynamic headers and live element inventories (2026-11-01)

Original queue status remains Y04/Y05/Y06 partial, Y09.02 blocked; Backfill A/B
partial. This extends the existing declaration planner, not the source AST,
state, owner layout, admission or compiler. Approved YQ1–YQ7 remain recorded in
[scope](../solidity-scope.md). The original goal remains BLOCKED unchanged.

`StorageDeclaration` is indexed by the actual Source declaration type. Its fixed
case reuses FixedDeclaration and the ONE scalar cursor; its uint256[] case
aligns entry and exit, registers the ACTUAL STy.cell uint256 length cell and
reserves exactly one word regardless of current length. It never substitutes
inline Data for a storage reference. StorageDeclarations computes the complete
ordered supported persistent root inventory; ComputedStorage checks existing
owner C3, declaration identity/order, bank and MOST-DERIVED computed active
literal/default origin. Existing flat/fixed/root/origin APIs and guards remain.
Successful pack derives paths, exact end, Word bounds and field separation.
Headers are traced/extracted from the actual successful computation; no caller
provides desired slot equalities, default/inverse/readback/adequacy law fields.

DynamicHeader.element constructs the ACTUAL Source root[index i] uint256 cell
and Storage.Loc.data of the computed header. Its physical word is exactly
`(Fixed.keccak(layoutPreimageBytes(.data headerSlot)) + i) % 2^256`.
The preimage is the approved exact32byte big-endian header word; existing Fixed
hash provenance is reused. Nonwrapping is proved only with its real sum bound.
No collision-freedom axiom/global injectivity. Distinct elements use modular
Word-offset injectivity; different arrays/root words retain the EXACT actual
per-run RegionsDisjoint/preimage/root membership and offset conditions. No
larger guessed root prefix is substituted. Agreement with word-granular owner
HashedLayout.locate exposes its EXISTING `i < Storage.lmax` premise ONLY there;
source index/physical computation do not acquire that extra limit. Arbitrary
packed/nested/dynamic owner agreement is still open.

DynamicInventory constructs all indices in List.range of the actual uint256
length, with no new fuel/node/depth/list cap. DynamicInventoryWriteback's public
snapshotWriteback chooses that length FROM the raw header itself, constructs
its length-cell/live-element registry, uses actual typed Source.Storage and
retains all unowned bytes/unknown slots from the SAME snapshot. Separation and
complete successful raw-map reconstruction are derived, including unrelated
path preservation and whole-store unchanged identity. There is no claim that
this potentially enormous mathematical enumeration is a practical whole-store
runner, nor that changing a length proves program reachability, allocation or
universal dynamic ownership. Dirty/packed/nested/shared ownership remains open.

DynamicSource and DynamicLengthWorld connect actual Source.readLen/writeLen,
indexLoc/reference results, exact Panic0x32, static empty revert and every
original H owner MemOK. Ordinary writeLen writes an explicit Some intWrap256(n)
and journals even zero; pure unchanged-view preparation preserves none versus
explicit default. These operations are NOT identified administratively.
DynamicSourceSequence executes an arbitrary finite list of validated plans
through ACTUAL applyOp and updates the paired residual only after success. Its
complete nonstatic result equals the existing packed journal sequence; static
failure preserves the entire prefix. No product-of-runs adequacy assumption.

Inhabited Base/DS layout-at42 has private uint8 + uint248 sharing42, xs header43,
uint16 at44 with nonzero high padding, ys header45, marker46; declared transient
uint16 at0. Actual source cells, two aliases, maxWord elements, index success/
error, zero shrink/regrow, unrelated bank/account, complete complement/raw-map
reconstruction, caller-prefix child rollback, committed-child outer rollback,
static failure, persistent survival and logical/residual transient reset are
controls. Synthetic hash1000/2000 ONLY inhabits the finite region algebra;
real Fixed function/input provenance is separately kernel-proved and numeric
real Keccak/EVM observations separately tested. Direct decoded-store installation
is a preparation read witness; the actual five-operation source prefix/child
sequence has its OWN exact source/journal proof. Neither is a constructor-store
or source/compiler correspondence theorem. Kernel unknown-slot seed77 differs
from fresh external zeros except where fixture explicitly initializes a slot.

Pinned DynamicStorage.sol/reference adapter uses solc0.8.38/Osaka legacy+viaIR,
unchanged100m gas/5m steps, inherited layout-at42 and separately transient0.
Independent exact expected22word arrays include real header hashes, length/raw
slots, both aliases, maxWord, untouched tail77, padding, marker55/sentinel999,
shrink-to-zero/regrowth, complete100byte Error("dynamic"),36byte Panic0x32,
static-call false and fresh postfailure reads. ALL preceding436 ordered calls
and18 compiler classifications are preserved as prior report fields. Finite
compiler/EVM evidence is separate from kernel/source/compiler adequacy.

Validation and independent reviews are recorded in the versioned
`/workspace/vy2-evidence/dynamic-storage/HANDOFF.md`, exact signatures and raw
command/exit logs. Initial normalization/type/record/proof failures are retained;
no proof/recursion/heartbeat/test budget was raised. Global docs remain exit1
with exact-base identical48missing/37ambiguous findings; zero delta separately.
No manifest promotion. No goal mutation, owner replacement or worker import.

Remaining ORIGINAL obligations: general nested/mapping/runtime hashed/path and
packed dynamic ownership, dirty owned bits, whole storage writeback/residual
adequacy; broader memory/shared-zero/interior/dirty forms and actual assembly
MemOK; reachable allocation provenance/refinement; concrete V10/V11 agreement
instances; Y06 source/calldata/hash/environment bindings; actual published VY1
source execution and Y09.02 calculus/notation/printers/compiler/joint closure.
Existing MemOK/World/ContractWorld/memory-call/Bridge are AVAILABLE, not assembly
adequacy. Published producer absence is not absence of whole owner lanes.

Further same-checkpoint composition: ComputedDynamicSnapshot traverses the
ACTUAL attached header trace and derives each typed header certificate from
successful packing. Every raw header chooses every live index; no manual
complete element list or skipped unsupported entry. It joins these with all
computed fixed/header registrations, checks actual resulting field separation,
and derives whole raw-map reconstruction and unchanged whole-store identity.
ComputedDynamicControls proves the generated TWO-array inventory equals the
independently specified nine-field control registry and its entire decoded
store/result, not only projections. Growth2→3 decodes previously residual tail77
as the new actual typed element. General changing ownership through a paired
journal is STILL OPEN: snapshot reconstruction is not a proof of such adequacy.
DynamicSourceAliasControls separately observes both real local aliases after
ACTUAL source operations, with inhabited/every-H owner MemOK. General source
sequence account/bank/unselected-cell/complement preservation is derived from
validated operations, rather than expanding a particular concrete state.

The complete cumulative declaration-name audit found a new control-name
collision with the accepted DynamicUintControls memory family. Only the NEW
storage control was renamed dynStorageState; the accepted family stayed intact.
Initial audit/proof failures and algebraic repairs are preserved. This is not
a Source representation change; checking uses the original budgets and private
serial Lean wrapper. New inventories can cost proportionally to runtime lengths,
without a newly imposed traversal bound or a practical host totality claim.

The same original source-closure work continues in DynamicLengthCodec and
ComputedSnapshotSource/Reads/Controls. Actual DeclPosition.registration codec
transport (including its dependent source type/position) proves the full-width
header encoding and derives the actual uint256 length value FROM its concrete
view. Generated root/element bank facts derive from real declaration metadata.
No caller now needs to supply a finished readLen/readCell agreement for the
checked snapshot operation. Every generated cell's real readCell result, every
computed header's complete readLen result and whole raw-map reencoding derive
from successful actual Source.applyOp and the SAME computed snapshot/complement.
A nontrivial TWO-array source operation inhabits this composition and every-H
MemOK, rather than only supplying an assumed view law.

`applySnapshot?` is an EXPLICIT EFFECTFUL canonical account operation at the
current frame's intrinsically bound account. It preserves actual source static
empty-revert, ordinary operation/journal administration and success/error MemOK.
It is NOT automatic writeback for arbitrary Yul/read-only/static blocks, NOT
pure administrative unchanged identity, NOT a raw Yul semantics and NOT a
changing-ownership residual journal adapter. Pure snapshot preparation APIs and
ordinary writeLen remain separate and unchanged. These distinctions are needed
for eventual actual producer/semantic/refinement composition, which stays open.

Final dynamic-source checkpoint gates: actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs exit0; affected187jobs and mandatory ./run-lean.sh
1212default+262TestSuite/131annotations exit0. Complete3517public signatures/
2019theorem reports:1950standard-only/69axiom-free, no missing/unexpected.
Strict491automatic/61budgeted/11refuted/0pending; trust1242sources/246sites/
0findings; layers403core/0elaborator reach; imports1227reachable/0orphans;
Markdown base1/head1/new0. All25cumulative negative families pass, including607
new strict negatives/398coherent ABI-word mutations.460ordered external calls
and18SEPARATE compiler classifications; EVERY preceding436report field identical.
Final cumulative reference SHA256
496adf1c8b9ddd42f9791ef1f687cdb9e966b28488b4a2206aedb471ab1104fd.
Actual global docs remains EXIT1 with pinned-base BYTE-IDENTICAL48missing/
37ambiguous findings, zero delta SEPARATE. No global documentation pass.
The explicit snapshot API's static refusal is conditional on successful canonical
preparation; None is unsupported preparation, never a source/Yul refusal/no-op.
Independent read-only finder/skeptic reviews found no remaining semantic issue;
complete audit's naming finding was fixed only in new storage controls. Reviews,
raw failures, exact gates/resources/premises and versioned exports remain in
`/workspace/vy2-evidence/dynamic-storage/`. Entire original lane unfinished.

Dynamic checkpoint identity: repository `/workspace/solidity-lean`, branch
`codex/solidity-inline-assembly5-20261031/vy2-physical`, pinned base
`0b078cefaf7daad79007b87b72df64eb6936420f`, accepted parent
`f44d7c523159b07e0b0b4975ec9c035de94737cc`. The complete committed head, tested
source hashes, commands/exits and versioned original patch/bundle/checksums are
recorded after commit in `/workspace/vy2-evidence/dynamic-storage/HANDOFF.md`.
No claim of full queue completion; original goal BLOCKED unchanged, questions=[].


## Ownership-changing dynamic complements (2026-11-01)

Continuation from accepted `40337e715392c517a73f3bc1eefd85a036c2feb3`;
base, branch and repository above remain unchanged. YQ1–YQ7 remain approved
implementation directions. This is original Y04 / Backfill A–B progress; full
Y04/Y05/Y06 and both backfills stay PARTIAL, Y09.02 BLOCKED, goal BLOCKED
unchanged. No admission/manifest/owner representation change or producer import.

OwnershipInventory computes OLD live fields from ACTUAL Source.readLen and the
checked declaration/header trace. OwnershipPlan computes the full old raw map
from actual source storage plus its complementary journal slice, applies one
raw word update, computes NEW live fields, checks real finite separation and
canonical decoding, and prepares the actual Source account operation. Only
successful Source.applyOp updates the complementary journal. Static source
failure preserves BOTH prior states and its actual empty-revert result; None
means unsupported preparation, not source/Yul refusal/no-op/deallocation.

OwnershipTransport derives support from the written slot plus old AND new
field slots. On that finite union, it writes the new mask of the SAME raw map;
outside the union, actual old encoding proves the raw word already equals the
old residual. The resulting ENTIRE complementary map is the new snapshot mask.
Duplicate support slots retain every undo entry; old journal entries belong to
historical ownership and are NOT asserted zero under the current inventory.
No unknown slots, high bits, padding or dropped words are reset or discarded.
No global hash/collision premise, extra domain/length/fuel cap or opaque final
readback/inverse/adequacy field is introduced. Hash provenance and existing
per-run region/offset/type/separation conditions retain their exact boundaries.

OwnershipFrame.pure_connection proves equality of the WHOLE store AND
complement produced by pure changing-snapshot writeback and ACTUAL source /
residual execution. Fresh following preparation is proved equal to the ordinary
executable preparation at the exact output states; its raw map equals the
previous updated map. Actual child rollback preserves caller prefix; child
commit followed by enclosing rollback restores the complete companion. EndTx
preserves the entire represented persistent map and clears actual transient
source/residual cells and both journals. This adapter changes persistent current
account ownership only; transient dynamic ownership is still OPEN. Other banks,
accounts, paths and locals are preserved by actual-operation laws. Every original
owner typing H MemOK transports through source success/error and arbitrary finite
request batches. No assembly MemOK or compiler adequacy follows.

OwnershipBatch retains exact successful-prefix state/residual when a later
preparation returns None, and stops on the complete actual source error.
OwnershipBanks.same_word_store preserves whole administrative storage, including
none versus explicit-default cells; effectful account operations still journal.
It does NOT assert unchanged whole EMState or unchanged historical journals.

Inhabited controls start at the PREVIOUS actual source snapshot operation,
then run two arrays 2/1 -> 0/0 -> 3/1 through dependent checked plans and the
executable batch. Former data12/MAX/33 and tail77 become residual words during
shrink; regrowth derives actual typed Source.readLoc tail77 at the original
hashed location. Two real local aliases observe length3 and index/read payload;
index3 produces original Panic0x32. Actual static failure, caller-prefix and
child-commit/outer-revert laws, other account/bank, every-H/inhabited MemOK,
nonzero padding/unknown words and complete persistent EndTx reencoding are
checked. Synthetic hashes1000/2000 and arbitrary kernel seed77 are not numeric
real Keccak, constructor equality or reachable-execution evidence.

The original DynamicStorage.sol/pinned compiler/Osaka/legacy/viaIR report and
ALL460 ordered calls/18 separate classifications remain unchanged. New narrow
history mutations discriminate lost newly residual words, stale masks, reversed
shrink/growth, aliases, wrong physical roots and failed/static observations with
coherent ABI bytes. External observations do not prove kernel source/compiler
correspondence or nested source-frame reachability. Raw proof failures remain
in /workspace/vy2-evidence/ownership-transport; no budget was raised. Large
closed-state normalization was replaced by proved existing source provenance,
typed checker equations and generic transport, not relaxed guards.

Final commands/exits, complete signature/axiom sets, resources, independent
finder/skeptic reviews, committed head and versioned patch/bundle/checksums are
recorded in `/workspace/vy2-evidence/ownership-transport/HANDOFF.md`. Global docs
retains its real exit1; exact-base zero delta is separate evidence. All original
whole ownership/dirty/nested/mapping/transient cases, universal memory/shared-zero/
interior writeback and reachable allocation refinement, V10/V11 instances, Y06
source inputs/environment, actual VY1/source/assembly MemOK, physical calculus /
notation/printers and source/compiler/joint closure remain OPEN. Questions=[].


Ownership checkpoint final kernel/runtime gates: Lean4.24.0 and
Lake5.0.0-src+797c613, KeySort2jobs exit0; focused196jobs, full policy wrapper
1225default+262TestSuite/131annotations exit0. Complete3638public signatures /
2113theorem reports:2043standard-only and70axiom-free, missing0/unexpected0.
All25prior negative families plus190new ownership-history mutations pass. Fresh
both-pipeline dynamic replay equals EVERY field of its accepted24-call receipt;
entire460-call cumulative reference and18separate compiler classifications remain
byte-identical SHA256496adf1c8b9ddd42f9791ef1f687cdb9e966b28488b4a2206aedb471ab1104fd.
Independent final finder/skeptic review is clear across THIRTEEN new Ownership
modules, narrow external test and documentation, without reviewer checks/builds.
The initial review request's14-module count was corrected by actual filenames;
no theorem or source finding was hidden. Exact remaining gate/resource outputs
and committed identity are in the versioned handoff above. Entire original lane
remains unfinished and its blocked goal unchanged.


## Packed dynamic unsigned ownership (2026-11-01)

Original Y04 / Backfill A–B continuation from clean accepted
`b1980de8913f0e2bc68953399ade48dc0159c469`, same pinned base/branch/repository.
Approved YQ1–YQ7 remain implementation directions, not implemented admission.
Full Y04/Y05/Y06 and both backfills PARTIAL; Y09.02 and original goal BLOCKED
unchanged. No owner state/AST/compiler edit, producer import or manifest promotion.

StorageDeclaration adds a typed properly-packed unsigned-array certificate;
actual rootTy/cellTy, declaration order, active origin/bank and ONE existing
header scalar pack/cursor still compute header position/end. The new constructor
covers bits<256; uint256 retains its original constructor/legacy trace visibility.
This is a disjoint certificate normal form, not a language width exclusion:
unsignedTrace includes BOTH existing full-width and new packed cases. Original
header?/headerTrace/snapshotInventory and uint256 contracts remain unchanged in
meaning and explicitly scoped to their original full-width element profile.
The new unsignedSnapshot enumerates all live fields of the supported unsigned
trace, without silently skipping an unsigned constructor or adding a length cap.
Header trace root uniqueness derives from actual checked declaration uniqueness.

PackedDynamicHeader derives width=bits/8, elementsPerSlot=floor(32/width),
slot=(Fixed.keccak(BE32(header))+floor(i/elementsPerSlot))%2^256 and low-byte
offset=(i%elementsPerSlot)*width. Width positivity/field fits derive from actual
IntTy validity; same-slot fields and distinct quotient slots are proved separate.
Exact live-byte ownership is proved from the computed length and fields.
Uint24 leaves two padding bytes even in a full slot. Header/registered-region
separation keeps genuine per-run RegionsDisjoint and actual QUOTIENT-offset
bounds; no global hash injectivity or stronger convenience premise. Optional
no-wrap has its real sum bound. HashedLayout remains word-granular, not a packed
compiler layout proof. Exact full ScalarPath compatibility (including codec)
with the preserved uint256 element construction is kernel-proved.

PackedOwnership adapters reuse actual scalar codecs/finite writeback,
OwnershipTransport's exact old/new complement union and real Source.applyOp /
frame/journal operations. Old inventory derives from ACTUAL Source.readLen;
new inventory derives from the updated raw headers. On source success only,
residual updates preserve all dropped fields, padding/high bytes, unknown slots
and histories. Static/error preserves both prior states. Whole raw reencoding,
pure/effectful whole-store+complement agreement, fresh following preparation,
exact source cell/length results, every-H owner MemOK, caller-prefix rollback,
committed-child/enclosing rollback, bank/account/unselected-cell preservation,
transaction reset and finite batch failure accounting derive from concrete
operations. No opaque inverse/view/safety/result law field or duplicate Source
state/IR is introduced. None stays unsupported canonical preparation, never a
Yul refusal/no-op/deallocation. Existing whole-memory/assembly obligations and
all proof/fuel/node/heartbeat/test budgets stay unchanged.

Inhabited uint16 controls run actual Source/residual operations 0->17->1->0->18
across the slot boundary. Shrink exposes formerly owned bytes in the SAME slot;
zero keeps the entire dirty/full-width raw words; regrowth recovers tail77 and
newly-live0xcccc. Two actual local aliases observe length/index/read77 and
Panic0x32 bounds. Nonzero partial padding, other account/bank and unknown words,
static failure after caller prefix, real nested rollback/commit, actual inhabited
and every-H MemOK and full persistent endTx map are checked. Mixed live uint16 /
uint24 roots additionally prove actual uint24 maximum-value Source.readLoc and
nonzero0xaabb full-slot padding preservation. Pure unchanged preparation preserves
none versus explicit default; effectful account no-op still journals. Synthetic
hash1000/2000 controls are separate from real approved Fixed input provenance,
compiler Keccak numbers, constructor reachability and source/compiler adequacy.

Pinned PackedDynamic.sol adds independent complete ordered legacy/viaIR external
controls for uint16/uint24 lengths/aliases/fields/raw slots/padding/unknown words,
member writes, static failure, full Error("packed"), Panic0x32 and fresh reads.
Compiler0.8.38 commit1835d247, Osaka, gas100m/steps5m and every old receipt stay
unchanged. The initial NEW adapter omitted the standard dynamic-array ABI
head/length; its raw failure remains preserved. Only the independently specified
ABI offset32/length23 was added; semantic expected words/status/source and ALL
460 old report fields were unchanged. The 917 new strict negative controls
include652 coherent complete ABI-word mutations plus packed-history/padding/
revert mutations. Initial mutation-count arithmetic failure is preserved;
eight additional meaningful mutations per pipeline fulfilled its917 target,
without dropping controls or changing gas/step/verdict budgets.

Full original dynamic/mapping/signed/bytes/dirty-owned/transient ownership,
universal memory/shared-zero/interior writeback, reachable allocation refinement,
concrete V10/V11 agreements, Y06 input/environment/source bindings, actual VY1 /
source/assembly MemOK and Y09.02/calculus/notation/printers/compiler/joint closure
remain OPEN. No admitted dirty form is cleaned, excluded or given no-op semantics.
Actual available owner MemOK/World/ContractWorld/memory-call/Bridge components are
not substitutes for missing Yul adequacy. Original blocked goal is never mutated;
get_goal read is unavailable. Questions=[]. Final tested identity, exact theorem
signatures/premises/axioms, raw gates/failures/resources, independent finder/skeptic
reviews and versioned original exports/checksums are recorded in
`/workspace/vy2-evidence/packed-dynamic/HANDOFF.md`.


Final packed checkpoint gates: actual Lean4.24.0/Lake5.0.0-src+797c613,
KeySort2jobs exit0; final affected207jobs and mandatory ./run-lean.sh
1248default+262TestSuite/131annotations exit0. Complete3860public signatures /
2264theorem reports:2192standard-only and72axiom-free, missing0/unexpected0.
All26prior negative suites plus917packed controls pass. Final32new ordered
legacy/viaIR calls match every field of the first corrected packed replay;
ALL460preceding fields and18separate compiler classifications remain unchanged.
Cumulative492-call projection SHA256
b71e1adce243d0b04559de7bc1fe945be94442fa933d1ea16a7b93b60a537f78.
Independent final read-only finder/skeptic review is clear across23new modules,
4amended lane files, fixture/adapters/tests and appended docs. No reviewer Lean /
server/build/tests/edits. Exact remaining gate/resource results and committed
identity are retained in the versioned handoff. Global documentation retains its
ACTUAL exit1; exact-base zero delta remains separate, never a global pass.
Entire original assignment/goal remains unfinished/BLOCKED unchanged.


## Signed dynamic integer ownership (2026-11-01)

Original Y04 / Backfill A–B continuation from clean accepted
`135d4ab69ff98421b805e68ffd940a97327c030e`, same pinned base/branch/repository.
YQ1–YQ7 remain approved implementation directions, not admission evidence.
Full original Y04/Y05/Y06 and backfills PARTIAL, Y09.02 and goal BLOCKED unchanged.
No Source/owner AST/state/compiler rewrite, unpublished import or admission change.

StorageDeclaration adds a disjoint signedArray(t,signed=true) certificate,
including int256. Actual rootTy/cellTy/order/active-origin/bank and the SAME
uint256 length-header pack/cursor determine coordinates. Old unsigned/u256
selectors, guards and theorem premises remain unchanged; signed cases are
explicitly skipped by those profiles. NEW integerTrace/integerSnapshot covers
all supported old unsigned and new signed integer constructors. IntDynamicHeader
is a NEW actual-declaration-indexed construction, not an alias of the old
conditional unsigned API. Full PackedDynamicHeader->IntDynamicHeader ScalarPath
compatibility INCLUDING codec is proved, then composed with existing uint256
compatibility. Constant-motive eliminators preserve G0 representation discipline.

Physical width/quotient-slot/remainder-byte geometry, field fits, same-slot /
distinct-quotient separation and exact live byte ownership derive from real
IntTy and declaration metadata. Signedness changes ONLY the existing codec's
payload interpretation, not coordinates. The header is always UNSIGNED uint256.
Actual Fixed BE32-header provenance and genuine per-run region/quotient-offset /
nonwrapping facts remain explicit; no global hash injectivity or new arbitrary
length/root/node/fuel cap. Integer trace is not nested/mapping/bytes coverage.

IntPayloadInverse uses EXISTING intPayload/readIntPayload/intCodec. It proves
readIntPayload range, intPayload(readIntPayload n)=n for n<2^bits, and the actual
concrete codec.decode result. Existing read_intPayload supplies the opposite
direction. IntDynamicValues reconstructs actual typed Source.Val.int negatives
with that decoder and proves exact field reencoding/readLoc. It never uses
unsignedStorageValue or a new signed policy. Minima/MAX/-1/zero/sign-threshold
payloads retain all low-width two's-complement bits. Canonical FIELD decoding is
not dirty source-local/high-owned-bit transport, cleaning policy or YQ4 closure.
All unowned/padding bytes remain in complete residual words.

IntOwnership computes old inventory from ACTUAL Source.readLen, new inventory
from actual updated raw headers, then uses existing scalar/source/complement
algebra. Whole old/new raw-map reencoding and pure/effectful store+complement
connection derive from actual preparations. Source.applyOp succeeds BEFORE any
residual updates; static failure preserves both prior states. Real source/frame
rollback, committed-child/enclosing rollback, endTx persistent reconstruction,
other account/bank/unselected-cell/locals and every-original-H owner MemOK laws
remain actual operations. None is unsupported preparation, not a language
refusal/no-op/deallocation. Pure unchanged store preserves none vs explicit
zero; effectful account no-op still journals. Transient-array support is NOT
inferred. New actual source writes cross int16 MIN->MAX and MAX->MIN in place,
with complete mixed snapshots and MemOK, beyond static decoder vectors.

Inhabited signed16/24 controls use real Source metadata and run0->17->1->0->18,
partial final slots and nonzero0xcccc/0xaabb/0xdddd padding/tails. Two actual
local aliases read negative -1 and -32768 after regrowth; source0/1/2/3 reads
prove MIN/MAX/-1/zero and signed24 counterparts/tail. Index18 gives actual
Panic0x32. Shrink/zero retain exact full raw words; regrowth and mixed-root
preparation preserve padding. Source static-after-prefix, child/outer rollback,
accounts/banks, actual every-H/inhabited MemOK and full persistent endTx are
checked. Synthetic kernel hashes1000/2000 and explicit seed maps are distinct
from EVM real Keccak, constructor execution and whole-program reachability.

SignedDynamic.sol adds independently specified complete legacy/viaIR finite
controls using pinned solc0.8.38+1835d247/Osaka, unchanged100m gas/5m steps.
Full dynamic ABI is31words: offset32/length29 plus29specified values, including
signed values sign-extended to uint256, raw slot/padding/header/alias/hash roots,
MIN/MAX/-1/zero and sign-crossing member writes. Full Error("signed"), Panic0x32,
static-probe failure and postfailure/fresh reads remain exact. All increment
mutants are bounded modulo2^256;1073new negatives include808complete coherent
ABI-word corruptions and discriminating padding/sign/order/error mutations.
Final fresh replay preserves ALL prior492 fields/18classifications exactly;
total524 ordered calls, all28 negative suites pass. Full wrapper1274default /
262TestSuite /131annotations and strict/trust/import gates pass. Complete scoped
audit:4106declarations,2435theorems,2362standard-only/73axiom-free, no missing or
unexpected axioms. Global docs remains rawEXIT1 with byte-identical base findings;
finite EVM observations are not source/compiler/target or Yul adequacy.

Full original nested/mapping/bytes/other/transient/dirty ownership, universal
memory/shared-zero/interior/pointer writeback, reachable allocation refinement,
V10/V11 agreement instances, Y06 source/Yul input bindings and Y09.02 calculus /
notation/printers/rule-map/compiler/joint closure remain OPEN. Existing owner
MemOK/World/ContractWorld/memory-call/Bridge components are available, not Yul
adequacy. No original invariant, guard, expected observation or budget is weakened.
Raw failed attempts and all old artifacts/caches remain preserved. Exact final
source identity, complete signatures/axioms, gates/reviews/resources and original
patch/bundle/checksums: `/workspace/vy2-evidence/signed-dynamic/HANDOFF.md`.
Original goal BLOCKED unchanged; get_goal read absent; questions=[].


## Scalar-family dynamic ownership (2026-11-01)

Original Y04/Backfill A-B progress, not full-lane completion. Accepted parent
`1b133944b611b777a83f84beb06e1b22d81f613f`, same assigned branch and pinned base.
YQ1-YQ7 remain approved; no exclusions, semantic judgments or budgets changed.
Gate G0/history reviewed: actual Source/Heap/World/type representations unchanged;
additive constant-motive StorageDeclaration case, parameter-only scalar descriptor.
The constructor addition recompiles affected downstream proofs; prior speed-motivated
state/recursor design is preserved. Existing writer/private Lean locks and hard
12GiB/no-swap runtime retained, with measured resources and serial heavy launchers.

DynamicScalarKind selects ACTUAL bool, address(payability), valid bytesN types and
existing DeclScalar fields/widths/codecs. StorageDeclaration.scalarArray is indexed
by that real dynamic-array type. Existing u256/unsigned/signed APIs and guards are
unchanged, and their selectors skip the additive constructor. ScalarDynamicHeader
and scalarFamilyTrace derive actual header coordinates and all component live paths
from the original checked declaration traversal/active origin and Source.readLen.
Packing uses quotient slots/remainder low-byte offsets, exact widths, Fixed header
preimage bytes, genuine per-run region/offset/no-wrap premises, not global hash
injectivity or arbitrary runtime caps. Address leaves12padding bytes per slot;
bytes3 leaves2padding bytes per10elements. BytesN is big-endian WITHIN its low
storage field, unlike the high/left-aligned ABI/memory word.

This is a bool/address/fixedBytes component inventory. Separate integer traces,
mappings/nested data and arbitrary complete HashedLayout ownership are NOT silently
claimed covered. Existing scalar codec inverses are reused; successful concrete
family decoding is proved to exactly reencode, including bytesN/address and bool0/1.
No opaque inverse, safety, final-view or output-layout law is a certificate field.
ScalarOwnershipPlan derives old inventory from actual source, new inventory from
raw headers and success-only residual journaling from actual Source.applyOp. Exact
whole supplied map reconstruction retains unowned partial-slot bytes, padding,
unknown slots and dropped tails across shrink/zero/regrow. Whole unchanged store,
none-vs-explicit-default administration, other accounts/banks/unselected paths,
actual readLoc/indexLoc/length aliases, exact static errors, caller-prefix child
rollback, committed-child outer rollback, persistent endTx and every original H
MemOK are proved within the concrete preparation scope.

Inhabited actual source controls use bool34 across32-byte packing, bytes3 length12
across10-per-slot, three address elements, nonzero residual/padding, two aliases,
real false/true and byte/address payloads, repeated actual source operations and
nonempty fixed hash preimages. Canonical bool byte2 is NOT representable: growth
exposing it yields preparation None and retains the actual successful prefix.
This is neither a source/Yul refusal, no-op, cleaning policy nor deallocation.
The finite pinned EVM dirtyGrow succeeds and observes truthy2 with the original raw
byte retained; that unresolved representation bridge and YQ4 remain OPEN.

External ScalarDynamic.sol is independently specified for pinned solc0.8.38+
1835d247/Osaka, both pipelines, original100m gas/5m steps. New42 ordered calls cover
complete38word dynamic ABI, typed bytes3/address/bool return alignment, raw slots,
headers/hash roots/aliases/padding, shrink/zero/regrow/member changes, dirty growth,
full Error("scalar")/Panic0x32/static failures and fresh postfailure reads.
1561negative controls include1230bounded coherent ABI-word mutations plus strict
missing/reordered/wrong-root/type/hash/bytes/address-padding/dirty-byte/error tests.
Final fresh replay matches every field; all prior524 fields/18classifications
are unchanged, total566calls. All29negative suites pass. Repaired final wrapper
1298default/262TestSuite/131annotations, strict/trust/layers/zero-orphan checks
pass. Complete scoped audit:4371declarations,2613theorems;2538standard-only/75
axiom-free, no missing/unexpected axioms. Initial orphan exit1 is retained;
ScalarDynamicSnapshot now imports the acyclic ScalarDynamicRegions laws.
These finite tests do not prove source/compiler/target or Yul adequacy.

Independent read-only finder/skeptic reviews found no confirmed semantic defect;
component coverage and bool2 boundary are explicit. No reviewer Lean/server/build/
tests/edits. Final gate/signature/axiom results and actual committed source hashes
will be recorded in `/workspace/vy2-evidence/scalar-dynamic/HANDOFF.md`; raw failed
proof attempts retained, including unchanged-budget recursion failures. Global docs
remains rawEXIT1 with48missing/37ambiguous exact-base findings; equality comparison
is separate from a global pass.

All original Work/Backfill items remain: broader nested/mapping/storage-bytes/
transient/dirty ownership and cross-component closure; universal memory/writeback,
shared-zero/interior/pointer representations and reachable allocation/refinement;
concrete V10/V11 agreements; Y06 actual source/Yul bindings; actual VY1/assembly
MemOK/Y09.02 calculus/notation/printers/rule-map/source/compiler/joint closure.
Existing owner MemOK/World/ContractWorld/Bridge components are available, not Yul
adequacy. Producer prerequisites not assumed. Original goal BLOCKED unchanged;
get_goal read unavailable, no goal calls; questions=[]. Independent backfill remains.


## Combined primitive dynamic inventory (2026-11-01)

Original Y04/Backfill A-B progress; full assignment remains partial. Accepted parent
`57afdc4c9647c92cebed547c05b80d69beddf125`, same branch/pinned base. Gate G0/history
reviewed; no Source/state/type, owner implementation, old family API, codec, guard,
profile, expected observation or budget changed. Additive typed adapters reuse the
existing packing cursor, header/element registrations, actual Source.readLen,
source operations and complement/journal algebra. Kernel witnesses cost90seconds
initial preparation and115seconds final controls, inside unchanged limits; no
representation refactor or new fuel/node/root/length/address cap.

primitiveSnapshot = registrations ONCE ++ (integer live ++ scalar-family live).
Both live lists use the existing actual declaration traces and raw header words.
primitiveSourceInventory? reads both traces from the SAME actual source state,
with exactly that ordering and no duplicated fixed/header registrations. Actual
StorageDeclaration constructors prove selector coverage/disjointness; conflicting
integer versus bool/address/bytesN root types are impossible. Component membership
is exact, every live field is retained, and the executable combined check derives
path uniqueness and physical byte/slot separation. Per-run hash regions/offset and
nonwrapping premises remain real; no global hash injectivity/coverage axiom.

PrimitiveOwnershipPlan recovers the old combined inventory from source, encodes
its entire raw map, derives the new combined inventory after the supplied slot
write, performs actual Source.applyOp, and only on source success journals the
combined complementary update. Whole reencode and pure_connection identify the
SAME actual source/store plus complementary map, not equal projections or a
product of separate runs. Both family views follow from the complete combined
view. Other-family retained reads follow from actual live membership and untouched
header/data coordinates plus codec injectivity. Unselected paths/accounts/banks,
locals, full unchanged administrative store and None versus explicit default,
static errors, successful caller prefix, child rollback/committed-child outer
rollback, persistent endTx and every original H MemOK are proved. Unsupported
canonical preparation remains None with its exact prefix, not a source/Yul refusal,
cleaning, deallocation or successful no-op.

Inhabited single-environment controls include int16[],uint24[],uint256[],bool[],
bytes3[],address[] and a marker. All six length/data families share ONE source/map;
signed17->1->0->18 and bool3->0->3 ownership changes retain signed tail77 and all
other-family data. Repeated bool and signed payload writes preserve other families;
actual Source.readLoc observes -1/MIN,77,MAX,uint24,bool,bytes3 and address values.
Two actual local aliases observe the updated bool through indexLoc/readLoc; index
bounds give actual Panic0x32. Concrete source/residual marks restore caller prefixes
and enclosing states. Nonzero partial-slot/dirty-unowned bytes are checked, including
0xcc signed tail,0xcd uint24 padding,bool2,0xf4 bytes3 padding and0xaa address padding.
Missing/wrong metadata, duplicated inventory and dirty canonical bool inputs fail
checked preparation. Raw bool2 remains unrepresentable INSIDE an owned bool byte;
its external growth succeeds while canonical preparation returns None. YQ4 and
broader dirty representation/source adequacy remain OPEN.

PrimitiveDynamic.sol independently specifies six-family finite compiler/EVM
controls for solc0.8.38+1835d247/Osaka, legacy/viaIR, unchanged100m gas/5m steps.
New48 ordered calls include complete54word dynamic ABI (offset32/length52/payload),
4word typed ABI (including signed extension/bytes3 left alignment), all six headers/
hash roots,10 raw data words, aliases, unknown slot7, cross-family writes, shrink/
zero/regrow, dirty growth, full Error("combined")/Panic0x32/static failure and fresh
postfailure reads. 2537new negative controls include2170bounded coherent word
mutations, dropped/reordered calls, lost families/stale masks/erased padding and
wrong type/hash/ABI/error observations. First fixture parse failure and all proof
attempts are preserved; no expected verdict changed to fit output. Kernel synthetic
hashes1000..6000 and explicitly constructed source/residual seeds are NOT real
Keccak, a proved reachable Source constructor, source/EVM store equality or compiler
adequacy. Final fresh replay preserves every field, all prior566fields and18
classifications unchanged; total614calls. All30negative suites pass. Final full
wrapper1317default/262TestSuite/131annotations and focused252jobs pass; scoped
audit4626declarations/2780theorems:2705standard-only,75axiom-free, no missing or
unexpected axioms. A synthetic collision control proves each component check can
pass while the actual combined int16/bool byte-overlapping union fails; it does
not assert a real Keccak collision or a language refusal.

Independent read-only finder/skeptic reviews clear; final gate/scoped signature/
axiom/resource/source-commit results and exact artifact paths are retained in
`/workspace/vy2-evidence/combined-dynamic/HANDOFF.md`. Global docs remains rawEXIT1,
48missing/37ambiguous exact-base findings; zero delta is a separate comparison.
Original Y04/Y05/Y06 and Backfill A/B stay partial; Y09.02 stays dependency-blocked.
Broader nested/mapping/storage-bytes/transient/dirty ownership, universal memory/
writeback/shared-zero/interior/pointer forms, reachable allocation/refinement,
concrete V10/V11 agreements, Y06 bindings and actual VY1/assembly MemOK/calculus/
notation/printers/Lean-only rows/source/compiler/joint closure remain mandatory.
Existing owner MemOK/World/ContractWorld/Bridge are available, not Yul adequacy.
YQ1-YQ7 unchanged; original goal BLOCKED unchanged, get_goal read absent; no goal
calls or unpublished producer imports; questions=[]. Independent backfill remains.


### VY2 nested primitive members (2026-11-01)

Additive checked struct-member/root certificates bind actual `E.structFields`,
`E.pathTy`/`rootTy`, active inherited root order and computed active origin. The
single existing packing cursor derives structural `.field` header positions,
slot entry/exit alignment, scalar/fixed-field coordinates, exact leaf enumeration,
end and separation. Full-path integer/scalar header adapters append `.index`
without losing enclosing fields; approved Fixed hashes use the same exact header
preimages. Existing root certificates embed with identical packing/paths.
No owner representation/API, compiler, frontend, manifest or exclusion changed.

`MemberComputedStorage.snapshot` includes enclosing fixed fields/headers once and
ALL live primitive entries from the derived trace. `sourceInventory?` reads each
full-path length from the SAME actual source state. `MemberOwnershipPlan` derives
old/new ownership and couples actual `Source.applyOp` success with the existing
complementary residual update. General `reencode`, `pure_connection`, `old_agrees`,
`following_fresh/raw`, static/prefix/child/enclosing rollback, persistent endTx,
account/bank/unselected-cell/unchanged-store and every-original-H `MemOK` laws apply.
The batch runner preserves exact unsupported-preparation prefixes and source
errors. These are constructive canonical preparation laws, not Yul execution,
constructor reachability, dirty-bit semantics or compiler correspondence.

Premises remain actual successful checked declarations, source-derived length,
canonical codecs/defaults, finite encoding and executable old/new byte/path
separation. No hash injectivity, opaque inverse/view/safety conclusion, cap or
increased proof budget is introduced. HashedLayout stays WORD granular; this is
not V10 agreement or actual transient aggregate declaration layout. Ordinary
Source administration differs from pure unchanged-store preparation.

Inhabited actual `ND` has a struct containing uint16 guard, uint16[] and int24[]
members, bytes3/address siblings, plus a top-level bool[] and marker. Full paths,
partial-slot tails77, nonzero enclosing/data padding, shrink17/11->0/0->18/12,
signed -1, two actual source aliases/bounds/Panic, every-H MemOK and paired frames
are kernel checked. Malformed member/index, missing/duplicate metadata,
nonwrapping, synthetic hash overlap and canonical dirty-bool controls remain
preparation controls. The initial false negative (seed byte1, hence canonical
successful growth) is retained in raw evidence; an ACTUAL unowned-byte2 source/
residual write precedes the corrected unsupported canonical growth. No cleaning,
new refusal/no-op/deallocation interpretation or expected-verdict change follows.

Separate pinned solc0.8.38+1835d247/Osaka legacy+viaIR fixture adds34 ordered calls,
complete33word ABI/status/revert/storage/hash/alias/padding observations, static
failure, successful dirty-bool growth and fresh postfailure reads. 1207 strict
negative mutations include926 coherent bounded-word changes. All prior614 call
fields and18 compiler classifications stay unchanged (648 total calls). Original
100m gas/5m steps and proof/fuel/node/test budgets remain. Kernel synthetic hashes
and seed states are explicitly distinct from real Keccak/compiler constructor
execution. Versions/KeySort, final full/focused/TestSuite/strict/trust/scoped axiom,
reviews/resources and exact committed head are in the versioned handoff:
`/workspace/vy2-evidence/nested-dynamic/HANDOFF.md`. Raw proof failures retained;
field witnesses are factored rather than raising heartbeats (initial field-control
check166s). Global docs is STILL exit1/48missing/37ambiguous; exact-base equality is
separate zero-regression evidence, never a global pass.

Original queue accounting: Y04 partial (one dynamic struct level with primitive
leaves, fixed subaggregates via existing leaf certificates; recursive dynamic,
mapping/storage-bytes/transient/dirty ownership and arbitrary whole-store closure
remain); Y05 partial (universal memory/shared-zero/interior/pointer/writeback and
reachable allocation provenance/refinement remain); Y06 partial (actual source/
Yul input/environment bindings remain); Y09.02 blocked (actual producer execution,
physical calculus/notation/printers/Lean-only rows/final source/compiler/joint
closure). Backfill A/B partial, concrete V10/V11 agreements open. Existing owner
MemOK/World/ContractWorld/Bridge are available, not Yul adequacy. Public Yul exports
remain unavailable at inspected master099bfbe185731c354b12a40f28ccf5d98534c779;
no unpublished producer import. Human YQ1-YQ7 remain authoritative. Original full
goal BLOCKED unchanged; get_goal absent, no goal calls; questions=[]. Independent
work remains; this checkpoint neither completes nor exhausts the original queue.

Identity: repository `/workspace/solidity-lean`, branch
`codex/solidity-inline-assembly5-20261031/vy2-physical`, base
`0b078cefaf7daad79007b87b72df64eb6936420f`, prior reviewed head
`bedad5225f2481e5821e7b1b30a487ed7d1bf2ae`. Final committed SHA and complete exact
theorem signatures/premises/axioms, patch/bundle and cumulative checksums are
recorded in the versioned handoff/evidence. No push/merge/PR or goal mutation.


### VY2 recursive dynamic structs (2026-11-01)

`RecursiveStorageDeclaration`/`RecursiveStorageFields` are ADDITIVE finite
certificates indexed by actual Source type/member lists AND derived Bool dynamic
presence. Expanded structs require true, so all-fixed subtrees retain old leaf
certificates. Actual `E.structFields`/full `E.pathTy` bind metadata and field
order. Hot pack/end/path/header traversals use constant-motive mutual recursors
generalizing both indices and the ONE old scalar packing cursor. Every nested
struct aligns entry/exit; no recursion-depth, root, length or fuel cap is added.
Finite certificates do not claim cyclic metadata or dynamic aggregate elements.

Generic proofs derive complete ordered leaves, exact end, bounds, path/byte
separation and full-path header trace soundness. Bool-only cast invariance and
exact old one-level pack/path/end/header ordering/cursors/kinds/snapshot equality
are proved; actual source inventory agreement retains its real input-view premise.
Every original root certificate embeds with identical packing/paths. Existing
APIs/guards/source representations remain unchanged. New recursive layout traces
feed actual same-state `Source.readLen` at arbitrary finite .field prefixes, then
reuse concrete finiteAccountWrite/Source.applyOp/complement operations. General
whole-map `reencode`, `pure_connection`, old/new ownership and sequential refresh,
static/source-error/None prefix, account/bank/fixed-sibling/alias, paired frame
rollback/commit/endTx and EVERY original-H owner MemOK laws are constructive.
No inverse/read/safety/output-view/adequacy law is a certificate input.

A three-struct O->M->I actual environment derives xs/ys/bs headers2/3/5, nested
uint16/int24/bool primitive leaves, stamp/guard/tag/address siblings, marker7 and
exact root end256. Controls prove 17/11->0/0->18/12, recovered77 and32768/-8388608,
signed-1, actual nested aliases/index Panic, nonzero padding, malformed/truncated
paths, missing/duplicate metadata/coverage, overflow and synthetic hash overlap.
Whole unchanged preparation preserves the ENTIRE administrative Source.Storage,
not just projections. Dirty bool2 remains residual at length3; canonical growth4
is unsupported preparation None with exact successful prefix. External growth
still succeeds. No cleaning/refusal/no-op/deallocation/profile change is inferred.

G0/design finder/skeptic reviews preceded edits and warned of checking cost.
The first monolithic concrete get-of-prepare witness exceeded unchanged200k
heartbeats; ALL raw failures remain. Repaired using named ACTUAL leaf computation
outputs and proved constructor composition, then exact public checked-preparation
equality (`rc_prepared`). No coordinates/result law are supplied as assumptions.
Factored initial controls pass8.6s; no proof/fuel/node/test budget was raised.

Separate pinned solc0.8.38+1835d247/Osaka legacy/viaIR fixture adds34 ordered calls
with COMPLETE40word ABI, all nested header/hash/layout/raw/padding/min-signed/alias
observations, successful dirty growth, full Error(recursive)/Panic0x32, static
failure and fresh postfailure reads. 1405 negatives include1122 coherent bounded
word mutations. The saved final comparison verifies all preceding648 call fields and18
classifications exactly unchanged; the combined total is682 calls. These are FINITE external tests, not source/compiler adequacy,
constructor reachability/store equality, dirty representation or allocation proofs.
Kernel synthetic hashes/seed states remain explicitly distinct from compiler ones.

Final actual versions/KeySort/full/focused/TestSuite/strict/trust/signatures/axioms,
reviews/resource/tested-tree/commit details and patch/bundle/checksums:
`/workspace/vy2-evidence/recursive-dynamic/HANDOFF.md`. Global docs remains ACTUAL
exit1/48missing/37ambiguous, exact-base identical; zero delta is a SEPARATE pass.
No repeated historical failure is relabelled successful. Every previous receipt,
including the earlier false dirty-seed explanation, is retained.

Entire ORIGINAL queue: Y04 and Backfill A/B partial (recursive finite structs
with supported primitive dynamic leaves now constructive; arrays OF dynamic
structs, nested dynamic arrays/mapping/storage-bytes/transient/dirty/general
whole-store/path/hash adequacy remain); Y05 partial (universal memory/writeback,
shared-zero/interior/pointer forms, reachable allocation provenance/refinement,
actual full assembly MemOK); Y06 partial (actual source/Yul input/environment
bindings); Y09.02 blocked (actual VY1 execution/physical calculus/notation/printers/
Lean-only rows/final source/compiler/joint closure). Concrete V10/V11 agreements
remain open. No whole-lane completion or independent-backfill exhaustion claim.
Existing owner MemOK/World/ContractWorld/Bridge exist, not Yul adequacy. Public
master099bfbe185731c354b12a40f28ccf5d98534c779 lacks Yul exports per auditor immutable
tree evidence; the old local object128 is retained and NOT absence evidence.
YQ1-YQ7 unchanged. Original goal BLOCKED unchanged; get_goal absent/no calls;
questions=[]. No push/merge/PR, unpublished imports, owner/admission changes.

Repository `/workspace/solidity-lean`, branch
`codex/solidity-inline-assembly5-20261031/vy2-physical`, pinned base
`0b078cefaf7daad79007b87b72df64eb6936420f`, prior reviewed full HEAD
`9b0b5b4cfa1b2bbe0e79b175ebe6c3b57cebabe2`. Final committed full SHA and exact
public theorem signatures/premises/axioms are checksum-bound in the handoff.
