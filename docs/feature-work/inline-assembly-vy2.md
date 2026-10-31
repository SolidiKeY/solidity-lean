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
