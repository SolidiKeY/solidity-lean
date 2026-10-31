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
| Y04 | Existing HashedLayout slot interpretation; intrinsic field widths; read/update/low/high/unchanged/bounded-word arithmetic; typed canonical codec/region reconstruction; residual bytes and raw slot updates; actual source reset/rollback controls | Full typed storage packing codecs/layout for all source aggregates/paths, dirty/noncanonical owned bits, derived source view instance and typed writeback, persistent/transient residual journal/reset, VY1 sload/sstore/tload/tstore composition, V10 agreement instance |
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
