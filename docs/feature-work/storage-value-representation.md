# Typed storage value representation

Assigned branch: `codex/solidity-independent5-20261029/storage-values`.
Exact base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
Repository: `/workspace/scratch/storage-values-assigned`.
Original `/workspace/solidity-lean` checkout is preserved on `work`.

This is a preparation component of G27.01–G27.05, not full source-to-bytecode
preservation. Source reads remain the committed intrinsic `SVal.find`.
The original gap is stated in [storage-hashed-layout.md](storage-hashed-layout.md),
checkpoint 4: `Occ`, `locate` and separation do not relate stored values.
The baseline has no `Solidity/Storage/Representation` module.

## Checkpoint 1

`TypeRep` and `FieldTypesRep` fix layout shapes independently of values.
`ValueRep`, `FieldsRep` and `ElementsRep` relate existing intrinsic source
values to a symbolic word store; they do not execute an encoder to define
source reads. Positive controls: `wallet_represented` (owner plus mapping),
`nested_represented` (two bool-key levels, exceptional nine versus default
seven), `fixed_represented`, `array_represented` (live prefix and shadow).
`wrong_scalar` rejects a mismatching word. `scalar_read` enforces the word.

Supported primitives/keys are precisely existing `PrimTy.bool`, `uint`, `int`;
all occupy full words. Keys use `PrimTy.toWord`, including signed two's
complement, and hence lie below 2^256. `STy` has no packing, bytes/string
short/long headers, string/bytes mapping keys or recursive graph constructor.
No such constructors or cryptographic assumptions were added.

Dynamic live length and total retained extent are both at most `lmax=2^64`;
source `SVal.array` itself allows lengths below 2^256. This is the exact
existing layout coverage boundary, not a claim that every source value is
represented. Array shadows are retained, not silently reset. A mapping's
unused header is unconstrained. `TypeRep.strct` inherits `structDef`, including
its empty fallback for unknown names; it is not source admission validation.
`StoreRep` aliases `FieldsRep` over the existing intrinsic contract-root
`Storage C`; root read/write composition and the separate recursive
declaration graph still require proofs.

Finder and skeptic independently reviewed Model/Controls read-only with no
Lean server. Neither found a false theorem or vacuous witness. Both required
exact axiom pins and explicit bounds/coverage; those are now recorded. Skeptic
requested heterogeneous array order/shadow controls before checkpoint 3;
that remains queued. Headline witness axiom sets are pinned to exactly
`[propext, Classical.choice, Quot.sound]` using `#guard_msgs`.

## Queue and parent obligations

Checkpoint 1: implementation, focused kernel checks, exact axiom pins,
independent finder/skeptic reviews, layer/orphan/trust gates passed. The
doc-path checker exits 1 with exactly the same 46 missing references on the
exact base archive and this head; zero new findings. The inherited gate is
not marked passed. Original-interface-only `tests/storage-values/Gap.lean` passed with explicit
-j1 and a 145059840-byte cgroup peak. Checkpoint 1 is ready for its committed
handoff; whole-assignment validation remains open. Checkpoint 2: scalar/member and nested mapping source saves/defaults and
symbolic other-member frames proved, reviewed and checked; physical finite-run
transport remains checkpoint 4. Checkpoint 3: array reads/writes, header/element frames, exact live/retained
bounds and local nested-path composition proved, independently reviewed
and checked. Checkpoint 4: explicit finite touched-set transport through `Loc.word`,
existing source observations and covered writes/sequences proved, reviewed
and checked. Backfill A: recursive
typed path/graph composition pending. Backfill B: supported full-word normalization, nested alias controls and
stronger finite-run transport/frame laws proved, reviewed and checked. No queue item is waived.

Manifest IDs: `structTypes`, `mappings`, `fixedArrays`, `dynamicArrays`,
`storageLocation`, `storageAliasing`, `deleteMappingTails`, `storageLayout`.
Anchors: `Semantics/Storage/Values.lean` (`SVal`, `SFields`, `Path`),
`Semantics/Storage/Ops.lean` (`find`, `save`, their source laws),
`Storage/HashedLayout.lean` (`STy`, `Loc`, `locate`, `word_inj`),
`Storage/HashedSeparation.lean` (`Occ`, occupied-region frames),
`TypeGraph.lean` and `Semantics/RecursiveStorage/Paths.lean` (recursive graph).

Remaining parent integration includes source admission and graph migration,
allocation, runtime copies, liveness, deletion/recycled mapping tails, packed
layout, unsupported keys/headers, numeric slot compiler changes, pinned EVM
and whole compiler/session composition. Existing numeric-slot, separation,
hash and reserved lanes are read-only; none are reimplemented or imported
from an unmerged lane. No instruction-slice or EVM test is claimed as a
whole-group proof.

## Runtime and evidence

Actual Lean: 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b.
Actual Lake: 5.0.0-src+797c613. Both match the base's lean-toolchain.
User/system systemd scopes are unavailable; managed Docker cgroup v2 was
verified to enforce memory.max=12884901888 and memory.swap.max=0.
The enclosing cgroup is 17179869184 bytes. Builds use LEAN_NUM_THREADS=1
and Lean -j1 through an untracked alternate TOML, with the writer lock.
No Lean MCP tools are exposed. One heavy check runs at a time.

KeySort passed: `Built Solidity.KeySort (1.7s)`;
`Build completed successfully (2 jobs).` Cgroup peak: 139689984 bytes.
RUNTIME_GATE_PASS applies only to this runtime prerequisite. An earlier
`lake build Solidity.KeySort -j1` failed (`unknown short option '-j'`);
-j1 belongs to Lean, not Lake. The corrected alternate-TOML invocation passed.
Model focused build: 21 jobs, peak 614789120 bytes. Controls focused build:
22 jobs, peak 259317760 bytes; only inherited AST unused-variable warning.
Intermediate failed control checks were repaired using committed equation
lemmas for opaque collection operations and explicit intrinsic field indices.

Evidence directory: `/workspace/scratch/storage-values-evidence`.
The task-local `tests/storage-values/run-bounded.py` records commands, exits,
elapsed time, sampled aggregate RSS, actual limits and cgroup peak outputs.
The documentation same-base comparison found 46 missing references on both
base and head, no new findings. Full/import closure remains pending. Scalar
axiom pins initially guessed axiom-free were rejected by Lean; the actual
standard three-axiom sets are now enforced and the final check passes.
Short-check RSS sampling produced no valid samples; JSON records null, not
a zero-memory claim. Cgroup peaks above are actual measured values.

## Checkpoint 2 — symbolic reads, saves and frames

The implemented layer is symbolic: finite physical transport under the
existing per-run region premise is checkpoint 4, not a global injectivity
claim for all mapping entries. `ValueRep.congr`, `FieldsRep.congr` and
`ElementsRep.congr` prove locality to the committed `Occ` footprints.
`scalar_save`, `scalar_frame`, `mapping_read`, `FieldsRep.get`,
`struct_member_read`, `FieldsRep.set`, `struct_source_save`, `struct_save`,
`member_patch_frame`, `mapping_save` and `mapping_path_save` connect the
source operations and whole-value symbolic representation. The last theorem
composes an arbitrary typed inner path given its source-save proof and
represented changed subtree; this is not yet the full graph/path theorem.
`source_frame` reuses the existing source divergence/frame law.

`patch` is a classical abstract subtree update, preserving everything outside
its `Occ` footprint. It is not generated code, allocation or a runtime copy.
Each source equation is proved from the committed source implementation,
separately from representation. Same-type `keyWord_inj` is a full-word
value-encoding fact, including negative signed keys, not hash injectivity.
`word_normalized` and `keyWord_lt` discharge the supported full-word portion
of backfill B without internal packing. New lanes are not dependencies.

Independent controls include a zero mapping default, a scalar save/frame,
a two-level mapping save with written-path read and untouched inner/outer
default reads, and an inhabited Wallet owner update to zero preserving its distinct nine-valued
mapping member. Same-address scalar and nested mapping/array aliases reject the
frame conclusion. `negative_key_word` proves -1 normalizes to 2^256-1;
it uses algebraic normalization after an initial direct decision reached
the unchanged recursion budget. No budget was raised.

Finder/skeptic CP2 reviews found no false theorem or circular semantics.
Both required an inhabited member-save/frame combination and exact axiom
pins; skeptic also requested untouched nested defaults. All are implemented;
both read-only rechecks accepted fixes. Finder additionally requested distinct
post-update member values; the Wallet now writes owner zero while preserving
stash nine. Focused kernel gates and layer/orphan/trust gates pass; doc-path
checks retain the exact-base 46 failures and zero new findings. The typed setter now also
exports `TypeRep` of its replacement layout, avoiding a vacuous/unusable
unknown-layout client obligation. Every pinned CP2 headline has the exact
standard axiom set `[propext, Classical.choice, Quot.sound]`; whitespace in
messages is ignored, axiom content is not.

Resource sampler correction: Docker top requires a PID column; prior
samples were null and are preserved as such. The corrected PID/RSS sampler
measured 743911424 bytes aggregate RSS on the passing CP2 control run;
cgroup peak was 265105408 bytes (shared mappings make these different).
Full final/import closure remains pending. Checkpoint 3 array writes/nested
paths, checkpoint 4 finite numeric transport, and backfill A graph composition
remain open. These symbolic results alone are not full G27 completion.

CP2 final focused gate: `lake -f lakefile.storage-values.toml build
Solidity.Storage.Representation.UpdateControls` passed (29 jobs), 3.139982675 s,
758833152-byte sampled aggregate RSS, 277999616-byte cgroup peak. Exact log
and JSON: `cp2-reviewed-final.log` / `cp2-reviewed-final.json` in evidence.
Checkpoint 1 committed head: `76b1acf4d4204f7bd437fd291f29bb7809825410`.
No full/import-closure pass or final assignment completion is claimed.

## Checkpoint 3 — array representation and source operations

`ElementsRep.set`, `fixed_path_source_save`, `fixed_path_save`,
`array_path_source_save`, `array_path_save` preserve the represented whole
fixed/dynamic value after an arbitrary typed inner-path save. Actual source
reads/saves are the existing implementations. `array_read` includes retained
slots; `array_live_read` separately proves successful live reads.
`fixed_missing`, `array_missing`, `fixed_save_missing`, `array_save_missing`,
`array_live_missing` state exact source failure boundaries: stale aliases
may access retained shadows, normal live reads may not. No word contents
can turn an out-of-range source read/write into success.

`array_header`, `array_header_patch_frame`, `array_element_header_frame`,
`array_other_element_frame` enforce header/element and other-element frames.
`lengthWord` and `array_repartition` prove changing the live/shadow partition
of an identical retained list changes only the header. This is NOT ordinary
`pop`/`delete`: committed source pop may apply defaultOf; no such clearing,
allocation, runtime copy or liveness theorem is claimed here.

ArrayControls independently checks heterogeneous seven/nine elements,
fixed and dynamic saves to zero, the unchanged distinct element/shadow,
header preservation, zero/empty defaults, writes beyond extent, positive live
reads and live-end failure, an actual dynamic/fixed nested-path save, and a
shadow-slot write that preserves live seven/header one while findLive still
fails at the shadow. Exact headline axiom sets are guarded, including the
smaller `[propext, Quot.sound]` set for beyond_extent. Finder identified the
positive-live and shadow-write gaps; both are fixed. Skeptic found no false
source equation or frame assumption and required the explicit repartition
versus pop/delete boundary above. Neither reviewer used Lean/server/builds.
General recursive path/graph closure remains backfill A; physical finite-run
transport remains checkpoint 4.

Passing reviewed control run: 5.280609739 s, sampled aggregate RSS 757862400
bytes, cgroup peak 282734592 bytes; final default/control check passed in 3.689199329 s with 754999296-byte
aggregate RSS and 282992640-byte cgroup peak. Both read-only review rechecks
accepted the source/documentation fixes. Layer/local-import/orphan/trust
gates passed; doc-path findings remain the exact-base 46 with zero new ones. Only the inherited AST unused-variable warning is replayed.

CP3 local import check: all 10 owned modules have zero forbidden frontend or
other-new-lane dependencies (`tests/storage-values/check-local-layers.mjs`).
Base-module membership is checked against the exact assigned commit.

## Checkpoint 4 — finite physical transport and backfill B

`FiniteRun N L R H P touched` bundles exactly the existing `Loc.word_inj`
conditions: H's output range, L≤N, R≤N, `RegionsDisjoint` on the finite P,
per-touched-location `Loc.Bounded`, and every preimage in that location's
`Loc.pres N H` covered by P. It adds no cryptographic premise or global
injectivity. `Transport` relates only these finite touched terms to numeric
words. `FiniteRun.restrict`, `Transport.restrict`, `transport_exists`,
`transport_write`, `transport_sequence`, `transport_extend`,
`sequence_outside_frame`, `transport_patch`, `transport_patch_frames` prove
realization, source-symbolic/numeric write commutation, finite coverage
growth and frames. Coverage growth requires the premise for the extended
run; it is not inferred from a shorter valid prefix.

`transport_patch` alone is an existential finite realization, not an in-place
update from an initially related memory. `transport_patch_frames` supplies
that additional initial-Transport hypothesis and preserves every covered
cell outside the symbolic target plus every word outside the finite image.
`patch_word` identifies scalar patching with one word write.

`source_word_observation` and `source_length_observation` reuse existing
`SVal.obs` and source `find` equations. Their exact boundary is successful
source reads plus independently proved represented leaf/header and touched
coverage. They do not decode source presence, retained extent or liveness
from physical word contents. `source_failed_presence` and
`source_failed_word_default` separately preserve the existing failed/default
source observations, without authorizing an unguarded numeric read. Full
StateExport/decode, compiler bounds checks and liveness composition remain
parent obligations.

The kernel proves a concrete finite run with roots, two mapping entries and
a dynamic data region, N=16, L=2, R=1, three preimages and five touched terms.
H deliberately ignores some arguments, so it is not globally injective. This
small finite witness tests the generic theorem; it is not a Keccak/EVM vector
or a change to the approved 256-bit profile. Source mapping reads use
`mapping_read source_represented`; source mapping save + whole representation
+ numeric write + exact observation commute. A source array header and
primitive element share one transported store. A finite sequence updates two
regions, preserves an untouched entry, and frames outside-address 15.

Negative/combination controls expose omitted conditions: uncovered word 8
may disagree; the committed `Loc.word_data_alias` rejects unbounded offsets;
a collision under H=0 cannot represent distinct seven/nine observations.
The source can report failed presence and a zero/default word while numeric
address 14 contains nine. This explicitly prevents an unearned has/liveness
claim. Exact axiom pins enforce standard sets (the sequence outside-frame
uses only propext; alias refusals use propext/Quot.sound).

Backfill B now includes supported full-word normalization, same-type key
injectivity, nested alias/frame counterexamples, and generic finite
write-sequence, outside-image, patch-frame and coverage-growth laws. No
string/bytes key/header or internal packing work was added. Full word types
need no internal packing under the approved unobservable-physical-layout
abstraction. Backend/numeric-slot/hash separation work remains read-only.

Both read-only CP4 reviews found no false theorem/premise; finder requested
source-save/header/failure controls and exact pins, skeptic requested a
generic outside-image/initial-Transport frame and explicit scope. These are
implemented. Both independent read-only rechecks accepted the fixes. Layer/local-import/
orphan/trust gates pass, with 12 owned import closures and no forbidden or
other-new-lane dependency. Doc-path checks retain the exact-base 46 failures
and zero new findings. Passing focused
run: 37 jobs, 3.679156949 s, aggregate RSS 778084352 bytes, cgroup peak
298176512 bytes. Only inherited AST/Obs.Values warnings replayed; owned files
are clean. Backfill A recursive typed path/graph composition remains open,
as do final full/import-closure and the exact-base inherited-gate comparison.
