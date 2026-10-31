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
`Storage C`; whole-contract transition composition remains a parent
obligation. The separate recursive graph observation extension is proved below.

Finder and skeptic independently reviewed Model/Controls read-only with no
Lean server. Neither found a false theorem or vacuous witness. Both required
exact axiom pins and explicit bounds/coverage; those are now recorded. Skeptic
requested heterogeneous array order/shadow controls before checkpoint 3;
that is discharged by checkpoint 3. Headline witness axiom sets are pinned to exactly
`[propext, Classical.choice, Quot.sound]` using `#guard_msgs`.

## Queue and parent obligations

Checkpoint 1: implementation, focused kernel checks, exact axiom pins,
independent finder/skeptic reviews, layer/orphan/trust gates passed. The
doc-path checker exits 1 with exactly the same 46 missing references on the
exact base archive and this head; zero new findings. The inherited gate is
not marked passed. Original-interface-only `tests/storage-values/Gap.lean` passed with explicit
-j1 and a 145059840-byte cgroup peak. Checkpoint 1 is committed and reviewed. Checkpoint 2: scalar/member and nested mapping source saves/defaults and
symbolic other-member frames proved, reviewed and checked; physical finite-run
transport remains checkpoint 4. Checkpoint 3: array reads/writes, header/element frames, exact live/retained
bounds and local nested-path composition proved, independently reviewed
and checked. Checkpoint 4: explicit finite touched-set transport through `Loc.word`,
existing source observations and covered writes/sequences proved, reviewed
and checked. Backfill A: recursive
typed path/graph composition proved, reviewed and checked below. Backfill B: supported full-word normalization, nested alias controls and
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
base and head, no new findings. Full/import closure subsequently passed in final validation. Scalar
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
At this checkpoint, array writes, finite transport and graph composition were
still queued; all are discharged below. Symbolic results alone do not establish
full source-to-bytecode preservation.

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
are clean. Backfill A and final full/import-closure are discharged below.
The inherited documentation comparison is recorded separately from source completion.


## Backfill A: recursive typed graph paths

GraphLayout, GraphFrames, GraphRepresentation, GraphCompatibility and GraphControls
extend the component through the committed TypeGraph.Path/Value abstractions.
inlineSize uses the existing well-founded inline rank, not a public path-depth
cutoff. Apart.observe_save proves arbitrary divergent-path source frames;
ancestor_header_frame separately handles a header above a saved array element.
Represented.prefix composes arbitrarily long successful typed paths.
Represented.write_frame requires source Apart and explicit symbolic nonalias;
no new graph separation premise is silently derived. Represented.numeric composes
covered observations with the same finite-run transport. Query compatibility is
query-local: word queries do not certify bounds of every intermediate array;
length queries certify the observed terminal header only. This is deliberately
weaker than whole ValueRep, with an oversized-header rejection control.

inlineSize_legacy, keypath_subvalue_rep, keypath_word_represented and
keypath_header_represented bridge existing whole legacy values and arbitrary
committed Legacy.KeyPath mapping chains. The inhabited recursive schema has a
uint field and a mapping back to itself. Controls prove default reads and
representation at every natural depth, a concrete depth-three source save,
other-branch and failed-read frames, ancestor-header preservation and a two-branch
numeric combination under an inhabited finite region premise. Aliasing the
written path cannot frame its old value. Index/header bound refusals are explicit.

Whole recursive graph value migration, automatic graph compiler separation
certificates, source StateExport/decode, runtime copy/allocation/liveness and
full source-to-bytecode composition remain integration obligations. This
component does not claim those parent groups complete. Backfill B remains
full-word normalization and finite-run strengthening as recorded above.


## Final graph review and diagnostics

All Work checkpoints 1–4 and backfills A/B are implemented. The component
retains the exact success/coverage/nonalias boundaries above; parent integration
obligations are not missing assigned component proofs. Both independent read-only
finder and skeptic accepted the final graph source and all requested additional
axiom guards. Neither reviewer used Lean, a server or a build. Their prior
findings and fixes were: query-local versus whole-value bounds (documented with
oversized controls), committed legacy word/header bridges (added), separate
ancestor-header framing (added), inhabited two-branch numeric transport (added),
and exact new headline axiom pins (added and kernel-checked).

`ancestor_observation_frame` and `ancestor_header_frame` pin exactly propext;
`inlineSize_legacy` pins propext/Quot.sound. The legacy subtree/word/header
bridges, represented ancestor header frame and recursive numeric combination
pin exactly propext/Classical.choice/Quot.sound. No new axiom or proof-budget
override was added. `graph-guards-final` passed 51 jobs in 5.229277274 s;
sampled aggregate RSS 777736192 bytes, cgroup peak 307044352 bytes.

No Lean MCP was exposed. The task-local `check-files.py` therefore ran serial
`lake -f lakefile.storage-values.toml env lean --tstack=131072 -j1 FILE` on
all 17 owned modules, the independent gap fixture and Solidity.lean. All 19
files passed cleanly, without warnings, in 28.520272533 s; sampled aggregate
RSS 1521823744 bytes, cgroup peak 1942282240 bytes. This checks kernel
elaboration; it is not an external compiler or Keccak/EVM vector test.

The original `./run-lean.sh` completed with exit 0: default/import closure
768 jobs, TestSuite 262 jobs, and real SolKey check parsed 377 taclets,
131 read-bearing, table covers 131, annotations match the configured rules.
Derived17 actually passed in 145 s under the cap; no historical OOM waiver was
used. Cgroup peak was 12884901888 bytes, memory.events max=2291 but oom=0,
oom_kill=0, oom_group_kill=0. Recovery RSS samples reached 11589025792 bytes;
earlier client sampling was interrupted and is not claimed complete. VM transport
interruptions left the same original container running; read-only reattachments
preserved earlier logs and collected its terminal exit. No duplicate build,
other-session kill, goal reset, VM replacement, push, merge or PR occurred.


## Final handoff

All assigned checkpoints and backfills are done. Final source gates pass;
no theorem, refusal, source observation, target predicate, approved profile,
packing exclusion or proof/test budget was weakened. Final cached full gate
passed in 8.400015830 s (RSS 2053373952 bytes, cgroup peak 3816939520 bytes).
The prior cold full gate is also retained; its terminal Docker exit was 0.

| Gate command | Final result and decisive evidence |
|---|---|
| `lake -f lakefile.storage-values.toml build Solidity.KeySort` | Pass; actual runtime versions and passing output above. |
| `lake -f lakefile.storage-values.toml build Solidity.Storage.Representation.GraphControls` | Pass; exact headline guards, inhabited positive/negative/combination controls. |
| `python3 tests/storage-values/check-files.py` through the bounded runner | Pass; 19 clean per-file checks, including all 17 owned modules. |
| `./run-lean.sh` via `bash tests/storage-values/final-gates.sh` through the bounded runner | Pass; 768 default jobs, 262 TestSuite jobs, 377 taclets/131 annotations match. |
| `node scripts/check-layers.mjs` | Pass; 168 core modules, zero reach elaborator. |
| `node tests/storage-values/check-local-layers.mjs` | Pass; 17 owned modules, zero forbidden/other-new-lane dependencies. |
| `node scripts/check-orphans.mjs` | Pass; 783 reachable, zero orphaned/not allowed. |
| `bash scripts/check-trust.sh` | Pass; 798 sources, 241 inventoried sites, zero findings. |
| `bash scripts/check-testsuite.sh --complete --solkey tests/migration/solkey/keyext.solidity.examples` | Pass; 564 functions = 552 derived + 11 refuted + 0 pending + 0 divergent + 1 excluded; 2 skips. |
| `node scripts/check-automatic.mjs --strict --build-log /workspace/scratch/storage-values-evidence/full-gate-recovery3.log` | Pass; 491 automatic + 61 with a step budget, 0 manual; 11 refuted, 0 pending; all 26 timed TestSuite modules within unchanged 300 s budget. |
| `bash scripts/check-doc-paths.sh` | Raw exit 1 on exact base and head: 46 missing plus 24 ambiguous references each, zero new findings. This inherited debt is not reported as a raw pass. |
| Task-document relative links and staged whitespace | Checked separately in final evidence. |

The first separate TestSuite parity attempt used the external setup copy,
which lacks a sibling pin file; it failed ENOENT before auditing. Rerunning
against the repository's pinned snapshot passed without changing inputs.
The final runner reproducibility check initially refused insufficient enclosing
headroom (about 3.2 GiB filesystem cache, no Lean running). Only own idle
build-file pages were released with fsync/POSIX_FADV_DONTNEED; disk artifacts
were retained, no global cache drop or limit change occurred. The unchanged
preflight then passed, and the focused check passed in 2.707287413 s. Failed
attempts remain evidence rather than invented passes.

The private alternate TOML is reconstructed from tracked project settings by
run-bounded.py; it adds only Lean -j1, preserving all proof and stack budgets.
The assigned branch starts at the exact stated base. Earlier committed heads:
CP1 76b1acf4d4204f7bd437fd291f29bb7809825410;
CP2 3331fe4703c76f5e00882b7cb616b8b43925882c;
CP3 c360d104012547a94a6c55fa3575a9b3bef54d2f;
CP4/B 32c04ef8aa27e8af0bf1d84f1104d9376f6c5816.
The graph checkpoint is the commit containing this section. Its full SHA,
complete file inventory, absolute patch/handoff/evidence/checksum paths and
elapsed wall time are recorded in the external handoff bound to committed HEAD.
No scope question remains. Parent obligations listed above remain open as
integration work, not as claims discharged by this preparation component.

Elapsed wall time from earliest saved task evidence (cp1-controls.log) to final handoff preparation: 15605.556 seconds, including VM/transport interruptions.


Reproduction requires caller-held writer ownership; run-bounded.py supplies the
resource cap, not the lock. Every recorded Lean invocation used the outer flock.
For example, the exact full-gate invocation is:

```sh
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 tests/storage-values/run-bounded.py final-full-gate bash tests/storage-values/final-gates.sh
```

Use the same outer flock for the per-file command (inner command:
`python3 tests/storage-values/check-files.py`) and focused targets. The per-file
checker now rejects warning/error diagnostics as well as nonzero exits; the
saved final 19-file pass was warning-free before this strengthening too.


Final strengthened per-file rerun passed all 19 files, explicitly rejecting any
warning/error output, in 27.519333580 s; RSS 1344344064 bytes, cgroup peak
2229149696 bytes. Both final read-only reviewers accepted the external-lock
clarification and stricter diagnostic checker; no confirmed source, runner,
pin or documentation finding remains. Final source code is unchanged since
the successful full/import-closure run. Only the final handoff and diagnostic
runner documentation/strictness were updated afterward.

## Combined integration repair (2026-10-30)

Retained review found missing explicit result types on `Store` and `WordStore`.
Both abbreviations now declare `: Type`; their bodies, all proofs and budgets
are unchanged. Sequential per-file Lean MCP diagnostics for Model and Transport
completed with no diagnostics. Independent read-only finder and skeptic reviews
used no Lean server and cleared the focused repair.

The earlier backend-failure documentation ambiguity is already repaired by
the qualified `Solidity/Backend/Failure/Gap.lean` reference. The strict doc-path
check still exits 1 with exactly the retained baseline output: 46 missing
references and no new findings. Combined gates remain the coordinator's check.
