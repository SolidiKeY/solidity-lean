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
handoff; whole-assignment validation remains open. Checkpoint 2: scalar/member,
nested mapping writes/defaults and other-member frames pending. Checkpoint 3:
array reads/writes/headers/bounds/nested paths pending. Checkpoint 4: explicit
finite touched-set transport through `Loc.word` pending. Backfill A: recursive
typed path/graph composition pending. Backfill B: full-word normalization and
stronger alias/frame/finite-run controls pending. No queue item is waived.

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
