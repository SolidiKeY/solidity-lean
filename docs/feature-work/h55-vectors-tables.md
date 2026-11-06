# H55 vectors and tables: inventory preparation

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. The 2026-11-02
coordination correction makes existing producer and consumer files read-only
migration inputs until an explicit owner handoff transfers the exact files.
This preparation changes no such input.

`python3 scripts/h55/vectors-tables/vector_census.py` checks the complete bytes,
count and sequential declaration names of nine frozen vector modules against
`tests/h55/vectors-tables/vector-manifest.json`. It reports 6,903 declarations.
The nine SHA-256 values were independently compared with the corresponding Git
blobs at the stated base. The manifest contains hashes and metadata, not bulk
vector data. `python3 -m unittest discover -s tests/h55/vectors-tables -p
"test_*.py" -v` passes missing, extra, order, schema and altered-output negative
controls as well as the full inventory check.

This is an integrity census, not the requested generator, an independent EVM
oracle, or a Lean proof. Source equality alone proves no opcode semantics.
The full generator, deterministic reproduction, lossless generation, compile,
Raw family case accounting and validation, table migration patches, timings,
KeySort and full affected-module gates remain outstanding. A filename census
finds 102 tracked `Solidity/Yul/Raw*.lean` files; that is not case accounting.
The independent finder and skeptic reviews remain outstanding. No runtime
pass is claimed. Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613 were observed.
No cache pack or full export has yet been created. The H58 hold remains in force.

## Additive codec preparation

`vector_codec.py extract /workspace/scratch/h55-vectors-tables/vectors.json`
extracts structured rows from the authenticated frozen files, and `check` renders
all rows and compares each complete output file byte-for-byte with its input.
A second independent invocation produced identical data bytes. The off-Git bulk
file is `/workspace/scratch/h55-vectors-tables/vectors.json`; its SHA-256 is
committed in `tests/h55/vectors-tables/bulk.sha256`. The four Python tests pass,
including per-file missing, extra, reordered, malformed schema and changed-output
controls. The extracted expected results are transcribed from the originals;
this neither validates the arithmetic oracle nor substitutes for kernel checks.
The codec is preparation, not acceptance of the full requested generator.

A KeySort prerequisite check ran with `LEAN_NUM_THREADS=1`, Lean `-j1`,
`--tstack=131072`, the repository writer lock and a preflight 4 GiB available
memory guard. It exited 0 in 1.634 seconds with no diagnostic output; log:
`/workspace/scratch/h55-vectors-tables/keysort.log`. An initial attempt did not
run Lean because `/usr/bin/time` was absent; the successful retry used the shell
timer. No whole-task runtime gate, compile, speed comparison or review is claimed.

## Emitted modules: serial Lean check

`vector_codec.py emit` checks all records against the authenticated original
bytes, then writes nine Lean files to a new directory outside the checkout. It
refuses an existing destination. End-to-end tests verify complete emitted bytes,
no overwrite, and refusal of a changed result before creating the destination.
The five Python tests pass. The 30 WordTable parts contain 439 theorem
headings; the 45 FixtureControls files contain 45. These preliminary counts are
not exact migration case accounting or an owner-approved patch.

`PYTHONDONTWRITEBYTECODE=1 python3 -u scripts/h55/vectors-tables/compile_vectors.py`
compiled the six local imports and all nine emitted modules, serially, using
Lean 4.24.0, `LEAN_NUM_THREADS=1`, `-j1`, `--tstack=131072`, and a guard of
4 GiB against both available host memory and cgroup headroom. Full command and
per-file outcomes are in `/workspace/scratch/h55-vectors-tables/compile.log`.
The first attempt failed because the generated source was outside the default Lean
root; `/workspace/scratch/h55-vectors-tables/compile-attempt1.log` retains
that failure. The successful retry supplies an explicit root and strengthened
the memory guard. No source theorem or owner file was edited. This validates the
emitted declarations against these freshly built imports, not universal opcode
agreement, full acceptance, or a whole-repository build.

The isolated object cache is `/workspace/scratch/h55-vectors-tables/lean-objects.tar.gz`;
its SHA-256 is recorded in the external handoff checksum manifest. The baseline
and post-migration speed comparison, independent finder and skeptic reviews,
exact Raw case accounting, table migration patches and production owner
handoffs remain pending. The current compile timings are not that comparison.

## Fixture control generator preparation

`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h55/vectors-tables/fixture_controls.py
check` reproduces all 45 complete StatementGrammar FixtureControls modules and
checks the ordered 45 corresponding definitions in FixtureData. `emit --output`
writes to a new directory outside the checkout. A committed manifest pins the
FixtureData bytes and every control file; their hashes were checked independently
against the base Git blobs. Missing, extra, wrong-position, changed proof schema,
and missing/renamed fixture definition controls pass. Seven Python tests pass
across both vector and fixture helpers. This preparation does not edit owned files,
provide a production migration patch, compile these fixture controls, or prove
anything beyond the stated byte and inventory comparisons. WordTable migration,
actual owner handoff and full acceptance remain pending.

## WordTable proof extraction preparation

`word_table.py` extracts 30 pinned parts into external structured proof text and
renders all 439 complete theorem declarations and module bytes. A second extraction
was byte-identical. The bulk JSON and emitted files are under
`/workspace/scratch/h55-vectors-tables/`; the committed `word-table-bulk.sha256`
pins the JSON. All 30 source hashes match the published base Git blobs. Negative
controls cover missing, extra, reordered and malformed entries and changed proof
text. The first schema matched only 438 headings because it omitted
`table_prefix_root`; the full-count test failed and the corrected schema rejects
unrecognized theorem headings. Attempt-one data and manifest are preserved in
that scratch directory. This transcribes proof bodies, does not synthesize them,
compile them, or provide an owner-approved production migration patch.

## Raw source census preparation

`raw_census.py` pins all 102 Raw source files and records eight inductive headings,
20 recognized constructor headings, and 1,839 candidate branch lines. Detailed
line records are off Git at `/workspace/scratch/h55-vectors-tables/raw-census.json`,
with a committed checksum; a second extraction matched byte-for-byte. All 102
source hashes match the published base. Negative controls exercise missing and
extra files, missing, extra, changed and reordered-looking branch declarations,
and a changed family schema. The candidate-line scan is textual and may include
non-case syntax or omit cases not written at line starts. It does not establish
semantic case accounting or prove that any parametrisation preserves behavior.
All source-file migrations, meaningful Lean validation and owner handoffs remain
pending. Eleven Python tests passed after the WordTable correction.

## H70 table annotation proposals

`table_proposals.py` produces two exact owner-reviewable patches without writing
to the owner files. The WordTable proposal adds one provenance comment in each
of 30 parts; the FixtureControls proposal does so in each of 45 controls. The
patches are `/workspace/scratch/h55-vectors-tables/word-table-annotation.patch`
and `/workspace/scratch/h55-vectors-tables/fixture-controls-annotation.patch`.
Their hashes are committed in `table-proposals.sha256`. Both apply-check against
the frozen sources and repeated generation produced identical bytes. Tests show
that removing each proposed marker restores the exact source, including all
proofs, assumptions, imports and observations. These annotations do not migrate
the tables or replace proof generation; substantive migration patches and Lean
validation remain pending owner coordination. No owner files were edited.

## H70 Raw lexical token accounting

`raw_tokens.py` scans all 102 pinned Raw files for pipe and `case` occurrences
outside line comments, nested block comments and strings. It records 1,933
occurrences with line and column locations in the external
`/workspace/scratch/h55-vectors-tables/raw-tokens.json`; a second extraction
matched and its checksum is committed. Tests cover comments, nested comments,
escaped strings, inline occurrences, malformed input and missing, extra and
reordered tokens. This scanner is not the Lean parser: occurrences are not all
semantic cases, and exact semantic case coverage and meaningful Lean validation
are still pending. Current master includes an additional RawFrameLogic module
and changes RawFrame and RawBoundary, so this 102-file frozen census is not a
claim about the updated master inventory. Sixteen Python tests pass.
