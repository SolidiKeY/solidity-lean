# Metadata binding and zero-declaration observations

The assigned lane was fetched and fast-forwarded to coordinator master
`81512fd7298eb0257a9bcbde9913d10eb8229951`. Original base remains
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The authenticated export records
actual final head, original VM paths, state and hashes. No push, reset,
replacement goal, master change or completion occurred.

## Planner follow-ups

Relative summary paths now resolve against `--baseline`, with canonical absolute
paths in the output. Existing absolute historical evidence paths outside the
baseline remain supported; this is a resolution rule, not path containment.
Summary hashing and JSON parsing consume the same captured bytes. Final checks
still reject subsequent changes to census, inventory, generator, original
sources and summaries. Tests cover relative resolution, a summary changed after
its bytes were captured, and final CLI rejection when a source or summary changes.
All 83 Python tests pass in 25.864 seconds. Two final plan generations are
byte-identical: 1774 modules, 55647 declaration records, nine zero-declaration
modules, zero queries performed by the planner. Finder and skeptic approved the
code without findings. No Lean/model edits were needed for this work item.

## Nine bounded old observations

A separate finite collection inspected all nine original modules with zero own
kernel declarations, rather than inferring absence from that count:

- `Solidity.Yul.CheckedParse`
- `Solidity.Yul.Checks.Arithmetic`
- `Solidity.Yul.Checks.ClosedSyntax`
- `Solidity.Yul.Checks.Contracts`
- `Solidity.Yul.Checks.DeclarationParsing`
- `Solidity.Yul.Checks.Parsing`
- `Solidity.Yul.Checks.Shifts`
- `Solidity.Yul.DeclarationParse`
- `Solidity.Yul.Interfaces.P16`

Every bounded probe passed and its selected declarations/classes/instances/
defaults counts were zero. Raw output, probe reports, sealed observations,
original-kernel coverage checks, exact reproduction command arrays and launcher
are saved under the artifact phase `resume-81512fd72/zero-kernel-metadata`.
Generators are the unchanged committed external `ExportDeclarationMetadata.lean`,
`build.py` and `declaration-metadata.py`; the launcher only orchestrates them.
Initializer execution uses unsafe IO in the external inspector, with no model or
proof dependency. The header flag is self-reported; the prior compiled finite
fixture corroborates initialization behavior without proving it universally.
These observations do not establish absence of generic attributes, public
classification, semantic correctness or new-toolchain compatibility.

Actual tools were Lean 4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b` and Lake 5.0.0-src+797c613.
One process ran at a time with `LEAN_NUM_THREADS=1`, `-j1`, `-M12288`, no swap,
a 12 GiB sampled RSS guard and 4 GiB reserve. Sum of the nine individual probe
walls was 17.683652906 seconds; maximum sampled RSS 1952473088 bytes; minimum
available estimate 15164993536 bytes. This is not an end-to-end clean build or
old/new timing comparison. No Lean 4.35 run or unchanged STOP retry occurred.
Final independent read-only reviews are saved with the authenticated evidence.

## Full remaining assignment and retrieval

All four original checkpoints remain partial overall:

1. Original import/kernel/compiler inventories and clean old build passed;
   selected metadata collection across the remaining corpus and broader API
   evidence remain incomplete. Nine modules were actually queried here; the
   planner's zero-query output is a separate preparation artifact. Prior
   Allocation/fixture evidence remains separately preserved.
2. Official pinned 4.35 migration remains incomplete, including full assigned
   builds and H78 generated public API preservation. Eight Allocation kernel
   differences and two old-only extraConstNames entries remain unresolved.
   Direct new IR lookup of those two names was not performed. No shims added.
3. Common-source clean old/new wall/RSS comparison and root gates remain pending.
   Existing inspection STOP remains +42.8164% wall and +119.6682% RSS; no unchanged
   retry was performed. Historical old timings are not a current-tree comparison.
4. Reviewable cumulative patch, full-history bundle, evidence and hash manifest
   preserve this checkpoint; final API/dependency/root acceptance is unfinished.

Waits remain with root-gate for API/shims/performance, and syntax/hash/backend/
frontend/sortcheck for previously reported producer dependency failures.
Source.Ctor's previously changed proof needs renewed validation. H82 standing
permission for statement-preserving work is not an exact-file approval blocker.
Independent work remains in broader old metadata collection, deterministic
acceptance and explicitly assigned case/witness backfill. No scope expansion,
statement/body/budget/axiom/interface/exclusion change or new trust shortcut.
Old KeySort passed 377/131/131 previously; new Parser String API gate failed.
No RUNTIME_GATE_PASS is claimed. The official pinned 4.35 archive and actual
versions are preserved in historical authenticated evidence.

The complete original frozen rendered assignment, full work/backfill queue and
1777-entry scope remain in sibling `original-rendered-prompt.md`,
`original-work-and-backfill-queue.md`, `exact-scope-manifest.json` and
`prompt-provenance.json`. Original `SHA256SUMS` are unchanged. The cumulative
patch/bundle and copied source tree include these files; `scope-files.json`
records absolute paths and hashes. Prompt provenance distinguishes the
transcription from unavailable launcher bytes. Historical retirement records
were superseded by explicit Nov7 continuations. The original goal remains
unfinished; `get_goal` is not exposed and no replacement is created.

Handoff recipient: `solidity-h62-6-20261106/migrate-root-gate` through coordinator.
Fresh-thread handoff after 3-5 completed items preserves the original goal/VM;
it never launches a replacement or competing continuation. Bulk evidence stays
off git. No H71 lane-push authorization arrived, so nothing is pushed.
