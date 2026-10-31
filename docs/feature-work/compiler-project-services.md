# Compiler projects and editor services

Version 0.5 connects the ordinary compiler command and persistent Solidity LSP
to the existing complete compilation-unit format. Imports preserve every original
AST, source ID, digest, pragma and resolved import target. No concatenated AST or
single-source provenance substitutes for a multi-file compilation.

The shared resolver follows relative imports, longest prefix/context remappings,
include roots and cycles. Open buffers override disk by canonical file identity,
including symlinks; conflicting aliased buffers are rejected. A one-source self-import
still has no proof-admission adapter. Compilation units
are bounded to 256 files/16 MiB. Source changes invalidate analysis, cached proofs,
diagnostics and Testing rows of importing documents, including in-flight work.
Verification rechecks dependency snapshots before publishing. The CLI checks all
dependency digests around proof runs.

## Specifications and compiler scope

Multi-file contract-local specifications use the existing declaring-contract
namespace. They are admitted only when the entire unit has no file-level variables
or enum/struct/UDVT declarations. The producer checks that each original custom
specification comment belongs to a contract or member-function documentation span.
Lean independently tracks structural ownership from the root source-unit array to
direct contracts and their direct functions. Duplicated IDs, nested units/arrays
and metadata cannot create annotation ownership.

Native regressions prove true imported-library postconditions, preserve distinct
private constants with the same name, and refute an exact false postcondition
with a kernel-checked certificate. A separate native Lean check bypasses the
producer and rejects six forged ownership/global/nominal fixtures.

Multi-file loop annotations, free-function/global/nominal specification namespaces,
mixed legacy ABI inheritance and schema-2 compiler-code constants remain explicit
admission gaps. Valid Solidity outside this proof profile still gets language
services; no unsupported proof is presented as verified. This extends source
admission without new calculus rules, axioms or larger proof budgets.

## Editor behavior

- Completion uses compiler receiver types for named/field receivers, contracts,
  structs, enums, arrays, addresses and compatible library extensions. Incomplete
  code uses live-text declarations in the current file. Imported receivers during
  a parse error and complex call-result inference remain limited.
- Definitions, references and symbols preserve foreign file locations. Workspace
  searches inspect up to 10,000 source paths and compile at most 256 matching
  roots, with cancellation and explicit bounds.
- Rename preserves indexed versions and source hashes, searches reverse importers,
  recompiles every edited root and rechecks all original snapshots. Dependent
  compiler errors block rename. Specification-text renames still require a manual
  update.
- Formatting preserves strings, comments, prefixed literals and scientific
  notation. For valid inputs it recompiles the result and checks specification
  attachment. A change to loop-annotation attachment is rejected.
- Quick fixes offer explicit SPDX choices and safe removal of unused parameter
  names/primitive locals. Ordinary NatSpec and custom-specification references
  prevent destructive removal. Foreign diagnostics retain related source locations
  and cannot offer a main-file license fix.

With multiple workers, the server first reads the checked obligation list and
schedules exact function signatures through the shared bounded pool. Each result
must match its selected contract/signature. Failure cancels sibling tasks.
Assertions within one function remain one proof task; mixed audited/non-ready
reports retain the sequential audit path. This is function scheduling, not
assertion-level proof splitting or declaration-level proof caching.

## Read-only reviews

Finder and skeptic reviews identified symlink buffer identity, remapping order,
stale secondary rename ranges, omitted reverse-importer validation, imported
error locations, invalid literal whitespace, missing importer/UI invalidation,
ordinary NatSpec quick fixes, audit-row aggregation and annotation attachment
under admission gaps. These were fixed with focused and native regressions.
The source-admission review also caught numeric-ID-only annotation authorization;
it was replaced by structural ownership, with direct Lean negative tests.

## Final validation and measurements

The [validation record](../../tests/editor-parity/compiler-project-validation.json)
retains 134 passing combined tests, five passing focused CLI regressions, 40
native VS Code checks, the 263-target API build, native metadata diagnostics and
a zero-finding trust audit. Both pinned compiler versions were exercised.
Two old CLI expectations were reconciled with the current backend: captured
reference-copy ordering is proved, while an out-of-bounds indexed read is lowered
and pending. The previous and current compiler produced byte-identical fixtures
for both controls; no proof rule or budget was changed to obtain these results.

The [measured report](../../tests/editor-parity/compiler-project-baseline.md)
contains 20 isolated editor launches, including four warmups, with no broken
scenario. Each worker setting has three measured repetitions. One-worker local
median initial/incremental verification was 6.35/5.07 s; two-worker local medians
were 6.47/3.51 s. Thus function scheduling helped changed-buffer verification on
this fragment while listing/startup costs kept cold latency similar. The matching
Dafny medians were 1.18/0.246 s and 1.07/0.264 s. These remain end-to-end editor
comparisons, not pure solver timings or general parity.

Local exact-snapshot cache medians were 133/170 ms for one/two workers. Two-file
verification medians were 8.40/5.33 s. Cache hits, changed-source checks and
cross-file throughput are separate operations. Three repetitions are descriptive;
no stable tail-latency or general speedup claim follows.

Final native validation also caught delayed dependency notifications cancelling
fresh requests. UI invalidation now clears stale rows without aborting a new
request; the server owns cancellation. Duplicate filesystem events with unchanged
bytes preserve proofs, while version-only changes refresh navigation metadata.
A compiler-code proof-admission gap likewise preserves analysis/navigation
without producing a proof artifact.
