# E3 feature citations — schema/checker pass; citation checkpoint pending

Base: `a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e`.
Branch: `codex/plan-e3-feature-citations-1107/e3-feature-citations`.
Checkout: `/workspace/e3-feature-citations`.

## Scope and rules

The initial lease covers the manifest, `scripts/check-feature-citations*`, coverage
plan and `docs/feature-work/e3-*.md`. Coordinator answer E3-Q1 (#167) extends
it to only the schemaVersion assertion in `scripts/solidity-feature-audit.py`
and its compatibility test; all other reader validation remains unchanged. No Lean statements, premises, axioms or
proofs change. H112 requires end-to-end reuse of generic interfaces; H117
requires studying hard problems rather than patching them here. H44 keeps bulk
resolution/census output off git with SHA256 manifests and a deterministic
generator. H136 supplies this disjoint lane; H62/H63 require an isolated branch
and hashed handoff, without lane push, merge or pin edits. No current status
has been upgraded or downgraded at this checkpoint.

## Schema

Each feature row in schema version 2 retains its existing fields and adds a
`theorems` list. An entry has `name` (fully qualified Lean declaration),
`module` (Lean import module), `class` (`a`, `b`, `c`, or `d`), `premises`
(a list of named premises, required and nonempty for class b), and `direction`
(`model` or `model-to-solc`). Classes follow F8: a is kernel-proved against
repository semantics; b is proved modulo named premises; c is finite tested
evidence; d is definition/table evidence. A resolvable declaration alone does
not establish relevance, coverage, or agreement with solc. Empty lists record
an uncited row, never proof of absence. The planned checker must reject a
`present` row with no citation or only class d, and resolve names through an
elaborated Lean environment rather than source-text matching.

All 212 rows now carry empty lists; no names have been invented or claimed
resolved. The schema is reviewable, but is not a passing implementation.

## ESCALATE E3-Q1 — reader ownership

Sources: queue 1's schema bump and existing-reader gate; the sole write scope;
`scripts/solidity-feature-audit.py` line 280 at the base. The reader asserts
`schemaVersion == 1`. Baseline `python3 -I scripts/solidity-feature-audit.py
--check` exits 0 with 212 rows and 783 upstream symbols. Version 2 necessarily
fails this assertion. The reader is outside this lane's permitted writes.

Options:

- A (recommended): authorize only the reader version assertion and relevant
  compatibility test; preserves all validation and permits the schema gate.
- B: keep lane scope; coordinator/another owner adapts the reader and supplies
  an authorized integration base; this lane waits for that dependency.

Neither option changes any theorem, exclusion or premise or waives a gate.
The required question was submitted successfully using `coord-ask` to
`coord-q/codex/plan-e3-feature-citations-1107/e3-feature-citations/20261107T162218Z`.
No lane branch was pushed and no PR was opened.

## Verification and pending queue

Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. Toolchain discovered under the setup activation file;
its default thread count must be overridden with `LEAN_NUM_THREADS=1`.
The serial KeySort command below passes; checkpoint/full builds and
RUNTIME_GATE_PASS are not claimed. No new axiom or sorry; no Lean files changed.

Historical initial state: queue 1 was partial, blocked on E3-Q1. Queue 2
controls passed independently. E3-Q1 is now resolved as recorded below.
Queues 3–6, both required rounds of independent finder/skeptic reviews,
citation classification, checked arithmetic corrections,
model-to-solc gaps, deterministic summary and CI fragment remain pending.
No semantic citation review is claimed for empty lists. No proof or external
test result has been converted into a coverage claim.

The attached off-git evidence contains baseline and changed-reader outputs,
path-check output, original patch and checksum manifest. Existing readers
beyond the demonstrated conflict have not been certified. `get_goal` is not
exposed by this runtime; the existing persistent objective was preserved and
no second goal was created.

## Checker checkpoint and controls

`python3 -I scripts/check-feature-citations.test.py` runs real Lean integration
controls using `Solidity.KeySort.le_refl` in artificial fixtures. This is not a
Solidity feature citation. Twelve tests cover positive resolution, repeated
byte-identical positive output, absent citation/name, misspelling, class-d-only
present evidence, absent module, wrong owning module, definition masquerading as
a theorem, missing b premises, injection, and both row-cell counting cases.

The checker runs serial `lake env lean -j1 -M8192 --tstack=131072` queries outside
the repository, sets `LEAN_NUM_THREADS=1`, checks declaration presence, owning
module, and theorem kind for a/b. Import artifacts must already be built with
the pinned toolchain; it fails closed when they are unavailable. Class c/d
entries may name a declaration recording tested or definitional behavior; class
c is not promoted into an all-input kernel theorem.

Actual bounded preparatory command (exit 0, no diagnostics):

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 --tstack=131072 \
  -o .lake/build/lib/lean/Solidity/KeySort.olean Solidity/KeySort.lean
```

A writer lock surrounded this and all writes/Lean controls. No Lean source was
edited. Output in the attached `KeySort.log` is empty on success; the recorded
shell output was `KeySort-exit:0`. Controls initially caught a wrong Lean API
(`Name.fromString`); correction to `String.toName` made positive and negative
controls pass. A final rerun includes the 8 GiB Lean memory cap.

`rowCells` counts each row once per current/class/direction cell; cells overlap
when a row cites multiple classes or directions and must not be summed as a
partition. Model-only, model-to-solc and uncited top-level row counts are a
partition. No final-manifest metric is published: all lists remain empty,
so the final-manifest checker correctly fails at the first present row.

Read-only checkpoint reviews (no Lean server): independent finder
`schema_finder` confirmed unchanged existing fields/statuses and correct query
and summary logic; its request for a mixed-direction test was implemented.
Independent skeptic `schema_skeptic` confirmed the reader blocker and found no
bypass of the requested checker gates. A valid unrelated declaration labeled c
can still pass; theorem relevance, finite-test evidence, and completeness of
named premises require the required later human/agent citation reviews. These
checkpoint reviews do not discharge the queue 3 and queue 6 review obligations.

Documentation path gate: `bash scripts/check-doc-paths.sh` exits 0, all cited
Lean paths resolve (143 existing ambiguous references). Structural comparison
confirms exactly version 1→2 and 212 empty lists, without changes to existing
fields. `git diff --check` passes. No current downgrades yet; class and direction
citation counts are all zero, and all 212 rows remain uncited.

## Coordinator CI registration fragment (pending integration)

Place after the existing library/example artifact build and before publication;
the final-manifest gate is expected to fail until later citation checkpoints.
This fragment is supplied for review, not installed in any workflow.

```yaml
- name: Check feature theorem citations
  env:
    LEAN_NUM_THREADS: '1'
  run: |
    python3 -I scripts/check-feature-citations.test.py
    python3 -I scripts/check-feature-citations.py
```

## Blocked handoff

The ordered schema compatibility checkpoint remains failed at an out-of-scope
reader assertion. Checker development and controls were completed as independent
work; no citation checkpoint or full-assignment completion is claimed. Resume
at E3-Q1 ownership resolution, pass queue 1's reader gate, then perform queues
3–6 in order. Recheck schema compatibility after any forced status downgrade:
the old generator also renders current statuses into out-of-scope artifacts.

Artifacts are at `/workspace/e3-feature-citations-evidence`: `original.patch`,
`handoff.md`, `e3-feature-citations.bundle`, and `SHA256SUMS` describe the exact
committed checkpoint. No task branch was pushed or merged. The only push was
the explicitly required question ref. Bulk evidence is outside git.

## E3-Q1 resolved — coordinator answer #167

The coordinator selected A: the lease now includes the reader's schemaVersion
assertion and a compatibility test; no other validation may change. The reader
accepts versions 1 and 2 via a single assertion change. The compatibility test
`python3 -I scripts/check-feature-citations-compat.test.py` validates the exact
base version-1 manifest and current version-2 manifest, verifies unchanged
rendering for the citation extension, rejects unsupported versions, and confirms
missing evidence still fails both versions. No other reader logic changed.
Earlier blocked-checkpoint sections above record historical results; E3-Q1 is
resolved. Citation population and its final gates remain pending.

## Active state after reader compatibility checkpoint

Coordinator E3-Q1 (#167) is fully implemented at
`23afe15b178b2726fc44a1412a806c5670a6e83f`: one assertion change, five passing
old/new compatibility tests, and `solidity-feature-audit.py --check` passing
(212 rows; 783 upstream symbols; generated files current). Independent read-only
finder `schema_finder` and skeptic `schema_skeptic` both confirm the exact
one-line reader change, no weakened other validation, and meaningful old/new
controls. Both ran the five tests successfully; neither used a Lean server.
No findings remain for this reader checkpoint.

Additional existing consumers were run at both this lane and an isolated clean
worktree at the exact base (`/workspace/e3-reader-baseline`). G00 scope check
and source-grammar check pass identically. G03 `--check` reports the same stale
ledger Markdown/JSON at both base and lane; this baseline failure was not fixed
or hidden. Other corpus-dependent readers remain uncertified.

### ESCALATE E3-Q2 — generated metadata ownership

Sources: queue 3's forced downgrades; F8's definition-only `boolType` evidence;
`render_lean_info`, `render_report` and the unchanged generated-output reader
gate; sole write scope plus E3-Q1 (#167). A dry-run of only `boolType` from
`present` to `partial` changes generated `Solidity/Language/FeatureInfo.lean`
and `docs/solidity-feature-inventory.md`. The generated scope module stays
identical. Both changed outputs remain read-only: E3-Q1 permits only the
reader assertion and compatibility test. No status or generated file has been
changed. The complete example diff is saved off git as
`Q2-generated-downgrade-example.patch` in the evidence directory.

Options (neither waives compatibility or changes an exclusion/premise):

- A: extend this lease solely to regenerating metadata in those two outputs
  for audited manifest downgrades; no theorem statements/proofs or other
  reader validations may change; review the exact generated diff.
- B: retain coordinator ownership; coordinator supplies a regeneration commit
  for the final audited manifest and authorizes incorporating it before the
  final reader gate.

Submitted successfully using `coord-ask` to
`coord-q/codex/plan-e3-feature-citations-1107/e3-feature-citations/20261107T163438Z`.
This is the active scope dependency; E3-Q1 must not be reopened.

Queue 3 has read-only source research for all 13 present rows and the actual
checked-arithmetic guard interfaces. Candidate names are not yet elaborated or
entered in the manifest, and are not claimed as resolved citations. Six F8
rows have definition-only backing: booleanLiterals, timeUnits, boolType,
parentheses, msgSender, blockTimestamp. Their reassessment must not be evaded
by relabeling definitions as tested or kernel-proved. All 212 citation lists
remain empty; class/direction totals remain zero. The final checker correctly
fails on uncited present rows. Queues 3–6 and their required reviews remain
pending; no statement/proof/source change or RUNTIME_GATE_PASS is claimed.
