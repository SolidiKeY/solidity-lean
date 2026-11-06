# H62 item 1: duplication scanner (partial prototype)

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. This is the first,
incomplete scanner checkpoint. It is not a complete audit, proof, ownership
decision, or RUNTIME_GATE_PASS.

`scripts/h62/item1/duplication-scanner/scan.py ROOT GLOB... [--owners JSON]
[--registry JSON] [--previous REPORT]` emits deterministic JSON, including input
hashes, recognized declaration inventory, lexical statement and body leads,
rejection reasons and incremental input/configuration changes. An unmatched glob
fails. Missing ownership is unknown; registry path, directory and glob references
are advisory and may be stale. A path-to-owner JSON file provides explicit
labels, not a grant to edit. Every statement lead retains
`intrinsic-signature-unresolved` and `ownership-requires-live-verification`.
Context hashing distinguishes some namespace/import differences; it is not
Lean name resolution. Confirm elaborated signatures and current ownership before
acting. No lead is identified as unowned.

The scanner is a conservative lexical prototype, not a Lean parser. It cannot
account for every declaration form, and equation-style definitions and
structures without `:=` are rejected rather than analyzed. Other unsupported
forms may not be recognized. Body matches can be trivial or affected by syntax
boundaries; they are weak leads. Normalization only handles a limited explicit
binder grammar; unsupported binders are reported. The acceptance controls are
external Python tests, not Lean proofs.

Independent read-only finder and skeptic reviews, without the Lean server,
found retroactive binder substitution, dot-prefixed constructor and
apostrophe-identifier collisions, string/delimiter boundary errors, missing
registry directory references, missing singleton rows and unreported unmatched
globs. Those concrete cases were fixed and covered by controls. Both reviewers
also found remaining parser and signature-resolution limitations described
above. Their reviews do not establish complete coverage.

Validation so far:

- `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item1/duplication-scanner/test_scan.py`:
  six tests pass; these exercise scanner behavior, not proof obligations.
- `LEAN_NUM_THREADS=1 lake env lean -j1 --tstack=131072 Solidity/KeySort.lean`:
  exit 0, no diagnostics, with a 12 GiB virtual-memory limit and 4 GiB
  available-memory precheck. Lean 4.24.0, Lake 5.0.0-src+797c613. The initial
  timing attempt did not run because `/usr/bin/time` is absent. This is not the
  full build or a runtime gate.
- Two V07 sample scans at identical pre-final scanner bytes produced equal SHA-256
  `43c5e2d73da1ec1ad3c090c7d739ac5d2740a30b31bca6882038b75f01c28857`
  and took 3.04 and 3.30 seconds. A prior version took 21.41 seconds on the
  same input; its second timing was interrupted. Output changed with the
  inventory additions, so these numbers do not establish a semantic
  before/after comparison. Bulk outputs remain off Git.

Pending: complete the scanner's declaration accounting and signature safety,
full acceptance and final independent reviews; index all 19 supplied audit
items; identify only coordinator-confirmed unowned opportunities; deterministic
incremental whole-scope reports and backfill; required affected and full gates,
timings and final handoff. No frozen Lean statements, proofs, axioms or sorry
counts were changed by this prototype. The supplied ownership snapshot is
historical and does not itself establish live ownership.

## Audit index and whole-tree lexical reports

The [pinned source](../../tests/h62/item1/duplication-scanner/audit-source.md)
has SHA-256 `31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`.
The [generator](../../scripts/h62/item1/duplication-scanner/index_audit.py)
reproduces the [19-item index](../../tests/h62/item1/duplication-scanner/audit-index.json)
and rejects modified input. Every item retains its exact source text and an
unresolved live-ownership status. Finder and skeptic independently checked the
source, item order, and absence of unowned claims. They found a portable
reproduction-test gap; the pinned in-scope source fixture and unconditional
byte comparison resolve it. Neither reviewer used Lean. The skeptic's
read-only sandbox could not run scanner tests requiring temporary files; the
owner's permitted test run supplies that result.

A bounded serial scan of `Solidity/**/*.lean` and `tests/**/*.lean` at
the first scanner commit read 6,657 files, reported 114,034 recognized
declarations and 69,517 explicit rejections in 101 seconds. After the
structure-default fix, the incremental scan reported 114,034 recognized
declarations and 69,589 rejections. Its two runs took 97 and 100 seconds,
with byte-identical SHA-256
`5cfb658f214a45d90402dceafd0ccf285c7f03e77bc1ff9897f099c44db3d1a7`.
There were no changed, added or removed Lean inputs, and the report correctly
recorded changed scanner bytes. These large reports are off Git in the
evidence directory; they are lexical snapshots, not proof of complete Lean
declaration coverage or current ownership.

The skeptic found that body leads lacked unresolved-signature and ownership
reasons even where statements appeared to match. Both reasons are now
unconditional and have an acceptance control. Structures, classes,
inductives, axioms and constants are explicitly rejected rather than treating
a field default as their definition delimiter. Unrecognized syntax and
unresolved names remain open limitations.

The initial prototype creation command reported a bad lock descriptor but
continued to write the new file; this did not hold the intended writer lock.
The checkout was otherwise clean and no concurrent writer was observed. All
subsequent edits, checks involving writes, and commits used the specified lock.

Pending work remains as listed above; the index and reproducible lexical
reports do not complete the scanner, ownership, backfill, full validation or
final handoff.

## Binder coverage follow-up

The lexical normalizer now supports simple explicit, implicit and named
instance binders, including Unicode names, while retaining binder delimiters.
It rejects anonymous binders, escaped identifiers and nested binding syntax in
binder types. These refusals are deliberate: the tool still does not resolve
Lean names or establish intrinsic signature equality. Finder and skeptic
independently identified anonymous-binder, nested-binder, Unicode-token and
escaped-identifier cases; fixes and negative controls were added and both
reviewers rechecked them without Lean.

The V07 sample took 3.225 and 3.145 seconds after this change, compared with
3.038 and 3.298 seconds before it (means 3.185 and 3.168 seconds, approximately
0.6% slower). Both new runs emitted SHA-256
`4f07d6877235f5a497f131cb3b5dd6492bae1c982d3ec2d1bce22ee7cc986088`.
The comparison uses the same input and VM; output differs because the scanner
changed. The whole-tree reports above predate this binder change and are
historical evidence, not a current-head census. A first edit attempt failed
with a Python quoting syntax error before writing files; the following test
ran the old code and is not evidence for the attempted edit.

The scanner remains incomplete. Full current-head census and incremental
reports, live owner verification, remaining backfill, and final validation are
still required.
