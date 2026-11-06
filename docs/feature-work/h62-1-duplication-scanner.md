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

## Selection-pinned incremental reports and discovery controls

Version 2 records the absolute scan root and selected glob patterns and rejects
a previous report with a different selection, an incompatible version, duplicate
input paths, or prior scan errors. It reports changes to statement and body
candidate groups as well as files. A current scan with an input read error or
unmatched pattern exits nonzero and suppresses file and candidate deltas;
`scanner-output-comparable` only means the two scanner outputs are comparable,
not that the Lean census is complete. Source bytes are read once for both hash
and parsing. Historical version 1 reports are deliberately not accepted as
version 2 baselines.

The finder identified omitted `partial` and `unsafe` declarations, field
assignments in `where` declarations mistaken for declaration bodies,
existential shadowing in binder types, qualifier differences missing from body
rejection reasons, and rejection counts that mixed categories. The skeptic
identified selection changes mislabeled as file removal and deltas produced
from incomplete scans. The changes and controls address those concrete cases;
both reviewers rechecked them independently without Lean. Unsupported syntax
still exists, and an unchanged lexical group is not an elaborated-signature
proof. A first v2 whole-tree attempt was interrupted by the owner before
completion to fix read-error handling and was not used as evidence.

At the scanner bytes in this checkpoint, two deterministic V07 sample scans
took 3.061 and 3.101 seconds, compared with 3.225 and 3.145 seconds before
the changes; means 3.081 and 3.185 seconds, about 3.3% faster. Whole-tree
baseline and incremental runs took 99, 102 and 102 seconds; the previous
baseline took 101 seconds and the previous incremental runs 97 and 100
seconds. The two incremental files are byte-identical with SHA-256
`64445dc4f4e9d6461c0e5a9631506dc61f8bb5273323113be11c907918094bdd`.
They scanned 6,657 files, recognized 114,487 declarations, and reported
67,825 explicit rejections; the remaining unrecognized forms are not counted.
No file or candidate group changed against the v2 baseline. These are
off-Git lexical reports, not kernel proofs or unowned-opportunity claims.

Acceptance on this checkpoint: `PYTHONDONTWRITEBYTECODE=1 python3
tests/h62/item1/duplication-scanner/test_scan.py` passed 11 tests and
`PYTHONDONTWRITEBYTECODE=1 python3
tests/h62/item1/duplication-scanner/test_index.py` passed 2. They are external
scanner tests. The previously recorded bounded KeySort run remains a
prerequisite result for unchanged Lean sources, not a full gate. Full
declaration accounting, resolved intrinsic-signature safety, live ownership,
remaining backfill and final repository gates remain unfinished.

The repository `./scripts/check-doc-paths.sh` exited 0: every checked
backticked Lean path resolved; it reported 115 ambiguous references under its
non-strict mode. Its complete output is retained off Git.

## Equation forms, literal boundaries, and matched performance pair

The scanner now recognizes a conservative subset of equation-style
definitions with explicit result types and keeps equation bodies distinct
from assignment bodies. It suppresses body grouping when an indented
declaration, local helper, command boundary or escaped header can make the
captured body incomplete. Escaped identifiers, character literals and Lean
raw strings are kept opaque to comment and declaration-boundary discovery;
raw and escaped literal contents remain distinct body tokens. Other Lean
syntax remains unsupported or unrecognized. Body matches and signatures are
still lexical leads with unresolved intrinsic-signature and ownership reasons.

Independent read-only finder and skeptic reviews identified false delimiter
and truncated-body cases involving local helpers, indented commands, escaped
identifiers, character literals and raw strings. Controls were added for the
reported examples and their reviews found no further concrete collision in
their focused final pass. Their reviews did not use Lean. Two preliminary
whole-tree scans were interrupted before completion to fix literal handling.

The initial extension's two complete whole-tree incremental runs took 110 and
114 seconds versus the previous 102 seconds. The 114-second repeat exceeded
the required 10% stop threshold; the stopped uncommitted work and reports
remain in `/workspace/h62-duplication-scanner-evidence/perf-stop/`. The
coordinator subsequently directed one matched before/after pair on the same
input and VM. Profiling identified repeated full-text masking, path resolution
and signature normalization. Reusing the aligned full-file skeleton and
caching those values produced the pair 103.565 seconds before and 99.170
seconds after, a 4.24% improvement. Both used the same 6,657-file selection,
registry, previous report, 8 GiB virtual-memory ceiling and 4 GiB
available-memory precheck. This satisfies that timing decision; it does not
make the scanner or full task complete.

The optimized records matched the preserved unoptimized implementation on
166 real files and an opaque-literal fixture. The full optimized incremental
report also matched the earlier unoptimized full report after replacing only
the recorded scanner SHA256; both normalized to
`fa3f6023b816705877225db067f808e2499f22fc1e64c599619bba9c82768a04`.
The finder and skeptic independently reviewed the optimization and alignment
control. The full report recognized 114,487 declarations, including 6,064
equation forms, and 65,368 explicit declaration rejections; other omitted
forms remain unknown. Its scanner hash changed and candidate-key changes
therefore include scanner changes, not established cleanup opportunities.
The paired timing, differential and bulk reports are retained off Git.

The current scanner acceptance suite passed 20 tests and the pinned audit
index suite passed 2. These are external tests, not kernel proofs. Live owner
verification, full declaration accounting, intrinsic signature resolution,
remaining backfill and final repository gates remain pending.

## Isolated elaborated-signature fixture

The additive test-only `SignatureFingerprint.lean` serializes elaborated
`ConstantInfo.type` structures. It preserves fully structured names, constant
universe arguments, level constructors, de Bruijn indices, binder kinds,
applications, literals, let flags and projections; it renames binder display
names and maps declared universe names by parameter position. Free or
metavariables, loose bound variables, undeclared or duplicate universe
parameters, universe metavariables and expression metadata are refused. Its
`#h62_signature` command labels records `environment_binding: unbound`:
module names and Lean versions do not bind source bytes, imported artifacts or
the dependency closure. The scanner does not consume these records or treat
them as resolved candidates. Equal serialized types alone do not establish
body equality, safe extraction or permission to edit.

The isolated fixture checks six elaborated declaration comparisons, thirteen
synthetic expression comparisons, seven refusals, six refusal reasons and
universe arity. The theorem fixtures themselves use `rfl`; guarded
`#print axioms` controls verify that all ten depend on no axioms. These
kernel-checked small fixture theorems and axiom observations are distinct from
the encoder's `run_cmd` comparisons and Python record checks, which are
tooling acceptance rather than proofs that serialization is injective. A
separate importing consumer emits five fixed records; its pinned 4 KiB
expectation and checker refuse eight mutations and two malformed-JSON cases.
A guarded missing-name control verifies resolver refusal. The fixture check is
not authentication of arbitrary records or the imported environment.

Reproduce with Lean 4.24.0 available on PATH:

```sh
bash scripts/h62/item1/duplication-scanner/check_signature_fixture.sh /absolute/evidence/directory
```

It locks the checkout, verifies the toolchain, uses serial Lean `-j1`, checks
visible cgroup and host headroom before each invocation, refuses unsupported
nested cgroups and swap, and bounds virtual memory without systemd. Its
headroom checks are snapshots; other allocations or hidden ancestor limits
are not continuously observed. The run at
`/workspace/h62-duplication-scanner-evidence/signature-fixture/h62-signature.1dbDUt4w`
passed build, consumer, missing-name and axiom controls and has a SHA256
manifest. The first Lean attempt failed on a reserved identifier; its
diagnostic is retained in `signature-first.log` and the identifier was fixed.
No full repository gate or RUNTIME_GATE_PASS is claimed.

Independent read-only finder and skeptic reviews identified missing refusal
and structural controls, insufficient fixture-output checking and a
host-only memory guard. The current controls pin the complete fixture records,
check malformed and fabricated records, and the runner checks visible cgroup
headroom. Both reviewers rechecked those changes without using Lean.

Proposed registration fragment for coordinator review, if these test-only
helpers are later placed in an owner-approved area; no registration is applied:

| Module or fixture | Purpose |
|---|---|
| `SignatureFingerprint.lean` | Conservative elaborated-type serialization and isolated controls |
| `SignatureConsumer.lean` | Imported-command fixture |
| `SignatureMissing.lean` | Guarded missing-name refusal |
| `SignatureAxioms.lean` | Axiom checks for ten isolated fixture theorems |

The historical whole-tree scanner reports predate these four added Lean test
files. Current-head scanning, actual environment binding, scanner
integration, full declaration accounting, live ownership, backfill and final
repository gates remain pending.

A staged whitespace check initially rejected a trailing blank line in the
axiom fixture. The line was removed and the guarded fixture was rerun against
the final bytes. The subsequent staged whitespace and proof-shortcut checks
passed. The repository doc-path check exited 0 with 115 ambiguous references.

### Incremental report including the signature fixtures

After adding the four isolated Lean fixtures, two bounded incremental scans
against the matched-pair report took 95 and 94 seconds and were byte-identical,
SHA256
`01e696eee1f088dc3e1482b6a4362a76f9e320cf1a0d8f1a83455b7a8a35ad63`.
They read 6,661 Lean files, recognized 114,507 declarations and returned no
file errors or unmatched globs. The input delta is exactly the four new
fixture files; no Lean inputs were changed or removed, and the scanner hash
was unchanged. The report adds one statement group and changes one body group;
these are lexical group changes, not resolved intrinsic-signature matches or
unowned opportunities. These two runs used four more input files than the
matched performance pair and are not a same-input slowdown comparison.
Bulk outputs and status logs remain off Git in
`/workspace/h62-duplication-scanner-evidence/signature-fixture/`.

The scanner still does not consume the isolated signature records. A future
integration needs a verified binding among the record, exact source,
compiled module and dependency environment before using elaborated signatures.
The live ownership dependency, unsupported declarations, remaining backfill
and final repository gates remain open.
