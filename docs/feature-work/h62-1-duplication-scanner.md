# H62 item 1: duplication scanner (partial prototype)

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. This is the first,
incomplete scanner checkpoint. It is not a complete audit, proof, ownership
decision, or RUNTIME_GATE_PASS.

`scripts/h62/item1/duplication-scanner/scan.py ROOT GLOB... [--owners JSON]
[--registry JSON] [--previous REPORT --previous-sha256 SHA256]` emits deterministic JSON, including input
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

## Caller-pinned incremental baseline

Incremental comparisons now require `--previous REPORT` together with
`--previous-sha256 SHA256`. The scanner reads at most 512 MiB of prior
report bytes, checks the supplied lowercase SHA256 against those exact bytes,
then strictly decodes and parses them before scanning. It rejects duplicate
JSON keys, nonfinite or floating numbers, incompatible selections, malformed
candidate members and incomplete reports. Deeply nested or oversized inputs
fail closed. The input-byte ceiling is not a bound on JSON's in-memory
expansion; the caller must still impose process resource limits.

A matching caller pin identifies bytes only. It does not authenticate the
producer or establish that the prior report accurately represented a scan;
the result explicitly labels its baseline provenance
`caller-pin-unverified`. Existing version 2 reports can be reused with their
actual SHA256, but invocations that omit the new paired argument now fail.

The pinned-baseline change was measured on the same 6,661-file selection,
previous-report bytes, machine and resource ceiling. The committed scanner
took 97.394 seconds before; the pinned version took 98.262 seconds after,
a 0.89% increase. A repeat took 96.393 seconds and was byte-identical to the
first pinned output, SHA256
`f4b482c802f30ede222422119fca124c591aea4e07aa0d8864f0a6ff03ad8a2a`.
The complete before and after reports matched after normalizing only the
intentional pin fields and scanner-identity fields. The exact prior pin was
`01e696eee1f088dc3e1482b6a4362a76f9e320cf1a0d8f1a83455b7a8a35ad63`.
A preliminary after run was deliberately interrupted to fix an independently
found malformed-member case; its timing is not a passing measurement.

Finder and skeptic reviews, without Lean, found and rechecked the exact-byte
pin, duplicate/deep JSON and malformed-member cases. Controls include a
one-byte mutation against the original pin, changed selection, incomplete and
oversized baselines, a targeted late serialization failure, and a fabricated
well-shaped prior with a fresh caller pin. That last case remains explicitly
unverified. The scanner acceptance suite passed 21 tests and the audit index
suite passed 2. This is external tool validation, not a Lean proof. Full Lean
signature binding, declaration coverage, live ownership, backfill and final
repository gates remain pending.

## Fixture-local import observation

The isolated fixture now records Lean's effective imports, search path and
fresh `findOLean` lookups after import. The accompanying observer checks
first-package-root selection, refuses ambiguous roots and missing artifacts,
and hashes regular `.olean` files and loader sidecars. It compares snapshots
before and after the observed consumer, checks the probe and consumer logs,
and recaptures the currently resolved artifacts. The fixture driver also
checks selected source and command-path hashes before and after compilation.
Its completed run observed 1,561 modules and passed all five pinned
signature controls, the guarded missing-record check and the axiom checks.
Thirty Python tests passed, including changed and forged snapshots, shadowed
roots, sidecar and symlink changes, malformed inputs and swapped source paths.

This is a fixture-local observation, not an attestation. The lookup occurs
after import; matching snapshots cannot exclude transient replacement, prove
which bytes Lean loaded, or prove a source-to-artifact relationship. The
command paths and other extra paths are caller-supplied and may be wrappers;
hidden runtime dependencies and ancestor resource limits are not established.
Even fabricated mutually consistent logs and artifacts can satisfy the local
checks. Records remain `environment_binding: unbound`, and the scanner does
not consume them or promote any ownership candidate. The fixture commands are
bounded individually; resource headroom checks are point-in-time checks.
Evidence and its SHA256 manifest are outside Git under
`/workspace/h62-duplication-scanner-evidence/environment-observation/`.

Independent finder and skeptic reviews used no Lean server and confirmed the
above boundary. These controls validate tooling behavior; they do not prove
serializer injectivity or a project-wide signature binding. The expanded
fixture workload is not a matched performance comparison; production scanner
code did not change in this checkpoint. Full repository gates remain pending.
The three additional Lean files are test-only modules; any eventual area-module
registration requires owner approval and must not be inferred from this fixture.

### Incremental report after import-observation fixtures

Two bounded scans of the same selection and caller-pinned baseline completed
in 95.035 and 93.739 seconds. Their full output bytes match, SHA256
`42000b1f3a5eacf6d262a98c60a97e8d7198faf35b91fc512636510bd292c42d`.
The report selects 6,664 Lean files and recognizes 114,509 declarations, with
no file errors or unmatched globs. It records exactly the three new
`SignatureEnvironment`, `SignatureEnvironmentProbe` and
`SignatureObservedConsumer` fixtures as added, no changed or removed inputs,
and no statement or body group delta. Scanner and registry identities are
unchanged from the caller-pinned baseline. All recognized declaration owners
remain unknown; these lexical observations do not establish complete Lean
coverage or live ownership. The runs include three more inputs than the prior
performance pair and do not constitute a matched before/after performance gate.

Finder and skeptic independently checked the input selection and interpretation
without Lean. Full reports, commands and timing records are outside Git at
`/workspace/h62-duplication-scanner-evidence/environment-incremental/`.

## Retirement checkpoint: identifier continuation fix (unfinished)

A finder identified that splitting `?` and `!` from Lean identifier
continuations can conflate a free name such as `x?` with binder `x` during
normalization. This checkpoint changes the lexical token and binder patterns
and adds negative and alpha-renaming controls. The acceptance suite passed 31
Python tests, but the change has not had its required final independent
finder/skeptic reviews or its matched after timing and full-tree differential
scan. Do not treat this checkpoint as validated or promote its output. Lean's
full identifier grammar includes Unicode cases beyond these patterns. The
same review also found selected symlink aliases and broken symlinks can be
silently omitted by input selection; that issue remains unfixed.

The matched before run, using the previous caller-pinned baseline and 8 GiB
virtual limit, exited 0 in 96.882 seconds. Its command, output and test log
are outside Git under
`/workspace/h62-duplication-scanner-evidence/suffix-fix/`. The coordinator
ordered this worker retired before the after run. The successor must check the
fix, complete negative controls and reviews, measure the matched after run
and stop if slowdown exceeds 10%; no passing performance gate is claimed.

## Post-merge identifier controls

After the published master was merged, a skeptic found that the earlier
continuation fix still split Lean letterlike and subscript characters, so
`(x : Nat) : x℘ = x` and the corresponding `y℘` expression could normalize
together. The scanner now uses character classes from the pinned Lean 4.24
`isIdFirst` and `isIdRest` rules for identifiers, binders, and literal
predecessors. Controls cover free-name differences, alpha-renamed binders,
subscripts, astral letterlike characters, and operators adjacent to character
literals. The 33-test Python suite passed. A first overbroad intermediate
range incorrectly included operators; independent finder and skeptic reviews
found it and the final controls cover their counterexamples. One reviewer
compared the final continuation class with a transcription of Lean's predicate
through U+1D59F. These controls do not prove full lexer or parser equivalence.

On master `20e492ee99a3fa8679aa526de0b6e731d85e4134`, the matched full-tree
pair for the earlier punctuation change took 96.098 seconds before and 96.333
seconds after (+0.24%). Using that same-tree after run as the before of the
Unicode correction, the corrected scanner took 97.220 seconds (+0.92%).
All three runs selected 6,932 Lean files, recognized 118,563 declarations and
reported no file errors or unmatched patterns. This is lexical discovery, not
proof of complete declaration accounting or intrinsic-signature equivalence.
The unfinished overbroad intermediate run was interrupted and is not a gate.
Bulk outputs, commands and timings remain outside Git in
`/workspace/h62-duplication-scanner-evidence/postmerge-timing/`. Selected
symlink aliases and broken links remain a separately identified open defect.

The post-merge repository documentation-path gate exited 1 on five missing
references in `h62-6-migrate-theory.md`, the audit-abi-world census test,
`packet-panic/H71-CANDIDATE.md` and generic-structuredflow registration. None
is in this scanner document. Its log is `postmerge-timing/doc-paths.log` in
the evidence directory; the repository-wide gate remains open.

## Selected symlink and nonregular input controls

Selected `.lean` paths are now kept as logical paths. A selected symlink,
symlinked parent, nonregular file or path-escape pattern makes the scan
incomplete instead of silently collapsing or dropping that path. For
recursive patterns, a non-following walk checks the literal prefix and
reports symlinks and walk errors, including dangling links. This is a
conservative refusal: a symlink under the prefix may be unrelated to the
actual glob. Incremental added/removed/changed lists remain null on such
errors. Nonrecursive wildcard traversal can still omit an inaccessible
subdirectory without a reported error; checks and reads are not race-proof
against concurrent replacement. Full selection completeness is not claimed.

Finder and skeptic reviews identified the recursive directory, dangling link,
nonregular-file and parent escape cases; controls cover them. The final Python
suite passed 35 tests. A same-tree bounded scan took 97.220 seconds before
and 97.746 seconds after (+0.54%), with 6,932 inputs and no scan errors. The
complete before/after outputs agreed after normalizing the scanner hash.
Commands, timing and differential logs are outside Git in
`/workspace/h62-duplication-scanner-evidence/postmerge-timing/`. The earlier
repository documentation-path gate remains failed on the five unrelated
published-tree references recorded above.

### Post-merge deterministic replay

A repeat of the committed selector against the same caller-pinned prior report
and current tree exited 0 in 105.414 seconds. It was byte-identical to the
97.746-second report, SHA256
`fb7e40a93e687b7a0865908d85cde9bf1c490be53430dc098ada7760806bdf9b`.
Both selected 6,932 files and recognized 118,563 declarations, with no errors
or unmatched patterns; all recognized owners remain unknown. The input delta
versus the older caller-pinned report is 271 added, 22 changed and none
removed. The scanner identity also changed, so candidate-group deltas include
possible normalization and selection changes and cannot be attributed solely
to source edits. The prior pin identifies bytes, not an authenticated scan.
Independent finder and skeptic reviewed the evidence without Lean; these two
runs establish byte repeatability only. Full outputs and timing records are in
`/workspace/h62-duplication-scanner-evidence/postmerge-timing/`.

## Nonrecursive wildcard traversal

Wildcard directory components now receive an error-aware, non-following walk
under their literal prefix, including nonrecursive patterns. Such walks stop
at the pattern's directory depth; recursive `**` patterns still walk below
their prefix. A traversal failure makes the report incomplete and suppresses
incremental deltas. The walk may conservatively refuse unrelated siblings
within that depth, and selection and reading remain non-atomic. The
permission-error control is simulated; it does not prove behavior on every
filesystem. These limits refine the earlier nonrecursive-wildcard caveat.

The Python suite passed 36 tests. Independent finder and skeptic reviews
without Lean identified the need to bound the nonrecursive walk; controls
include an unrelated deeper link and a simulated inaccessible directory. A
matched bounded full-tree pair on master
`5da4771e63a4278ed53932ac39a032e3d7aea6ed` took 110.043 seconds before and
104.998 seconds after (-4.58%). Both scans selected 7,143 files, recognized
121,486 declarations, and reported no errors or unmatched patterns. Their
complete reports agree after normalizing the scanner hash and the
`scanner_changed` flag. This is an external lexical-tool check, not a proof
of complete declaration accounting or intrinsic-signature equivalence.
Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/wildcard-traversal/`.

A separate review found that multiline section-variable continuations are not
included in the lexical context hash. The scanner's intrinsic-signature
rejection remains essential; this context hash does not establish elaborated
signature equality. Resolving that limitation and live ownership remains open.

## Multiline lexical context spans

The context hash now includes comment-masked text from each recognized
context command through the next recognized command or declaration boundary.
This distinguishes the reported multiline section-variable universe case
and retains literal contents while using the literal-hidden skeleton to find
boundaries. It is still a lexical approximation: local definitions, notation,
macros, syntax quotations and unrecognized commands can affect elaboration
without proving different context hashes. A control with different local
`T` definitions confirms that a remaining lexical candidate retains both
`intrinsic-signature-unresolved` and ownership-verification rejection reasons.
No candidate is promoted to an intrinsic-signature or unowned result.

Finder and skeptic independently reviewed the implementation without Lean.
The Python suite passed 38 tests. On the same tree and input selection, a
bounded full scan took 104.998 seconds before and 108.550 seconds after
(+3.38%); both read the same 7,143 input hashes and recognized 121,486
declarations without file errors or unmatched patterns. Statement and body
group counts remained 4,412 and 5,432 respectively, although group identities
can change with the new context spans. These are external lexical-tool checks,
not Lean proofs. Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/multiline-context/`.

### Multiline-context report replay

Two bounded scans with the same tree, scanner, selection, registry and
caller-pinned previous report took 108.550 and 105.122 seconds and produced
byte-identical reports, SHA256
`f70746c5529c35d14a076007a526011357d6738cc8fc5eecd64d38d3d9b79285`.
Both selected 7,143 files and recognized 121,486 declarations, with no file
errors or unmatched patterns; all recognized ownership remains unknown. The
input delta against the older caller-pinned report is 211 added, 339 changed
and none removed. Both the tree and scanner changed from that baseline, so
group deltas cannot be attributed solely to source changes. The pin does not
authenticate the prior report's producer. These runs demonstrate repeatability
for this snapshot, not complete census, Lean signature equivalence or live
ownership. Independent finder and skeptic reviewed the replay without Lean;
full reports and timing records are outside Git in the multiline-context
evidence directory.

## Multiline attribute declaration boundaries

Line-initial attribute prefixes are now balanced and masked in the scanner's
literal-hidden skeleton, preserving source offsets and newlines. This
recognizes stacked and nested multiline attributes before declarations,
reports the declaration keyword's line, avoids reading attribute text as
qualifiers, and keeps a following declaration's attribute bytes out of the
preceding body. An unterminated prefix reports a file error. Arbitrary syntax
quotations, detached/custom commands, macro-generated declarations and
modifiers split across lines remain outside complete lexical coverage.

Independent finder and skeptic reviews found and rechecked nested attributes,
qualifiers, indentation and preceding-body boundaries without Lean. The
Python suite passed 39 tests; these are external tool controls. A preliminary
regex approach and its timing were stopped after review findings, and are not
passing measurements. The reviewed implementation took 110.962 seconds
versus 114.443 seconds before (-3.04%) on the same tree and selection. Both
scans selected identical inputs, recognized 122,786 declarations, and had no
file errors or unmatched globs. Statement-group counts were 4,476 in both;
body-group counts changed from 5,506 to 5,510. Counts do not establish equal
group membership or semantic equivalence. Bulk reports, timing and test logs
remain outside Git under
`/workspace/h62-duplication-scanner-evidence/multiline-attributes/`.

A separate notation example after a preceding declaration can still share a
lexical context hash despite different expansions. Candidate signatures and
ownership remain explicitly unresolved; full source/environment binding and
complete declaration accounting remain open.

## Notation command context and body boundaries

Line-initial notation, infix, prefix and postfix commands, including local or
scoped modifiers, now contribute lexical context spans. The same recognized
commands terminate preceding bodies; an indented command boundary rejects the
body fingerprint. This addresses the reported notation-after-declaration
case, but macros, unrecognized commands, scope resolution and imported
meaning remain unmodeled. Signature and ownership rejection reasons remain
mandatory for every candidate.

Finder and skeptic independently reviewed the implementation without Lean
and found the initial preceding-body boundary omission, which the final
controls cover. The Python suite passed 40 tests. The preliminary measurement
was interrupted after that finding and is not passing evidence. A bounded
same-input pair took 110.962 seconds before and 112.714 seconds after
(+1.58%). Both scans selected identical inputs, recognized 122,786
declarations and reported no file errors or unmatched globs. Statement-group
counts were 4,476 in both and body-group counts were 5,510 and 5,511;
counts do not prove equal group membership or semantic equivalence. Full
reports, controls and timing are outside Git under
`/workspace/h62-duplication-scanner-evidence/notation-context/`.

### Notation-context report replay

Two bounded scans with the same tree, scanner, selection, registry and
caller-pinned prior report took 112.714 and 114.373 seconds and produced
byte-identical reports, SHA256
`e60eda341e2c219f2ec92e3ac8a3f2dbacc9cdbbecd3708631225f59f04dcc22`.
Both selected 7,247 files and recognized 122,786 declarations, with no file
errors or unmatched patterns; all recognized owners remain unknown. Relative
to the older caller-pinned report, 104 inputs were added, 23 changed and none
removed. The scanner also changed, so candidate deltas combine tree and tool
effects. The prior pin identifies bytes, not an authenticated producer.
Independent finder and skeptic reviewed the replay without Lean. This checks
repeatability for these runs, not complete coverage, signature equivalence or
live ownership. Reports and timing records are outside Git in the
notation-context evidence directory.
## H82 successor: selected path identities

The inherited identifier-continuation fix passes its full 31-test suite. Selected symlink paths now retain their lexical identity and owner/registry lookup instead of collapsing into resolved targets. Strict containment is checked separately. Broken, outside-root, looping and non-regular selected Lean paths report errors and suppress incremental completeness. An input_aliases list records internal aliases, and candidate families warn shared-resolved-source when distinct selected paths resolve to the same source. Overlapping globs deduplicate lexical paths.

The expanded suite passes 35 tests with real filesystem fixtures. A serial same-VM/corpus/resource pair measured 129.793310s before and 118.114590s after (-8.997937%), peak child RSS 3,325,784,064 and 3,325,313,024 bytes. Whole-scope reports match except scanner_sha256 and the new empty input_aliases field. Input hashes, declarations, candidates and errors match exactly. This is external lexical checking, not Lean coverage, signature equivalence, live ownership or a runtime gate.

Independent read-only finder and skeptic confirmed the selected-path fix. The skeptic identified a separate inherited limitation: pathlib glob can suppress directory enumeration errors. That remains a pending scanner item; implicit recursive symlink-directory traversal, hardlink identity and full Lean signature accounting are not established by these controls. Evidence is off Git under /workspace/h62-audit-readonly-calls/h82b-intake/evidence/.

## Error-aware selection checkpoint

Explicit scandir traversal now reports inaccessible selected directories as errors and marks the report current-incomplete. Exact literal components use direct lookup; wildcard components require directory enumeration. Trailing slashes retain directory-only selection. Recursive ** does not implicitly follow directory symlinks; finite explicit directory components can follow them, with resolved containment checked before source reads. These semantics are tested against supported pathlib pattern cases.

Forty tests pass, including a real chmod000 subtree, an execute-only directory with a readable exact file, trailing-directory patterns, symlink aliases, and malformed current/previous reports. Finder and skeptic identified and confirmed fixes for trailing-slash and exact-path permission regressions. Neither reviewer ran Lean or benchmarks or wrote files.

The intermediate error-aware pair was 118.114590s to 113.311471s (-4.066491%). After the two review fixes, the paired final run took 107.120424s (-5.463742%), peak child RSS 3,327,791,104 bytes. Both whole-report comparisons match exactly except scanner_sha256; selected input hashes and membership are identical. Resource bounds: one scanner process, RLIMIT_AS 12GiB, 16GiB VM, no swap and 4GiB reserve preflight. These timings precede upstream adoption and are not post-rebase whole-tree performance claims. The earlier 35-test selected-alias checkpoint is historical. No Lean/runtime gate or complete signature/ownership claim follows.

## Authenticated allocation census

`ownership_census.py` guards stale owner-label promotion and cross-chain allocation leakage. It verifies the coordinator-pinned H82b manifest, selected assignment/scope/head/report bytes, member ancestry and source blobs. A historical added path is insufficient: current bytes must match the member head or the separately authenticated H70 requester checkpoint fc59bfc04c76e25e259b5b5b43e0349007b6c870. Clean later mutations without that evidence stay owner-review. Allocation patterns alone do not establish ownership of existing files, and provenance cannot expand the allocation.

Tracked Lean/cleanup paths and untracked or ignored scanner-area Lean/cleanup inputs are accounted. Dirty, nonregular, overlapping and untracked cases remain explicit review/unknown states. Missing proof-cleanup provenance is a limitation, never an unowned grant. This is a file-allocation census for this authenticated cleanup scope, not a live global ownership service or permission to edit other chains. Real committed-Git mutation and cross-allocation controls verify the distinction.

## Live source/signature fixture gate

`scan.py ROOT GLOB... --fixture-binding-output NEW_ABSOLUTE_DIRECTORY` guards stale/unbound signature promotion by performing a canonical live rebuild; it does not accept a saved receipt. Only the five pinned declarations in SignatureFingerprint are supported. Their raw H62_SIGNATURE records and expected-record bytes remain unchanged with environment_binding=unbound. Five matching source rows receive fixture_signature data; ownership and intrinsic-signature refusal reasons remain. Other declarations are not upgraded.

The separate bind_signature_fixture.py controller copies pinned sources into a fresh private tree, checks copied bytes before any subprocess, rejects pre-existing/symlink outputs, sanitizes import/loader environment variables, and compiles with the exact pinned Lean binary, explicit -j1 and --tstack=131072. The project import graph contains only the isolated fixtures and Lean; no Solidity Source, Premises or stopped workload is imported. Standard bundled module and IR/editor/native companion hashes are observed across the build, together with compiler runtime hashes. This is trusted local execution evidence with compiler/executor and concurrent-mutation limits; it is not remote attestation, ABA-proof loader provenance, official-release authentication or general repository signature binding.

Memory limits are derived from available memory minus a 4GiB reserve, capped at 12GiB. The corrected audit monitor polls aggregate RSS/reserve/no-swap state and retains the writer lease until all live owned descendants drain, including a zero-exit parent case. Tests exercise actual child address limits, simulated active reserve loss, descendant cleanup and copy-time mutation before execution.

All 69 scanner controls pass. The accepted live run annotates exactly five rows and observes 1,559 bundled module artifacts plus 4,677 companion presence/hash states. Seven fresh compiler steps passed in 7.757 summed child seconds, peak observed aggregate RSS 647,147,520 bytes. Canonical scan output is stable across the independently regenerated execution/resource packets; default scanner output matches the previous implementation except scanner_sha256. No default full-tree performance or production proof pass is inferred. The original +80.254966536% stopped Lean workload was not rerun and remains a hold. Independent read-only finder/skeptic findings were fixed and reviewed; neither reviewer ran Lean, tests or benchmarks or wrote files. New guard/pin/control docstrings identify their regressions under H90.

Accepted evidence is under /workspace/h62-audit-readonly-calls/scanner-binding/accepted-scan/; earlier fresh-fixture/fresh-scan packets are development diagnostics, not the final accepted gate. Whole-repository declaration/type/dependency coverage, producer-owned interfaces, live global ownership and all original cleanup queues remain unfinished.

## Full selected-input allocation accounting

The allocation census now unions the scanner's exact four-area selection with tracked cleanup files and Git-discovered untracked/ignored inputs. This includes nested Git repositories, which git ls-files can omit. Every selected nontracked input remains ownership-unknown, and directory selection errors make the census nonpassing. A real nested-repository control guards that omission.

The authenticated H82b scopes provide 5,793 foreign live allocation entries as read-only exclusion/conflict hints. Migration-only scopes are ignored. These hints do not identify current producer routing, transfer another chain's scope or grant edits; conflicts with cleanup allocation remain owner-review. H70 Claude producer routes retain priority. Full suite: 71 controls pass; both independent read-only reviewers confirmed the final coverage and exclusion boundaries without running tests, Lean or benchmarks or writing files. General repository signature/dependency binding and current global ownership remain incomplete.

## Selected lexical signature coverage

The opt-in live fixture report now partitions every selected lexical row in its coverage ledger. Path, source line, name, kind and lexical refusal reason remain explicit, so same-spelling declarations and unsupported forms are retained individually. The completeness flag refers only to these lexical rows; generated kernel declarations are not enumerated, and ownership remains unverified. Default output is unchanged except scanner_sha256.

The fresh scanner-coverage run accounts for 20 lexical rows: five local fixture links and 15 unresolved, with complete_signature_coverage=false. Seven isolated compiler steps passed (7.973 summed child seconds; peak aggregate RSS 647,118,848 bytes). These are run observations, not a matched performance comparison or production proof gate. All 73 controls pass. Independent read-only finder and skeptic reviews found no substantive issue; neither ran Lean, tests or benchmarks or wrote files. Evidence: /workspace/h62-audit-readonly-calls/scanner-coverage/. The original +80.254966536% timing STOP and all 792 audit obligations remain unchanged.

## Imported fixture kernel census

The separate census_fixture_kernel.py live-only command guards omission of generated and same-spelling constants. Its pinned SignatureKernelCensus probe enumerates env.constants entries whose imported owning-module index is SignatureFingerprint. Every visible constant becomes a serialized or unsupported row. Full structured names retain string/numeric components and namespaces. The default scanner and original five-record contract are unchanged. No old receipt is accepted as an input.

The controller performs a fresh canonical fixture rebuild, executes the pinned probe with bounded serial Lean, checks import/artifact/runtime/companion stability, and confirms the original five signatures. Live acceptance additionally requires four actual generated declarations (recursor, constructor, case splitter and matcher) and three binder/universe/namespace comparisons. The structural validator alone cannot authenticate completeness; a self-consistent omitted packet is not a live execution result.

Two independent fresh runs produced byte-identical censuses of 46 visible constants, all serialized. They include 32 definitions, 11 theorems, one inductive, one constructor and one recursor. This counts the imported environment, not source-line correspondence, unloaded/private artifact levels, general project coverage or ownership. New probe timings and resource observations are in /workspace/h62-audit-readonly-calls/kernel-census/evidence/acceptance.json; these are not a matched regression gate for an old workflow. The original +80.254966536% timing STOP remains and its workload was not rerun. No theorem, premise, exclusion, axiom, budget or production import changed.

Independent read-only finder and skeptic reviews found no remaining substantive issue after the generated-declaration acceptance fix. This probe remains an isolated test module with a staged local module name; it is not registered in generated production roots or module maps. Full original and inherited cleanup assignments remain unfinished.

Final acceptance: 82 external scanner controls pass. The global documentation path gate retains the same four inherited missing references outside cleanup scope. The new test probe declares no theorem or axiom; its bounded per-file execution is not a production proof or RUNTIME_GATE_PASS.

## Direct source-location binding

The separate bind_source_locations.py command guards namespace guesses, generated parent aliases and ambiguous source locations. A pinned additive probe reports direct findDeclarationRangesCore? metadata, avoiding the editor navigation parent fallback. A fresh canonical kernel census and a second bounded probe establish local execution provenance; exact imported-name sets, source bytes, identifier text, codepoint positions and declaration kinds determine the join. Missing, ambiguous and unsupported rows remain unresolved. Lexical refusal reasons are retained.

Both accepted fresh runs link all 20 lexical rows in the pinned fixture, retaining 26 additional visible constants without lexical links in the 46-constant inventory. This is fixture source/name/type linkage, not proof-body equivalence, general project coverage, unloaded/private artifact coverage or ownership. The default scanner and original five-record contract remain unchanged. No production roots, module maps, statements or budgets changed.

Child receipt, census and rebuild bytes are hash-checked against the successful in-memory live result before parsing and rechecked after the probe. A saved receipt cannot authorize the CLI. Post-child mutation controls reject altered artifacts before another compiler step; this does not eliminate ABA or authenticate a remote executor. A development failure exposed integer-only receipt parsing; finite timing decimals are now supported without changing observation/signature parsers or accepting nonfinite numbers. Failed diagnostics are preserved.

Independent read-only finder and skeptic reviews found no remaining issue after the provenance and receipt-number fixes. They ran no Lean/server, tests or benchmarks and wrote no files. Accepted evidence: /workspace/h62-audit-readonly-calls/source-locations/accepted-two/ and accepted-three/. Resource observations are in evidence/acceptance.json; these are not a matched old-workflow timing gate. The original +80.254966536% STOP and all 792 obligations remain, with the stopped workload not rerun.

Final source-location acceptance: 94 external controls pass; two fresh binding packets are byte-identical. The global path gate retains four inherited missing references. No new theorem, axiom, sorry or production import was introduced, and no RUNTIME_GATE_PASS is claimed.

## Scanner consumes direct source bindings

The opt-in --source-binding-output mode runs the live direct-location controller and consumes only hash-verified results from that invocation. The selected source hash and exact lexical row-key set must match. Only direct source/name/type links annotate rows; the remaining selected rows stay unresolved. Source mode and the original five-record mode are mutually exclusive, and their baseline selection contracts remain distinct. The scanner checks the live in-memory receipt hash before annotation and again before sealing its report. Saved outputs cannot authorize a run.

Two fresh mixed-scope runs account for 22 rows: 20 fixture links and two unresolved rows from another file. The separate imported inventory retains 26 constants without lexical links among 46 visible constants. The caller-pinned second scan has no input or candidate deltas. All candidate intrinsic-signature and ownership refusal reasons remain, and the original five-record live mode passes. No automatic helper move or ownership grant follows. Default output matches the predecessor except scanner_sha256.

Five paired measured default text scans, after one warm pair, used the same current 27-file WorldCalls corpus and alternating order under bounded memory. Medians were 0.12779389599745627s before and 0.13590442100394284s after (+6.34656682401169%); maximum child RSS 15,204,352 bytes. This scoped scanner result is below the 10% STOP threshold and does not resolve the original +80.254966536% Lean STOP. Its workload was not rerun. /usr/bin/time was unavailable before any sample ran; native os.wait4 supplied per-child RSS measurements.

All 100 external controls pass. Independent read-only finder/skeptic reviews found no substantive issue without Lean/server, tests, benchmarks or writes. Source/code/receipt evidence is under /workspace/h62-audit-readonly-calls/scanner-source-binding/. Binding remains limited to the pinned fixture; general coverage, unloaded/private artifacts, proof-body equivalence, live ownership and all original proof obligations remain open. No production or Lean source, frozen statement, budget or axiom changed, and no RUNTIME_GATE_PASS is claimed.

## Pinned real-project leaf binding

The additive bind_project_leaf.py producer guards fixture-only provenance being promoted to project declarations. It admits only the pinned, unchanged, import-free Solidity/KeySort.lean source. The controller copies exact source bytes into a fresh sparse tree, compiles the proper Solidity.KeySort module with the pinned compiler and bounded serial resources, and probes visible constants/types/direct locations. Existing fixture dependencies must remain byte-identical, and the imported closure may extend by exactly the fresh KeySort artifact at its expected path/hash. Runtime, source, server/private sidecars and IR/editor/native companions are checked. Cached objects and saved receipts cannot satisfy this producer.

The two fresh accepted runs emit KEYSORT_COMPILE_PASS and identical source bindings. All 16 named source declarations link; all 16 anonymous example rows remain unresolved. The separate imported inventory contains 161 visible constants, including generated declarations. Passing source compilation does not supply stable imported identities for anonymous examples, and no names are invented. No production source was edited. The existing metadata validators now accept an explicit target module while preserving their original fixture defaults; the old fixture bindings remain byte-identical.

All 108 external scanner controls pass, including source/import drift, unexpected dependencies, cache/path substitution, sidecars, module identity and replay controls. Independent read-only finder/skeptic reviews found no substantive issue without Lean/server, tests, benchmarks or writes. Evidence: /workspace/h62-audit-readonly-calls/project-leaf-binding/. Timings are repeated new-workflow observations, not a matched old-workflow regression gate. The original +80.254966536% Lean STOP remains; its workload was not rerun. No proof budget, statement, axiom or exclusion changed. This prerequisite compile and real-module identity linkage do not discharge owner compiler-success, all-model/runtime gates, global/private/unloaded coverage, ownership, proof-body equivalence or any original ordinary witness.

## Project producer consumed by scanner (item six)

H110 resolves Q-FRESH-THREAD (GitHub issue60): the coordinator waived the fresh-thread boundary for this lane, authorizing continuation in the current thread on the same original goal, VM, checkout and branch. Earlier handoffs record the historical boundary; it is no longer a wait.

The opt-in --project-binding-output mode consumes a fresh pinned KeySort producer. Its project_signature annotations and project_binding aggregate are distinct from fixture fields and modes. Shared attachment checks require matching source hashes, exact row-key sets and multiplicities, matching direct-link counts and no stale designated annotations before mutation. Missing/ambiguous/anonymous/other-source rows stay unresolved. Saved receipts cannot authorize a run.

Two fresh mixed-scope project scans account for52rows:16named project links and36unresolved rows (16anonymous examples and20fixture rows). The imported project inventory separately retains161visible constants and145without lexical links. Candidate intrinsic/ownership refusals remain. The pinned incremental second run has no input/candidate deltas, and original source-mode output matches its prior result except scanner_sha256. All116external controls pass; independent read-only finder/skeptic reviews found no substantive issue without executing Lean/server/tests/benchmarks or writing files.

Five paired measured default text scans after one warm pair use the same current27-file WorldCalls corpus with alternating order and bounded memory. Before median0.13843812600680394s; after0.13780417600355577s (-0.45793021152064073%); peak child RSS15335424bytes. This scoped text result does not resolve the original+80.254966536% Lean STOP; its workload was not rerun. No production, Lean source, frozen statement, budget, axiom or exclusion changed. General/private/unloaded coverage, ownership, body equivalence and original proofs remain unfinished. Evidence:/workspace/h62-audit-readonly-calls/scanner-project-binding/.

## Compiler-parsed declared import inventory (item seven)

The header_dependencies.py producer guards regex-only import guesses and accidental processing of inventoried project code. A pinned streaming Lean tool calls Parser.parseHeader and HeaderSyntax.imports on captured source strings; it never processes imports, loads inventoried modules, elaborates bodies or executes their commands. Eight live controls cover nested comments/body strings, module/public/meta/all flags, prelude, quoted components, nonexistent modules, invalid headers and an inert body marker. Tooling SDK/fixture dependencies are loaded separately. SDK resolution records mean file observations without loading those imports for inventoried sources.

The captured source commit selects the tracked core tree. Configuration bytes must match its Gitblob, final HEAD/config are rechecked, and source bytes must match their tree blobs. Additional roots are normalized before primary-root handling; duplicate roots collapse and overlaps fail. Aliases, dirty/missing/unsafe/ambiguous sources or SDK resolutions remain unknown. Separate packages, root tests and untracked sources are outside this explicitly bounded inventory; registration is not established. Body/dynamic/ownership uncertainty remains on every source row.

Both final fresh captures are byte-identical:6,454 source headers parsed;31 SDK file observations;1,011 tracked Lean files outside the selected core roots. All 129 original frozen module-map files are retained:25 declared paths to the held Premises module,104 with no declared path. No-path is not compilation permission, body/dynamic coverage, signature/artifact source binding, ownership or clearance of the original timing STOP. The 792 obligation count is retained as a reference; this tool does not recensus theorem signatures or discharge witnesses.

All 130 external scanner controls pass. Independent read-only finder/skeptic findings on snapshot/config binding, overlapping roots and equivalent primary-root spellings were fixed and reviewed. Neither reviewer executed Lean/server, tests or benchmarks or wrote files. Three development API/JSON compiler diagnostics and superseded captures are preserved; only accepted-four/accepted-five are final acceptance. Evidence:/workspace/h62-audit-readonly-calls/header-dependencies/. No proof budgets, frozen statements, axioms, production files, roots or maps changed. Original +80.254966536% Lean STOP remains and its workload was not rerun; no RUNTIME_GATE_PASS.

Final layout admission explicitly supports the normalized default package srcDir; other package-level roots fail rather than receive a guessed mapping. The existing V08 helper remains an unchanged lexical build-orchestration tool; its supported input shape does not replace compiler grammar/flag/source-snapshot capture. Final inventories name the immutable source tree bb9a9c899b3719db8940cb3b4dc66f04c0c764b5; its extra tracked test probe is outside core selection, so the excluded tracked count is now 1,011. Both final inventories still contain 6,454 parsed core headers and the same 129 frozen targets. The 104 no-path rows do not clear any hold or grant compilation permission.

## Fresh intrinsic AST dependency closure

The additive `scripts/h62/item1/duplication-scanner/bind_project_closure.py`
compiles unchanged pinned KeySort and AST sources in dependency order into a
fresh isolated library, then enumerates AST types and direct declaration ranges.
The probe checks that exactly those two fresh project objects extend the fixed
fixture/SDK imports. Existing objects, missing/extra/preloaded dependencies,
changed source hashes, stale dependency objects and companion drift reject.
The lexical join reads the exact staged AST buffer checked against its compile
pin; parsed probe bytes must match the checked process output hash.

Two final captures export identical metadata and source bindings: 135 lexical
rows, 98 direct source/type links and 37 unresolved rows. All 781 visible AST
constants remain in the census, including 683 without lexical links. Every
visible type serialized; this establishes neither general coverage nor semantic
or body equality. Anonymous instances and unsupported lexical binder forms stay
unresolved. The unchanged AST emits one existing unused-variable warning.
KeySort is a fresh checked dependency, not an additional type census in this probe.

All 140 scanner controls pass, including nine new closure/refusal controls.
Independent read-only finder and skeptic reviews corrected staged-source and
probe-log provenance and the dependency docstring; final reviews are clear.
Original production sources, intrinsic representations, statements and budgets
remain unchanged. The new test probe is staged and unregistered; no production
root or map was edited. No new axiom, sorry or native decision was introduced.

The scanner CLI still consumes the earlier KeySort producer; AST consumption
and general dependency admission remain independent queue work. Live ownership,
private/unloaded coverage, all 792 original audit obligations and owner compiler
success remain open. This isolated check does not rerun the held WorldCalls
workload or clear its +80.254966536% timing STOP. Actual Lean is 4.24.0, Lake
5.0.0-src+797c613; fresh bounded KeySort prerequisites pass. New-workflow timings
are observations, not a matched production timing gate or RUNTIME_GATE_PASS.
Raw outputs and manifests remain under
`/workspace/h62-audit-readonly-calls/project-closure-binding/` on the original VM.

## Live AST scanner integration

The existing live project mode now accepts `--project-binding-target ast`
with `--project-binding-output` pointing to a fresh absolute directory. KeySort
remains the default. AST uses its own pinned closure contract and explicit target
in the selection, so leaf or unbound baselines cannot be promoted into this mode.
The scanner verifies the original live receipt before deriving the single AST
source hash and applying the shared exact source/row/count checks. Saved execution
receipts remain inadmissible.

A mixed selection contains 187 lexical rows: 98 direct AST links and 89 unresolved
rows. Selected KeySort and fixture declarations receive no AST annotations, even
though KeySort is freshly compiled as a dependency. All original candidate and
ownership refusals remain; every row still lacks verified live ownership. A second
fresh AST scan has identical metadata/bindings and no incremental candidate change.
The live KeySort default output matches its previously committed hash-pinned
historical report exactly except for the scanner hash.

All 144 controls pass. Independent read-only finder and skeptic reviews found no
substantive issue and used no Lean server or execution. A matched text-only timing
check over 27 WorldCalls files (107364 bytes), five alternating measured pairs
after warmup, changed median from 0.138316705998 s to 0.135584431999 s (-1.98%).
Default outputs match except for scanner hash. This text-scanner comparison does
not execute Lean or clear its original +80.254966536% STOP. Fresh bounded KeySort
prerequisites pass; actual tools remain Lean 4.24.0 and Lake 5.0.0-src+797c613.
No production Lean files or lines changed, no new Lean declaration was added, and
no statement, definition, exclusion, budget or axiom changed.

All 792 original theorem obligations and pending owner/compiler-success work
remain open as previously classified. General dependency admission, live ownership,
private/unloaded coverage and full original/inherited acceptance remain unfinished.
Raw evidence and manifests are retained at
`/workspace/h62-audit-readonly-calls/scanner-closure-binding/` on the original VM.

## Completed-process log provenance

Live fixture, kernel, source-location, KeySort, AST and header metadata readers
now share a bounded byte reader. Each live parse checks the exact buffer against
the hash from its successful in-memory process step, then parses that buffer.
Missing, duplicate, failed, timed-out or malformed step records refuse. Final
seals recheck parent and child logs, including the intermediate kernel probe.
The kernel reuses the existing live receipt seal rather than accepting the hash
of potentially replaced child receipt bytes. Offline parser calls without a
hash remain explicitly unbound and retain their prior behavior.

Eight new controls cover log substitution, byte limits, nonregular live inputs,
completed-step authority and parent failure after an intermediate log changes.
All 152 controls pass. Independent read-only finder and skeptic reviews found
the missing intermediate-child seal; it was fixed and covered by a positive and
negative parent-orchestration control. Final reviews are clear. Development
failures remain recorded; the census validator was never weakened to accept an
incorrect empty synthetic fixture.

Fresh serial source, KeySort, AST and header captures pass with unchanged
signature/range outputs and coverage. This is tooling provenance under a trusted
local process model, not remote attestation, malicious-ABA exclusion, body equality,
verified ownership or a theorem witness. The same-checkout canonical fixture
profile retained all five records; after one warmup and three measured runs per
cohort, medians were 24.851651143 s before and 20.499273840 s after (-17.51%).
Baseline measured runs ranged from 21.31 to 51.69 s, so this difference is not
attributed to code speed. The measurement covers the fixture producer, not all
binding modes or the held model proof workload.

No production Lean files, lines or declarations changed. Actual tools remain
Lean 4.24.0 and Lake 5.0.0-src+797c613; fresh bounded KeySort prerequisites pass.
All 792 original audit obligations retain their previous classifications. The
+80.254966536% Lean timing STOP, owner compiler-success dependencies and full
original/inherited acceptance remain open. Raw evidence, baseline variation and
reproduction commands are retained under
`/workspace/h62-audit-readonly-calls/checked-probe-logs/` on the original VM.

## Intrinsic Scope binding through the admitted closure interface

The existing closure producer now accepts explicit `ast` (unchanged default) and
`scope` profiles. Scope pins unchanged KeySort, AST and Scope sources/imports in
that dependency order, compiles all three fresh, and enumerates only Scope types
and direct source ranges. The scanner accepts `--project-binding-target scope`
with a distinct pinned contract. Arbitrary manifests and reused execution receipts
remain inadmissible; AST/KeySort dependency rows receive no Scope annotations.

Two fresh mixed scans account for 224 lexical rows: 25 direct Scope links and
199 unresolved rows. Scope itself has 37 lexical rows, including 12 unresolved.
The complete visible Scope census contains 312 constants: 286 serialized types
and 26 retained unsupported records (`expression metadata`), with 287 constants
lacking lexical links. No unsupported record is dropped or simplified. Both
captures have identical metadata/bindings and no incremental candidate changes.
All original candidate refusals and unverified ownership rows remain.

All 158 controls pass, including six new admission/dependency/replay controls.
Independent read-only finder and skeptic reviews found no substantive issue and
used no Lean server or execution. Existing AST workflow timing was measured in
the same checkout with source/SDK/cache policy and bounds retained: one warmup
and three measurements per cohort, median 41.271550384 s before and 43.448407344 s
after (+5.2745%, below the 10% stop threshold). AST metadata/bindings remain
byte-identical. Fresh AST CLI and KeySort-default compatibility checks also pass;
only scanner hash and fresh dependency observations differ where applicable.

Production Lean files, statements, representations, budgets and axioms are
unchanged. One 54-line test-only probe was added; it is staged and unregistered.
Fresh bounded KeySort prerequisites pass with Lean 4.24.0 and Lake
5.0.0-src+797c613. This extends observed context signatures, not model witnesses,
verified ownership, body equivalence or global/private/unloaded coverage. All
792 original audit obligations, owner compiler-success work and the original
+80.254966536% Lean STOP remain. Raw captures, refusals, timings and manifests are
retained at `/workspace/h62-audit-readonly-calls/scope-binding/` on the original VM.

## Separate metadata-preserving type observations

The additive `MetadataFingerprintV2.lean` exporter retains `Expr.mdata` entries,
keys, value constructors, list order, duplicate keys and the wrapped expression.
It reuses legacy primitive/name/universe/binder encodings. Syntax-valued metadata
remains refused. Its declaration-type domain is explicitly versioned; metadata
is neither erased nor interpreted as a semantic-equivalence result. The legacy
exporter, pins, five-record contract and scanner annotations remain unchanged.

The separate live producer `observe_metadata_types.py` first executes the pinned
Scope closure, then compiles a fresh test-only exporter and probe. It verifies
the exact additional helper artifact, dependencies, source/runtime/sidecar/log
hashes and final child metadata seals. Every legacy declaration and range must
match the original Scope result. Metadata-free v2 types must equal the legacy
encoding except for the version domain; other legacy refusals stay refusals.

Two final captures have identical observations for all 312 visible Scope constants.
Legacy results remain 286 serialized and 26 metadata-refused. The separate v2
observation serializes all 312, preserving the annotation payloads. This adds no
scanner links, model witnesses, ownership or body-equivalence claim. Earlier
captures before final sealing fixes are retained as superseded development.

All 167 Python controls and fourteen Lean separation/refusal controls pass.
Independent read-only finder and skeptic reviews fixed the helper-marker checked
read and final child metadata recheck; mutation controls cover both and final
reviews are clear. Existing code paths were not refactored or changed, so the
new workflow's timings are observations rather than a matched old-mode comparison.
Actual tools remain Lean 4.24.0 and Lake 5.0.0-src+797c613; fresh bounded KeySort
prerequisites pass. Production Lean, statements, budgets and axioms are unchanged;
two staged test-only files were added without generated-root or module-map edits.
All 792 original obligations, full acceptance and the original +80.254966536%
Lean STOP remain. Raw final captures, legacy refusals and manifests are retained
under `/workspace/h62-audit-readonly-calls/metadata-observations/` on the original VM.

## Lossless accounting of completed declaration observations

The additive `account_observed_declarations.py` executes the fresh Scope metadata
observer, preserves its completed observation, and accounts for every imported
constant and lexical source row exactly once. It rechecks protected child JSON,
logs and exact staged source bytes and requires the original source-range join to
recompute identically. This is not a new compiled/runtime artifact recertification,
source identity inference or semantic/witness/ownership result.

Two final byte-identical ledgers retain all 312 Scope constants and 37 lexical
rows. The 25 existing direct links are unchanged. The remaining constants are
classified by recorded evidence: 242 have no compiler range, 28 have a range whose
fragment differs from the declaration name, and 17 have a matching-name range
without a legacy link. All 17 of the last group are constructors; no constructor
identity is inferred or attached. All 26 legacy expression-metadata refusals are
in the no-range category. Their separate v2 observations remain separate; V1
retains 286 serialized and 26 refused records, while v2 observes all 312 types.

All 174 controls pass, including seven new omission/duplicate/correspondence,
parent-range nonpromotion, version/refusal and replay controls. Independent
read-only finder and skeptic reviews found no substantive issue and used no Lean
server or execution. Existing producers/exporters/scanner paths were unchanged;
new workflow timings are observations, not a matched prior-workload comparison.
Actual tools remain Lean 4.24.0 and Lake 5.0.0-src+797c613; fresh bounded KeySort
prerequisites pass. No Lean file, statement, definition, budget or axiom changed.
All 792 original audit obligations, original +80.254966536% Lean STOP and full
original/inherited acceptance remain open. Raw ledgers and capture chains remain
at `/workspace/h62-audit-readonly-calls/declaration-accounting/` on the original VM.


## Upstream context and identifier integration

Rebased the assigned branch onto master ba3c0f1539c8b64ac0c6c89e729481d3d398ee83
rather than duplicate its multiline lexical-context and Lean identifier-boundary
fixes. The old head f9328c235cf6ba9f062fed44c23585f9ce8e0520 remains under
`refs/h62-backups/pre-context-upstream` and in the exported history bundle.
Historical evidence packets retain their original identities.

The conflicting selection cases retain this lane's existing policy: safe internal
aliases remain distinct lexical input rows with shared-source warnings; broken,
escaping, nonregular or inaccessible selected inputs suppress incremental
conclusions. Recursive globbing excludes directory symlinks; finite patterns can
select a contained directory alias. Three reconciliation controls adapt the
upstream invalid-input, alias and failed-literal cases to this policy. This does
not establish intrinsic signature equivalence or live ownership.

All 181 Python controls pass. Five alternating measured text-scan pairs after a
warmup pair on the same 27-file, 296-declaration tree show median 0.144871182s
before and 0.137663267s after (-4.98%); peak child RSS 15104 KiB. Source hashes,
lexical identities and rejection fields match on that corpus. Multiline context
and Unicode boundary changes are exercised by dedicated fixtures; candidate keys
remain lexical approximations. The bounded runner uses 512 MiB address space,
10-second CPU limit, no swap and 4 GiB available reserve.

A fresh isolated Scope observation passes with all 37 lexical rows and 312
imported constants, preserving 25 links and all evidence categories. Legacy V1
retains 286 serialized types and 26 metadata refusals; separate V2 observes 312.
Fourteen Lean controls and the bounded KeySort prerequisite pass. Actual tools
remain Lean 4.24.0 and Lake 5.0.0-src+797c613. No model source or toolchain changed
in this integration; Scope/AST/KeySort bytes match the pre-rebase branch.
Independent read-only finder and skeptic reviews found no issue and ran no Lean
server. Detailed gates and old/new Git history are exported under
`/workspace/h62-audit-readonly-calls/upstream-context/` on the original VM.

All 792 original obligations, unresolved/private/global coverage and refusals
remain. This text-scanner timing does not clear the original +80.254966536% Lean
STOP. Full original/inherited acceptance, owner RO v2 migration, actual V13
compiler success with fixed V15/P10 outcomes, and exact retired proof-cleanup
object recovery remain outstanding. No RUNTIME_GATE_PASS is claimed.


## General project declaration accounting

The shared `declaration_ledger.py` now accounts for every recorded constant and
lexical row for the admitted unchanged KeySort, AST and Scope sources. The new
`account_project_declarations.py` defaults to KeySort; AST and Scope require an
explicit target. It always runs the existing fresh producer, verifies its returned
receipt and exact staged source, recomputes the source-range join, and rechecks
child metadata, bindings, receipts, logs and source before sealing the ledger.
Saved receipts cannot authorize a run. Dependency artifact identities remain in
the referenced completed-child capture; the parent does not recertify its runtime.

Fresh captures retain these per-target observations, without creating links:

| Target | Lexical rows | Observed constants | Existing direct links | Legacy metadata refusals |
|---|---:|---:|---:|---:|
| KeySort | 32 | 161 | 16 | 0 |
| AST | 135 | 781 | 98 | 0 |
| Scope | 37 | 312 | 25 | 26 |

The table is per imported observation, not a global declaration census. Every
unmatched range, missing range, constructor/generated record, type refusal and
ownership uncertainty remains explicit. Matching a range fragment never creates
a source link. The existing Scope metadata wrapper reuses the same core and
retains its byte-identical ledger, including the separate v2 domain. A fresh
wrapper run also passes all fourteen Lean controls and preserves all 26 V1
refusals while recording 312 separate v2 types.

All 189 Python controls pass, including generic target/count/refusal, omitted-row,
module/path mismatch, post-child mutation, replay and shared-core provenance
controls. A warned matched comparison on identical saved Scope inputs gives
0.010005347s before and 0.010100444s after per accounting call (+0.95%); full output
is equal. Five alternating pairs follow a warmup, fifteen calls per sample in
the same process, capped at 512 MiB address space and 30 seconds CPU. Observed
whole-process peak RSS is 37008 KiB, not independent per-version peaks. Fresh
producer timings are observations, not matched performance comparisons.

Finder review caught the missing shared-core hash in the existing Scope receipt;
the fix records its initial hash just as the new driver does. Final finder and
skeptic reviews found no remaining issue; neither executed tests or used a Lean
server. Initial tool hashes and completed-child checks are not remote attestation.
Actual versions remain Lean 4.24.0 and Lake 5.0.0-src+797c613; all fresh bounded
KeySort prerequisites pass. No Lean source, statement, budget or axiom changed.
All 792 obligations, original +80.254966536% Lean STOP, live ownership limits,
producer waits and unfinished original/inherited acceptance remain. This adds no
feasibility, compiler-success, body-equivalence or RUNTIME_GATE_PASS claim.
Evidence and deterministic reproduction commands are saved on the original VM
under `/workspace/h62-audit-readonly-calls/project-accounting/`.

## Declaration modifier accounting

The scanner now recognizes `public`, `meta` and `nonrec` along with its
previous declaration modifiers, including modifiers split across lines and
following attributes. It retains visibility and all recognized modifier
spelling in candidate keys. Body candidates with different modifiers retain
an explicit differing-statement rejection, in addition to the unresolved
signature and ownership reasons. Attribute-associated declaration
indentation uses the prefix line so an indented closing attribute line does
not itself make the declaration appear nested. This is lexical recognition;
the scanner can still overaccept invalid modifier orders and does not account
for macro-generated declarations or all Lean syntax.

Independent finder and skeptic reviews without Lean identified the missing
modifiers and the multiline case and rechecked the final controls. The Python
suite passed 41 tests. Two intermediate test runs failed while correcting the
attribute-prefix indentation and are not passing evidence. A matched bounded
whole-tree pair took 113.383 seconds before and 109.784 seconds after
(-3.17%). Both used the same 7,273 inputs, recognized 122,960 declarations
and reported no file errors or unmatched globs. Statement-group counts changed
from 4,481 to 4,412 as modifier distinctions were retained; body-group
counts stayed 5,516. Counts do not establish group membership or signature
semantics. Reports and controls are outside Git under
`/workspace/h62-duplication-scanner-evidence/declaration-modifiers/`.

## Scoped option lexical boundaries

Line-initial `set_option` commands now contribute context spans and terminate
preceding bodies; an indented boundary rejects the body fingerprint. Within
recognized option spans, an `in` followed on the same line by a declaration
keyword, modifier or attribute prefix makes the file incomplete, including
split option headers and modifiers continued on a later line. This prevents
the demonstrated hidden or misqualified declaration cases. The check is a
conservative lexical heuristic: it can refuse ambiguous text, does not model
the exact lifetime of scoped options, and does not handle every wrapper or
macro form. Candidate signature and ownership rejection reasons remain.

Independent finder and skeptic reviews without Lean identified and rechecked
the split-header and split-modifier cases. The final Python suite passed 42
tests. An initial overly broad guard caused a full-tree scan to exit 1 with
eight file refusals, and one intermediate split-modifier test failed; both
are retained as failed evidence. The refined implementation's matched pair
on the same tree and input took 109.784 seconds before and 119.423 seconds
after (+8.78%), within the 10% threshold. Both used the same 7,273 inputs,
recognized 122,960 declarations and reported no file errors or unmatched
globs. Statement-group counts changed from 4,412 to 4,413; body-group counts
remained 5,516. Counts do not establish equal group membership, intrinsic
signatures or complete declaration coverage. Reports, failed attempts,
controls and timings are outside Git under
`/workspace/h62-duplication-scanner-evidence/set-option-context/`.

## Recursive and finite alias accounting after integration

After rebasing onto the published signature-linkage and selector work,
recursive `**` selection now reports an incomplete scan when it skips a
directory symlink or encounters a dangling symlink. Finite directory
components explicitly report dangling or inaccessible symlink targets, even
when a different path matches. Explicit valid finite aliases retain their
logical paths and existing shared-source and containment checks. Recursive
selected paths continue to match the no-follow selection set, but the report
is incomplete when a directory alias was skipped; incremental removals and
candidate deltas remain null on selection errors.

This is point-in-time accounting, not a race-proof source attestation. An
explicit outside-root directory alias can still be enumerated before per-file
containment rejects its selected files. Lexical candidates retain unresolved
signature and ownership reasons; no semantic or unowned conclusion follows.

Finder and skeptic independently reviewed the rebase and selection fix
without Lean. The combined Python suite passed 195 tests. An initial run
failed because an upstream test expected skipped recursive aliases to be
silent; the reconciled test now requires an incomplete report while retaining
its finite-alias checks. A matched bounded scan took 110.215 seconds before
and 115.784 seconds after (+5.05%). Both used the same 7,303 inputs,
recognized 123,314 declarations and reported no file errors or unmatched
globs. Complete reports matched after normalizing scanner identity. Evidence
is outside Git under
`/workspace/h62-duplication-scanner-evidence/rebased-recursive-links/`.

The rebased repository documentation-path gate exited 1 on two missing
references named A.lean and B.lean, cited by the upstream audit-evm-compiler
scope test. These are outside this scanner lane; the gate remains failed.

## Finite directory alias containment

Finite directory symlinks are now resolved and checked against the selected
root before descent, for both literal and wildcard components. Outside-root,
dangling and inaccessible targets make the report incomplete; valid
inside-root aliases retain logical paths and existing shared-source checks.
This closes the stable-filesystem pre-descent enumeration issue noted above.
Resolution, containment check and enumeration are not atomic, so concurrent
replacement remains outside this guarantee.

Finder and skeptic independently reviewed the change without Lean. The
combined Python suite passed 196 tests, including literal and wildcard
outside aliases, a guard against enumerating the outside alias, and prior
inside-root alias controls. A matched bounded scan took 115.784 seconds before
and 113.029 seconds after (-2.38%). Both used the same 7,303 inputs,
recognized 123,314 declarations and reported no errors or unmatched globs.
The complete reports matched after normalizing scanner identity. These are
external lexical-tool checks, not proof of race-free confinement, complete
census or intrinsic-signature equivalence. Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/alias-containment/`.

The documentation-path gate still fails on the two upstream scope-test
references noted above. The first containment-check run also flagged two
references in this document's description of that failure; those descriptions
were corrected and the rerun reports only the two upstream failures.

### Integrated scanner report replay

Two bounded default-mode scans using the same tree, scanner, selection,
registry and caller-pinned previous report took 113.029 and 112.626 seconds
and produced byte-identical reports, SHA256
`88402b7207ab6655e5b48ce066f13c168eb68fdefac431a254a38a068260beb2`.
Both selected 7,303 files and recognized 123,314 declarations, with no file
errors, unmatched globs or reported aliases; all recognized owners remain
unknown. Relative to the older caller-pinned report, 30 inputs were added,
four changed and none removed. The scanner and tree both changed from that
baseline, so candidate deltas combine tool and input effects. The prior pin
identifies bytes, not an authenticated producer.

The scans did not invoke the upstream opt-in fixture or project
signature-binding paths. Independent finder and skeptic reviewed the replay
without Lean. These runs demonstrate repeatability for this snapshot, not
complete census, signature equivalence or live ownership. Full reports and
timing records are outside Git in the alias-containment evidence directory.

## Compound class declaration inventory

The lexical inventory now preserves the compound kinds and actual declaration
names for line-initial `class inductive` and `class abbrev` forms. Both remain
explicitly rejected as unsupported declaration forms: no statement or body
candidate is emitted for them. Controls cover ordinary classes, modifiers,
attributes, split compound keywords and surrounding body boundaries. This
does not enumerate constructors or establish complete Lean parser coverage;
source-binding receipts must match the updated row identities and cannot be
reused merely because a previous inventory existed.

Finder and skeptic independently reviewed the change without Lean. The
combined Python suite passed 197 tests. A matched bounded full scan took
116.686 seconds before and 113.712 seconds after (-2.55%). Both used the same
7,321 inputs, recognized 123,559 declarations and reported no file errors or
unmatched globs. No compound-form row was recognized in that selected project scan; the
focused controls demonstrate the identity correction. Statement
and body group counts remained 4,441 and 5,551 respectively, which does not
prove equal membership or semantic equivalence. Evidence is outside Git
under `/workspace/h62-duplication-scanner-evidence/compound-class/`.

## Explicit universe declaration names

The inventory now stops a declaration name before an explicit universe suffix
such as `.{u}`, preserving qualified names. The suffix remains in the header
and is conservatively rejected as unsupported binder syntax; no intrinsic
signature or body equivalence is inferred. Controls cover attributes,
modifiers, qualified names, multiple or multiline universes, malformed
suffixes and surrounding declaration bodies. Source bindings must match the
updated row identities and cannot reuse stale expected inventories.

Finder and skeptic independently reviewed the change without Lean. The
combined Python suite passed 198 tests. A matched bounded scan took 113.712
seconds before and 124.977 seconds after (+9.91%), within but close to the
10% stop threshold. Both used the same 7,321 input hashes, recognized 123,559
declarations and reported no errors or unmatched globs. The real selected
line in CollisionBound changed from the name `EagerAdaptiveBound.` to
`EagerAdaptiveBound`; both versions reject its unsupported binder syntax.
Equal group counts do not prove equal memberships or semantics. This single
measurement is not a Lean runtime gate. Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/universe-names/`.

### Universe-name report replay

Two bounded scans with the same tree, scanner, selection, registry and
caller-pinned previous report took 124.977 and 117.117 seconds and produced
byte-identical reports, SHA256
`55fbe28e339cbdb0e2c6e693fd0d58c1bd2cf0810e1ce8b7a4a886b49b540ea3`.
Both selected 7,321 files and recognized 123,559 declarations, with no file
errors, unmatched globs or reported aliases; all recognized owners remain
unknown. Relative to the older caller-pinned report, 18 inputs were added,
20 changed and none removed. The scanner and tree both changed from that
baseline, so group deltas combine tool and input effects. The prior pin
identifies bytes, not an authenticated producer.

The first after time was +9.91% against the recorded 113.712-second before
sample; the repeat was +2.99% against that same before sample. Both are
reported separately and neither crossed the 10% stop threshold. The pair of
matching reports demonstrates repeatability for these runs, not a robust
performance bound, complete census, signature equivalence or live ownership.
No opt-in fixture or project signature binding was invoked. Independent
finder and skeptic reviewed the replay without Lean. Full reports and timings
are outside Git in the universe-names evidence directory.

## Escaped declaration source spellings

The inventory now recovers escaped declaration components from the
comment-masked source spelling, including qualified, empty and multiline
components. It preserves the distinction between a single escaped component
such as `«a.b»` and an unescaped qualified spelling. This is lexical source
text, not a resolved Lean `Name`; escaped-name statements and bodies remain
explicitly rejected. Anonymous examples remain anonymous, and source bindings
must still use their admitted exact-location and environment checks.

Finder and skeptic independently reviewed the change without Lean; the
skeptic identified the empty/multiline component case and the final controls
cover it. The combined Python suite passed 199 tests. A matched bounded scan
took 113.984 seconds before and 118.999 seconds after (+4.40%). Both used the
same 7,369 inputs, recognized 124,000 declarations and reported no errors or
unmatched globs. Three checked real rows changed from anonymous to the exact
spellings `«return»`, `«split»` and `«a.b»`; their unsupported-signature and
escaped-body refusals remain. Group counts are not a proof of equal members,
full lexical coverage or Lean semantics. Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/escaped-declaration-names/`.

Named instances with explicit priority clauses remain a separate accounting
limitation; the scanner can still report such a named instance as anonymous.

## Named priority instances

The lexical inventory now recovers an optional source-spelled instance name
after a balanced priority clause and recognizes `scoped` among declaration
modifiers. All priority-instance statements and bodies remain explicitly
rejected as `unsupported-instance-priority`; anonymous instances remain
anonymous, and malformed unterminated priority clauses make the file
incomplete. Recovered private and scoped names are source spellings, not
canonical kernel identities. This resolves the named-priority accounting
case noted above without asserting priority semantics or full parser coverage.

Finder and skeptic independently reviewed the change without Lean. The
combined Python suite passed 200 tests, including five real metadata-fixture
names, anonymous and escaped names, scoped/private qualifiers and malformed
clauses. A matched bounded scan took 118.999 seconds before and 112.620
seconds after (-5.36%). Both used the same 7,369 inputs and reported no file
errors or unmatched globs; recognized declaration count changed from 124,000
to 124,001. In the checked fixture, five named rows are now recorded and each
retains both statement and body refusal. Group counts do not establish equal
membership, intrinsic signatures, proof semantics or live ownership. Evidence
is outside Git under
`/workspace/h62-duplication-scanner-evidence/priority-instances/`.

### Priority-instance report replay

Two bounded default-mode scans with the same tree, scanner, selection,
registry and caller-pinned previous report took 112.620 and 118.052 seconds
and produced byte-identical reports, SHA256
`fea9d7989a7ec05ca4ad6c14bb6e94afd164721055f49291f5e0321ee5020417`.
Both selected 7,369 files and recognized 124,001 declarations, with no file
errors, unmatched globs or reported aliases; all recognized owners remain
unknown. Relative to the older caller-pinned report, 48 inputs were added,
seven changed and none removed. The scanner and tree both changed from that
baseline, so candidate deltas combine tool and input effects. The prior pin
identifies bytes, not an authenticated producer.

No opt-in fixture or project signature binding was invoked. Finder and skeptic
reviewed the replay without Lean. This establishes repeatability for these
runs, not complete census, resolved kernel names, signature equivalence or
live ownership. Full reports and timing records are outside Git in the
priority-instances evidence directory.

## Scoped open command guard

The conservative inline scoped-command guard now covers `open` as well as
`set_option`. An inline declaration keyword, modifier or attribute prefix
after `in` makes the file incomplete, including split headers and prefixes.
Following-line declarations and ordinary open commands remain recognized.
This prevents the reported silent omission, but scoped namespace lifetime and
arbitrary wrappers or macros remain lexical approximations; ambiguous text
may be refused. Candidate signature and ownership rejection reasons remain.

Finder and skeptic independently reviewed the implementation without Lean.
The combined Python suite passed 201 tests, including incomplete-report,
multiline, attribute and string controls. A first baseline attempt was refused
before starting because the conservative resource preflight lacked 2 GiB of
job headroom beyond the 4 GiB reserve. Task-owned bulk-report cache pages
were released without changing files; the actual matched pair used the same
8 GiB address-space cap, re-advised the prior report before the after scan,
and sampled cgroup availability every half second. Neither run hit the
resource stop. This sampling is not a continuous or hidden-ancestor guarantee.

The pair took 118.079 seconds before and 118.075 seconds after (-0.0034%).
Both used the same 7,445 inputs, recognized 124,796 declarations and reported
no file errors or unmatched globs. Complete reports matched after normalizing
scanner identity. This is an external lexical-tool measurement, not a Lean
runtime gate, complete census or signature proof. Evidence is outside Git
under `/workspace/h62-duplication-scanner-evidence/scoped-open/`.

The repository documentation-path gate exited 1 on a missing witness reference
in the upstream audit-v09-passes document, outside this scanner lane. The
initial resource refusal is recorded as a transcription of the visible tool
response, not an independently captured runner log. Cache advice was applied
to the prior report before each scan, but the receipts do not prove identical
operating-system cache state.

## Initializer inventory boundaries

Line-initial `initialize` and `builtin_initialize` commands now terminate a
preceding declaration body and appear in the lexical inventory. The optional
named form is recognized only when a source-spelled identifier and type are
followed by a top-level left arrow; anonymous initializer bodies remain
anonymous. All initializer statements and bodies are explicitly rejected as
unsupported, and inline scoped initializer declarations make a scan
incomplete. This is not an elaboration of initializer semantics or a complete
parser for every layout and macro form.

Finder and skeptic independently reviewed the implementation without Lean;
they identified and rechecked the scoped-wrapper omission. The combined
Python suite passed 202 tests. A matched bounded scan took 118.075 seconds
before and 118.580 seconds after (+0.43%); both used the same 7,445 inputs,
8 GiB address-space cap and sampled reserve monitor, with no resource stop,
file error or unmatched glob. The prior report cache was re-advised before
each scan, but the receipts do not prove identical operating-system cache
state. Recognized declarations increased from 124,796 to 124,822, including
26 initializer rows, all explicitly rejected. The checked real source rows
include nextAuditOrigin, auditOrigin and importedAudit. Equal group counts do
not establish equal members or semantics. Evidence is outside Git under
`/workspace/h62-duplication-scanner-evidence/initializer-inventory/`.

The repository documentation-path gate remains failed on the same missing
witness reference in the upstream audit-v09-passes document noted above.

### Initializer report replay

Two bounded default-mode scans with the same tree, scanner, selection,
registry and caller-pinned previous report took 118.580 and 124.087 seconds
and produced byte-identical reports, SHA256
`1f589f93859bf026421c9e3ef06bffc815f0dc3f73c1ef0c04db30b3ea7b52be`.
Both selected 7,445 files and recognized 124,822 declarations, with no file
errors or unmatched globs; all recognized owners remain unknown. All 26
initializer rows retain statement and body rejection. Relative to the older
caller-pinned report, 76 inputs were added, 11 changed and none removed. The
scanner and tree both changed from that baseline, so candidate deltas combine
tool and input effects. The prior pin identifies bytes, not an authenticated
producer.

No opt-in fixture or project signature binding was invoked. Finder and skeptic
reviewed the replay without Lean. The 8 GiB cap and sampled reserve monitor
did not trigger a resource stop; sampling and cache advice do not prove
continuous or identical operating-system conditions. These runs demonstrate
repeatability for this snapshot, not complete census, Lean semantics or live
ownership. Full reports and timings are outside Git in the
initializer-inventory evidence directory.

## Include and omit context boundaries

Line-initial `include` and `omit` commands now contribute lexical context
spans and terminate preceding bodies. Indented command boundaries reject the
body fingerprint, and inline scoped declaration prefixes make a file
incomplete. This addresses the reported body contamination and context-hash
collision. Scope lifetime and implicit dependencies remain lexical
approximations; signature and ownership rejection reasons remain mandatory.

Finder and skeptic independently reviewed the change without Lean. The
combined Python suite passed 203 tests, including differing include/omit
contexts, prior-body boundaries, nested commands and incomplete inline scopes.
A bounded same-tree scan took 123.081 seconds before and 123.593 seconds after
(+0.42%). Both used the same 7,491 inputs, recognized 125,638 declarations
and reported no errors or unmatched globs. Statement-group counts were 4,511
in both; body-group counts changed from 5,664 to 5,666. Counts do not prove
equal memberships or semantic equivalence. Both scans used an 8 GiB address
space cap and sampled cgroup reserve monitor without a resource stop; cache
advice does not prove identical operating-system cache state. Evidence is
outside Git under
`/workspace/h62-duplication-scanner-evidence/include-omit/`.

## Anonymous examples and unsupported binders

Examples are recorded as anonymous: identifiers after `example` are not
source declaration names. An example signature is rejected from statement and
body grouping unless its result type follows only supported explicit binder
groups. In particular, bare binders both before and after typed binders are
rejected. This conservative lexical rule can refuse valid complex examples;
it does not identify generated kernel declarations or establish source binding.

The Python suite passed 204 tests. Independent finder and skeptic reviews
without Lean identified and rechecked the mixed-binder case. A bounded scan
of the same selected tree and pinned previous report took 123.593 seconds
before and 124.583 seconds after (+0.80%), with an 8 GiB address-space cap
and a sampled 4 GiB reserve monitor that did not stop either scan. Cache
advice does not prove identical cache state and sampling does not prove
continuous reserve. Evidence is outside Git in
`/workspace/h62-duplication-scanner-evidence/example-binders/`. Complete
Lean declaration and case accounting, authenticated source/dependency binding,
current ownership and final gates remain open.
