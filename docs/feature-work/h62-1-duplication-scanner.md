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
