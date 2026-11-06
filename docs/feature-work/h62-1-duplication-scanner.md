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
