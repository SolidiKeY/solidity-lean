# H62 item 1: binding fixtures — preliminary census

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The supplementary
lease names 18 `Solidity/Source/Agreement/*Controls.lean` files. None contains
the token `BindingRel` at this base. The audit describes ten controls with
private relations; a textual census finds ten `def BindingRel` declarations
under `Solidity/Lowering/V07` and seven `abbrev BindingRel` declarations under
`Solidity/Lowering/G19`. The ten V07 definitions are syntactically public, not
`private def`; their fixtures may nevertheless be specific to each control.
The original relation files and V07 files are not included in the supplementary
lease. No inference about permission to edit them follows from this census.

Run `python3 scripts/h62/item1/binding-fixtures/census.py` from any directory.
It enumerates tracked Lean source paths using Git and reports matching lines in
stable Git order as JSON. It is a lexical inventory: comments and references
are included, and multiline or differently named declarations are not parsed.
It does not establish semantic equivalence or exhaust all fixture cases. The
census is backfill, not a completed fixture-extraction checkpoint.

Lean 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
5.0.0-src+797c613. Under the writer lock, with `LEAN_NUM_THREADS=1`,
`lean -j1 Solidity/KeySort.lean` exited 0 with no output. Two census runs
compared byte-for-byte equal, and `python3 -m py_compile` passed. No Lean
statement or proof was changed. No before/after proof timing, extraction, full
validation, independent finder review, or skeptic review has yet occurred.
All four checkpoints remain pending. Exact-file owner coordination remains
necessary before modifying V07 originals; relation unification stays with its
owners. The assigned source controls are separately leased, but they do not
contain the named relations, so their relationship to this extraction needs
careful case-by-case analysis.

## H70 case reconciliation (source inspection, not a Lean proof)

`python3 scripts/h62/item1/binding-fixtures/reconcile.py` produces per-file
SHA256s, declaration names and line numbers, lexical `BindingRel` occurrences,
and source import reachability for the two named sets. At the base it reports
18 leased files with 105 named top-level theorems, ten V07 definitions, and
seven G19 abbreviations. None of the leased files contains the token; neither
set reaches a file in the other set through the scanned imports. The scanner
follows only column-zero, single-line `import` commands for files present in the
checkout: this is evidence about that source graph, not a Lean elaborator or a
proof of semantic independence. The output lists every named declaration so
that counts cannot stand in for case accounting.

The leased controls are separate source/model observations:

| Control file (`Solidity/Source/Agreement/`) | Cases, including negative and fuel controls |
|---|---|
| `BoolSlotAndControls.lean` | conjunction client, horizon, selected/skipped writes, short fuel, operator distinction |
| `BoolSlotConditionalControls.lean` | conditional client, horizon, true/false branches, reversal, selected/skipped writes |
| `BoolSlotControls.lean` | middle-slot source/model writes and wrong-slot refusal |
| `BoolSlotNotControls.lean` | negation client, horizon, both Boolean inputs and identity refusal |
| `BoolSlotOrControls.lean` | disjunction client, horizon, selected/skipped writes, short fuel and conjunction distinction |
| `BoolSlotReadControls.lean` | read then assign, client, two fuel controls, distinct copy and alias refusal |
| `BoolSlotRepeatedControls.lean` | double toggle, insufficient horizon, different slots and restoration refusal |
| `BoolSlotSavedControls.lean` | saved toggle, insufficient horizon, both inputs and overwrite refusal |
| `BoolSlotToggleControls.lean` | toggle client, horizon, both inputs, twice-toggle source/model and old-result refusal |
| `NormalBoolAssignControls.lean` | Boolean initialization and assignment, source/model/client, two horizons and wrong value |
| `NormalBoolControls.lean` | two Boolean initializations, source/model/client, two horizons and wrong value |
| `NormalControls.lean` | skips, agreement/client, zero horizon, early return and revert refusal |
| `NormalDefaultControls.lean` | defaults source/model/client, two horizons, names and wrong value |
| `PrimitiveCopySequenceControls.lean` | head/deep preservation, model heads, swap refusal, inward copy and order |
| `PrimitiveSavedAssignControls.lean` | middle/heads, Boolean case and old-target refusal |
| `PrimitiveSlotAssignControls.lean` | middle source/model, uint/int cases, reverse model and refusal |
| `PrimitiveSlotControls.lean` | primitive read client, horizon, uint/int copy and wrong value |
| `PrimitiveSlotReverseControls.lean` | middle/tail, Boolean case and direction refusal |

The ten V07 relation definitions are separately accounted for below. Reference
arms are exact initial memory/storage identities and unmatched cases are false
where the definitions say so; their removal or broadening is not authorized.

| Control file (`Solidity/Lowering/V07/`) | `BindingRel` cases |
|---|---|
| `P12Controls.lean` | Boolean equality, unsigned integer keys, fixed memory/storage identities, otherwise false |
| `AddressConversionControls.lean` | nonpayable address relation; other cases delegate to P12 |
| `AddressQualifierControls.lean` | address relation for qualifier `p`; other cases delegate to P12 |
| `EnumConversionControls.lean` | enum relation, fixed reference identities, otherwise false |
| `EnumSignedCastControls.lean` | enum relation, fixed reference identities, otherwise false, in its own environment |
| `FixedBytesAssignmentControls.lean` | fixed-byte relation, fixed reference identities, otherwise false |
| `UdvtAddressAssignmentControls.lean` | address UDVT relation, fixed reference identities, otherwise false |
| `UdvtAssignmentControls.lean` | integer UDVT relation with typed cast, fixed reference identities, otherwise false |
| `UdvtBoolAssignmentControls.lean` | Boolean UDVT relation with underlying-type witness, fixed reference identities, otherwise false |
| `UdvtFixedBytesAssignmentControls.lean` | fixed-byte UDVT relation, fixed reference identities, otherwise false |

The G19 files `AssignmentDoWhileBreakControls.lean`,
`AssignmentDoWhileContinueControls.lean`, `AssignmentForBreakControls.lean`,
`AssignmentForReturnControls.lean`, `AssignmentReturnFlagControls.lean`,
`AssignmentWhileBreakControls.lean`, and `WhileReturnControls.lean` each
abbreviate `P12Controls.BindingRel`; the aliases do not define seven new
relations. Their control-flow cases differ and are not covered by the leased
Source Agreement controls. No assertion of interchangeability follows from
similar cases, nor is moving a statement across modules validated here.

Independent finder and skeptic reviews remain outstanding. This reconciliation
is preliminary backfill; all fixture extraction checkpoints and their Lean
proof, resource, timing, acceptance, and full validation gates remain pending.
The coordinator has stated V07 is Claude-owned and that no original-file
permission is inferred; any required exact-file request must go through the
coordinator, not a VM installation of `relay.sh`.

## H71 census controls

Run `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item1/binding-fixtures/test_reconciliation.py`.
The controls compare the 17 named relation paths with the separate lexical
census, check the 18-file/105-declaration inventory and all seven alias texts,
and exercise a synthetic reachable cycle, a missing path, an unrelated path,
and a block-comment line that the scanner intentionally misreads as an import.
All three controls passed. These are external Python checks of census behavior,
not Lean proofs, a completeness proof of the lexer, or independent reviews.
A separate scan of the 191 files in the current lexical closure found no
missing `Solidity.*` module paths and no `public import`, `private import`, or
`import` followed by a tab. This check does not rule out other syntax or a
comment that resembles an import. V07 exact-file coordination is awaited from
its current Claude owner; the host-only relay is not installed or invoked here.

## H82 exact-source inventory backfill

`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/binding-fixtures/source_intervals.py`
captures the complete UTF-8 text of the ten V07 and seven G19 controls as a
preamble plus intervals starting at lexical declaration markers. Each file and
interval carries a SHA256 and each interval its original starting and ending
line. Its generated JSON is saved outside Git with the evidence manifest. Two
runs were byte-identical. `test_source_intervals.py` reconstructs each of the
17 files byte for byte, checks each interval hash, checks one `BindingRel`
marker per file, and exercises no-marker and block-comment false-positive
controls. It does not identify exact Lean declaration boundaries, separate
statement from proof, prove coverage of every language construct, or perform
fixture extraction. Comments and commands may belong to an adjacent interval.
No original file or frozen statement was edited. Owner coordination and
independent reviews remain outstanding; this inventory is not a completed
checkpoint or proof gate.

## Retirement handoff

The successor is `solidity-directruntime-20261104/shared-translator`. The
reconstructed assignment and exact path lists are in
`tests/h62/item1/binding-fixtures/handoff-assignment.md` and
`tests/h62/item1/binding-fixtures/handoff-scope.json`. The exact original
rendered prompt was not available as a file or through a goal-read tool, so
its required hash cannot be verified from this reconstruction. Obtain the
original from the coordinator. All extraction checkpoints, fixture proofs,
independent reviews, timing, acceptance and full validation remain open.
The bounded P12 MCP baseline was interrupted on retirement and did not pass.

## Successor intake and lexical controls (2026-11-06)

H82b authenticated metadata and all package checksums were verified. Final control-tuples `2366c57f099b27d4673dda504d258ba77ff3fcaf` and binding-fixtures `d1fcc57d78356fbdf38cbb12d4dd89df074c1295` were merged; coordinator confirms both stopped, paused and quiescent. The former frozen-assignment metadata wait is resolved by that authenticated package. Referenced external evidence archives remain separate delivery dependencies. Published master `5f14596531efea2be64f1a5e7a83afa5e151e865` was subsequently merged without discarding owned work.

The earlier comment false-positive controls above describe the historical scanner. The current shared lexical filter masks nested comments, strings, raw strings including zero hash delimiters, and character literals while preserving character positions and newlines. Quoted identifiers are masked and explicitly listed as unknown with original text and line in census, reconciliation and interval reports. Declaration/reference/import accounting is therefore incomplete for quoted identifiers; this remains a lexical inventory, not a Lean parser. Original interval text remains untouched and all 17 files still reconstruct byte for byte.

Six lexical, four reconciliation and two reconstruction controls passed. Independent read-only finder and skeptic used no Lean/server; their raw-string, trailing-escape and quoted-name findings were fixed and re-reviewed. `lexical-controls-manifest.json` records actual commands, exits, elapsed times and off-Git evidence hashes. No Lean statement, proof, interface, axiom, budget or exclusion changed. All four fixture-extraction checkpoints, proof gates, before/after Lean timings and full acceptance remain open. H81 policy clarification still gates heavy validation.


## Isolated P12 reference-fixture proof backfill

`tests/h62/item1/binding-fixtures/ReferenceFixtureControls.lean` adds five
controls over the unchanged P12 witness: memory/storage related-pair uniqueness,
memory/storage absent-target refusals, and explicit inhabited pairs for both
branches. Values and target references stay at P12's fixed layout and heap.
These are consequences of that fixture relation, not a new relation, relation
unification, arbitrary equal-content aliasing, cross-heap transport or a
source/world/compiler adequacy theorem. The positive witnesses address
empty-relation vacuity; the contradiction eliminations prove explicit refusals.
No original V07/G19 file, frozen statement or producer interface was edited.

All five kernel proofs pass and match the existing P12 `BindingRel`/`initial`
axiom reports exactly: `propext`, `Classical.choice`, `Quot.sound`. Source
SHA/Git comparison confirms P12Controls.lean is unchanged. The first MCP
attempt returned incomplete after 303.947 s of cold dependency setup, exit 2,
not a resource stop or passing diagnostic. Explicit serial dependency build
completed 106 jobs (including cached jobs) in 134.673 s and KeySort passed.
Cached diagnostics succeeded; after adopting published master a10b60f23315,
the import build/kernel checks passed again and MCP reported zero errors
in 6.6747 s. The post-merge validation command took 2.2197 s; these are checking
wall times, not matched performance acceptance. Before/after extraction
measurements remain pending because no extraction/refactor was performed.
Actual versions: Lean 4.24.0/Lake 5.0.0-src+797c613; unchanged 12 GiB/no-swap,
CPU 1, threads 1/-j1 and 4 GiB outer reserve. No runtime STOP was rerun or released.

`validate_reference.py` checks the exact five-declaration inventory, unchanged
producer bytes, standard/existing axiom footprints and the precise write scope.
An initial multiline declaration-name pattern failed before the Lean gate;
its exit 1 log is retained. Finder/skeptic found caller-dependent gate-log
routing: fixed by deleting the prior log and setting the subprocess destination
explicitly. The corrected verifier passed with caller `GATE_LOGS` unset.
Both reviewers rechecked the fix without Lean/server/builds or writes.
The only extra metadata edit pins the owned Shared ownership audit to immutable
published master a10b60f23315; all allowlists are checked unchanged.

Run from the checkout through the existing bounded runner:
```bash
bash tests/directruntime-20261104/shared-translator/bounded.sh env -u GATE_LOGS PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/binding-fixtures/validate_reference.py
```
The verifier derives its base record from pinned Git/source bytes, so these
controls require no VM-only fixture metadata. Existing records with altered
provenance are rejected. Shared full-evidence validators still require their
separately manifested H44 archives; this does not close that portability follow-up.

`reference-fixture-manifest.json` records the H44 evidence archive and source
pins. `validate_reference.py --pack` deterministically packs retained logs,
reports, authenticated assignment/scope copies and checksums; two encodings and
member roundtrip are verified. Restore under `artifacts/reference-fixture` for
historical evidence inspection. The packet contains proof evidence and authenticated metadata. H82b's 557 checksums and retired member ancestry were verified.

| Test registration proposal | Purpose | Dependency |
|---|---|---|
| `tests/h62/item1/binding-fixtures/ReferenceFixtureControls.lean` | Fixed P12 reference witness positive/negative controls | `Solidity.Lowering.V07.P12Controls` |

This is a standalone per-file test candidate; no generated root or central
module map was edited and no production registration is claimed. All four
fixture-extraction checkpoints, original declaration/case accounting, full
before/after extraction timings and acceptance remain open. Shared translator
H90/importer obligations and native/browser stack/cost holds also remain open.


### Published-master replay scope

Fixture source identity remains pinned independently to a10b60f23315 and its
P12 SHA. Edit-scope checking now delegates to the existing consolidated Shared
ownership audit at its explicitly recorded immutable publication, after
comparing every non-publication metadata field with the original authorized
scope. Published master history therefore is not mistaken for new unowned edits.
No allowlist expands; original P12 bytes still must match. The helper passed on
published80c156bf13d1 with the active Shared portability work present.

The historical `reference-fixture-manifest.json` records source pins at
16c7ecb40198 explicitly and uses a repository-relative evidence locator. Its
17,454-byte evidence archive remains off Git under H44, unchanged at SHA256
`cdac20d72b1e6aeabb26072ec3d1d815b7dfe5966f7a72295b92628da1d36d31`.
Current helper checks are recorded separately by portable-validation-manifest.json;
none of these metadata changes closes an extraction checkpoint.


### General fixed-reference proof backfill

`RigidReferenceControls.lean` extends isolated proof coverage from P12 to the
memory and storage arms of all ten inventoried V07 relations. Three general
lemmas derive inhabitedness, pair uniqueness and absent-target refusal from an
exact fixed-reference branch. Ten fixture theorems supply explicit witnesses
for both arms; qualifier, integer-type and fixed-byte-width parameters remain
universally quantified with their existing constraints. This covers twenty
reference arms without copying the three proofs for every fixture.

The property describes each unchanged relation at its own fixed layout and
heap. It neither replaces nor identifies the producer relations, relates
arbitrary equal-content objects, proves source/world transport, nor covers
their primitive arms or G19 control-flow behavior. All four extraction
checkpoints and before/after extraction measurements remain open.

The initial MCP response was incomplete during cold dependency compilation
(exit 2, no resource stop); it is not a passing diagnostic. After serial import
builds, cached MCP diagnostics report zero errors. A direct kernel check and
KeySort pass under Lean 4.24.0/Lake 5.0.0-src+797c613, with the unchanged 12 GiB,
no-swap, one-thread/explicit `-j1` bounds and 4 GiB reserve. All thirteen theorem
axiom reports are standard-only; the general lemmas introduce no axioms.
The new-file checks are individual checking observations, not matched
before/after performance acceptance. No stopped benchmark was rerun.

Independent read-only finder and skeptic found no scope, coverage, vacuity or
relation-unification blocker; neither used Lean/server/builds or wrote files.
All ten producer sources are byte-identical to the pre-work commit. Logs,
source hashes, axiom reports and the incomplete setup record are archived in
the private H145 evidence lane, outside the code branch. No generated root,
central module map or production registration was edited.

| Standalone per-file candidate | Purpose | Dependencies |
|---|---|---|
| `tests/h62/item1/binding-fixtures/RigidReferenceControls.lean` | General exact-reference laws and twenty fixture-arm witnesses | The ten inventoried `Solidity.Lowering.V07.*Controls` relation modules |
