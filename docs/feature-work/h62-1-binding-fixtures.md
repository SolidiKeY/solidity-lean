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
