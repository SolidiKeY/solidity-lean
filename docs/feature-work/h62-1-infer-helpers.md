# H62 item 1 infer helpers — preliminary handoff

Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4. This is an incomplete
inventory, not a completed checkpoint. Scope is the copied helpers only;
H55 retains both inferencers and their relations.

The lexical census reports Source `STy.isMapping`, `STy.isPayableArg`,
`STy.convLoc` and Frontend Static `isMappingTy`, `payableArg`, `convLoc`.
Its negative control detects a missing, duplicate, or unavailable source
file. It is not a Lean parser and cannot establish declaration equivalence,
reference completeness, or semantic preservation.

No Lean statement, proof, axiom, sorry, or original source was changed. No
helper module, migration patch, owner coordination, independent finder or
skeptic review, acceptance gate, affected validation, or comparative timing
has been completed. All four checkpoints and assigned backfill remain.

The coordinator-pinned official Lean 4.35.0 archive was verified against
SHA-256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Lean reports 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake reports 5.0.0-src+eb6cafb. A direct bounded KeySort diagnostic exited
0 in 1.91s, but does not satisfy the required MCP or run-lean.sh gate.
No runtime gate is claimed. The first attempted Lake command rejected -j1
as a Lake option; another diagnostic lacked /usr/bin/time. Neither passed.

Next: configure the pinned toolchain and serial -j1 driver without reusing
4.24 artifacts; obtain the required KeySort prerequisite; finish census,
fixtures and additive helpers, compare exact behavior and timings, arrange
owner coordination and independent reviews, then perform all required gates.

## Shape census and migration blocker (continuation)

`check_shapes.py` compares the six declarations with fixed token snapshots,
ignoring whitespace. It is a lexical check, not a Lean parser, proof, or
reference scanner. `test_shapes.py` checks all six against independent branch
mutations, and checks duplicate declarations, token splitting and absent files.
Both this test and `test_census.py` pass on the pinned base.

The source case inventory below covers the 18 `STy` constructors. Mapping
and payable columns are the expected Boolean outputs of both copies; the
location column is the expected output of both copies. For bytes/string,
`loc` is the input location, including memory, storage and calldata.

| Constructors | Mapping | Payable | Conversion location |
| --- | --- | --- | --- |
| `mapping` | true | false | memory |
| `address`, `contract` | false | true | memory |
| `bytes`, `string` | false | false | loc |
| `int`, `bool`, `fixedBytes`, `fixed`, `enum`, `udvt`, `array`, `struct`, `fn`, `rational`, `hexConst`, `stringLit`, `tuple` | false | false | memory |

These are source observations, not kernel-checked equivalence theorems.

On the unchanged base, the pinned 4.35.0 `./run-lean.sh` run used the
separate cache and external Lake configuration recorded in the evidence
directory, `LEAN_NUM_THREADS=1`, `-j1` per Lean process, a 12 GiB virtual
memory limit and the writer lock. The log shows `Solidity.KeySort` built in
1.5 s and then errors in `Solidity/Hash/CollisionBound.lean` (first at line
407: unsolved goal) and `Solidity/Language/FixedPoint.lean` (first at line
152: `generalize` failed). The already-failed run was interrupted, exit 130;
it did not complete the final gate. These files are outside this lane. No
runtime-gate pass or before/after comparison is claimed. Continue with
in-scope backfill; full validation requires the toolchain-migration owners
 to supply a compatible base, without changing frozen statements.

The writer-lock and exact-file ownership rules remain in force. A filesystem
search did not find `relay.sh` on this VM; no owner request or approval is
claimed. No inferencer merge or edit was made.

## H70 continuation: candidate cases and scanner repair

Coordinator routing reports the source-relations, migrate-hash and
migrate-language owner tickets accepted. These tickets do not authorize
changes to their files. The source-relations owner retains inferencer
unification; the earlier 4.35 build failures in `Solidity/Hash/CollisionBound.lean`
and `Solidity/Language/FixedPoint.lean` remain prerequisites for final gates.
The host-only `relay.sh` is not a VM installation task.

`tests/h62/item1/infer-helpers/CaseSpecifications.lean` is an additive candidate
with one explicit branch per `STy` constructor and source/static equality
statements. It imports the original inferencers and has not been elaborated
or kernel checked. It is not registered as a library module and is not proof
evidence. The candidate still needs a permitted bounded Lean check after the
migration prerequisites are resolved. No original file or frozen statement
was changed.

`check_cases.py` compares constructor names in `Solidity/Source/Types.lean`
with the candidate case names; `test_cases.py` checks missing, duplicate and
new-constructor controls. This is a lexical coverage check, not a check of
expected values, theorem elaboration or semantics. The census and shape
scanner previously counted definitions inside block comments; an author
review found that defect. `lean_mask.py` now masks ordinary nested comments,
line comments and strings before locating declarations, and rejects
unterminated comments/strings and unsupported quoted identifiers and
raw/interpolated strings. This remains a limited lexical scanner, not a Lean
parser. Added controls cover the reported comment failure and mask boundaries.

Independent finder and skeptic reviews are still required and must be
performed by reviewers other than the author without a Lean server. Please
review `scripts/h62/item1/infer-helpers/` and
`tests/h62/item1/infer-helpers/CaseSpecifications.lean`; this self-review is
not a substitute. Full acceptance, helper extraction, proof checks, proposed
migration, and comparison timings remain pending.

## H70 case-value controls and current dependencies

After `git fetch origin master`, master was
`96788a95383b6295dc13774ef681297adf1337a7`. The three copied pairs and the
18 `STy` constructors remain present there; the files owned by this lane
are absent from that tree. The five relevant original files, including the
hash and language files which failed under 4.35, have no changes between the
frozen base and that master. No completed version of this lane item was found
on master, so no rebase was performed.

`check_case_values.py` checks every constructor argument pattern and expected
triple in the candidate specification against an explicit textual oracle. It
rejects additional wildcard arms. `test_case_values.py` mutates each of the
three expected results in every case (54 mutations) and checks rejection.
This and the other scanner tests pass. This is external text checking: it is
not a Lean proof and does not establish equivalence to the inferencers.

Remaining producer dependencies are the accepted migrate-hash ticket for
`Solidity/Hash/CollisionBound.lean`, the accepted migrate-language ticket for
`Solidity/Language/FixedPoint.lean`, and H55/source-relations for coordination
of any proposed changes to `Solidity/Source/Infer.lean`,
`Solidity/Frontend/Static/Infer.lean`, and
`Solidity/Frontend/Static/InferComplete.lean`. Independent finder and skeptic
reviewers must also review the scanner and the Lean candidate; no independent
review is claimed here. The 4.35 full gate, candidate elaboration, proof and
axiom checks, before/after timing, migration patch and all checkpoint gates
remain pending. No new original-file edits or weakened statement were made.

## H70 semantic-specification continuation

The 18-constructor candidate now also states separate universal equality of
the two mapping, payable and conversion-location helpers, and positive and
negative witnesses. These include a top-level mapping versus an array whose
element is a mapping, both address payable flags, a contract name, a Boolean
payable refusal, and location preservation/default behavior. These are
unverified Lean statements and proof terms, not established theorems. The
case and value scripts remain lexical controls, not a substitute for Lean.

The reviewed hash owner overlay at
`2a18afcdba00a85645b0b3079704f78ffcd78860` was delivered for isolated
migration use. The checkout source blobs match its base prefixes exactly:
`Solidity/Hash/Adaptive.lean` is `cb5d5a1c61f7350aa01d9d0c81c8f4403b19fab3`
and `Solidity/Hash/CollisionBound.lean` is
`b54c93a5b24340a19160c1fb378d057ccee60f84`. The overlay has not been applied;
full hash migration gates, language migration and source-relations agreement
remain pending. No owner-file permission or completion is inferred.

A local Lean MCP package was discovered and two per-file diagnostic attempts
were made under the writer lock and memory guard. Although the LSP server and
worker were started with `-j1`, each attempt launched a `lake setup-file`
dependency check using the original configuration, and its child Lean command
lacked explicit `-j1`. Both attempts were stopped when observed. They do not
count as diagnostics or proofs; logs are in the evidence directory. A retry
must ensure the dependency setup uses the serial configuration before running.
The existing Lean source was not changed. Independent finder and skeptic
reviews, all checkpoint gates and timing comparisons remain pending.

## H70 typed owner compatibility inventory

The owner-facing boundary includes the inline premises of the original
relation, not just helper-to-helper equality. Source observations at the
frozen base are:

| Relation constructor | Source inferencer | Static inferencer | Completeness consumer |
| --- | --- | --- | --- |
| `Typed.delete` (`Solidity/Source/Typing.lean:849`) requires a non-mapping test and `Γ.deleteRefused τ e = false` | `STy.isMapping` in `Solidity/Source/Infer.lean:217` | `isMappingTy` in `Solidity/Frontend/Static/Infer.lean:202` | `delete_res` in `Solidity/Frontend/Static/InferComplete.lean:306` preserves both premises |
| `Typed.payable` (`Solidity/Source/Typing.lean:921`) requires an address-or-contract test | `STy.isPayableArg` in `Solidity/Source/Infer.lean:320` | `payableArg` in `Solidity/Frontend/Static/Infer.lean:591` | `payable_mem` in `Solidity/Frontend/Static/InferComplete.lean:721` preserves the true premise |
| `Typed.convElem` (`Solidity/Source/Typing.lean:912`) fixes the result location and requires `σ.explicit Γ.isBase τ = true` | `STy.convLoc` in `Solidity/Source/Infer.lean:298` | `convLoc` in `Solidity/Frontend/Static/Infer.lean:572` | `convElem_mem` in `Solidity/Frontend/Static/InferComplete.lean:700` retains the conversion test and the constructed result type |

The in-scope candidate now includes two non-mapping premise equivalences and
six typed constructor applications, one per helper copy. The delete
applications retain `deleteRefused`; payable retains the true premise;
elementary conversion retains the explicit-conversion premise and exact
result type. These terms have not been elaborated or kernel checked. They do
not authorize editing any original inferencer or prove the owner agreement.

The coordinator supplied partial owner patches for Hash CollisionBound and
Language FixedPoint with respective claimed SHA-256 values
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff` and
`a3cbeea6c8a243df761166dd558825898f2bbda8c8fa7d8a74850cd27cb8ad82`.
The local source blob IDs match the patch base IDs:
`b54c93a5b24340a19160c1fb378d057ccee60f84` and
`e2d7e18f385707bd375f9b326314b51b9b583b57`, respectively. The named patch
files were not found in the available coordinator-input or shared folders,
so their byte hashes were not independently verified and neither patch was
applied. Their full migration gates and the H55 source-relations agreement
remain pending.

## H70 completeness-consumer compatibility candidates

After the required fetch, `origin/master` was
`0b2a648b32335f35ff323ff468f75907e926fc13`. The relevant Source and Static
inferencer, typing and completeness files have no diff from the frozen base;
the lane artifacts are absent on master. No rebase was performed.

The new additive `tests/h62/item1/infer-helpers/CompletenessCompatibility.lean`
records three candidate applications of the existing static completeness
consumers using source-helper premises:

* `source_delete_res` retains both `τ.isMapping = false` and
  `Γ.deleteRefused τ a = false`, and targets membership in `prefixOne`, not
  full `infer` membership.
* `source_convElem_mem` retains both the existing inferred-operand membership
  and the explicit-conversion test at `el.ty σ.convLoc`.
* `source_payable_mem` retains both the existing inferred-operand membership
  and `σ.isPayableArg = true`.

These are candidate statements and proof terms only: neither their
elaboration nor their definitional-equality assumptions have been checked.
They do not prove equivalence between the Option-returning source inferencer
and the list-returning static inferencer, and they do not alter the H55-owned
relations or completeness theorem. No premises or exclusions were weakened.

The reported Hash CollisionBound overlay is still partial and its full gates
remain pending. The host-only path in the owner ticket is not a VM artifact;
the prior base-blob match does not verify the patch bytes. Language FixedPoint
migration and exact source-relations agreement are still outstanding. The
independent finder/skeptic reviews must include this new candidate file.

## Retirement handoff

The final additive `tests/h62/item1/infer-helpers/Shared.lean` candidate
imports `Solidity.Source.Types` and proposes the three shared definitions with
inline-rule correspondence statements. It is unregistered and has not been
Lean checked. It does not change original inferencers, and H55 has not reviewed
this file. Its intended destination, migration patch, registration fragment,
compatibility with frozen producer interfaces and proof/axiom checks remain
open. The exact frozen source snapshot and checksums are exported separately.

A bounded 4.35 MCP check through the corrected serial Lake route reported
`CaseSpecifications.lean` diagnostics unavailable with failed dependencies
`Solidity/Source/Const.lean`, `Solidity/Source/Ctor.lean` and
`Solidity/Source/Types.lean`. A separate serial MCP diagnostic on
`Solidity/Source/Ctor.lean` reported an isDefEq heartbeat timeout at line 641
and dependent elimination failures at line 715. No proof budget was changed.
These are failed diagnostics, not a gate pass; see the saved logs.

The successor is `solidity-sol2-20261104/numeric-literals`. All four original
checkpoints, backfill proofs, independent finder/skeptic reviews, exact owner
migration proposal, affected validation, acceptance, axiom checks, timing
comparison and final handoff gates remain incomplete. Waits include migration
of Source/Ctor, Language/FixedPoint and Hash/CollisionBound, H55 review of
this exact extraction and compatibility candidates, and independent reviews.
The exact original rendered prompt bytes are unavailable in this VM; the
committed queue excerpt explicitly identifies this limitation. The user
requested pause, but the only exposed goal tool accepts complete or blocked,
not paused. Do not resume this assignment without further authorization.
No H71 push permission was supplied in this thread; the original instruction
prohibits pushing, so this lane was not pushed.

## Resume after master integration

The coordinator explicitly resumed this lane and requested merging master.
The prior lane head was an ancestor of `origin/master`, so the lane was
fast-forwarded to `5f14596531efea2be64f1a5e7a83afa5e151e865`. The reported
master touched gate and reviews concern that integration; they do not validate
this new continuation or replace its pending independent reviews.

`Shared.lean` now has a passing per-file MCP diagnostic using the pinned
Lean 4.35.0, `LEAN_NUM_THREADS=1`, explicit `-j1` on the server and worker,
one open file, the writer lock and a 12 GiB virtual-memory limit. The saved
structured result reports `success=true`, `partial=false`, no failed
dependencies and three information messages: each correspondence theorem
uses `[propext]`. This covers only the additive shared module, not either
inferencer, the other candidates, import migration or full validation.

`propose_migration.py` emits `migration-proposal.patch` deterministically from
the current originals and the shared module. The proposal would add the
not-yet-created module
`Solidity.Source.InferHelpers`, import it from the two inferencers and
keep each existing helper name and type while changing its definition body
to call the shared definition. It was not applied; `git apply --check` passes
on this tree. It is a review artifact, not a checked migration: changed
definition bodies require the H55 owner, and theorem definitional equality,
all premise shapes, axiom inventories and timing must be checked after any
owner-approved adoption. No inference or relation merge is proposed.

Suggested owner registration fragment, subject to the final destination and
owner approval, for `docs/module-map/source-definitions.d/<lane>.md`:

The proposed Source-area row would name module `InferHelpers` and describe it
as shared top-level mapping, payable-argument and elementary conversion-location
helpers. Its destination file does not exist in this checkout.

The owner/coordinator must integrate the module registration and generated
roots according to repository policy; this lane has not edited them. The
review patch includes a new module path and changes existing definition
bodies, so it must not be applied merely on the strength of the text check.
Candidate compatibility files still fail to reach diagnostics because of
Source/Ctor migration failures. Full Hash and language migration, independent
finder and skeptic reviews, H55 agreement, affected validation, acceptance,
axiom comparison and before/after timings remain pending.

The shared module additionally checks eight direct witness examples: positive
mapping, an array containing a mapping (negative top-level test), both address
flags, contract and Boolean payable cases, bytes/string location preservation,
and the default array location. Per-file Lean 4.35 MCP diagnostics returned
`success=true`, `partial=false`, no failed dependencies and the same three
`[propext]` axiom reports. The patch proposal was regenerated after these
additions; its applicability check is not a semantic or full-gate pass.

## Integration and proposal drift controls

The coordinator reported the prior lane head integrated with a touched gate
and finder/skeptic review. `origin/master` was fetched and the clean lane
fast-forwarded to `b7c3cc5110b1ebee1eab45e8b1b9894ecada7237`. That tree
contains `tests/h55/source-relations/HelperCompatibility.lean` at SHA-256
`52d196ff64fe34b366d8b3f0456abd50e05ccf0284c522cd91432f4213eb302a`,
matching the separately supplied H55 handoff. That interface includes the
full conversion result-type premise, six adapters and three completeness
consumers. The H55 handoff reports a standalone 4.24 check and independent
reviews; it does not establish 4.35 validation or approval of this extraction
proposal. Do not duplicate the H55 interface.

`test_propose_migration.py` independently exercises the proposal generator on
copied fixtures: each of the six original declaration anchors is altered in
turn, and an already occupied destination is supplied. Every case is rejected
before any patch text is emitted. These are external controls for proposal
drift, not proof that applying the proposal preserves Lean statements or
axioms. The proposed patch still applies in check mode and remains unapplied.
The new control itself needs the usual independent finder/skeptic review.

Source/Ctor 4.35 errors, the full Hash and language migration gates, H55
agreement on existing definition bodies, frozen-statement and axiom checks,
full affected validation, acceptance and timing comparison remain open. No
prior stopped Lean build was rerun unchanged. No new owner source edit was
made, and no master push was performed.

## Re-baseline after drift-control integration

The coordinator reported the lane change integrated on master with touched gate
pass and finder/skeptic reviews. On fetch, master was
`2a43bf4fcdaf24750265afc8f8be5b420d1d22b0`. The reported lane commit
`07a49ac680edb41984c427aebc3049680a738e02` was not its ancestor, but the
cherry-picked commit `1a12272db` has the identical stable patch ID
`cb8071c8419de76ab4a255021c83b26b1f66f315`, and all lane scope files matched.
A normal merge retained the original lane ancestry and produced
`7e053a71fb811d3ae9f348480d477b038dcf76c4` without conflicts.

This tree includes Source/Ctor proof migration `087f76aa8360db0b89aa99b4f8fcc0022b925e4d`.
Using official Lean 4.35.0 and a freshly generated current-tree alternate Lake
configuration with explicit `-j1`, one open MCP file, `LEAN_NUM_THREADS=1`,
the writer lock, a 12 GiB virtual-memory limit and a 4 GiB available-memory
guard, the direct `Solidity/Source/Ctor.lean` diagnostic returned success
without items or failed dependencies. This is a per-file diagnostic, not a
full gate or timing comparison.

The candidate `CaseSpecifications.lean` still returned
`diagnostics_unavailable` with failed dependencies including the source and
static inferencer files. Separately, `Solidity/Frontend/Static/Infer.lean`
returned success with two unused-variable warnings. `Solidity/Source/Infer.lean`
returned six errors: dependent slice type mismatches at lines 308, 312, 315
and 316, and type mismatches at 345 and 382. The exact structured MCP logs
are exported; this lane did not edit the H55 inferencer or weaken types.
H55/source-relations must assess these current-tree diagnostics before the
combined candidate can be validated. The case file is still not known clean.

The proposal generator output remains byte-identical to its checked-in patch
and `git apply --check` passes on this tree; no proposal was applied. The seven
external scanner/control tests pass when temporary-file writes are permitted.
A first test attempt in the read-only sandbox failed because no writable
scratch directory was available; that attempt is not counted as a pass.
Owner agreement, independent reviews of any new changes, full affected gates,
axiom comparison, acceptance and timing remain outstanding.

## Proposal live-anchor control

The lane fast-forwarded to the coordinator-reported master
`cc1ea1c9c99522bff459dcc57e41339e1f347243`, which contains the previous lane
head. The relevant inferencer, Source/Ctor, language and hash files did not
change from the last diagnostic tree, so the earlier failed 4.35 source
inferencer check was not rerun unchanged.

An author review found that the proposal generator counted exact anchors even
when their only occurrence was inside a block comment. It now requires each
import and declaration anchor to be live according to the existing limited
Lean text mask before emitting any patch. Negative controls comment out each
of the six helper definitions and the import; all are rejected without output.
The generated patch remains byte-identical on the current tree and passes
`git apply --check`. This is a lexical safeguard, not a Lean parser, semantic
proof, independent review, or permission to apply the proposal. Unsupported
syntax and ambiguous anchors continue to fail the generator.

The coordinator reported touched-gate success and finder/skeptic reviews for
the integrated prior head. Independent review of this new control remains
pending. H55 agreement, Source/Infer 4.35 repair, migration gates, full
compatibility checks, axiom comparison and before/after timings remain open.
