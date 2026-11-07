# Readonly bind census and fixture specification

Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4. Preparation only: no
migration, owner approval or Lean validation is claimed.

| Original declaration | Case and retained observation |
| --- | --- |
| CapturePhases.compose | Five successful phase runs, admission false, actual post-instance state and captured values/bytes. |
| CaptureFailures.target_failed | Receiver halts at s1, before subsequent phases. |
| CaptureFailures.value_failed | Receiver succeeds, value halts at s2. |
| CaptureFailures.arguments_failed | Receiver and value succeed, arguments halt at s3. |
| CaptureFailures.encoding_failed | Earlier phases succeed, encoding halts at s4. |
| CaptureFailures.code_rejected | Phases and lookup succeed, no-code rejection reverts at s5. |
| EnvironmentCredit.known | Known instance and successful credit continue from final state. |
| EnvironmentCredit.unknown | No instance; continue from recorded state without credit. |
| EnvironmentCredit.failed | Known instance and failed credit return the same halt and final state. |
| EnvironmentCredit.callback_credit_failed | Admitted callback, known instance, failed credit; return same halt and final state before callback continuation. |

The halt branch must preserve the state returned by the first computation,
not the original state, and must not run the continuation. The success branch
must run the continuation on the returned state. All original premises, states,
branches, statements and producers remain frozen. These equations do not
establish a callee-body producer, whole-world preservation or native behavior.

Existing controls, not rechecked here: CaptureFailureControls provides
rejected_after_arguments, effect_not_rolled_back, no_callee_events,
receiver_exhaustion and admitted_control. EnvironmentCreditControls provides
static_credit_finishes, storage_kept, unknown_credit_skipped, overflow_halts,
callback_overflow_halts and callback_failure_has_only_attempt.

For remaining failure phases construct inhabited isolated fixtures using actual
typed evaluator inputs; an assumed run equation is not a witness. Include
observable state changes and a distinguishable continuation for both bind
branches, admitted and rejected code, known and unknown instances, and callback
guard acceptance and refusal. Do not claim an original theorem covers a branch
outside its premises. Record each fixture's producer, result and scope. Existing
controls do not establish that all ten cases are inhabited.

Solidity.Source.Hoare.run_bind already states the same equation over the
reducible EMState alias and imports Solidity.Source.Machine. Assess import
direction, exact elaborated statements, timing and dependency cost before
deciding whether to reuse it or introduce an additive shared lemma. Import
compatibility and timing equivalence have not been established.

The census is textual, not a Lean parser. Its synthetic controls are external
Python tests, not kernel proofs; they cannot establish semantic use, statement
equivalence or exhaustiveness under arbitrary Lean syntax. H55 V08/StorageOps
fixtures and Yul capacity_exact are excluded.

Reproduce with `python3 scripts/h62/item1/readonly-bind/census.py` and
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/readonly-bind/test_census.py`.
The latter passed six controls on 2026-11-06. Independent finder and skeptic
reviews and Lean checks remain pending; this preparation is not a milestone
acceptance. Exact-file RO agreement is requested for all three original files
listed above before edits.

## Isolated proof-sharing candidate

H71 grants owner agreement for the three exact files with the hashes pinned in
`scripts/h62/item1/readonly-bind/overlay.py`. The ticket JSON was not present at
its stated VM path; the coordinator message supplied the agreement and hashes,
which matched the checkout. Originals remain untouched. The generator creates
an additive overlay that imports the existing `Solidity.Source.Hoare.run_bind`,
removes each private copy and replaces proof references. `overlay.py --check`
verifies exact generated text against the pinned originals. It does not prove
semantic equivalence by itself.

With Lean 4.24.0 and Lake 5.0.0, serial `-j1` and bounded memory, the three
original modules built, then all three overlay modules elaborated. Existing
FullCaptureControls, CaptureFailureControls and EnvironmentCreditControls
also elaborated with overlay objects. Ten `#print axioms` outputs matched the
originals byte for byte: propext, Classical.choice and Quot.sound. Five paired
warm-cache measurements per file yielded median deltas of -9.18%, -6.69% and
-6.20%, respectively; these do not include building the extra Hoare dependency.
The initial sparse overlay failed to locate Hoare; a symlinked isolated library
with the overlay objects resolved the namespace lookup. Raw evidence is in
`/workspace/scratch/h62-readonly-bind/evidence/`.

This is a candidate, not an accepted migration: independent finder and skeptic
reviews, added inhabited fixture proofs, scope-complete affected validation,
full final gate and registration/owner integration decisions remain pending.

`tests/h62/item1/readonly-bind/BindControls.lean` checks synthetic success and
failure computations over the existing concrete `before`/`after` source states.
It proves those states differ, success applies the continuation to the returned
state, and timeout retains that state and bypasses the continuation. It does
not instantiate the remaining actual capture-phase failure premises. The file
elaborated under the bounded overlay setup; new phase fixtures remain pending.

## H82 migration and retirement handoff

H82 permits the statement-preserving proof changes directly. The three original
modules now match the previously checked overlay: the private duplicates are
replaced with the existing `Solidity.Source.Hoare.run_bind`. The generator now
uses the pinned Git base as its source and checks both the overlay and migrated
files. The migrated census reports zero private copies and the same ten direct
consumers. Seven Python controls pass against frozen-source copies and the
migrated tree. The three migrated modules and their three direct control modules
built serially (73 jobs). `PhaseControls.lean` supplies actual value and argument
timeout witnesses using the original theorem types, in addition to the existing
receiver-failure and code-rejection controls. Encoding-failure inhabitation
remains open; synthetic `BindControls` do not establish it.

The full `./run-lean.sh` run was interrupted deliberately at 38/4372 jobs to
allow remaining fixture work; it exited 130 and is not a passing gate. Complete
affected and full validation, direct theorem axiom audit after migration,
independent finder and skeptic reviews, remaining fixture/acceptance coverage,
and before/after timing confirmation on the final tree remain open. Prior
paired timings cover the text-identical overlay; they exclude initial Hoare build
cost. No statement, premise, definition body, proof budget or exclusion was
intentionally changed. See the checksum manifest in the VM evidence handoff.


## Checked source-statement replacements for the three removed private helpers

The additive `private_mapping.py` pins the original792-record census and selects
exactly CapturePhases, CaptureFailures and EnvironmentCredit's private run_bind
statements. It preserves their complete signatures and variable contexts, then
generates three public audit adapters proved by `Solidity.Source.Hoare.run_bind`.
The concrete common input tuple proves parameter-domain satisfiability only;
it is not an actual capture-phase, compiler-success or Source-adequacy witness.
No production source, private identity, registration root or axiom pin is edited.

The first absence assertion failed: the normal cached environment contained the
old private identities for CapturePhases and CaptureFailures even though their
current source no longer declares them. That failure is retained. The revised
check records this cached view separately and rebuilds the exact current three
files plus Source.Hoare in an isolated library; all three old identities are
absent there. The cached/source disagreements are binding refusals, not evidence
that production source restored those names. Both views export five exact types
(three adapters, shared law, parameter-domain witness); source, query, helper,
module objects, process logs and manifest are rechecked before sealing.

The final bounded check passed in10.057s with774299648bytes peak aggregate RSS.
Nine unit controls cover original membership, intrinsic-context mutation,
namespace/visibility/context drift, non-restoration and missing/foreign/new axiom
records. All five observed axiom sets are exactly propext, Classical.choice and
Quot.sound. Compiler/version/toolchain are recorded; actual tools remain
Lean4.24.0 and Lake5.0.0-src+797c613. No sorry, new axiom, native_decide or proof
budget change. Existing workflow timings are observations, not matched speed
comparisons; no historical timing STOP or full-runtime gate is cleared.

Finder/skeptic review fixed two assurance gaps: the shared law is now compiled
freshly too, and axiom output is checked rather than merely printed. Other
project/SDK dependencies still come from the cached environment and are not
independently source-bound here. This is a four-file controlled compilation and
imported-law replacement check, not full current-source certification. Original
private identities remain unavailable in that view; all792 original obligations,
three private mappings and the full inherited queue stay pending where required.
Exact original raw types use distinct generated private matcher names; they are
not normalized or asserted identical to the shared theorem's raw type. Evidence
and portable reproduction data are on the original VM under
`/workspace/h62-audit-readonly-calls/private-bind-mapping/`.

The global documentation gate currently fails on two inherited synthetic fixture
references in another chain's tests/h62/item2/audit-evm-compiler/check_scope.py.
That file is byte-identical to current master; it was not edited here. Whitespace
checks pass. The documentation failure remains an outstanding global gate.


## Actual encoding-failure fixture (2026-11-07)

The additive test `tests/h62/item1/readonly-bind/EncodingFailureControls.lean`
closes the previously missing concrete encoding-failure phase fixture. A typed
`bool[] memory` reference points to an allocated one-element array. At one
shared state and fuel6, receiver evaluation, zero-value evaluation and identity
argument conversion all succeed; `encodeVals` then returns the exact
`stuck "not ABI-encodable"` failure. The unchanged
`CaptureFailures.encoding_failed` theorem transports those jointly checked
runs to the complete external-call expression at fuel7, with the same state.
The declaration's actual `fnSig` and heap allocation are checked. Declaration
membership in EB, general array ABI support, compiler success, source/callee
outcome correspondence and physical-frame adequacy are not claimed.

Reproduce under the existing serial bounded runner with
`scripts/h62/item1/readonly-bind/check_encoding_fixture.py --output NEW_DIRECTORY`.
It compiles exact current Source.Hoare, CapturePhases and CaptureFailures, then
the fixture and an axiom query, in a private library. Normal cached CaptureFailures
initially failed due to an evaluator signature mismatch; the failed attempts
are retained rather than reported as passing. The controlled fresh-leaf check
passed initially in5.451s; the final source-pinned check passed in4.532s at299130880bytes aggregate peak RSS. All four fixture theorem
axiom sets contain only propext, Classical.choice and Quot.sound. Remaining
project and SDK dependencies are cached inputs, not independently source-bound.
Actual tools: Lean4.24.0 (797c613), Lake5.0.0-src+797c613; one Lean process,
-j1,12GiB cap,4GiB reserve, no swap. No before/after rebaseline or runtime-pass
claim; the historical +80.254966536% Premises STOP remains unchanged.

All792 original obligations and original private identities are retained.
This completes one inherited actual fixture, not complete declaration/case
acceptance or any of the other inherited queues. Evidence, failed logs,
receipt and handoff are exported under
`/workspace/h62-audit-readonly-calls/encoding-failure/`.
H121 routes actual compiler-success/G42.04 adequacy to memory-reference-structs;
our full RO source/callee outcome and physical-frame correspondence remain
unfinished. The exact retired proof-cleanup object remains UNVERIFIABLE.


Independent read-only finder and skeptic confirmed joint feasibility and the
allocated typed argument. Both found an evidence sealing gap; it was fixed by
parsing the exact hashed log buffer and rechecking staged sources, objects,
probe, process logs, compiler, toolchain and runner identity before the receipt.
Targeted controls reject substituted compiler/toolchain/source/object/probe/log
bytes and missing, duplicate, foreign or sorryAx theorem records (three tests,
all refusal subcases passed). Neither reviewer used Lean or wrote files.
These external tooling controls do not prove the imported cached dependencies.

The final finder follow-up also required retaining the captured source digest
before compilation. The driver now checks that initial digest before and after
compilation; an orchestration control replaces both original and staged source
after fake compilation and verifies refusal. Both final reviewers report no
remaining confirmed finding within this checkpoint's stated boundary.
The documentation gate still fails only on the two inherited references already
routed to v17-validation-release; this checkpoint did not edit that other chain.


## Complete three-file source declaration and case ledger (2026-11-07)

`scripts/h62/item1/readonly-bind/case_ledger.py` accounts for every original
named declaration in the three pinned migration files:25 rows, consisting of
ten public laws, eleven retained private helper theorems, one retained definition
and three removed private run_bind source identities. Original file hashes are
pinned; current files must equal the exact authorized import/helper/proof-reference
transformation byte for byte. Definition and statement changes are refused.
The original792 artifact is authenticated by SHA256; all24 theorem rows in this
subset keep their original signature digest, context, source name and visibility.
The definition recorded is additional source accounting, not a new original792 row.

Every public law has one explicitly described branch and a source fixture
reference. Each removed helper has both Except constructor cases mapped to
synthetic bind controls. There are16 mapping records but only12 distinct source
theorem references: the same two synthetic controls are reused for each removed
helper. These counts do not represent16 independent proofs. Every fixture status
is source-reference-only-not-current-kernel-acceptance; no cached fixture, broad
feasibility, gas/fork variant, original private identity or source adequacy is
promoted. Existing separately checked encoding evidence remains separate.
The ledger always reports full_goal_acceptance=false.

The generic census now exposes declarations_text so both file-based and supplied
source parsing use the same namespace/section stack. Review found that merely
finding a namespace could misattribute a theorem after its closing end; this was
fixed by scoped parsing. Six refusal controls cover original membership and
bytes, definition/statement/helper drift, missing/commented/duplicate/foreign
fixtures and the moved-outside-namespace regression. Five existing census tests
pass; old and new lexical parser outputs match across all129 current original
module-map files, including two without an original theorem row. Exact overlay
and ten-consumer checks also pass. These are external scanner checks, not Lean
proofs or renewed frozen/current statement certification of the whole repository.

Independent read-only finder and skeptic confirmed the final attribution fix
and source-only boundaries; neither executed Lean or wrote files. No Lean source,
frozen statement, premise, budget, axiom or exclusion changed. No held Lean job
was rerun; historical +80.254966536% STOP and full acceptance obligations remain.
Evidence and reproduction ledger are under
`/workspace/h62-audit-readonly-calls/bind-case-ledger/`.


## Fresh current-source fixture closure (2026-11-07)

`scripts/h62/item1/readonly-bind/check_capture_fixtures.py` recompiles the full
current import closure for FullCaptureControls, CaptureFailureControls and
EnvironmentCreditControls, then the inherited PhaseControls, BindControls and
EncodingFailureControls tests. All77 project modules and three test modules
compiled. The axiom probe checked38 existing declarations: ten migrated public
laws and28 controls. Every observed set contains only propext, Classical.choice
and Quot.sound. This validates current fixture proofs and the changed-local,
return-byte, encoding-failure and environment-credit observations they state;
it does not prove generalized feasibility or source/compiler correspondence.

The driver has no project-cache scaffold. It strips inherited Lean/Elan root
variables, pins the SDK root/private library/one thread and checks compiler
prefix before and after. A real negative control temporarily removes the
fresh private Hoare object: Lean must return the exact private-path missing
object error. The original object is restored and its digest checked. Original
source bytes/import graph are pinned before compilation; final checks cover all
original/staged sources, objects, probe, logs, compiler and driver/helper inputs.
SDK-provided modules are not independently source-certified.

The final bounded run passed in389.118s at1602379776bytes aggregate peak RSS.
An earlier run passed in406.356s before the root-isolation hardening; its evidence
is retained separately. These are two gate observations with different driver
configuration, not a matched speed comparison or a timing rebaseline. The held
Premises module is refused during dependency traversal, before compilation;
its historical +80.254966536% STOP remains. Actual tools remain Lean4.24.0
(797c613) and Lake5.0.0-src+797c613,12GiB cap,4GiB reserve,no swap,-j1.
Current KeySort compiled successfully as part of this fresh closure. No runtime
pass, full repository gate or full inherited migration acceptance is claimed.

Seven external controls passed: dependency order/pins, held-module refusal,
cycle/missing/foreign imports, unsupported import syntax, root override removal,
object restoration on normal/error paths and current theorem inventory.
Independent read-only finder and skeptic confirmed the final fixes and saved
77/38 evidence; neither executed Lean or wrote files. No Lean source or proof,
statement, premise, exclusion, axiom or budget changed in this checkpoint.
All792 original obligations and three removed private identities stay accounted
for separately. Remaining work includes formal joint-witness/fidelity integration,
other guard/gas/fork boundaries, broader binding/live ownership and the full RO
source/callee outcome plus physical-frame producer. Bulk evidence is off Git:
`/workspace/h62-audit-readonly-calls/capture-current-closure/`.


## Callback guard boundary witnesses (2026-11-07)

`tests/h62/item1/readonly-bind/CallbackBoundaryControls.lean` guards confusing
callback refusal with credit failure or suppressing environment continuation.
One saturated-balance state, nonzero value, target, sender, calldata and strategy
are shared. At depth1024 in ordinary mode, the depth guard refuses the attempt;
at depth1023 in inherited static mode, the nonzero-value guard refuses it. Both
runs record a completed revert attempt and then let the strategy answer with
success bytes[7]. At adjacent admitted depth1023 in ordinary mode, actual credit
overflows: execution halts with only the attempt event. Balance and exact event
lists are checked. These are model depth/static boundaries, not EVM gas/fork,
constructor reachability or compiler/source-world adequacy claims.

Three explicit closed conjunctions supply every hypothesis of the two refusal
specializations and adjacent callback-credit failure. Clients apply unchanged
EnvironmentSteps.refused and EnvironmentCredit.callback_credit_failed. All eight
new theorem axiom sets are standard propext,Classical.choice,Quot.sound. Source
headers, variable contexts and visibility for these two original interface rows
match the authenticated792 census; historical dependency/kernel equivalence and
whole-audit status promotion remain pending. All792 rows and three removed private
identities remain; these supplemental cases are not counted as completed full
original acceptance.

`scripts/h62/item1/readonly-bind/check_callback_boundaries.py` admits only the
exact previously executed fresh-closure receipt SHA256
6cc6b35a60ec17a7082721c467f086f3c3cd0114b75405e6f36eec2a69f26bee.
It verifies all80 reused current source/object inputs, exact import graph, helper/
tool pins and SDK root before and after compiling the new module and axiom probe.
This is checked-artifact reuse, not a fresh dependency rebuild or independent SDK
source certification. Missing/substituted parent bytes require authentic recovery;
no arbitrary parent receipt or replacement baseline is accepted. Final bounded
check passed in6.274s at666099712bytes aggregate peak RSS; four external refusal
controls passed. Actual tools:Lean4.24.0,Lake5.0.0-src+797c613,-j1,12GiB cap,
4GiB reserve,no swap. Historical Premises +80.254966536%STOP remains untouched.

Independent read-only finder and skeptic confirmed the joint cases, observed
outcomes, dependency reuse and refusal tests; neither executed Lean or wrote
files. Initial syntax/state-rewrite failures are retained; corrected proofs use
the existing standalone strategy pattern and explicit post-refusal state.
No original statement, definition, premise, budget, exclusion or axiom changed;
no sorry/native_decide/newaxiom. Rebased onto coordinator master8863c41276f9;
all80 parent source inputs remained unchanged. Evidence and handoff are under
`/workspace/h62-audit-readonly-calls/callback-boundaries/`.
