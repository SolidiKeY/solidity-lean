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
