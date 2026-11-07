# H19 natural Source accounts: interface step

Status: partial, owner-held; not ready for combined Source integration.

`Source.Account.balance` and `Account.withBalance` now use exact natural
money. Actual `ExecState.transfer` retains Word call value and delegates to
`transferNat`; affordability, distinct-recipient overflow refusal, self-transfer
no-op and the original rollback/refusal theorem strength are retained. Actual
credit/debit/deployment store exact natural balances. Known-code `evalE.balance`
uses the explicit modular `Monetary.wordView`; equality with exact money still
requires a separately proved range invariant. The external `Fixed.ledger` and
opening balance interface remain Word-valued and unchanged (H19-LEDGER1).

`Source.MonetaryWorld` states bounds on both current accounts and saved journal
accounts, proves withBalance/undo/undoN/rollback/endTx and actual successful
natural/Word transfer preservation, and pins twelve exact standard axiom sets.
Its wide-account control represents 2^256 exactly. Its saved-wide counterexample
shows that an in-range present world alone does not justify range after rollback.
These are execution primitive laws, not full reachable-EVM or session invariants.
Actual credit/debit/deployment range transport and initial-image closure remain open.

Measurements use the same serial bounded checker and source/import hashes:
[before/after numbers](vy5-natural-account-timings.json). World 0.642→0.595s,
Machine 1.674→1.642s, Eval 8.084→8.009s, Semantics 0.968→0.949s,
Horizon 346.956→340.924s, HorizonDeploy 8.888→8.849s,
Session 2.231→2.207s, Funds 0.242→0.246s. There is no noticeable checking-time
increase. Horizon remains a pre-existing FAIL against the 300-second module
policy; its kernel exit 0 does not waive that policy. Dependency-build elapsed
seconds are not these per-file checking times. Hard memory/swap limits remained
12GiB/12GiB; the after closure sampled 8,217,178,112 bytes aggregate RSS and
8,917,626,880 bytes minimum OS available, with no resource stop.

The two owned Source examples retain their exact prior numeric expectations.
The transfer example's actual axiom set decreased to empty; its pin was updated
after retaining the diagnostic mismatch. The initial range proof's let-reduction
failure is retained separately from the corrected per-file pass. Automation
attempts and exact signature output are preserved under
`/workspace/vy5-composition/natural-account-20261104/`.

Independent read-only finder and skeptic approved this narrow interface step,
with no findings; neither executed Lean or tests. They explicitly require the
remaining consumer migrations, whole-balance operations, external monetary
ledger decision, real reachability and full combined checks before release.
A hash-bound inventory records 57 downstream Source-account read files: the
two owned Source examples are migrated; 55 other read-file migrations remain. Whole-balance/selfdestruct consumers must use exact Nat operations,
not cast the amount to Word. No downstream compiler/EVM correspondence is claimed.

Queue: H16/P8a full execution/realization, immutable/funds release, remaining H19
consumers/ledger/reachability, all 24 original Y10 obligations and six general
Source combinations, Work2/3 and BackfillA/B remain partial or pending.
This step supplies no fresh native comparison. Original five optimized-viaIR
journal mismatches/exit1 and historical docs/G03 failures remain retained;
zero regression and finite Source controls are not full-lane gates.

## Whole-balance lifecycle consumer (2026-11-04)

The authorized H19 consumer migration updates VY4's existing Lifecycle module
to transfer the full natural account balance using actual `transferNat`. Burn
uses natural zero. Existing self-beneficiary, recipient overflow, actual two-entry
journal and rollback theorem conclusions remain intact, without new range
premises. Five owned controls prove full100 payment with retained caller
nonce/journal, complete rollback, distinct-recipient refusal for2^256, exact
old-self retention and fresh-self burn. Casting2^256 to Word would wrongly
produce a zero payment, so the refusal control discriminates that bug.

Both changed Lean modules and generated exact signatures pass per-file checks.
Five axiom guards pin four axiom-free controls and the existing rollback chain's
standard propext/Quot.sound. Independent read-only finder/skeptic approved this
narrow migration without findings and without executing checks. Initial runner
environment, reserved identifier, structure-update and non-Decidable state
equality diagnostics are retained alongside corrected passes.

The original57-file read inventory now has three migrated entries (two Source
examples and Lifecycle), leaving54 inventoried read-file migrations plus other
constructor/whole-balance sites. No full combined checkpoint, native comparison,
external ledger migration or actual reachable-EVM invariant is supplied. All
original queue and proof obligations remain open as recorded above.

## Balance observation and world-control consumers (2026-11-04)

Six further H19 consumers are migrated: VY4 WorldChecks/SelfDestructControls
and VY2 Views SourceBalanceInputs/SourceBalanceReads/StorageBalanceInputs/
SourceBalanceControls. Existing numeric values, storage/log/returndata traces,
rollback and overflow expectations are retained; two balance tuples now carry
Nat instead of Word. No Source core or evaluator body changes in this increment.

Known-code balance observations explicitly use `Monetary.wordView`, exactly
matching actual Source.evalE.balance. Existing observation/storage-preservation
laws gain no range premise. A separate new `sourceObservedBalance_system_exact`
law requires visible `Fits` for equality to the exact natural balance. External
ledger observations are unchanged. A synthetic2^256 Source account retains
its exact money, observes Word zero and evaluates that result through the actual
evaluator for arbitrary pipeline. This is a deliberate negative control against
claiming lossless projection without range, not a reachable-EVM witness.

All six changed modules and generated signatures pass focused checks; six exact
axiom guards retain only propext/Classical.choice/Quot.sound. Simp-only automation
proves the new bounded equality. Original tuple-type, structure-update and
Pipeline-name failures are retained separately. Read-only finder and skeptic
approved the scoped migration without findings; neither ran tests or Lean.
The57-file read inventory now has four migrated entries, leaving53 inventoried
read-file migrations plus other constructors and representation bridges. Full
H19 ledger/reachability, H16/P8 realization, immutable/funds release and all
original24 obligations/six Source combinations remain open. No fresh native
comparison, combined release gate or whole-lane completion is claimed.

## V08 account-consumer batch (2026-11-04)

44 existing V08 modules are migrated:37 inventoried direct account-balance
reads plus seven projection/constructor fixture dependencies. Numeric amounts,
full state vectors, traces, revert/timeout distinctions and proof budgets remain
unchanged. Source core modules are not edited in this increment.

EnvironmentProjection exposes `liftBalance = liftWord ∘ Monetary.wordView`.
Existing target observation laws use this explicit projection with no new range
premise. The new `lower_lift_balance_exact` has an explicit Fits premise; the
external session ledger stays unchanged. Generated signatures pin the new two
laws to standard propext/Quot.sound and contain checked wide2^256→Word0 and
non-Fits controls. These are projections, not a universal monetary ledger or
Source/EVM reachability proof.

The first38-file focused batch had34 passes and four failures. Actual dependent
errors identified WorldReset's old projection and conditional/compact Fin
account constructors in ProjectionControls/LibraryPremises. Those and five
additional constructor fixtures were migrated; every one of the final44
changed modules has a matching-source per-file exit0. Original failure logs
and their dependent axiom-error cascades remain preserved separately. No
failed gate is relabelled passed. Independent read-only finder and skeptic
approved the complete migration scope without findings; neither executed
Lean/tests.

Evidence: `/workspace/vy5-composition/natural-v08-20261104/`. The original
57-file read inventory now has41 migrated entries, leaving16 inventoried
read migrations plus other constructors/representation bridges. Combined
Source/H19 release, external ledger/range/reachability, H16/P8 realization,
immutable/funds release and all24 original Y10 obligations/six combinations
remain open. Full-lane gates are not inferred from this consumer batch.
No fresh native comparison or original goal status change is claimed.

## H25 exact authority adapter draft (2026-11-04)

Human H25 resolves H19-LEDGER1: exact money has its own authority; the shared
Word ledger is not made unbounded. `Source.MonetaryAuthority` implements the
small typed representation/adapter draft for G01 owner review. Exact balances
include2^256. Actual Source account writes use the existing journal and undo;
the isolated actual requestScope transfers the entire Nat post-fee amount
into the returned authority, retaining the other Source state/local fields.
That scope leaf starts at ordinal0 and is not session/H18 wiring.

The funding adapter saturates to the largest Word only for affordability
checks. Its theorem proves equivalence for EVERY Word-valued request, with
no Fits assumption. It must never be used as the observed balance. Optional
checked balance conversion rejects an unrepresentable Word conversion, not
the request or failure plan. Wide controls distinguish exact2^256, saturated
funding and modular Word zero. No Source/Eval/Session/shared-ledger body is
changed; actual fee settlement, authority synchronization and reachable-EVM
range remain pending G01 review and implementation. Six axiom guards use
only standard axioms. Read-only finder/skeptic approved this narrow draft.

G01 review request H25-G01-REVIEW1 asks review of the exact Source and external
funding/balance signatures before session wiring; coordinator relays it.
H26 helper scope is disjoint credit/debit and checkedWord arithmetic over
committed046292ee Source.Monetary/MonetaryLaws, with exclusive new MonetaryBounds
packet paths and no Source edits.

H26 P8 interfaces are already published: FrozenInterface has OperationalReference,
SourceOrigins, FailureProjection and SourceRealization; SourceRealization.lean
anchors the actual current session. Existing CorrectnessInstances.Stages and
CorrectnessPublic.PublicBoundary are reused, not duplicated and not inhabited
with a fabricated assembly instance. Concrete P8 realization/full resource
execution and all24 original obligations/six combinations stay open. HOST1's
previous typed packet979c7444 remains separately relayed to V17.

The H25 interface is split for early review: `MonetaryAuthority.lean` imports
only the unchanged pure `Monetary.lean` (Roadmap.Contracts dependency). Both
can be reviewed without the held Source core migration. Actual journal and
request-scope adapters are in `MonetaryAuthoritySource.lean`, which explicitly
requires the owner-held H16 cursor/H19 account changes. No interface is a
claim that fee settlement or session authority wiring already exists.

## Remaining read/constructor consumers (2026-11-04)

39 more modules are migrated: the final16 inventory reads plus23 related
Source-account constructor/dependency fixtures. All57 original read sites are
now migrated. Values and complete expected state/trace/failure distinctions
remain unchanged; no Source core module is edited in this increment. Initial
failures and corrected passes are retained separately.

Readonly StaticJournal required an isolated representation amendment: balance
certificate steps and their storage-preservation lemma now accept the actual
Nat monetary field. All start/write/static/child/rollback rules and conclusions
are unchanged. Word-step and Word-storage compatibility are explicit. Actual
credit/transfer histories are proved without an added range premise; transfer
unfolds the real transferNat wrapper. This generalizes storage-preservation
coverage, not payment admission or settlement. The readonly owner is requested
to review the isolated patch before integration. Read-only finder and skeptic
approved this scope without findings or running Lean/tests.

The global .balance.val search is clear, but this does not itself prove full
consumer/Source closure. Combined checkpoint, Source release/timing acceptance,
G01 H25 authority settlement/session wiring, full balance reachability, H16/P8
realization and original24 obligations/six combinations remain pending. No
fresh native observation or whole-lane completion is claimed.

Combined checkpoint at1ad93a4d: affected closure PASS135s, library FAIL2187s
with three remaining migration roots, examples/TestSuite PASS, trust/orphans/
layers/roots/doc-paths PASS. Pin inventory had zero axiom errors but unrecorded
new/shrunk standard pins and therefore FAILED. All raw exits remain failures.
The checkpoint roots were repaired only after completion: LifecycleAdapterChecks
keeps the same four numeric tuples with Nat balance types, G18SourceMapping/
G18ArrayAccess preserve their exact modulo expression as a Nat field, and
SourceBalanceOperands mirrors actual Source.evalE via explicit wordView. These
four modules and StaticJournal pins pass focused checks. The axiom inventory is
regenerated by script; no non-standard axiom or weakened expectation is accepted.

Corrected checkpoint at5331fff9: affected closure PASS10s; full Solidity library
PASS2s from the now-populated cache; examples/TestSuite PASS1s; complete trust,
orphans, layers, generated roots, current doc paths and axiom inventory PASS.
A separate strict automatic gate passes. This is a real combined kernel/static
checkpoint, not fresh native testing or a complete Source/G01/P8 realization.
The first library failure2187s and pin-drift failure remain recorded unchanged.
Readonly certificate owner review and full Source timing acceptance remain
integration requirements; H25 G01 review/session wiring, balance reachability
and all original24 obligations/six combinations remain open.


Actual monetary execution increment (2026-11-04): MonetaryExecution proves six
laws directly from Source.credit/debit, including exact full-state results,
current-and-saved-account range preservation, credit refusal at2^256 and
successful zero debit retaining2^256. Initial range is explicit; successful
debit alone does not imply it. No Source implementation, helper-reserved
arithmetic, shared ledger, observation or budget changed. Standard axiom sets
are pinned. Read-only finder and skeptic reviews found no issues. Focused
per-file checks pass; initial syntax/normalization failures remain retained in
/workspace/vy5-composition/monetary-execution-20261104. No fresh native test,
whole-program reachable-balance theorem, H25 settlement/session wiring or
original24-obligation/six-combination closure is claimed. Combined gates are
not rerun for this focused increment; prior corrected checkpoint remains
attributed to its tested tree.


Monetary rollback increment (2026-11-04): actual mark, attempt(credit) and
rollbackTo compose to restore arbitrary complete caller state and return the
actual captured success/revert. This needs no assumed execution outcome.
Rollback range transport requires current AND saved journal-account range.
The heap is preserved because credit leaves it untouched; rollbackTo itself
does not restore heap contents. Eight inhabited controls reuse the existing
DEAD heap alias, event/log prefix, function locals and add a nonempty journal.
They distinguish attempted-but-not-rolled-back credit, a wrong zero mark, zero
credit journal changes and a real heapBytes continuation reading full DEAD.
Five execution laws plus eight controls use only pinned standard axioms.
Finder and skeptic independently reviewed read-only without Lean/build/tests;
no findings. Initial proof normalization and incorrect heap-field diagnostics
remain failed in /workspace/vy5-composition/monetary-rollback-20261104.
No Source implementation or budget changed. No fresh native comparisons or
full Source/EVM/reachability/session/transaction-finalization claim. H25 G01
review and authority wiring, H16/P8a realization, immutable/funds release and
original24 full obligations/six combinations remain open. Helper-reserved
pure monetary arithmetic is unchanged.


Mutable storage range increment (2026-11-04): five laws connect real
Source.applyOp/setCell/writeAt to the current-and-saved-account balance
invariant. Persistent writes retain account money and save its old bounded
account; transient writes add only a nonmonetary journal entry. Static refusal
and invalid type/stuck paths preserve the entire state. Eleven inhabited
controls use actual registered EB persistent/transient paths with balance17,
nonempty journal, heap alias and event/log/function-local prefixes. They
verify changed cells9/7, full result/state, range, static/type refusal and
exact undo. These are direct storage-operation controls, not registered
contract dispatch or a full evaluator induction. No Source write semantics,
helper-reserved arithmetic, journal contract, observations or budget changed.
Finder and skeptic reviewed independently read-only without Lean/build/tests;
no findings. Original dependent-elaboration and syntax failures remain in
/workspace/vy5-composition/monetary-storage-20261104. Standard axioms only,
with exact pins. No fresh native observations. H19 full reachability/consumer
closure, H25 G01 review and settlement/session wiring, H16/P8a execution and
realization, immutable/funds release and original24 obligations/six general
combinations remain open; Work2 and BackfillA/B remain partial.
