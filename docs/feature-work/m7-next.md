# M7-next lane `m7-decision` (AU01): DecisionTheorem′ and Residue

Batch `hard-20261106`, branch `cloud/hard-20261106/m7-decision`, base
`c73b8b33f4e75228c78b2752cf078bbc3f211b56`. Single writer of
`Calculus/Decision*.lean` (except the sibling `m7-gaps` lane's new gap
modules), the `Examples/Decision*.lean` splits and the M7-next section of
`docs/automation.md`.

## Status

**2026-11-06, Q1 answered.** The coordinator relayed the user's answer to Q1
[Residue]: **route-refusal Residue**. Residue is the named refusal of each
pipeline route, with VA1's finer source reasons reported where they apply,
each refusal with a fixture; exact and decidable; verdict correctness proved.
In the user's words to be stated plainly: **"total off Residue" holds by
definition, so `DecisionTheorem'` is not a completeness result**, and it is
not presented as one here, in its docstring or in `docs/automation.md`.

## Checkpoint 1: the residue and `DecisionTheorem'` (items 1, 2, 5)

`Calculus/DecisionResidue.lean`:

* `RouteRefusal`: the routes of `decideGoal`, each with a one-line reason.
  On a leaf without a hash the first ten are tried in order (`dependent`,
  `quant`, `array`, `ledger`, `ledgerBlock`, `arrayBlock`, `memory`, `kint`,
  `kenc`, `quantLedger`: `leafRoutes`); on a leaf with a hash `decideGoal`
  tries only `hash`, in their place.
* The refusals, computed from each leaf route's front end, never from
  `decideGoal`: `Fml.leafARefuses` (the six reductions return `none`),
  `Fml.memRefuses`, `Fml.kintRefuses`, `Fml.kencRefuses`,
  `Fml.quantLedgerRefuses`, `Fml.leafRefuses`, `Fml.hashRefuses` (every
  hash try answers `unknown`; a try is itself a decision, so this one
  refusal is stated on the try's verdict).
* `Fml.residue` (Bool) and `Fml.Residue` (Prop) with a `Decidable` instance.
* Exactness, route by route: `decideLeafA_unknown_iff`,
  `decideMem_unknown_iff`, `decideKInt_unknown_iff`, `decideKEnc_unknown_iff`,
  `decideQuantLedger_unknown_iff`, `decideLeaf_unknown_iff`,
  `decideHash_unknown_iff`, and `residue_iff_unknown`.
* `DecisionTheorem'`: for every waiver setting, contract and leaf in
  `Fml.inTarget w` with `¬ Fml.Residue`, either `decideGoal φ = .proved` and
  `Fml.ValidH φ`, or `decideGoal φ = .refuted σ` and `¬ Fml.holdsH σ φ`. The
  hash premise is the goal's own (e3′); no global premise. The target premise
  is not used by the proof (stated to keep the theorem about the user's
  fragment).
* `decideGoal_proved_iff_off_residue` (the verdict is exact off the residue)
  and `decisionTheorem_iff_residue_disjoint` (the unchanged `DecisionTheorem w`
  holds exactly when no in-target leaf is in the residue; that later rounds
  only shrink it is the milestone policy, not enforced by the code).
* `Fml.sourceReasons`: VA1's source classes decidable from the leaf alone
  (two-binder and primitive-prefix normalization budget, mapping-bearing
  reversed field, array path kinds), attached to residue leaves as labels:
  they are not residue tests, and no class is proved to lie in the residue;
  `Fml.routeRefusals`; `Fml.residueReasons` (labels then route reasons, empty
  exactly off the residue, `residueReasons_eq_nil_iff`). VA1's halting-`||` class is parameterized by
  contract roots and is not reported (its fixtures are residue members below).
  `DecisionTheorem`, `Fml.inTarget`, `Fml.Covered`, `Waivers` and every route
  are unchanged.

`Examples/DecisionResidue.lean` (item 5):

* Residue members in target: `floorClaim 1` (valid) and `floorBad` (false),
  a halting `||` guard in an APF block, no VA1 label; `mappingReversed`, VA1's
  mapping-field label, with `routeRefusals = leafRoutes` (every leaf route's
  refusal named on one leaf); `exhausted`, both normalization-budget labels;
  `sibling` (1025 visits), in the residue with no label (a label is not a
  residue test); `hashBudget`, a leaf with hashes every hash try refuses.
* Witness controls (the hypotheses are jointly satisfiable): twelve in-target
  non-residue feature fixtures of earlier milestones (quantified linear
  arithmetic proved and refuted, a `bool`-quantified APF leaf, a storage-array
  block, fixed arrays proved and refuted, a storage-array column, a ledger
  write, a ledger block, a given-heap parameter, a reversed struct field
  refuted at its exact state, KeY `int` binders of features 26 and 30/31, a
  quantified ledger leaf, hashes of one kind), each answer certified through
  `DecisionTheorem'`. Which route answers each is not pinned.
* Negative control `residue_not_claimed`: `floorClaim 1` valid,
  `floorBad` not valid, both residue, the theorem's conclusion fails at each.
* Axioms of every fixture and of the four headline theorems are pinned with
  `#guard_msgs` (Lean's three only).

## Q1 evidence (kept for the record)

The assignment asks for a decidable `Fml.Residue` that is *exactly* the set of
in-target goals `decideGoal` answers `unknown` on, built from named, documented
shapes each with a fixture, and a proof that every in-target non-Residue goal
is answered correctly. The evidence below shows that the three requirements
(exact, structural, proved) cannot all be met in this lane, and that each way
of dropping one changes the theorem's meaning. That is a weakened statement,
which the assignment reserves for the user.

1. **Unknown is decided by the routes themselves, not by a source shape.**
   `decideLeafA` answers `unknown` exactly when all six reductions
   (`dependentReduction?`, `quantReduction?`, `arrayReduction?`,
   `ledgerReduction?`, `ledgerBlockReduction?`, `arrayBlockReduction?`)
   return `none` (each `verify` always answers), and `decideLeaf`/`decideGoal`
   chain this with `decideMem`, `decideKInt`, `decideKEnc`,
   `decideQuantLedger` and the hash tries (`Calculus/Decision.lean`,
   `decideLeafA` … `decideGoal`). A structural Residue that is exact must
   therefore restate, for each route, the precise set it refuses on
   in-target leaves: a completeness proof of each recognizer against
   `Fml.target`. That is the AU01 "exhaustive target-to-covered/hash bridge"
   VA1 left open after its whole lane (`after-roadmap-va1.md`, queue
   accounting); VA1 delivered supported-family components, not the bridge.
2. **Resource budgets make `unknown` depend on computed work.** In-target,
   valid goals are `unknown` only because a budget is exceeded:
   `Examples/DecisionNormalizationResidue.lean` (2049 normalizer visits
   against the unchanged 2048), the 511-node flattening cap
   (`DecisionNumericFuel`), and the hash family bound (`famCheck`). An exact
   Residue needs a named measure reason per budget per route, each proved to
   coincide with that route's refusal on target leaves.
3. **`Covered` is not exact either.** The 517-node control is answered
   `proved` while neither `Covered` nor `hashCovered`
   (`docs/automation.md`, numeric source-size increment), so
   "Residue = in target and not covered" contains answered goals. The
   reverse inclusion `Covered ⊆ inTarget` is false (VA1-Q1 counterexample,
   `∀ uint x; (1 + 1) * x = x + x`); the human revised it to a certified
   boundary on 2026-11-01 (`docs/solidity-scope.md`), which
   `Calculus/DecisionCoefficientBoundary.lean` proves. Work-queue item 3's
   "Covered ⊆ inTarget (old step 8)" is therefore done in its revised form;
   nothing further is owed there.
4. **The recorded culture rejects a renamed complement.** The VA1 census
   ("Actual remaining target gaps, without a Residue shortcut") and the
   VA1-Q1 receipt ("not presented as proved under a vacuous/circular …
   precondition") rule out defining Residue as `decideGoal φ = .unknown` or
   as `¬ Covered` without the user's say.

## The options put to the user

* **Route-refusal Residue.** `Fml.Residue` is the conjunction, per route in
  `decideGoal`'s order, of a named refusal (for example "no dependent
  reduction", "fresh-array cut refuses and no struct answer", "no hash try
  covers"; question text as asked, the implemented wording is above), each with an in-target fixture; where an existing VA1 source
  classifier (normalization budget, halting `||`, mapping-field reversal,
  array reasons) applies it is reported as the finer reason. Exact and
  decidable; `DecisionTheorem′` then proves correctness (sound, certified
  refutation, per-goal hash premise) and totality off Residue, but totality
  follows from the definition, so it is not a completeness result.
* **Supported-family theorem.** `DecisionTheorem′` quantifies over the union
  of the families with proved source bridges (QFUIntLinear prefixes, ground
  numeric sources, coefficient family, source literal chains, given-heap and
  compound-field classes); Residue is the in-target complement of that union.
  Non-circular, but Residue is not exact: it contains goals that are answered.
* **Keep the exact structural theorem open.** No `DecisionTheorem′` in this
  lane; the lane continues per-route structural refusal classifiers and their
  bridges, plus item 4, and reports `partial`.

## Gates

Checkpoint 1 (MCP, per file): `Calculus/DecisionResidue.lean` and
`Examples/DecisionResidue.lean` have no errors or warnings;
`#print axioms DecisionTheorem'` is `[propext, Classical.choice, Quot.sound]`
(pinned). `hashBudget_residue` costs about 24 s of kernel checking (profiler,
language server). The base commit failed `fragments.sh --check` (a README row
without its fragment); this lane adds the fragment row.

Final gates (2026-11-06, on the review-fixed head):

* `./run-lean.sh`: every Lean job of the default targets and
  `SolkeyTestSuite` builds without an error (two incremental runs: the first
  was stopped when `Examples/Tactics/OpenLoops`, outside this lane, was killed
  by the out-of-memory killer (exit 137) beside resident language-server
  workers; the rerun built it and finished the Lean build in 10 min 55 s).
  The script's last step, `scripts/check-solkey.sh`, then reports 167 drifts
  against the sibling `../solkey` checkout (b8d5f88); this lane touches no
  `SortCheck/`, rule or taclet file, so the drift is the checkout's, not this
  lane's, and the step is recorded as not passing.
* `layers`, `orphans`, `register.sh --check`, `fragments.sh --check`: pass.
  `check-doc-paths.sh` fails on one citation outside this lane
  (`after-roadmap-va1.md`, a Mathlib test path); `check-axiom-pins.mjs`
  reports 0 errors and a repository-wide inventory of 4403 unrecorded
  changes, none from this lane's modules.
* Item 4 (module time under 300 s), measured per module. `lake build` times
  from the full run: `DecisionGapOperators` 229 s, `DecisionFeatures` 156 s,
  `DecisionResidue` 97–101 s, `DecisionHashKeys` 86 s, every other built
  `Examples/Decision*` module under 60 s. The 19 modules the build replayed
  from language-server artifacts were timed as fresh language-server checks
  (wall time of the file worker, CPU in brackets): `DecisionGaps` 239 s
  (236 s), `DecisionMemory` 83 s (81 s), `Decision` 73 s (65 s),
  `DecisionHashCore` 63 s (60 s), `DecisionHaltingOrGaps` 26 s,
  `DecisionKInt` 24 s, `DecisionQuantLedger` 20 s,
  `DecisionNormalizationResidue` 19 s, `DecisionArrayGaps` 9 s,
  `DecisionCoefficientBoundary` 7 s, `DecisionArrayCore` 4 s,
  `DecisionHashes` 2 s, and `DecisionGapCensus`, `DecisionGapData`,
  `DecisionMappingFieldReason`, `DecisionMemoryFixtureData`,
  `DecisionMemoryParameterData`, `DecisionResidueReasons`,
  `DecisionVerdictData` 1 s or less; all without an error. Every module
  checks in under 300 s, so no split was needed and no guarded command or pin
  moved. The older 966 s (`Decision`) and 417 s (`DecisionHashes`) figures in
  `declarations-metadata.md` and `solidity-upstream-tests.md` were
  single-worker retries under load before earlier splits. These timings are
  not controlled benchmarks; the slowest margin is `DecisionGaps` (about 60 s).

## Reviews

Checkpoint 1, read-only finder and skeptic (soundness area, no Lean server):
both confirmed that every refusal predicate copies its route's branches in
`Calculus/Decision.lean`, that the per-route `*_unknown_iff` lemmas tie them
to the code, that the only circular part of `DecisionTheorem'` is the agreed
totality and is disclosed, that the hash premise stays per goal, and that no
`sorry`, axiom or `maxHeartbeats` change was added. Confirmed findings, all
fixed:

1. "Source reasons answer the structural question" overclaimed: VA1's classes
   are now described as labels, not proved to lie in the residue.
2. "Later milestones may only shrink the residue" was stated as a property: now
   a policy the code does not enforce.
3. The hash refusal is a try's verdict, not a front end: disclosed in the
   module docstring, `docs/automation.md` and the module-map row.
4. `RouteRefusal.memory` prose described a conjunction the code does not
   take (struct answer only when there is no cut): fixed.
5. Route order: `hash` replaces the leaf routes rather than following them.
6. "Quantifier-free" for the dependent route: it takes a universal prefix.
7. Fixture header misstated how membership is obtained (several fixtures run
   `decide +kernel`): fixed.
8. Witness coverage: "each route family" overclaimed and the answering route
   was not pinned; four witnesses added (storage-array column, ledger write,
   ledger block, KeY `int` binder) and docstrings no longer name routes.
9. The negative control did not prove `floorBad` false: `floorBad_notValid`
   added.
10. `hashBudget` docstring claimed an unproved cause and a timing: removed.
11. Fixture axioms were printed, not pinned: now `#guard_msgs`.
12. `docs/automation.md`'s next paragraph ("does not introduce a `Residue`")
    read as contradicting the new one: scoped to the ledger lane.
13. Stale m7-next sections (this one, gates): updated; docs index row added.
