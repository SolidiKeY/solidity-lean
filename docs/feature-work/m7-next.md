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

* `RouteRefusal`: the routes of `decideGoal` in order (`dependent`, `quant`,
  `array`, `ledger`, `ledgerBlock`, `arrayBlock`, `memory`, `kint`, `kenc`,
  `quantLedger`, `hash`), each with a one-line reason.
* The refusals, computed from each route's front end, never from
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
  holds exactly when no in-target leaf is in the residue; later milestones
  may only shrink it).
* `Fml.sourceReasons`: VA1's source classes decidable from the leaf alone
  (two-binder and primitive-prefix normalization budget, mapping-bearing
  reversed field, array path kinds); `Fml.routeRefusals`; `Fml.residueReasons`
  (source reasons then route reasons, empty exactly off the residue,
  `residueReasons_eq_nil_iff`). VA1's halting-`||` class is parameterized by
  contract roots and is not reported (its fixtures are residue members below).
  `DecisionTheorem`, `Fml.inTarget`, `Fml.Covered`, `Waivers` and every route
  are unchanged.

`Examples/DecisionResidue.lean`: residue members per reason, witness
controls per route family (item 5), and the negative control.

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
  covers"), each with an in-target fixture; where an existing VA1 source
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

See the CLOUD-RESULT marker commit for the gate lines of this checkpoint.

## Reviews

None yet: no Lean or decision source changed; the finder/skeptic reviews are
due with the first source checkpoint.
