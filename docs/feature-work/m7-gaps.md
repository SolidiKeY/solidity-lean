# M7-next decision gaps (AU02) — handoff

Lane `m7-gaps` (batch hard-20261106), branch `cloud/hard-20261106/m7-gaps`,
base `c73b8b33`. The sibling lane `m7-decision` owns `Calculus/Decision.lean`,
`Fml.Residue` and `DecisionTheorem'`; this lane adds feature modules and
wires them only through extension points, plus one small separate commit in
`Calculus/Decision.lean` (below).

## For the sibling: what leaves `Fml.Residue`

Every row is in `Fml.inTarget {}` (checked by `decide +kernel` in the named
fixture), now `Fml.Covered`, and answered by `decideGoal` with a certified
verdict. None of them may be in `Fml.Residue`.

| Gap | Before | After | Route | Fixture |
|---|---|---|---|---|
| `memStructMapping` (`∀ fresh Wallet w; w.owner = w.owner`) | unknown | proved | void binder | `Examples/DecisionGapVoidBinder.lean`, `Examples/DecisionMemory.lean` |
| `mappingReversed` (`∀ fresh Wallet w; 0 = w.owner`) | unknown | proved | void binder | `Examples/DecisionGapVoidBinder.lean`, `Examples/DecisionResidueReasons.lean` (`mapping_global_proved`) |
| `mappingOne` (`∀ fresh Wallet w; 1 = w.owner`) | unknown | proved | void binder | `Examples/DecisionMappingFieldReason.lean` (`actual_proved_controls`) |
| a root binder `∀ fresh S x; φ` with `S` in `RefTy.memVoid` (a struct with a direct mapping member, a mapping, a nonempty fixed array of mapping references), any body, when negative-block preparation finds no array cut (`mxTop = none`, the route to `structAnswerWithCompound`) | unknown | proved | void binder | `ledgerSeven` in `Examples/DecisionGapVoidBinder.lean`; not proved here: the binder under a prefix (`∀ uint k; ∀ fresh Wallet w; …`) |
| `floorClaim 1` (halting-OR APF block, valid) | unknown, not covered | proved | partial-OR floor | `Examples/DecisionHaltingOrGaps.lean` (`validAPF_proved`) |
| `floorClaim 0` (key zero) | unknown, not covered | refuted | partial-OR floor | `zeroAPF_refuted` |
| `floorBad` | unknown, not covered | refuted | partial-OR floor | `falseAPF_refuted` |
| every `PartialOrBlockAt sp v k r φ` over any contract's uint and `uint ⇒ uint` roots | unknown | proved iff `0 < k ∧ r = v`, else refuted | partial-OR floor | `Examples/DecisionGapPartialOrFloor.lean`, `Examples/DecisionHaltingOrCertificate.lean` |
| every formula `PartialOrRoots.subClaim sp i j c v k r` (the floor block with `s - c` for a literal `c ≥ 1`, any uint/mapping roots, any literals; recognition complete: `partialOrSub_iff`, `Calculus/DecisionPartialOrSubComplete.lean`; it contains the floor family, `c = 1`) | unknown, not covered | proved iff `0 < k ∧ r = v`, else refuted | partial-OR at any subtraction literal (round 2) | `Examples/DecisionGapPartialOrSub.lean` |
| negative companions of the five array source shapes: reads past the bound and wrong values, below mapping keys (`rows[k][3]`, `rows[k][1] = 5`), fixed arrays below keys (`fixedRows[k][2]`), below struct fields (`box.xs[3]`), at struct elements (`cells[3].v`), nested arrays (`grid[k][3]`) | unknown, not covered | refuted | block refuter | `Examples/DecisionGapArrayNegatives.lean` |

The five positive array shapes (`belowKey`, `fixedBelowKey`, `belowField`,
`arrayStruct`, `arrayArray`) were already covered and proved on the base
(`sourceUIntLiteral_*` in `Examples/DecisionArrayGaps.lean`); this lane adds
their negative companions. `gapMemParam`, `gapMemStruct`, `gapMemInnerNeg`,
`gapArrayBlock`, `gapIntAnd`, `gapAddmod` and `gapKIntNeg` were already
covered with certified verdicts on the base.

## The routes

* **Void fresh binder** (`Calculus/DecisionMappingStruct.lean`). A memory
  mapping object is `Empty`, so a heap typing that has a heap lists no
  mapping (`objs_noMapping`), no reference to a mapping exists
  (`hRef_noMapping`), and a type with a mapping-reference member has no
  object (`mObj_void`). `∀ fresh R x; φ` is then valid for every `φ`
  (`allocAll_void_holds`); its negation is refuted at the given state. The
  source class is `RefTy.memVoid` at the root binder (`Fml.freshVoidBinder`);
  arrays of mapping references are excluded (the empty array is an object).
  This matches solc, which cannot construct such a struct in memory. Wired:
  `structAnswerWithCompound` consults `voidAnswer?` after all earlier struct
  answers (`Calculus/DecisionCompoundExtension.lean`), so `Fml.memCovered`
  covers it with no change to `Decision.lean`. The negated binder is outside
  `Fml.inTarget` (negative `allocAll`, decision d); the target holds no false
  member of this family. `RefTy.memVoid` is a syntactic subset: a struct whose
  member is a void struct is void too but not recognized, and a void binder
  under a universal prefix is not recognized.
* **Partial-OR floor** (`Calculus/DecisionPartialOrFloor.lean`). The guard
  `(i ≤ j && i < s - 1) || i ≤ i` is `true` exactly when `j < i` or `1 ≤ s`
  (checked subtraction halts at `s = 0`; `||`/`&&` short-circuit left to
  right). Exact verdict: `PartialOrFloor.valid_iff`. Refutations use one
  symbolic region (`counterState`: `s = 0`, the mapping one entry over a
  default). Discovery is from the formula alone (declared roots × skeleton
  literals, after a constant-work shape check), sound and complete for the
  family (`partialOrFloor_iff`). The general APF guard-floor reconstruction
  for partial guards is not repaired; this decides the family.
* **Block refuter** (`Calculus/DecisionThresholdStore.lean`,
  `Calculus/DecisionBlockRefute.lean`). `∀ x̄; (∀ uint i; i < n → body) →
  concl` is refuted at a candidate state once the prefix is instantiated at
  defaults, the `n` instances `body[i]` are checked true and `concl` false by
  the proof-carrying `Fml.checkMemoryAt`; instances `i ≥ n` fail the guard.
  Candidates are threshold-uniform regions (`ThresholdStore.Fill`): every
  dynamic array of one length (past every literal index), mappings as one
  default, leaves `c` below index `n` and `h` past it, `c`/`h` from the
  formula's literals, zero and words different from them; `n ≤ 64`. The
  region is symbolic: no key or slot list. This is a certified refutation
  search (a sound semi-decision), not a complete decision: a false block it
  misses stays unknown. Arrays are at most `lenCap` (129) slots, and literals
  past that are not indices any region reaches.

## The extension point and the `Decision.lean` commit

`Calculus/DecisionGapAnswer.lean` holds `gapAnswer?` and `Fml.gapCovered`
for families without fresh allocation. `givenHeapAnswerWithFixed` consults
`gapAnswer?` only on its own miss
(`Calculus/DecisionGivenHeapFixedExtension.lean`, `givenHeapAnswerWithFixed_gap`).
Commit `3a2fd331` ("Decision: admit Fml.gapCovered in Fml.memCovered") is the
only change to `Calculus/Decision.lean`: the disjunct
`(!φ.hasAllocAll && φ.gapCovered)` of `Fml.memCovered` and its
`decideMem_complete` case. Later families extend `DecisionGapAnswer.lean`
without touching `Decision.lean`. All earlier routes stay first, with their
exact answers and counterstates; `Covered`, `inTarget`, `Waivers` and
`DecisionTheorem` statements are otherwise unchanged (`memCovered` widens).

## What stays in Residue, with reasons

| Shape | Reason | Fixture |
|---|---|---|
| Normalizer-budget shapes, exactly: `TwoUIntPrefixOverNormalizationBudget` — two uint binders over a `QFUIntLinear` body with `2048 < normalizationWork + 2` (`exhausted`: work 2049, normalizer returns none, `exhausted_normalizer_none`); `PrimitivePrefixNormalizationResidue` for primitive prefixes; and bodies that normalize but exceed the 511-node leaf cap (`sibling`: work 1025, normalizes, still unknown) | resource bounds of the public pipeline (2048 normalizer visits, 511 leaf nodes); deciding them means raising those budgets, which is not done here | `Examples/DecisionNormalizationResidue.lean`, `Examples/DecisionPrefixNormalizationResidue.lean` |
| False literal-bounded blocks the region search misses (bound above 64, an index literal past `lenCap`, non-uint leaves that need a value other than default/one, conclusions needing two different past-bound values, a body that is not a quantifier-free storage/arithmetic formula `Fml.checkMemoryAt` reads) | the search is sound, not complete. No completeness fragment is proved: stating one needs read lemmas for threshold regions along arbitrary storage paths, not done in this lane | none beyond the controls in `Examples/DecisionGapArrayNegatives.lean` |
| Partial guards in APF blocks outside the decided partial-OR families, e.g. a right disjunct other than `i ≤ i` (`j ≤ i`), a non-literal subtrahend (`s - x`), swapped `&&` operands, a body other than `m[i] == literal`; only the first is pinned | the APF OR reconstruction needs left-operand definedness (`partialOrBlockReason`); the decided families rely on the right disjunct being total and true | `otherClaim` (`other_residue`) in `Examples/DecisionGapPartialOrSub.lean`, `Examples/DecisionHaltingOrReason.lean` |
| A negative KeY-`int` binder compared against literals past about `2^511`: `(∀ int z. z > 0 → z > -2^600) → false` (false), `(… → z > 2^600) → false` and `(∀ int z. ∀ int y. y > z + 2^600) → false` (valid) | the two-word encoding (`Fml.kencB`) needs its multiplier `zMul n` to fit a word, so it refuses them, and the three pinned members are not covered by any route; this pins examples, not a general uncovered theorem. A positive binder with such literals was observed covered (`∀ int z; z > 2^600 → z > 2^600 - 1`, a probe, not pinned) | `big_residue` and the covered small-literal control in `Examples/DecisionGapKIntResidue.lean` |

Outside the target (decisions c, c′, d, e3″), so not Residue: `twoAnchorNonlinear`,
`gapHashNegForall`, `notApf`, `namesBound`, `&`/`|`/`^` with two symbolic
operands and `addmod`/`mulmod` with a symbolic modulus or two symbolic
factors (checked: `inTarget {} = false`). `addmod(x, y, 7)` with two symbolic
addends is in the target and already covered.

## Round 2 (coordinator request, queue item 4)

* Partial APF guards: the floor family is generalized to any halting
  subtraction literal (`Calculus/DecisionPartialOrSub.lean`, wired after the
  floor family in `gapAnswer?`); the remaining shape is narrowed and pinned.
* KeY-`int` past the encoding: in-target uncovered members pinned
  (`Examples/DecisionGapKIntResidue.lean`); not decided. A one-binder
  test-point decision (thresholds `c`, `c ± 1`, and one point beyond each end)
  would decide the single-binder members; the two-binder member needs
  elimination. Neither is implemented.
* Block refuter completeness: not proved on any fragment (see the table).
* Normalizer budgets: characterised above; no budget changed.

## Reviews

Read-only finder and skeptic reviews, neither using the Lean server, after the
three families were in. The skeptic confirmed all five soundness claims (void
vacuity from `MObj (.mapping ..) = Empty`; the partial-OR guard re-derived by
hand from `binopT`/`shortT`; block refutations cover every `i` through the
guard; every new route is a last `orElse`, so earlier answers and their
counterstates stay authoritative; fixtures test both polarities with
kernel-checked countermodels). Findings fixed:

* `fills` sized arrays by the largest literal of the formula, so a large value
  literal could build huge regions, and a literal near `2^256` disabled the
  search: lengths now come from literals below `lenCap` only, and candidates
  are deduplicated.
* Wording that overclaimed: `RefTy.memVoid` is a syntactic subset; the block
  refuter and `Fml.gapCovered` are a semi-decision; the void-binder row above
  is narrowed to the root binder on the `mxTop = none` route.
* Stale present-tense prose in `docs/automation.md` now points here.
* Missing theorem docstrings in the new fixtures; `original_controls` now
  states `floorBad`'s refutation; `notWallet` is written in `cdl{}`.
  `totalClaim` stays in constructors: `dl{}` cannot spell a `&&` under `||`.

Not changed: partial-OR discovery tries `roots² × literals³` candidates after
its shape check (no current `Covered = false` pin has that shape; reading the
literals off their fixed positions would make it constant work), and the
positives of `Examples/DecisionGapArrayNegatives.lean` are pinned only as not
refuted there (their `proved` verdicts are in `Examples/DecisionArrayGaps.lean`).

## Gates

* Per-file MCP diagnostics: zero errors on every new and edited Lean file.
* Axiom pins (`#guard_msgs in #print axioms`, recorded in
  `scripts/g07-axiom-pins.d/`): `good_proved`, `atZero_refuted`,
  `wrongValue_countermodel`, `PartialOrFloor.valid_iff`, `allocAll_void_holds`,
  `mappingOne_proved`, `arrayOut_refuted` — only `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, no axiom, no
  `maxHeartbeats` change.
* `./run-lean.sh`: the first run (100 min, cold cache) found one break,
  `Calculus/DecisionGivenHeapFixedBoundary.lean` (a `simp` past the new
  `memCovered` disjunct), fixed in `DecisionGivenHeapFixedBoundary: close…`;
  the rerun printed `Build completed successfully (6409 jobs).` The script
  then exits 1 in `scripts/check-solkey.sh`. It reports 167 mismatches against
  the solkey checkout beside the repository: unknown tokens and unannotated
  reads in storage taclets. This lane touched no rule or sort annotation, so
  the mismatches are not caused by it.
* `scripts/check-doc-paths.sh` fails on the base too: `after-roadmap-va1.md`
  cites a Mathlib file under `Bridge/.lake`, absent on this VM.
  `check-axiom-pins.mjs` reports about 4,380 inventory entries that were not
  recorded before this lane. This lane's 5 new pins are recorded.

Round 2 gate (HEAD `ff40b3b6`): `./run-lean.sh` printed `Build completed
successfully (6413 jobs).` and again exits 1 only in `check-solkey.sh`
(`167 mismatch(es)`, unchanged). An earlier round-2 run was killed for memory
(exit 137 in `DecisionHashThreeKinds`) while language-server workers were
resident; the rerun with them stopped passed. Slowest touched modules:
`Examples/DecisionGaps.lean` 192 s and `Examples/DecisionGapOperators.lean`
153 s, under the 300 s limit but above the 105 s/90 s recorded earlier; this
lane has not attributed the difference (parallel load versus the gap
searches its interpreted unknown verdicts now run). Round-2 finder/skeptic:
the skeptic confirmed every semantic claim; the finder's circular-membership
finding is fixed by `partialOrSub_complete`, and its wording findings by
narrowed residue rows.

