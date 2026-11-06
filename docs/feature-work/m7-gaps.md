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
| every `∀ fresh S x; φ` with `S` a struct with a direct mapping member (or a mapping, or a nonempty fixed array of mapping references), any body | unknown | proved | void binder | `ledgerSeven` in `Examples/DecisionGapVoidBinder.lean` |
| `floorClaim 1` (halting-OR APF block, valid) | unknown, not covered | proved | partial-OR floor | `Examples/DecisionHaltingOrGaps.lean` (`validAPF_proved`) |
| `floorClaim 0` (key zero) | unknown, not covered | refuted | partial-OR floor | `zeroAPF_refuted` |
| `floorBad` | unknown, not covered | refuted | partial-OR floor | `falseAPF_refuted` |
| every `PartialOrBlockAt sp v k r φ` over any contract's uint and `uint ⇒ uint` roots | unknown | proved iff `0 < k ∧ r = v`, else refuted | partial-OR floor | `Examples/DecisionGapPartialOrFloor.lean`, `Examples/DecisionHaltingOrCertificate.lean` |
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
  member of this family.
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
  search, not a complete decision: a false block it misses stays unknown.

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
| Two uint binders over a numeric body past the normalizer budget (`TwoUIntPrefixOverNormalizationBudget`: `exhausted`; `sibling` past the 511-node cap) | resource bound: deciding needs a larger normalization/node budget, a performance decision not taken here | `Examples/DecisionNormalizationResidue.lean`, `Examples/DecisionPrefixNormalizationResidue.lean` |
| False literal-bounded blocks the region search misses (bound above 64, non-uint leaves that need a value other than default/one, conclusions needing two different past-bound values) | no candidate region certifies them; the search is sound, not complete | none beyond the controls in `Examples/DecisionGapArrayNegatives.lean` |
| Partial guards in APF blocks outside the partial-OR floor family | the APF OR reconstruction needs left-operand definedness (`partialOrBlockReason`) | `Examples/DecisionHaltingOrReason.lean` |
| KeY-`int` remainders past about `2^511` (`zMul n ≤ 2^256`) | the two-word encoding's multiplier exceeds a word | not pinned by this lane |

Outside the target (decisions c, c′, d, e3″), so not Residue: `twoAnchorNonlinear`,
`gapHashNegForall`, `notApf`, `namesBound`, `&`/`|`/`^` with two symbolic
operands and `addmod`/`mulmod` with a symbolic modulus or two symbolic
factors (checked: `inTarget {} = false`). `addmod(x, y, 7)` with two symbolic
addends is in the target and already covered.

## Gates and reviews

Recorded at the end of the lane (see the CLOUD-RESULT block of the final
marker commit).
