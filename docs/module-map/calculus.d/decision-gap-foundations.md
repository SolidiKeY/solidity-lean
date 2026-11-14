| `Calculus/DecisionMappingStruct.lean` | Fresh binders of a memory type no heap can hold (a struct with a mapping member, a mapping, a nonempty fixed array of mapping references, `RefTy.memVoid`): vacuously valid, negation refuted; certified answers on the lazy compound fallback. |
| `Calculus/DecisionPartialOrFloor.lean` | Exact decision of the nested partial-OR floor family (`PartialOrFloor`): recognized from the formula alone, valid exactly at a positive key with matching result (`PartialOrFloor.valid_iff`), otherwise refuted at one symbolic mapping region (`counterState`). |
| `Calculus/DecisionPartialOrSub.lean` | Certified positive-key/matching-value answers and symbolic countermodels for the partial-OR family at every halting subtraction literal. |
| `Calculus/DecisionPartialOrSubComplete.lean` | Exact recognition of the halting subtraction-literal partial-OR family from source roots and literals (`partialOrSub_iff`). |
| `Examples/DecisionGapPartialOrSub.lean` | Positive/negative source membership, semantic validity, explicit countermodels, certified family answers and public verdict/coverage controls. |
| `Calculus/DecisionThresholdStore.lean` | Threshold-uniform symbolic storage regions, consumed by the proof-carrying bounded-block refuter. |
| `Calculus/DecisionBlockRefute.lean` | Certified refutations of literal-bounded blocks at checked threshold regions; a sound capped semi-decision whose misses remain unknown. |
| `Calculus/DecisionGapAnswer.lean` | Certified floor/subtraction/block gap answers and source coverage, used only after prior given-heap routes miss. |
| `Examples/DecisionGapKIntResidue.lean` | KeY-int cases beyond the two-word encoding, with explicit semantic validity/countermodel controls and residue pins. |
