# Dynamic storage array access

[The consumer](../../Solidity/Backend/Aggregates/G18ArrayAccess.lean) uses the
existing Source machine and intrinsic values. A declared dynamic integer array
path determines its uint256 length cell. The published `array_path` theorem
determines the element cell type after the complete ordered suffix; it supplies
no bounds proof.

`length_run` derives the actual `readLen` result from the persistent account's
stored bounded integer. `index_success` consumes the real inequality to derive
`indexLoc` success with the selected location and the whole locals/state pair
unchanged. `index_failure` derives the exact index-panic revert payload under
the complementary inequality. No desired execution is an input.

`read_element` combines the actual bounds check and `readLoc` with an initial
`IntCellAt` relation. It derives both the Source integer result, with its width
range and unchanged full state, and the existing intrinsic `SVal.find` result.
Dependent equality transports are proved rather than erased. This is a selected
cell observation; it does not establish whole-array length/layout agreement.

[The controls](../../Solidity/Backend/Aggregates/G18ArrayAccessControls.lean)
reuse the declared Basket and intrinsic target witness. They create actual
`Env.cellTy` storage with length2 and cells7/11, plus nonempty locals, heap,
prior journal and logs. The checked Source read returns11 and matches the
existing target's allocated slot1. The complete chosen observer vector contains
length, both Source cells and both target cells.

A separate negative state keeps cells7/11 but omits the length cell. Its actual
Source default length is0, so even index0 panics. This is an invalid aggregate
representation input, not an admitted or reachable program witness. Wrong
length and wrong location controls reject the relevant inputs/results. Index99
still has the declared element type, but the Source check panics while the
intrinsic lookup returns `none`. These are distinct outcomes, not failure
agreement. The index panic has nonempty data distinct from division-by-zero
panic and timeout. Failure controls execute `indexLoc` itself; the composed-read
failure cutoff is a separate, unproved routine consequence.

These are actual primitive executions and intrinsic lookup transports, not a
resolved `RExpr.indexArray` theorem, frontend admission, whole-array lowering,
physical storage/hash correspondence, numeric EVM driver or compiler coverage.
No SourceSpec or global failure/resource premise is discharged here.

Independent read-only finder and skeptic reviews found no semantic defect.
Sixteen generated guards pin the scoped theorem dependencies to the observed
standard axiom sets.
