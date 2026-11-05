import Solidity.Examples.DecisionArrayReplay

/-!
# The closer's decision on blocks over storage arrays (M7, feature 32)

`decideLeaf` (`Calculus/Decision.lean`) on a negative block over a storage
array, over `Gaps` of `Examples/Decision.lean`: the counterexample once
pinned there (`gapArrayBlock`, proved), its false variant (`arrayBlockBad`,
an element past the guard, refuted) and the shape Bradley, Manna and Sipma
state, a guard against the live length (`arrayLenBlock`, proved).  The
pipeline is `arrayBlockReduction?` (`Calculus/ArrayBlock.lean`): the
lengths read as atoms, the blocks instantiated at the index set, the
Theory's slot reads folded, the array reads cut.  Coverage and the
fragment are the kernel's; the same verdict values are replayed by the
kernel-checked certificate in `Examples/DecisionArrayReplay.lean`.
This test does not benchmark the original arithmetic search or materialize
its potentially enormous countermodel.
-/
