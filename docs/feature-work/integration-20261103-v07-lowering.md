# v07-lowering integration checkpoint

Producer: `d2e5bec2fe83b090489192ef6f5ec81310914adf`. This imports only the following modules:

- `Solidity/Lowering/V07/SignedNarrowing.lean`
- `Solidity/Lowering/V07/SignedWidthCasts.lean`
- `Solidity/Lowering/V07/SignedWordSubtraction.lean`
- `Solidity/Lowering/V07/UnsignedCasts.lean`
- `Solidity/Lowering/V07/UnsignedWidthCasts.lean`

The increment preserves the producer statements, hypotheses and exclusions;
it does not establish completion of the remaining lane queue.
Touched-module and library checkpoint gates pass: trust, roots, orphans,
layers, documentation paths and axiom inventory.
Independent read-only finder and skeptic reviews are required before publication.
