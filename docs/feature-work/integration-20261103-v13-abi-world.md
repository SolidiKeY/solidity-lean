# v13-abi-world integration checkpoint

Producer: `b651f8395089061b00c77f5a1832d148a05caa4a`. This imports only the following modules:

- `Solidity/Lowering/V08/LiteralFailureDynamicReturn.lean`
- `Solidity/Lowering/V08/LiteralFailureDynamicReturnControls.lean`
- `Solidity/Lowering/V08/LiteralFailureReturnSlots.lean`
- `Solidity/Lowering/V08/LiteralFailureReturnSlotsControls.lean`
- `Solidity/Lowering/V08/LiteralFailureTupleAbort.lean`
- `Solidity/Lowering/V08/LiteralFailureTupleAbortControls.lean`

The increment preserves the producer statements, hypotheses and exclusions;
it does not establish completion of the remaining lane queue.
Touched-module and library checkpoint gates pass: trust, roots, orphans,
layers, documentation paths and axiom inventory.
Independent read-only finder and skeptic reviews are required before publication.
