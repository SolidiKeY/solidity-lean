# RawUintN controls

The kernel-checked fixtures are in
[`Controls.lean`](../../../Solidity/Backend/CalldataPackets/RawUintN/Controls.lean).
They execute the real Source calldata decoder, allocation, guarded entry and
resolved implicit conversion; no successful run is provided as an assumption.

Clean controls cover uint8 values 7/255, uint16 value 256, uint248 maximum,
nonzero offsets, an existing allocated prefix, zero length, zero padding and
coherent selector-prefixed dynamic entry. Negative controls cover dirty first
and second words, uint248 upper boundary, partial high byte, strict truncated
and missing entry heads, no masking, reversed observations, and horizons 0/1.
These are Source-machine laws, not compiled-bytecode or external EVM tests.

The [archived unsigned-range automation probe](https://github.com/SolidiKeY/solidity-lean-coord/blob/f50f3c05f75937adad347a524ab13aba29d4fec7/evidence/plan-x1e-classify-rest-1116/x1e-classify-rest/tests/calldata-packets-1105/RawUintN/range-goal.txt) was used by the shared
`try-tactics.sh`; failed candidate tactics are diagnostic attempts, not gates.
No test/proof/recursion/heartbeat limit is raised.
