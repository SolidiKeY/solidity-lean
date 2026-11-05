# Typed calldata-view packing

`Solidity/Backend/MemoryOps/CalldataViewPacking.lean` constructs the published V1 overlapping-view interface for every finite coherent family. It uses the existing executable Source type equality and chooses the first position with exactly equal type, raw offset and raw length. Logical keys are not physical offsets. Coherence supplies only the dependent payload equality required at a captured key. Input bytes and raw references are unchanged; uncaptured positions can contain redundant table entries.

`Solidity/Backend/MemoryOps/CalldataViewPackingControls.lean` checks seven mixed Boolean/uint views, duplicate identity, distinct static shape and lengths, partial overlap, maximum uint, actual typed payload extraction, impossible raw-offset keys and conflicting repeated payloads. Arbitrary runtime repetition and an empty table are also instantiated.

This is structural packing of supplied typed views, not ABI decoding, a Source execution theorem, emitted code or physical-memory correspondence. Decoder-demand coherence is an explicit input supplied by the consumer. The V2 stable-prefix-key extension remains open; no global G34 or whole-assignment completion follows.
