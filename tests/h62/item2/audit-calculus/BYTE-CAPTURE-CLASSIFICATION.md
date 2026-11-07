# Typed byte-capture classification

Guarded regression: computed image snapshots materialized as ghost typed heap objects must not be promoted into original-source callee execution or physical EVM allocation. Preserve byte/length bounds, heap identities and exact weakening.

Complete frozen-selected Solidity/Evm/TryByteCapture.lean:11 named signatures match frozen/adopted master. Prior1617 rows and owner map unchanged;1628 reviewed/3655 pending of5283;3806 confirmed owners/1477 unresolved. No semantic owner guessed; zero fresh joint witnesses.

Typed UInt8 words roundtrip exactly and lie below256. The actual allocated bytesObj, read through the real HRef returned by the matching allocation, yields the original list under bs.length<2^256. Fresh identity equals the old heap length, old heap objects/alias identities are kept along prefix_append, and old locals are weakened along exactly that extension. Storage/net/transaction/self balance remain equal; heap and environment do change through allocation and weakening.

bytesHalt sequences that existing capture with existing raw memory-revert semantics and returns the full typed THalt.ofData result, including empty normalization. snapshot_halt uses the actual computed FrameMem/ByteSpan snapshot, not desired bytes or a supplied halt equation, and retains the snapshot length bound. It is not the original-source callee run or a new admission/evaluation rule.

Fresh capture cannot alias an old typed reference because old ids are below the old heap length. A boolean-array HRef in the extended heap cannot name the appended bytes object because its indexed heap type disagrees. Neither fact establishes physical memory-address separation outside this intrinsic model.

No source/statements/definitions/interfaces/budgets/axioms/exclusions/toolchain changed; no fresh Lean/kernel/replay acceptance. H28 pauses and all STOPs remain. Exact H145 input publication: evidence: 4f8722f12dae4f516332d892b025def2ca09fec9 evidence/solidity-h28-sol-20261104/automation-benchmark/. The loader pins byte-capture-inputs-v128 at this commit; tests/h62/item2/audit-calculus/BULK-INPUTS.md describes reproduction. Historical unavailable bytes remain UNVERIFIABLE; exact archive-backed duplicate evictions remain restorable.
