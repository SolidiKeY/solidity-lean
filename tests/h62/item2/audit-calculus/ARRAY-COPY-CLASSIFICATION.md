# Runtime array-copy classification

Guarded regression: dynamic memory-to-storage copying must retain actual memory headers/payloads, word/range bounds, stale-tail cleanup and source representation rather than implying unconditional compiler or physical-EVM adequacy.

Complete frozen-selected Solidity/Evm/MemoryStorageCopyCode.lean and Solidity/Evm/MemoryStorageCopyLaws.lean:14 named declarations including six private helpers/identities. Frozen/adopted-master signatures match; prior1603 rows and owner map unchanged;1617 reviewed/3666 pending of5283;3806 confirmed owners/1477 unresolved. Zero fresh joint witnesses; no semantic owner guessed.

The two-loop code reads the source header from memory and the previous destination length from storage. Exact run success needs n<W, base+1+n<=W, the actual encoded header and every live payload word. The proof handles n=0 at the upper memory boundary without reading a wrapped payload. Copy and stale-tail clear precede replacing the length. Machine updates preserve original caller stack, all memory, balances and environment within this symbolic model.

Private setup helpers retain their own exact bounds: enterCopy and replaceLength need n<W and the header equality; enterClear needs the header equality but no explicit n<W. Four-pop cleanup restores its supplied machine. Final header replacement consumes both temporary base/destination entries and restores the original machine stack.

Store laws distinguish length n<W, live prefix i<n, discarded tail n<=i<old length, and the complement of the entire typed dynamic-array footprint. No unbounded zeroing or arbitrary finite frame is inferred. ReprV excludes slot words from represented primitive payloads. The actual heap snapshot is primitive elements with an empty tail; private strip/overlay identities remain primitive-only.

The final representation theorem needs full ArrayRepr (space, actual header and per-element representation) jointly with heap length<L, then represents the snapshot overlaid on any supplied old destination. This is conditional symbolic execution/representation, not a producer of whole compiler success, gas/fork/world or physical storage adequacy.

No source/statements/definitions/interfaces/budgets/axioms/exclusions/toolchain changed; no fresh Lean/kernel/replay acceptance. H28 pauses and all STOPs remain. Exact H145 input publication: evidence: 109856958e6df7a445c12b518c7da2d60a1d74af evidence/solidity-h28-sol-20261104/automation-benchmark/. The loader pins array-copy-inputs-v127 at this immutable commit; tests/h62/item2/audit-calculus/BULK-INPUTS.md describes reproduction. Historical unavailable bytes remain UNVERIFIABLE; exact archive-backed duplicate evictions remain restorable.
