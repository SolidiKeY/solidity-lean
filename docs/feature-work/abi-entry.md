# ABI entry (G40)

Status: partial. `Solidity/Backend/AbiEntry/` states the G40 obligations for
calldata decoding, dispatch and entry composition, and proves the parts that
need no new decoder.

- **Interfaces.** `Interface.lean` (source boundary), `CompositionInterface.lean`
  (ordered entry recursion), `RejectionInterface.lean` (conditional rejection
  through the existing checked byte-slice runner) and
  `WordValidationInterface.lean` (emitted primitive validators). They are
  narrow contracts with source-only graph controls, not runtime, decoder or
  admission instances.
  Source coverage is derived from exact graph agreement, with inhabited graph
  and empty-relation controls. Dispatch helper equalities are bookkeeping and
  may be definitional; they do not establish runtime dispatch.
- **Proofs.** `WordValidation.lean` gives actual numeric bytecode for
  unsigned, bool and enum word bounds. Bounds at or above 2^256 accept every
  word. `EntryTransport.lean`, `RawFreeTransport.lean`,
  `EntryComposition.lean` and `EnumEntry.lean` hold the entry-only part of the
  V13 ABI-world work over the existing indexed decoder; the codec and window
  proofs stay in `Backend/AbiWorld`. Eager/lazy correspondence reuses
  `Semantics/AbiEntryProofs.eager_cref` directly, without a duplicate wrapper.
  `Consumers.lean` inhabits the rejection
  and composition interfaces.
- **Premises.** `Premises.lean` and `Premises/CalldataViews.lean` (with its
  additive extension `CalldataViewExtensions.lean`) name the pending G34
  overlapping-view, G35.03 and G24.03 producers. No instance is supplied.

Open: emitted calldata decoding, dispatch and full entry composition against
the backend, and the G46.02/G46.03 Bridge backfill.

Numeric validation uses the existing gasless scalar runner, retains arbitrary
stack suffixes and checks every stack boundary with an inhabited scratch bound.
It does not certify calldata loads or external EVM execution. Signed and bytesN
validators remain open. Future consumers use Selection and MemoryCopies V2;
the weaker V1 capacity fields are not evidence for this work.

Validation of the interface cleanup: targeted Lean import closure and scoped
standard-axiom guards. Independent finder and skeptic reviews found no remaining
issues after correcting the contract-scope wording.
