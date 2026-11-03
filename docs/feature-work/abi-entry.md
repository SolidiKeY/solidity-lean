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
  every semantic word kind: uint/address, signed integer, bool, enum and
  left-aligned bytesN. Oversized unsigned bounds accept every word without
  immediate truncation. `validator` supplies each exact predicate certificate;
  `frameCertificate` exports its code through Selection V2.
  `EntryTransport.lean`, `RawFreeTransport.lean`,
  `EntryComposition.lean` and `EnumEntry.lean` hold the entry-only part of the
  V13 ABI-world work over the existing indexed decoder; the codec and window
  proofs stay in `Backend/AbiWorld`. Eager/lazy correspondence reuses
  `Semantics/AbiEntryProofs.eager_cref` directly, without a duplicate wrapper.
  `Consumers.lean` inhabits the rejection and composition interfaces.
- **Premises.** `Premises.lean` and `Premises/CalldataViews.lean` (with its
  additive extension `CalldataViewExtensions.lean`) name the pending G34
  overlapping-view, G35.03 and G24.03 producers. No instance is supplied.

Open: emitted calldata decoding, dispatch and full entry composition against
the backend, and the G46.02/G46.03 Bridge backfill.

Numeric validation uses the existing gasless scalar runner, retains arbitrary
stack suffixes and checks every stack boundary with an inhabited scratch bound.
It does not certify calldata loads or external EVM execution. Concrete emitted
controls cover dirty sign/padding bits, signed ranges, full-width words, all
factory branches and stack-capacity boundaries. Frame export uses Selection V2;
future memory-copy consumers must use MemoryCopies V2. The weaker V1 capacity
fields are not evidence for this work.

Validation covers source-graph controls, emitted numeric cases and concrete V2
frame witnesses/refusals. Scoped guards pin standard axioms. Independent finder
and skeptic reviews checked exact predicates, suffix preservation and capacity;
these are local runner and stack-bound controls, not external EVM tests.

The partial G46 access interface lives in
`Bridge/SolidityBridge/AccessBridge/Interface.lean`. It states raw calldata-word,
charged fetched-step and continuation obligations over the pinned EVM state,
with explicit low driver budgets. No instance is supplied. CALLDATASIZE reuses
P10's existing source-input theorem; memory/copy and storage bridges remain open.
Its positive-fuel continuation makes no `X` equality claim at budgets zero or
one. Read-only finder and skeptic review checked that budget partition and the
exact initial byte identity.
