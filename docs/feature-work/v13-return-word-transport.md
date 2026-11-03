# Canonical return words into the existing byte reader

ReturnWordTransport constructs actual indexed uint256 Vals for arbitrary lists.
encoded_values derives its static word layout; wordAt_index proves every ordered
word at the actual32-byte position, and words_readback discharges the published
ExternalReturnBytes.words complete-word check. Arbitrary extra bytes, including
incomplete trailing words, are preserved in the supplied packet but ignored by
that explicit demanded count. There is no alternative loader/codec/decoder.

The bytes_word/load_word arguments reuse the original owned CanonicalReadback
proofs at85d13e5c, avoiding its unrelated entry/call dependency closure. Those
facts are credited reuse, not new completed backfill. The new index/list reader
composition and known-packet emission/readback consume those facts. Full words
include300/highbit/max with no ByteRange premise. Natural positions/lengths are
not automatically physical-address/resource bounds; emission requires realFits.

The truncated theorem proves rejection of a missing final demanded byte, even
though the underlying entry load itself zero-pads. decode_transport leaves ALL
actual Binders.decodeT primitive validation in place with explicit count equality.
It does NOT prove Source declared-return demand equals remaining caller binders.
Readonly-external owns that phase: SourceInvocationSite.returnTypes versus
SourceInvocationPlan.returns and same-invocation/raw/static-frame provenance.
Zero demand on[1] succeeds in the low-level words API while one demand fails;
neither is permission to skip a declared Source int validation before discard.

Controls execute the real byte reader and three-uint binder decoder, proving
full ordered words, reversed local-environment order and empty remaining words.
They discharge actual known-packet emitter Fits/stack for the reached bytes.
Empty/one/multiple/31/32/33word lists,300/highbit/max, arbitrary partial suffix,
truncation, over-demand and reordered-byte negatives are included. Reordering
inequality is not a malformed decoder failure. No CALL/RETURNDATA execution,
Source invocation, aggregate decoder or unknown-memory encoder is inferred.

Initial length normalization and concrete cast proofs failed; raw failures are
retained. Explicit existing word lengths and natural-to-Int expected casts fixed
them without recursion/heartbeat/fuel/node/time increases. Per-file diagnostics
PASS; readonly source finder/skeptic PASS nofindings. Final artifact reviews
retained externally. All old modules/fixtures/seals remain unchanged.

G21/G41/G42.04/G42.06/BackfillsA/B and original arbitrary self/external-world
obligations remain partial. G40/G42.05 transferred; G42.03/P3 readonly-external.
Original missing actual source/compiler/native/world/resource relations and
mandatory gates remain open/failed. Goal unchanged blocked; no administration.
No reserved Source/runtime/Failure edits or trust shortcuts. Core registration:

- `Solidity.Backend.AbiWorld.ReturnWordTransport`
- `Solidity.Backend.AbiWorld.ReturnWordTransportControls`
