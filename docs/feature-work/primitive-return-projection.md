# Primitive return bytes and caller projection

`Semantics/ExternalReturnBytes.lean` reads the required complete 32-byte words
before invoking the existing intrinsically typed binder decoder. It rejects
short demanded words and invalid primitive encodings; unused trailing bytes,
including an incomplete final word, are ignored. Error/Panic classification
uses the existing decoders, and raw catches retain the original bytes.

`Semantics/PrimitiveReturnProjection.lean` validates every declared primitive
result before projecting it into caller binders. `Projection` permits keeping
all results or discarding all of them. Binder labels may differ, but contexts
and values retain their types. `success_reads_actual_words` supplies the words
read from those same bytes; `success_complete_word` retains the demanded-length
condition. The existing nil-binder decoder is unchanged: the new consumer's
explicit declaration is what prevents discarded nonempty results from skipping
validation. The failure-existence lemma alone gives no byte provenance.

The two matching modules in `Examples/Tactics/` check signed/mixed word order,
canonical integers, invalid booleans, missing/short words, discarded values,
zero-return declarations, ignored suffixes, mismatched caller types and raw
noncanonical Error/Panic payloads. Their proofs use the kernel, and headline
axiom reports are pinned in source and `scripts/g07-axiom-pins.json`.

## Integration boundary

This is a scoped checkpoint recovered from original O1 commit
`06fbbcabbf61381a3a0c2262b3a3bcffabc8812a`, with its pure projection extracted
from the unfinished operational consumer into a separate module. Every selected
statement and proof is retained; the failure-witness comment is clarified.
The original bundles, full operational source and failed receipts are preserved.

No callback, importer, admission profile or existing expected verdict changes.
A caller still needs a genuine declared signature and actual callee outcome;
these modules do not certify that source/execution origin. The static-call,
caller/callee failure-phase and actual invocation/frame producers remain with
O1 and its consumers. This checkpoint establishes neither C5 completion nor
source-to-compiled-EVM correspondence, and the original O1 goal remains partial.

Local focused checking, all four per-file diagnostics, the combined core and
SolKey TestSuite build, and the retained `473da8944c` sort-annotation check pass
with cache reuse. The combined run peaked at 1.43 GiB under a hard 12 GiB cap,
no swap and a monitored 12 GiB host reserve. Independent finder and skeptic
reviews confirmed the selected statements, proofs, controls and scope.

Trust, import-layer, orphan and whitespace checks pass. Global documentation
and axiom-inventory checks retain their exact master baseline failures; the
checkpoint introduces no new findings. These comparisons do not assert that
the unrelated global inventories are clean. Raw failures and byte-bound gate
receipts remain in the coordinator's integration record.
