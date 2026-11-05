# VC1 source-inventory reconciliation

Upstream `1e367905c938186aac1680f25d1059721ddce333` adds the assumption/profile
modules. The existing lexical trust scanner reports two `opaque` sites in
`Solidity/Calculus/Assumptions.lean`: the `HashReading.opaque` constructor and
its default record-field value. Neither is an opaque declaration, axiom,
unsafe implementation, native decision or kernel-check bypass.

The inventory pins only those two exact existing-source fingerprints. Scanner
rules and all forbidden-token checks are unchanged. Existing inventories
already retain exact lexical fingerprints of `.opaque` data references in
`Solidity/Calculus/RewriteScoped.lean`; this uses the same strict convention.
The source modules and theorem statements are unchanged. Both independent
read-only classification reviews and the unchanged scanner tests must pass
before publication; final combined kernel and axiom gates remain mandatory.
