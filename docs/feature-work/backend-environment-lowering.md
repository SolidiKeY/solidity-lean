# Environment lowering

[Authoritative source](../../Solidity/Backend/Environment).

An opcode result is meaningful only for the same transaction/world context as the source observation. Keep block/session and account-code provenance explicit. Agreement with a synthetic stack fixture does not establish that an external request supplied the required context.
