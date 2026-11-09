# Storage compilation assumptions

[Authoritative source](../../Solidity/Backend/StorageOps).

Source values and physical/numeric layout must be related by the actual demanded paths and preimages. Mapping barriers, reference aliases and stale-tail clearing cannot be justified with global hash/address injectivity. Lazy function-valued model traversal is not eager emitted execution; general recursive traversal and Source/physical correspondence remain separate obligations.
