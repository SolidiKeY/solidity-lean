# Hashed storage assumptions

[Authoritative source](../../Solidity/Storage).

The layout abstraction needs separation only for demanded storage/hash regions of the actual run. Do not claim global Keccak injectivity or infer layout correspondence from concrete unequal hashes. Source aliasing, mapping barriers and packed residual ownership must survive the concrete layout relation.
