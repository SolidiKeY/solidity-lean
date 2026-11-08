# Hash assumptions

[Collision assumptions](../../Solidity/Hash/CollisionBound.lean) and [adaptive bounds](../../Solidity/Hash/Adaptive.lean).

A per-run collision-free region is an explicit assumption about demanded hash/slot queries, not global injectivity of Keccak. The random-oracle probability model is separate from deterministic kernel semantics. Neither concrete distinct test hashes nor a finite transcript proves universal collision freedom; storage/compiler clients must retain their exact demanded-domain premise.
