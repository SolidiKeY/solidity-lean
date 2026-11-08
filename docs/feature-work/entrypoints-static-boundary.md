# Static-call semantic boundary

[Authoritative source](../../Solidity/Semantics).

Static-call correction must preserve the distinction between write prohibition and a callback/world frame guarantee. Restricting callbacks merely to make a compiler proof pass changes the source semantics. Follow the approved correction boundary; do not retrofit a narrower call profile or infer caller rollback from an evaluator revert.
