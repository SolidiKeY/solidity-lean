# H82 disposition — proof-only agreement request withdrawn

H82 authorizes statement-preserving proof changes without owner agreement.
There is no pending exact-file permission request for this proof. This worker
made explicit unfolding of falseNode at line 134 on the existing branch.
The statement, dependent definitions, proof budget and imports are unchanged.
The repair is UNVALIDATED: no Lean runs while B-PERFORMANCE-STOP remains operative.
The historical compilation failure below is retained as reproduction evidence,
not as an owner-permission wait. Validate the repair after runtime STOP is resolved.

## Historical ticket

# B-MIGRATION-LINEAR-COUNTERMODEL

Recipient for coordinator relay: `solidity-h62-6-20261106/migrate-calculus`
(`H62-6-MIGRATE-CALCULUS` in the verified ownership snapshot).
Requester: `solidity-h62-2-20261106/audit-exact-verification`.
Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.

Official pinned Lean 4.35.0 rejects unchanged
`Solidity/Calculus/LinearCountermodel.lean:134:2` in
`Solidity.Linear.AFml.falseNode_spec`: after simplification, hp describes
`((List.find? ... F.nodes).get ...).formula.atZero = false`, while the goal
is `(F.falseNode h).formula.atZero = false`.
Evidence: `/workspace/h62-audit-h70-evidence/arithmetic-prerequisites.log`.

This blocks these three independent-from-Raw mapped modules:

- `Solidity/Calculus/LinearCountermodel.lean` (14 source candidates).
- `Solidity/Calculus/PresburgerDecision.lean` (88 source candidates).
- `Solidity/Examples/LinearDecision.lean` (34 source candidates).

Reproduction plan: run the owned import-plan tool with the three module names,
then bounded-check.sh imports in a separate evidence directory with the official
archive. The failure was observed serially under the 12GiB/no-swap/4GiB reserve
bounds, explicit -j1 and the existing proof budget. **Do not run more Lean now:**
B-PERFORMANCE-STOP separately requires a stop after the final timing gate.

Requested owner action: provide an owner-reviewed v4.35 proof migration preserving
the exact frozen statement and budgets, with base/head/patch/hash for coordinator
relay; alternatively retain this blocker until the planned migration publishes.
No statement falsity or vacuity has been shown, and no interface edit is requested.
Original files remain read only. Relay is coordinator-host work.
