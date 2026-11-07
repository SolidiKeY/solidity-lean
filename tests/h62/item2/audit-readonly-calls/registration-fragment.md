# Coordinator registration proposal

These audit modules remain under the assigned tests directory. Do not regenerate
library roots, module maps, or axiom pins from this lane. Registration/relocation
requires area-owner approval; the fragment is a proposal only.

| Audit module (repository relative) | Purpose |
|---|---|
| tests/h62/item2/audit-readonly-calls/ImpossibleDispatch.lean | Refute the contradictory frozen empty-input dispatch hypotheses. |
| tests/h62/item2/audit-readonly-calls/AlwaysRevert.lean | Exact nonempty target-revert consumer applications and empty-domain reject-all controls. |
| tests/h62/item2/audit-readonly-calls/SupportedCalls.lean | Joint callback premise witness and actual Source success/failure/timeout/gas-refusal controls. |
| tests/h62/item2/audit-readonly-calls/JointClients.lean | Twelve exact ordinary consumer applications with all inputs jointly supplied. |
| tests/h62/item2/audit-readonly-calls/HiddenClients.lean | Eleven ordinary hidden-input clients and three callback-choice joint-impossibility proofs. |
| tests/h62/item2/audit-readonly-calls/CallBoundaryWitnesses.lean | Joint static-operation and short/reverted-return inputs with actual Source observations; no compiled callee/frame claim. |
| tests/h62/item2/audit-readonly-calls/JournalWitnesses.lean | Funded distinct-account transfer, persistent storage history and actual credit inputs; no static-call or runtime-frame claim. |
| tests/h62/item2/audit-readonly-calls/InvocationModeWitnesses.lean | Checked captured invocations for inherited/view/pure mode laws; no callee execution or physical-frame claim. |
| tests/h62/item2/audit-readonly-calls/CallerStorageWitnesses.lean | Joint caller-storage premises with actual modeled Source call, nonempty field and caller-owned layout; no compiler/physical-frame claim. |
| tests/h62/item2/audit-readonly-calls/PrivateTransportWitnesses.lean | SDK test-only exact-private-name harness; never import/register in core roots. Four helper premise witnesses and proof-constant identity checks. |
