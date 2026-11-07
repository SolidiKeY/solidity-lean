# Osaka applicability checkpoint

Fetched origin/master and inspected log and all four outstanding core files.
Rebased owned branch onto 71c5963f3cd9da2eb2989be1e19c810def6ff019; no relevant
producer implementation was duplicated. Ignored H44 evidence was preserved
outside checkout during replay and restored without changes.

OsakaWitnesses.lean implements five original applicability cases: one closed
fidelity, three data-domain samples, one simultaneous proof-premise witness.
The IDENTITY failure-law samples establish applicability of the equivalences,
not an actual malformed rejection. The joint gas witness retains LengthPriced
and ordered nonempty inputs together. No native crypto/compiler success claim.
Five exact axiom guards pass (propext/Quot.sound, or none).

Bounded serial pinned check: Lean4.24, explicit-j1/-M11264/--tstack=131072,
threads1,12GiB AS cap,no swap,4GiB reserve;0.503252s,263331840B aggregate peak.
Raw failure and successful receipts stay off Git, bound by
osaka-evidence-manifest.json. Initial namespace error is fixed and its failed
receipt remains unaccepted. No module above60s. Lean MCP unavailable.

Separate read-only finder and skeptic approve all five cases; neither used
Lean/server/build/tests or edits. Both note IDENTITY equivalence is not an
actual malformed rejection and monotonicity need not be strict.

Ledger intentionally remains97/138 until these five are integrated with the
receipt/type-fidelity/acceptance mutation checks. Thus41 ledger cases remain;
five now have checked proof payloads,36 still need implementation. Next ready
items: BLS18,PointEval6,Stipend12, then integrate all exactly once. No missing
producer blocks this continuation. Full gates and actual compiler success remain
open. Migration435 and G43 owner waits unchanged; no goal reset/completion,
master push, producer edits or budget increase. This is a proof checkpoint,
not full assignment acceptance or RUNTIME_GATE_PASS.
