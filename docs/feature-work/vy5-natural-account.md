# H19 natural Source accounts: interface step

Status: partial, owner-held; not ready for combined Source integration.

`Source.Account.balance` and `Account.withBalance` now use exact natural
money. Actual `ExecState.transfer` retains Word call value and delegates to
`transferNat`; affordability, distinct-recipient overflow refusal, self-transfer
no-op and the original rollback/refusal theorem strength are retained. Actual
credit/debit/deployment store exact natural balances. Known-code `evalE.balance`
uses the explicit modular `Monetary.wordView`; equality with exact money still
requires a separately proved range invariant. The external `Fixed.ledger` and
opening balance interface remain Word-valued and unchanged (H19-LEDGER1).

`Source.MonetaryWorld` states bounds on both current accounts and saved journal
accounts, proves withBalance/undo/undoN/rollback/endTx and actual successful
natural/Word transfer preservation, and pins twelve exact standard axiom sets.
Its wide-account control represents 2^256 exactly. Its saved-wide counterexample
shows that an in-range present world alone does not justify range after rollback.
These are execution primitive laws, not full reachable-EVM or session invariants.
Actual credit/debit/deployment range transport and initial-image closure remain open.

Measurements use the same serial bounded checker and source/import hashes:
[before/after numbers](vy5-natural-account-timings.json). World 0.642→0.595s,
Machine 1.674→1.642s, Eval 8.084→8.009s, Semantics 0.968→0.949s,
Horizon 346.956→340.924s, HorizonDeploy 8.888→8.849s,
Session 2.231→2.207s, Funds 0.242→0.246s. There is no noticeable checking-time
increase. Horizon remains a pre-existing FAIL against the 300-second module
policy; its kernel exit 0 does not waive that policy. Dependency-build elapsed
seconds are not these per-file checking times. Hard memory/swap limits remained
12GiB/12GiB; the after closure sampled 8,217,178,112 bytes aggregate RSS and
8,917,626,880 bytes minimum OS available, with no resource stop.

The two owned Source examples retain their exact prior numeric expectations.
The transfer example's actual axiom set decreased to empty; its pin was updated
after retaining the diagnostic mismatch. The initial range proof's let-reduction
failure is retained separately from the corrected per-file pass. Automation
attempts and exact signature output are preserved under
`/workspace/vy5-composition/natural-account-20261104/`.

Independent read-only finder and skeptic approved this narrow interface step,
with no findings; neither executed Lean or tests. They explicitly require the
remaining consumer migrations, whole-balance operations, external monetary
ledger decision, real reachability and full combined checks before release.
A hash-bound inventory records 57 downstream Source-account read files: the
two owned Source examples are migrated; 55 other read-file migrations remain. Whole-balance/selfdestruct consumers must use exact Nat operations,
not cast the amount to Word. No downstream compiler/EVM correspondence is claimed.

Queue: H16/P8a full execution/realization, immutable/funds release, remaining H19
consumers/ledger/reachability, all 24 original Y10 obligations and six general
Source combinations, Work2/3 and BackfillA/B remain partial or pending.
This step supplies no fresh native comparison. Original five optimized-viaIR
journal mismatches/exit1 and historical docs/G03 failures remain retained;
zero regression and finite Source controls are not full-lane gates.
