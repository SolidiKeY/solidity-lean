# Proof automation: guarded selector cancellation

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Worker handoff (historical): **patch_ready_unvalidated**. The implementation was delivered by a patch
worker without compilation or kernel checking. Current combined checks and
the original source regression's integration result are tracked in integration.md. The overall proof-automation group remains partial.

## Implementation

`Facts.cancel` in `Calculus/Closer/Normal.lean` already cancels
`(a + b) - b` after checking that the sum returns. It now also recognizes
`(a + b) - a`, returning `b` with the same whole-sum guard. Both cases retain
the typed result cast; neither changes the representation or the search
bounds. `Facts.cancel_eval` includes the second case for checked unsigned
and signed integers. It derives the subtraction result from `evalT_add`
and converts the surviving typed value back with `ofInt?_ival_self`.
`Closer/Bytes.lean` already delegates subtraction to this function and
proves its fold by `cancel_eval`; no second integration path is added.

The KeY correspondence is a composition of `polySimp_*` normalization,
including `polySimp_elimSub`, `polySimp_addAssoc` and `polySimp_addComm0`
in the frozen `intSimplificationRules.key`.
KeY's arithmetic is unbounded. The Lean whole-sum success premise is
necessary for checked machine integers, and cannot be weakened to success
of the individual operands. The rule-map row records this distinction.

## Regressions and diagnosis

`Examples/Tactics/FunctionTypes.lean` adds universal `selectorOfValue` beside
`addressOfValue`, plus a concrete normal-return witness at address `7`.
After `cancelDiv`, the existing selector lowering reads
`(address * 2^32 + selector) - address * 2^32`: exactly the newly supported
orientation. Direct matcher regressions cover both operand orders, unsigned
overflow, signed underflow and failed operands. Two diamond counterexamples
retain failure before subtraction, using kernel evaluation proof scripts.

`tests/solc/FunctionTypes.sol` adds an isolated public selector assertion and
a deliberately false selector assertion. Its original `externalValue`
function is unchanged. `tests/solc/GuardedCancellation.sol` checks both
signed/unsigned orders and includes overflowing and false-property cases.
`scripts/guarded-cancellation.test.mjs` runs these through the public source
runner and retains `externalValue == proved` as a hard integration gate.
The existing function-type suite's expected verdict is unchanged. New false
source cases permit `refuted` or `pending`, but reject `proved`, unsupported
admission and missing obligations. The explicit Lean counterexamples provide
the intended semantic rejection independently of the runner's search.

This is a confirmed missing local normalization shape, not yet a confirmed
complete diagnosis of `externalValue`. If `selectorOfValue` proves but
`externalValue` remains open, inspect the remaining indirect call's decoded
address/selector, helper captures, self-call dispatch and ABI-width premises.
Do not replace the original expected result with `pending`.

The current source-admission snapshot also has independent blockers:
`Frontend/SolcJson/Admission.lean`'s `walk` rejects stored function members
with `solidity.functionMemberKind`, and `scan` rejects `unresolvedDispatch`.
`Frontend/SolcJson/Contract.lean` populates that list through
`unresolvedValueCalls`, including dynamic calls in the existing positive
function-type suite. Consequently the new source gates require the primary's
admission integration before they can establish an end-to-end repair. Typed
ABI-kind projections and exact finite typed call-target extraction are
dependencies; this patch does not remove conservative admission guards.

## Integration checks due

1. Per-file Lean diagnostics for `Closer/Normal.lean` and
   `Examples/Tactics/FunctionTypes.lean`; inspect the universal theorem and
   the two invalid-diamond proofs. The cancellation soundness theorem must
   retain only the standard axioms, with no `sorryAx`.
2. Build the affected example and `Frontend.Testing`, then run
   `node --test scripts/guarded-cancellation.test.mjs` and the existing
   function-types case in `scripts/test-solidity.test.mjs`.
3. Run the relevant library/TestSuite, frozen SolKey/corpus, layering,
   reachability and generated inventory gates after integrating main.
4. Measure source-runner cost on the original `externalValue` and the new
   isolated selector function. No heartbeat limit or size cap was increased.

## Review

Read-only finder review confirmed the missing operand order and the need
for the whole-sum guard. The read-only skeptic found that direct matcher
tests could not use `decide` on `LTm` equality without a `DecidableEq`
instance; these tests now use definitional proofs (`rfl`). The skeptic
found no guard weakening in the symmetric soundness branch. Artifact
integrity checks and compiler-only fixture checks are recorded in the patch
manifest. Neither preparation reviewer invoked Lean. These historical results
are separate from the combined Lean and source-runner checks in integration.md.

## Scope boundaries

The worker inspected `origin/master` (`dd905139` when preparing the patch):
its `Closer/Normal.lean` and `Closer/Bytes.lean` match the real working tree.
Master's newer modifies-aware loop frame (`Prog.frame` now returns an
optional root set) and M7 array/hash/fresh-memory decisions are not copied
or changed. Quantified/memory loops, callback diamond semantics, invariant
inference, large storage-push loops and broader exact verification remain
separate work. No feature inventory status is upgraded by this patch.
