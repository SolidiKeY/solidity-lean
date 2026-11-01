# Entrypoints: approved static-call correction boundary

Investigation at `07b4f350bbe15279dc9849bb0d2f4eb7e48d9885`, 2026-11-01.
This is an unfinished repair handoff. No semantic implementation or successful
combined gate is claimed. The `proved` expectation for
`SolcPaymentsOpen.tryArgumentSideEffect` remains unchanged.

## Authority and retained failures

The direct human answer recorded in
`/home/guilherme/.local/state/codex-solidity-feature-monitor/decisions/20261101-approved-pure-external-try/human-decision.json`
authorizes the model correction with proofs and checks. Its SHA-256 is
`5521ea1290fbcfa2623a1926466f97804ad806a1a3be8f2567c6e459e5368afa`.
No further approval of that same correction is requested here.

The retained complete
`/home/guilherme/.local/state/codex-solidity-feature-monitor/integration/entrypoints/c5fbd7b83db64414b73883b6c6045e8a70a35390/attempt-5/gate-23.log`
reports 68 tests, 57 passes and
11 failures. Its assertions include `indexOutOfRange`, `tryScopeExit` and
`tryArgumentSideEffect`; it predates the focused repairs. The applied
division, callback-continuation, literal-reason and Gate G0 repairs are preserved,
as is modifier-only commit `46253180`. No old patch was reapplied.
The current integration already contains local `origin/master` at `099bfbe1`;
no fetch, merge, commit, index write or publication was performed by this worker.

## Confirmed obstruction

The source evaluates `postinc()` before the external `id(int)` call and reads
`ix` afterwards. The retained exact probe
`.lake/entrypoints-repair/payments-current.log` contains a success leaf with
`{ havoc }` between those operations. Its expected result remains `proved`.

* [`ExtCall`](../../Solidity/Syntax/Scoped.lean) has only `addr`, `fn` and
  `args`. There is no static invocation certificate. The solc try printer in
  `Frontend/SolcJson/Body.lean` and the reconstruction in
  `Syntax/Elab/Arms.lean` do not transport one.
* [`ExecS.tryOk`](../../Solidity/Semantics/Callback.lean) permits arbitrary
  invariant-preserving caller storage, ledger and balance. A pure annotation
  on the selected declaration does not restrict this relation.
* [`TTx`](../../Solidity/Semantics/State.lean) has no inherited static mode.
  [`ContractWorld.Context.tx`](../../Solidity/Semantics/ContractWorld.lean)
  cannot carry that mode into the intrinsic run. Its `World.callFrame`
  deliberately rejects nonempty readonly bodies.
* A known self-body proof needs receiver equality with `selfAddress`.
  The original unpinned obligation fixes the receiver to `0xDeaDBeef`, but
  does not supply that equality.
* [`Evm.inFrag`](../../Solidity/Evm/Compile.lean) rejects `tryCall`.
  Its payment-only `CALL` does not execute recipient code; it is not a
  static-call adequacy theorem for this example.

The independent Source interpreter does have dynamic write refusal and
inherited restrictions (`Source/Machine.lean`, `Source/Eval.lean`). It uses
the live state for a nested mark and restores failed frames to that mark.
However, there is no existing Source-to-intrinsic callback bridge. Source
statement inference also refuses try statements. Its environment can issue
credits even while static, so whole-world/balance equality must not be inferred
from its storage-write restriction.

## Bounded interface and ownership decision

The retained O1 producer audit at
`/home/guilherme/.codex/visualizations/2026/10/31/01a19286-57ee-7b20-b170-64ffbc37119a/reinspection-20261031/readonly-external-targeted.json`
assigns typed call modes and static callback/frame
laws to that producer. It records the assignment as incomplete and explicitly
excludes new Source/world/compiler refinement. That audit is historical ownership
evidence, not a fresh live status check. This worker did not contact or modify
the producer VM.

The coordinator needs to settle **which operational interface supplies the
adequacy theorem and who owns its bridge** before parallel work changes that
shared boundary. Two concrete alternatives are:

1. Reuse O1's mode interface once its prerequisite is published, and add the
   missing operational static-call relation and projection at the intrinsic
   callback boundary. Keep the independent Source interpreter unchanged.
2. Extend the independent Source path to accept this try, then prove its typed
   caller-state projection into intrinsic callback reasoning. This adds Source
   inference and cross-interpreter refinement work outside O1's recorded scope.

The first alternative has the narrower integration surface, but neither is
already supplied by a theorem in this tree. This is an interface/ownership
proposal, not a request to relax the approved result or its gates.

Either implementation must provide all of the following before replacing
storage havoc at this invocation:

* derive static provenance from this resolved invocation, retaining compiler
  profile, receiver, arguments, declaration/signature identity and evaluation
  position; a function name or purity flag alone is insufficient;
* enforce attempted-write restrictions transitively, including unknown-code
  callbacks, against the active caller state **after** argument evaluation;
* prove preservation of the caller's typed persistent storage, with failed
  descendants rolling back only their own checkpoint; do not silently infer
  preservation of balances, ledger or all-world observations;
* retain arbitrary successful return bytes, revert/error/panic/raw outcomes,
  ABI decode failure, caller continuation writes, invariant obligations, scoped
  frames and tails, and exact divergence/exhaustion behavior;
* prove the projection into callback semantics and the calculus rule using
  only standard axioms; keep success havoc for ordinary or mutating calls,
  including their reentrant executions, and all failure controls;
* rerun pinned native checks, fresh finder/skeptic review and every original
  combined gate under the unchanged budgets.

Threading execution modes through indexed syntax/run consumers can affect
checking cost. Before such a refactor, inspect the sharing history, including
`96e36569` (checked context sharing), and warn about the affected verification
surface. No such refactor was made in this investigation.

## Checks completed and limits

`.lake/entrypoints-repair/StaticTryBoundary.lean` proves the current unknown-call
boundary for arbitrary typed caller state, storage, ledger and balance. Per-file
MCP diagnostics completed, and `unknownSuccess` depends only on `propext`,
`Classical.choice` and `Quot.sound`. It constructs an actual `ExecS.tryOk`
success at a nonzero nonself receiver, even with an empty self body. This is a
general interface witness, **not** a kernel refutation of the full imported
obligation and **not** a static adequacy proof.

A fresh per-file run of the exact payments probe did not finish and was stopped
before extending the original 300-second source-tool allowance. Its retained
attempt record is `.lake/entrypoints-repair/payments-approved-baseline-attempt.json`.
No current passing result is inferred from the older residual log.

The proposed native observation script retains the exact source hash,
0.8.34 compiler bytes and original legacy/Osaka/unoptimized settings. Execution
stopped at `verifyBudgetArtifact`: the available dependency tree did not match
the audited patched engine. Attempts to derive the exact engine from two local
base trees also failed their full-tree pin checks. No pin, dependency, opcode,
profile or budget was changed, and no native observation passed. The script and
failure remain in `.lake/entrypoints-repair/native-static-boundary.*`.

Finder and skeptic separately confirmed the interface obstruction without Lean
server use. Their reviews also rejected the empty-body helper, a purity-only
shortcut and a pinned-self substitution as solutions to the original unknown
receiver case. Final documentation review corrected the prior-probe wording,
limited the witness description to storage/net/self-balance replacement,
distinguished ordinary reentry from static reentry and added the retained
ownership evidence path. Full combined validation remains
the coordinator's work.
