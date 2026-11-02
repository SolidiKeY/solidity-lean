# Entrypoints: approved static-call correction boundary

Investigation at `07b4f350bbe15279dc9849bb0d2f4eb7e48d9885`, 2026-11-01.
This is an unfinished repair handoff. No semantic implementation or successful
combined gate is claimed. The `proved` expectation for
`SolcPaymentsOpen.tryArgumentSideEffect` remains unchanged.

## Integration refresh at `f1808176`

The ownership choice below is historical: the coordinator has since selected
alternative 1, the original O1 mode producer plus intrinsic operational
projection. That choice and the human's model-correction authorization remain
valid. No repeated approval of either is needed. Independent Source try
inference and general world/compiler expansion remain outside this repair.

The current integration contains the zero-divisor, callback-continuation,
literal-reason and modifier-only repairs. No content conflict markers were
found in the affected source, tests or scripts. Its `ExtCall` still has only
receiver, name and arguments, and `ExecS.tryOk` still permits arbitrary
invariant-preserving storage/net/balance replacement. The original pending
payments residual remains relevant; it was not rerun or reported as passing.

The supplied O1 cumulative bundle was independently checked against SHA-256
`7e7b44e829a1269c8900dc32bd89f29ccce5776c143163ce6e9dd3f1668cccd3`
and inspected at `cb82043daac3f72865a722225b994dd1ca9e6a5d` in a private
object database under `.lake/entrypoints-repair/`. It was not merged or applied.
The following are source findings, not local kernel validation of that branch:

* `SourceInvocation.AtCall` contains actual prefix and capture executions;
  its `oracle` proves lookup-key agreement. Neither supplies an execution of
  the selected unknown callee. `StaticInvocation.AtCall.storage_projection`
  still takes `StaticInvocation.Frame .static` as a premise.
* `StaticInvocation.Exec.credit` permits net/balance changes. The byte-linked
  callback success theorem separately requires ledger and balance agreement;
  storage preservation cannot discharge those premises.
* `ExternalReturnBytes.decode` reads the caller binder context's word count.
  Here `id` declares `int`, but the try has no return binders. The retained
  `SourceInvocationSite.returnTypes` metadata does not yet validate those
  discarded declared returns or establish the caller's ABI-failure phase.

### Exact remaining prerequisite

Within the selected alternative, the operational invocation/ABI producer must
supply an execution judgment for this actual resolved call, at its post-capture
checkpoint, retaining runtime/profile, receiver, arguments, evaluation position,
inherited restrictions, descendant checkpoints and exact outcome bytes. The
typed projection must derive
`StaticInvocation.Frame .static origin.point.st exactOutcome typedFinal`
from that execution and its caller-state representation. This expression is
the proposed result type, not an available theorem or an assumed certificate.
Its storage conclusion must not silently strengthen ledger/balance behavior.

The same invocation must validate the declaration's return demand before
discarding its values, then project either typed success binders or the actual
caller decode failure. A successful malformed child return must not become a
callee failure caught by the try. Ordinary havoc, mutating/reentrant calls,
failure bytes, invariant obligations, frames/tails and exhaustion retain their
existing obligations. The bounded implementation consists of that execution
and representation interface followed by O1's call-linked projection. No such
producer declaration was found in the supplied source. This remains missing
implementation under the existing authorization, not a request to approve the
model correction or owner choice again. An independent Source/world/compiler
expansion remains excluded; an assumed frame or a synthetic issuer cannot
replace the missing actual-execution input.

### Fresh evidence and review

An exact copy of O1's `scripts/check-static-capture-vectors.mjs` passed all
32 native controls across its four existing profiles, using the recovered
audited dependency artifact, original compiler/source hashes and unchanged
attempt budget. The script was run from a private directory against the
current fixture. The full receipt is
`.lake/entrypoints-repair/native-static-source-reference-current.json`.
All four malformed-return cases observe successful child bytes `0x01`, caller
storage `ix = 1` before and after that child, then outer empty revert and root
`ix = 0`. Ordinary mutation, false-preservation, readonly reentry and nested
write-refusal controls remain asserted. The earlier failed draft native probe
and its raw observations were preserved. These finite controls are not
invocation/frame adequacy or an original combined-gate pass.

The current-tree investigation probe
`.lake/entrypoints-repair/StaticTryCurrentBoundary.lean` completed per-file MCP
diagnostics with no errors. It proves arbitrary successful unknown-call
storage/net/balance replacement, acceptance of every word list by nil binders,
and rejection of an absent demanded signed return. Axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`. These are interface witnesses,
not the full imported obligation's refutation or the missing adequacy proof.

Fresh read-only finder and skeptic reviews independently confirmed both
missing producer facts and the separate ledger/balance premises; finder also
confirmed the retained zero-divisor, continuation-dispatch and modifier fixes.
Neither used the Lean server. No semantics, public premises,
fixtures, pins, profiles, assertions or budgets were changed. The original
combined gates remain with the coordinator; this refresh does not complete
the repair or clear publication.

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
