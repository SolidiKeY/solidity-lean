# Shared-checkout feature integration

The ten Chalmers feature chats used one checkout at the user's request. The
old serial writer queue is stopped. The source-admission writer completed its
checks and voluntarily handed off; its live lock was not stolen. Nine stalled
groups continued in context-preserving recovery chats that wrote patch artifacts
outside the checkout. Those workers never polled or acquired the shared writer
lock. All nine have finished. The integration coordinator applies patches and
runs Lean alone. A final app-server audit found no active original feature chat
(all ten unloaded in the latest audit).

The existing work was checkpointed in `ea06b814` and current upstream main was
merged in `c48c52e7`. Subsequent integration preserves that upstream work,
including the current array/hash/memory closer and loop-frame improvements.
Unrelated build logs and scratch files are excluded from delivery.

## Integrated milestones

| Group | Delivered boundary |
|---|---|
| [Source admission](source-admission.md) | Compiler provenance, exact literals, declaration identities, transitive admission and finite dispatch. |
| [Declarations](declarations-metadata.md) | Declaration metadata, source ABI identities and primitive public getters through actual self-call programs. Reference/nominal getter limitations remain explicit. |
| [Operators](numeric-operators.md) | Resolved operator aliases, typed lowering and evaluation-order/failure checks. |
| [Aggregates](aggregates.md) / [slice copies](../calldata-slice-copies.md) | Inline arrays, reference captures and fresh primitive calldata-to-memory materialization. |
| [Recursive storage](recursive-types.md) | Typed graph storage, copy admission, snapshot copying and an ordinary-value subtree bridge. Ordinary recursive source/State/calculus support remains missing. |
| [ABI and hashes](abi-hashes.md) | ABI boundary repairs, ERC-7201, recovery reference vectors and exact-width hex literal evidence. |
| [Transient storage](transient-storage.md) | Typed transient effects composed with ordinary programs and transaction entry/reset. Ordinary source transient declarations remain refused; scoped formulas/taclets are not extended. |
| [Contract world](contract-world.md) | Explicit typed creation/call/library frames and restricted source factories/libraries with stated environment premises. No general Solidity world or joint transient/world execution is claimed. |
| [Calls and exceptions](calls-exceptions.md) | Eager operands, failure priority, exact panic/catch transport, fixed-byte custom-error ABI alignment and declaration-resolved positional emit operands. Named/qualified emits remain refused; logs are abstract. |
| [Proof automation](proof-automation.md) | Symmetric guarded cancellation, including overflow/underflow and failed-operand controls. |

## Integration review

Read-only finder and skeptic passes reviewed the affected areas without opening
Lean workers. Confirmed issues were fixed: stored function projections retain
their ABI kinds; finite dispatch includes synthesized getters without erasing
source-kind collisions; fixture regeneration updates all previously valid hashes
while preserving intentionally stale tests; fixed-byte error operands preserve
their widths, widening and eager captures; narrow self returns retain decoder
guards outside catches and reject incompatible fixed-byte bindings.

Calldata alias tracking distinguishes a fresh memory result from its arguments.
The recursive memory-argument check and nested assignment tracking retain the
original conservative mentions. Identity, forwarding and nested-assignment
negative controls accompany the valid copied-return mutation. Ordinary calldata
pointer rebinding retains proven calldata provenance; captured slice bases stay
stable. Assignment-result and conditional-reference write bases cannot conceal a
readonly origin. The struct constructor uses legacy allocation-before-fields
and via-IR fields-before-allocation, backed by pinned compiler output and
first/last failing-field regressions. Source event emission preserves operand
order while its logs remain abstract.

Lean elaboration repairs preserve theorem statements and avoid larger heartbeat
limits or new proof axioms. Frontend parser evidence is checked by executable
guards; it is not presented as a theorem about opaque JSON operations. Core
packages still have no external dependencies.

## Source and automation boundaries

The new primitive getter caller tests use explicit `@custom:key box` safety
obligations. Existing automation does not close diamond obligations across
external `try`, including resolved self calls. This remains an automation limit;
box safety is not a termination claim. `Examples/Tactics/PublicGetters.lean`
also contains separate concrete successes and false-assertion panic controls
from the initialized state with `selfAddress = 7`. Finite kernel certificates
are transported by `Prog.runF_approx` to actual `Prog.run` observations, so these
controls require completed runs rather than fuel exhaustion. Their current
validation belongs to the combined gates below.

Event import accepts only unqualified, declaration-resolved positional emits.
The existing native lowering evaluates operands and abstracts the log; it does
not prove a log payload. Named event lists are refused because the pinned
compiler/EVM controls observe parameter order in legacy and source order in
viaIR; positional controls use source order in both. Event support remains
partial, and no general argument-order rule is inferred from binary or modular
arithmetic scheduling.

Primitive slice materialization is part of the ordinary frontend. Graph storage
and transient effects are integrated foundations with separate explicit APIs;
they do not make ordinary recursive structs or transient declarations executable.
The world API supports its documented source fragments and explicit environment
premises, without general Solidity-world or joint transient/world semantics.
Historical worker handoffs and isolated validation in the group documents are
preserved as provenance; this page owns the current combined validation state.

Imported plain source obligations now state the [EVM input domain](../source-inputs.md)
`address(this) < 2^160`, including constructors; native states and native
`Problem.fml` keep their wider transaction fields. Source address casts remain
intact. Both explicit-self entry points reject out-of-domain addresses to
avoid contradictory input premises. The original `externalValue` positive
expectation remains a required gate. Boundary and concrete projection controls
are included in the passing combined validation below.

## Final review and build isolation

The read-only finder and independent skeptic reviews found no confirmed defect in the canonical source
self-address premise, explicit-self rejection boundaries, source printer scope,
or the callback pruning and ordinary-proof routes. The new `ProvesC.closeFalse`
rule requires the complete hypothesis wrapper to be callback-free; its soundness
uses the existing ordinary proof theorem. The bounded strategy keeps that
side condition and restores its metaprogram state on failed probes. The ordinary
compiled route retains the same sequent after the existing callback-free check.
Callback regression controls retain true hypotheses and nonlanding diamond
prefixes rather than discharging them by contradiction.

A fresh CLI import initially crashed during a scalar byte conversion, despite
passing focused checks. The crash-era runtime setup mapped only its direct
import; Lean resolved transitive imports through the local search path, where
an older grammar artifact remained. The import itself had been compiled with
the current cached grammar. An isolated rebuild of all 32 import dependencies
and a rebuild with a fresh private cache both passed the identical source import
without a source change. Final combined gates use that new cache and run serially.
This identifies a mixed-artifact failure; no new semantic restriction or proof
expectation was introduced to bypass it.

The final source-function dispatch repair preserves the raw selector quotient
and separately cleans call receivers to 160 bits, matching their `.address`
projection. Native contracts without source metadata retain their original
receiver behavior. Runtime controls cover canonical and wide receivers.

Callback pruning now checks up to eight typed context layers for an earlier
contradiction, including a prefix before callback havoc. Its soundness proof
retains every preceding update and diamond landing requirement. Direct proof
construction supplies the dependent arguments explicitly and checks the
refutation, modal-free guard and callback-free guard synchronously in the kernel.
`sol_prefix_false 8` replays that fixed certificate without tactic search.
The strategy also avoids ordinary-proof attempts while an explicit callback
`try` remains and prioritizes hiding a failed-call premise when its boxed catch
continuation immediately reverts. Both are choices among existing rules; no
callee behavior or live context is erased. A pinned replay covers the reverting
catch case.
Regressions cover a contradiction before havoc, true contexts, and both orders
of a contradiction and a failing diamond update. Finder and skeptic reviews
confirmed these invariants. Speculative arithmetic prefix search was removed.

The first combined library pass exposed four generated-output/fixture issues:
source self-address premises missing from two pins, repeated power evaluation in
LaTeX output, and duplicate declaration IDs in an operator-alias negative AST
mutation. The pins now show the full source premise, its bound is an exact
literal, and the mutation preserves declaration identities. All four files pass
focused diagnostics; the combined gates below remain authoritative.

The last combined pass exposed two callback-walk boundaries. A negative
program premise in the native self-receive proof now gets the full closer
before the existing `hideLeft` fallback. For a Boolean mapping key, the
source elaborator creates a joinable `if` that assigns a local before a
callback-capable `try`. `Stmt.forksIn` deliberately marks every `if` as
forking, while `Stmt.callsBack` proves this joinable assignment has no
callback. `ProvesC.update` now uses that latter condition; its soundness
uses `Stmt.eq_run` to equate all callback runs with the typed run, retaining
the panic and diamond-exhaustion obligations. The callback replay uses the
named constructor through `RuleExists.leaf`, which reconstructs typed holes
and checks its side conditions before the kernel accepts the rule. The final
read-only skeptic found no soundness or replay defect in these repairs; the
combined build and source regression below remain the performance and
integration checks.

The TestSuite's long-array refutation exposed a certificate shape assumption:
it recognized `wt(storage) → ψ`, while source obligations now put input-domain
premises before `wt(storage)`. The long-array certificate now evaluates and
proves each such premise at its concrete witness, then uses its existing
kernel proof for the `2^255`-element storage and false body. The original
`invariantClosedFormSum.refuted` theorem passes its focused build; the
TestSuite gate below checks it with the rest.

The corpus corollaries had the same earlier assumption about obligation shape.
Their generator now keeps and proves the source input premise at the imported
contract's initial state (`by rfl`) before deriving the typed run from the
existing `⊢` theorem and `wt(storage)`. Regeneration changed only
`Corpus/TestSuite.lean`: the frozen expected verdicts, scoreboard and other
generated modules are byte-for-byte unchanged.

## Validation

Integration validation passed with the private `validated-cache` and the
frozen SolKey snapshot:

- `./run-lean.sh`: 637 library jobs, 249 TestSuite jobs, then `solkeycheck`
  at 377 taclets and 131 read-bearing annotations.
- Frozen `check-corpus.sh`, without `--update`: 774 obligations and no drift
  in `tests/solkey/expected.tsv`; `check-testsuite.sh --complete` confirms
  552 derived, 11 refuted, zero pending and zero divergent TestSuite rows.
- The full 35-case source batch passed, including primitive getters,
  Boolean mapping keys, original function-value verdicts, guarded
  cancellation, reference refusals and transient source refusals.
- The feature audit classifies 211 features and 783 upstream symbols;
  layering checks find 143 core modules with no elaborator reachability;
  strict automation finds zero pending obligations. The new callback
  soundness theorem and full `ProvesC.sound_of` use only Lean's three
  standard axioms.

Read-only review found no confirmed defect in the final callback, long-array
certificate or corpus corollary repairs. The remaining static findings are
the pre-existing 33 ignored scratch orphans, 13 missing vendor/external doc
paths and 25 inventoried trust-drift entries; no new source or dependency
was introduced for those baseline findings.

## Branch consolidation (2026-10-26)

The current remote decision-procedure work and the committed `kintneg`
encoder are integrated with the source-feature work above. The encoder is
feature 30; the later uncommitted integer-anchor and array-block experiments
remain separate. No external dependency was added.

Read-only finder and skeptic reviews found stale feature numbers, missing
module-map entries and an obsolete description of negative KeY `int` binders
as undecided. These are corrected in the module guide and automation document.
The callback merge preserves the source-feature declarations and updates only
the generated send replay pin and its explanation.

The static integration gates pass: 143 core modules reach no elaborator,
strict automation reports zero pending obligations, and the frozen TestSuite
audit reports 552 derived, 11 refuted and one excluded function. The existing
33 ignored scratch orphans and 13 missing documentation references remain.

The final `./run-lean.sh` passes with current shared-cache artifacts: 646
library jobs, 249 TestSuite jobs and frozen SolKey's 377 taclets / 131
read-bearing annotations. Validation ran with a 10 GiB hard memory cap and
swap disabled. A fresh sequential check of the unchanged
`TestSuite/Derived17.lean` exceeded that cap and was stopped by the cgroup;
its matching shared-cache artifact subsequently allowed the full gate to
pass. A clean rebuild within 10 GiB is therefore not established.
