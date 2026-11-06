# Simplifier investigation and joined specification preparation

The bottleneck is repeated normalization of nested state updates, not the cost
of constructing the simp rule set. The same dynamic-logic calculus does not
imply the same executable checking algorithm: the previous specification
closer repeatedly simplified the complete continuation under dependent
binders, produced equality proofs, and asked Lean to check their types.
SolKey's native rule engine does not run that Lean elaboration pipeline.

## Evidence

The baseline is commit `1db639a2239195365250c26fe8d054c89b8507b5`, the six
identical-source measurements in [browser-simple-benchmarks.md](browser-simple-benchmarks.md).
The new investigation uses Lean 4.24.0, one Lean thread, the same native C
plugin control at `-O0`, and the same compiler and runtime pins.

For the baseline maximum example, the three major simp calls took 677, 307
and 344 ms. Their `mkSimpContext` calls took 3.3, 3.7 and 4.0 ms. A threshold-zero
Firefox profile attributes approximately 903 ms exclusively to simp traversal,
480 ms to `Meta.isDefEq`, 177 ms to its assignment work and 132 ms to `whnf`
inside the simp stacks. These are instrumented native diagnostic timings,
not browser wall times; profiling adds overhead.

The diagnostic counters explain the expression growth: `CloseS.Landed.val`
was unfolded 4,867 times, `Subtype.val` 2,684 times, `State.H` 1,439 times and
`State.tx` 803 times in the first large pass. Four broad rules each had 683
failed attempts (`forall_eq`, `forall_eq'`, `implies_true`,
`Close.forall_const_type`). Removing these four rules did not materially
improve the branch benchmark: failed-rule counts alone were a misleading
optimization target. Making projections opaque left proofs pending;
introducing binders before typed landed reads also broke positive proofs.
Disabling dependent simplification was not a consistent improvement.

Initial configuration probes did not demonstrate that the intended replacement
actually executed; their timings are excluded. The retained probe uses distinct
tactic names and a runtime `parts-active` marker. Pinned Lean 4.24 tries macros
before tactic elaborators: an unconditional whole-leaf macro would mask a
new step handler. The final regression checks handler order and absence of a
masking macro; the matched control records actual `step` / `whole` route events.

## Change

`CloseJ.prepareSteps` extracts the existing one-update-at-a-time preparation
from `closeSteps`. It holds the rest of the formula opaque during each step,
names intermediate values and retains their checked defining facts and
intervals. Specification preparation now tries it for local joined values.
The existing arithmetic solver handles its residual goals.

Trying the complete step *closer* first was rejected: it sped up true branch
claims but ran an expensive failed solver before repeating whole-leaf work
for false claims. Preparing only avoids that speculative closing search.
Global writes keep the original preparation: the step route left a storage
postcondition pending in the broader fixture. The attempt uses 20 million raw
heartbeats, below the existing step closer's 100 million, capped by the
enclosing declaration's remaining allowance. Failed preparation restores
its proof state; consumed heartbeats remain consumed. Sibling goals survive
both successful and failed preparation.

The first integration wrapped the old macro in `first`. Although the 18
small-program browser checks passed, the full Counter offline check exceeded
WASM's call-stack limit. The final routing uses an elaborator at the existing
`sol_spec_prep` dispatch point: an unsupported case falls through to a default
elaborator evaluating the original syntax body, without an enclosing `first`.
There is no macro on this dispatch kind. `sol.spec.stepPrep := false` disables
the new route for a direct old/new control.

The fallback covers failed **preparation**, not a later solver failure.
This is a heuristic change, not a proof of equal automation completeness.
`sol_spec_whole_prep` retains the original preparation for direct use and
comparison. No core semantics, axiom policy or heartbeat limits were weakened.

## Imported audit identity

Upstream `19bf3ba6` replaced the earlier pointer key with module names and
imported constant counts. These can collide when one native process imports
a different artifact with the same module name. A new regression serializes
two tiny checked modules with equal names/counts but different proof
contents. Against the old artifact it reproduces `cached=true, full=false`.

The final memo uses an atomically allocated, process-local `Nat` serial in a
nonpersistent environment extension. Derived environments inherit the serial;
each new import gets a new one. `modifyGet` makes concurrent allocation atomic,
and unbounded naturals cannot wrap. Serial equality is cheap. The memo retains
its import snapshot; generated declarations are still traversed, failed audits
never extend it and missing tokens force a full audit. The test
imports its synthetic axiom only inside restored environments and removes its
temporary files. No persistent axiom or unsafe pointer comparison is added.

An intermediate reference-token design was rejected by this same test. On the
pinned runtime, `lean_st_ref_ptr_eq` compares stored value pointers rather than
reference-cell addresses; two fresh `IO.Ref Unit` values compare equal. Both a
direct two-reference probe and the import collision reproduced this. The final
serial design does not depend on that primitive.

## Final measurements

[Raw evidence](benchmarks/simp-preparation-2026-11-02.json) retains source and
artifact hashes, phase events, the control wrapper, route events, result rows,
profiling counters and offline checks. The standard six-program harness uses
three rounds with distinct source hashes, identically matched to native Lean
and the prior pinned SolKey run. Values below are warm medians of rounds 1–2,
in milliseconds. Browser proof time excludes compiler/editor synchronization;
the separate full column includes it. The SolKey column includes its compiler
and request transport, from the pinned baseline report.

| Program | Browser proof before | Browser proof after | Full browser after | SolKey full |
|---|---:|---:|---:|---:|
| constant | 554 | 558 | 734 | 203 |
| identity | 760 | 756 | 913 | 214 |
| assignment | 1400 | 1466 | 1633 | 170 |
| increment | 2663 | 2283 | 2465 | 277 |
| branch | 4327 | 1803 | 1982 | 299 |
| false-constant | 513 | 465 | 636 | 171 |

The branch proof RPC is 2.4× faster. Compiled native command time for that same
program falls from 2,464 to 1,059 ms. Scalar storage writes retain whole-leaf
preparation; their small timing differences are not an implementation gain.
Cold startup through the first proof remains about 35.0 seconds. This change
does not establish parity: full assignment/increment checks remain roughly
9–10× slower than the pinned SolKey timings. Those still repeatedly normalize
global state projections and dependent values. The next useful target is
selective normalization of storage reads/writes without expanding unrelated
state fields; the direct generic step attempt was not sufficient for them.

The broader native control alternates enabled/disabled preparation in the same
compiled binary over three rounds, with fresh namespaces and identical source.
The final trace contains exactly **9 step / 27 whole** events, as required;
all 36 function results match. Warm medians below exclude the first round.

| Native function | Original preparation | Step route enabled |
|---|---:|---:|
| maximum | 2742 | 1078 |
| falseMaximum | 1992 | 977 |
| storeMaximum | 5289 | 4968 |
| twoChoices | 8712 | 1728 |
| constantOne | 328 | 298 |
| falseConstant | 218 | 212 |

Both false claims stay pending. The global-writing maximum keeps the original
path. These local samples show a large improvement for joined locals; they do
not establish a universal speedup or equal automation completeness.

Final validation passed 18 native compiled checks, the 36 matched controls,
18 fresh browser checks, all 14 offline website regressions and six protocol
checks. The website test includes real Counter proofs, cancellation, stale
result rejection, certified counterexamples, and new proofs after a fully
disconnected restart. The import collision, handler-order, timeout rollback
and sibling controls pass MCP diagnostics. The core layer check finds 194
modules and no elaborator dependency. Heavy jobs ran sequentially under the
12 GiB/no-swap limit and 12 GiB host reserve; the final offline browser run
peaked at 4.23 GiB aggregate RSS.

## Reproduction and validation

Build `Solidity.Frontend.Testing` first. Under the repository's memory and
thread limits, run:

```sh
lake env lean -j1 --tstack=131072 tests/automation/SimpPreparation.lean
lake env lean -j1 --tstack=131072 tests/automation/ProfileSimp.lean
lake env lean -j1 --tstack=131072 -Ddiagnostics=true \
  -Ddiagnostics.threshold=10 tests/automation/ProfileSimp.lean
lake env lean -j1 --tstack=131072 -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=0 \
  -Dtrace.profiler.output=.lake/simp-firefox.json tests/automation/ProfileSimp.lean
```

`ProfileSimp.lean` deliberately runs the original whole-leaf pipeline. Its
`SIMP_PARTS` events separate context construction from simplification itself.
The regression fixture checks maximum, two sequential choices, a storage
write and a constant, plus two false specifications. It also invokes the new
preparation directly, forces a tiny-budget failure and checks rollback and
sibling retention. The Pages workflow runs the result assertions.

Read-only finder/skeptic review caught a missing focus around preparation
and a result assertion that allowed duplicate rows. Both were corrected;
the rollback control also ensures focus is inside the saved bounded state.
Neither review found a remaining trust bypass in the final code. The completeness limit
above is explicit.

The follow-up [generated C inspection](generated-c-performance.md) separates
the native walk from its kernel-checked residue certificate and records the
limited hot-unit optimization comparison.
