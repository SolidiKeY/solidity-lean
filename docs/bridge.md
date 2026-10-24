# Correctness through other Lean libraries

`Bridge/` is a separate Lake package. It imports the core, Mathlib 4.24.0,
CSLib's 4.24-compatible revision, and the documented vendored modules. The
core's `lakefile.toml` still has no dependencies. Nothing in the core imports
the bridge; a consumer pays for these libraries only by choosing the bridge.

Run `./scripts/check-bridge.sh` to check it independently, or
`./run-lean.sh --bridge` for the core, TestSuite, bridge and solkey checks.
Both packages must use the same `lean-toolchain`. The bridge's manifest pins
its dependencies; the external EVM modules have an upstream commit and
verified checksums in `Bridge/vendor/EvmYul/VENDOR.md`.

## October 22 milestone

Implements the concrete correctness directions discussed with Claude on
October 22, while keeping statements at the level actually proved:

| Direction | Checked result | Scope |
|---|---|---|
| Arithmetic against other implementations | `Bridge/SolidityBridge/Arith.lean`: checked add/subtract/multiply return the mathematical result exactly in range at both primitive numeric types; unsigned wrapping add/multiply agree with `BitVec`; unsigned wrapping add/subtract/multiply agree with `ZMod`. | The actual `BinOp.evalT` and `PrimTy.ofInt?`, not detached arithmetic formulas. Narrow source types are elaborator lowerings and are not covered by a blanket all-width theorem. |
| Independent EVM model | `Bridge/SolidityBridge/ExternalEvm.lean`: exact word encodings, numeric stack-step agreement, a CSLib `Simulation` on the projected arithmetic stack LTS, and `upstream_step` against EVMYulLean's actual `execBinOp` transformer. | `ADD`, `SUB`, `MUL`, `DIV`, `MOD`, `AND`, `OR`, `XOR`, arbitrary operand words and numeric stack tails. Upstream stack underflow is checked; its other state is framed. Bytecode dispatch, gas, symbolic slots, jumps, account state and `CALL` remain outside the correspondence. |
| Compiler traces | `Bridge/SolidityBridge/Evm.lean`: successful instruction traces reflect source runs; payment-free successful source runs produce traces; successful termination is equivalent. | The existing compiler's `inFragP`, representation and array-bound hypotheses remain explicit. Calls are included when admitted by that fragment. This reuses core compiler correctness. |
| Weakest preconditions | `Bridge/SolidityBridge/WeakestPre.lean`: predicate transformer as a Mathlib order homomorphism, weakest sufficient precondition, nonempty intersection preservation and guarded duality. | Reads the actual modality and frame execution. Panic is rejected by both modalities; exhaustion is accepted by both. Box of top is panic freedom. Thus arbitrary empty-infimum preservation and unconditional box/diamond duality would be false. |
| Independent loop rules | `Bridge/SolidityBridge/Loop.lean`: invariants from Mathlib's `PFun.fixInduction`; definedness from `WellFounded` or a natural variant; total correctness combining both. | Proved through the bridge's first-return-map correspondence, without invoking the core's loop invariant/variant rules. Terminal errors are outcomes; the chosen postcondition must reject them if successful termination is required. |
| Adversarial reentrancy | `Bridge/SolidityBridge/Adversary.lean`: independently defined yield/resume and contract/callee LTSs; exact outcome correspondence with transfer semantics; `holdsC_iff_all_policies` and `holdsC_iff_all_callees`. | Callback-enabled transfer boundaries, including exit invariant violations and payment halts. A callee has arbitrary control/label types, entry/return relations and an LTS; `CallTr` executes its transitions. Safety covers finite completed traces **assuming invariant-preserving returns**, matching the core: violating returns cannot resume and infinite runs are not completed outcomes. Instantiating a callee with concrete Solidity callback bodies remains a correspondence obligation. |
| First-order compactness | `FO.finite_support` in `Bridge/SolidityBridge/ModelTheory.lean`. | Semantic entailment from `SolTheory` has a finite supporting subtheory. This does not establish calculus completeness or finite support of arbitrary dynamic-logic proofs. |

The bridge already includes the first-order term/formula interpretation,
proof-system soundness, Lindenbaum Boolean algebra, rewriting systems,
fresh names and the original loop/EVM adapters. The milestone repairs their
drift: explicit reflexivity in reduction closures, `grow` cases, local
valuation and ledger namespaces, noncomputable interpretations, and
propositional proof-theory elaboration.

## Review and validation

The root imports `Bridge/SolidityBridge/Checks.lean`: checked/wrapping overflow,
modal panic/exhaustion boundaries, external subtraction order and zero
division/remainder, a context under heap growth, an operational callee with
two internal steps, and pinned axiom audits for eight headline results.
Those audits permit only `propext`, `Classical.choice` and `Quot.sound`.
The separate bridge CI job builds the package and verifies the vendor hashes.

Read-only finder/skeptic review found and confirmed the missing `grow` case
in the formula-context API and the absence of bridge CI. Both are repaired,
with an imported regression for the context. A second pass confirmed the
upstream transformer linkage and operational callee traces; it emphasized
the invariant-preserving-return assumption and the EVM fragment boundaries,
which are stated above. Neither reviewer invoked Lean or edited files.

Final validation: the bridge gate passes (1,523 build jobs, including the
upstream dependency closure, regression module and axiom pins); the core
default targets and the separate TestSuite target pass. Sort annotations
match the frozen SolKey input: 377 taclets, 131 read-bearing annotations.
The default sibling checkout is newer and reports one unannotated
`localValueDelete` read; this milestone does not repin the core to it.
Shell syntax, whitespace, bridge module reachability and new documentation
paths pass. The core orphan check passes when its existing ignored scratch
modules are allowed; the unfiltered check reports 25 scratch modules. The
existing prose-path check reports 13 unrelated missing upstream/vendor
references; none was introduced by this milestone. CI was configured locally
but has not been run on GitHub in this task.

## Bridge-theorems milestones (2026-10-24)

### B0: build and dependency pins

Work starts on `bridge-theorems` from `origin/master` at
`82e75b10b180e72103be3a9e5884d1f44431a9b8`. This base already contains the
separate Bridge package, its pinned manifest, and the opt-in
`./run-lean.sh --bridge` gate. The default run is unchanged.

The reported CSLib URL failure does not reproduce on this base:
`https://github.com/leanprover/cslib` cloned and checked out
`e1fea784d55eae30275c205291f12a1b4868eed3` successfully. There is no local
`Bridge/build.log` in the fresh checkout. The current URL and revision are
therefore retained rather than repinning a working dependency. CSLib,
Mathlib `v4.24.0` (commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`), Bridge,
and the core all pin `leanprover/lean4:v4.24.0`; no toolchain change is needed.
The external EVM vendor checksums and the bridge shell syntax checks pass.

The required `cd Bridge && lake exe cache get` was attempted before the
build, including a retry in the resumed environment. The proxy still denies
`lakecache.blob.core.windows.net` with `CONNECT tunnel failed, response 403`,
even though that hostname appears in the saved environment configuration.
No public cache files were downloaded. The failed retry was stopped and
`cd Bridge && lake build` then passed from source (1,528 jobs), including
the imported regression module and its pinned axiom audits. Cache access is
an optimization, not a logical prerequisite for this build.

The core's default `lake build` passes under the same Lean 4.24.0 toolchain
(453 jobs). Vendor checksums and shell syntax checks pass. Independent
read-only finder and skeptic reviews confirm the installed dependencies
match the pins and that the existing script is opt-in. Retaining these
working pins is preferable to changing them solely to reproduce a stale
URL report.

B0 is complete. No configuration or manifest edit was needed: this base
already contains the working dependency pins and opt-in runner. B0 changes
only this validation record. The earlier October 22 results above describe
the baseline and do not establish the requested all-width/operator coverage.

### B1: primitive arithmetic and refuted universal claims

The package builds with the new imported `Bridge/SolidityBridge/Arith/`
family modules. The existing `Arith.lean` is now an import facade; its old
public theorem names are preserved in `Bridge/SolidityBridge/Arith/Basic.lean`.

The requested **all-width/all-operator milestone is not green**. In
particular its unqualified overflow/panic requirement has counterexamples
below. The positive results have this exact scope:

| File | New checked results | Quantification |
|---|---|---|
| `Bridge/SolidityBridge/Arith/Basic.lean` | The core range check fails exactly when conversion to an unsigned/signed BitVec changes the mathematical integer; core operands constructed from arbitrary library words. | All integers and all 256-bit words. |
| `Bridge/SolidityBridge/Arith/Checked.lean` | Actual `BinOp.evalT` for checked unsigned/signed `+ - *`, signed unary `-`, and unsigned `**`: returns the unbounded result exactly when it equals the corresponding BitVec result, otherwise `none`. | Every core operand; no no-overflow hypothesis. |
| `Bridge/SolidityBridge/Arith/Wrapping.lean` | Adds actual unsigned wrapping subtraction and power agreement with BitVec, and wrapping power with ZMod; baseline covers wrapping addition/multiplication with both libraries and subtraction with ZMod. | Every core unsigned operand and exponent. The helper identities `ofInt_sub`/`ofInt_pow` hold at every natural width; those identities alone are not source-elaboration correctness. |
| `Bridge/SolidityBridge/Arith/Division.lean` | Actual unsigned division/remainder, signed `sdiv`/`srem`; zero divisors return `none`, signed division overflow returns `none` exactly when the integer quotient differs from the word. | All 256-bit words/core operands, including minimum signed value divided by `-1`. |
| `Bridge/SolidityBridge/Arith/Comparison.lean` | All six comparisons, both unsigned and signed, against BitVec comparisons/equality. | All pairs of 256-bit words. |
| `Bridge/SolidityBridge/Arith/Bitwise.lean` | Actual unsigned AND, OR, XOR against BitVec. | All core unsigned operands. |
| `Bridge/SolidityBridge/Arith/Casts.lean` | Actual unsigned-to-signed and signed-to-unsigned conversions against BitVec word interpretation. | All 256-bit words/core signed operands. |
| `Bridge/SolidityBridge/Arith/Modular.lean` | Both actual `ModOp.evalT` builtins `addmod`/`mulmod`, retaining wide intermediates, against ZMod; zero modulus fails. | Every core unsigned operand and modulus. |
| `Bridge/SolidityBridge/Arith/Power.lean`, `Bridge/SolidityBridge/Arith/Shifts.lean` | Kernel-checked counterexamples described below. | Concrete inhabited inputs and actual source runs. |

These evaluator equations return `Option`; they do not relabel `none` as
panic. `TRes.ofOpt` in `Semantics/Run.lean` turns it into revert. The source
counterexamples separately test the actual `Prog.run`, including explicit
`checked` mode. No theorem assumes an impossible range or successful
execution to hide an overflow case.

Remaining requested coverage is explicit: generic signed bitwise operations,
unsigned complement, general unsigned/signed shifts, signed wrapping source
lowerings (including width 256), all narrow-width source operator lowerings,
and casts between distinct widths. The primitive type
`PrimTy` has no width parameter: only `uint256`, `int256`, and `bool`.
The lowerings to audit are `intTyOf`, `checkedNarrow?`, `narrowWrapNode`,
`narrowCapture`, `narrowCheck`, `lowBits`, `signedAt`, and `castCapture` in
`Solidity/Syntax/Elab.lean`; a detached arithmetic model or a projection
into `BitVec w` would not establish their correctness. Signed left shift,
signed complement, and checked signed power are rejected by the primitive
admission table; no agreement theorem is claimed for them.

Read-only finder/skeptic review confirmed the listed positive statements are
nonvacuous and the counterexamples read the actual evaluators/runs. The
skeptic identified missing explicit mention of signed wrapping at width 256;
the coverage list above includes it. This is a findings checkpoint, not a
claim that B1 satisfies the requested completion criterion.

Validation: `cd Bridge && lake build` passes (1,533 jobs), including the
imported new family files, source counterexamples and existing checks.
Every new family file ends with `#print axioms` for its headline results;
the outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.
No heartbeat limit was raised. Four files use `maxRecDepth 2048` to check
the existing 256-bit bound representations and concrete source reductions.

### Discrepancies

1. **Checked power overflow need not panic.** In
   `Bridge/SolidityBridge/Arith/Power.lean`, `checked_pow_reverts` proves that
   `checked { uint x = 2; uint y = 256; uint z = x ** y; }` reverts.
   `checked_narrow_pow_reverts` proves the same for a `uint8` base/result.
   Each has a minimal Lean `example` proving the run is not panic.
   `checked_narrow_pow_panics` checks the boundary: replacing the exponent
   by `8` at `uint8` does panic. The larger power fails the 256-bit
   evaluator before its narrow guard. `Syntax/Checked.lean` explicitly
   excludes full-width power from its checked guards. These are findings,
   not corrected semantics or weakened agreement statements.
2. **Negative signed shift counts differ from word-valued BitVec shifts.**
   In `Bridge/SolidityBridge/Arith/Shifts.lean`, the accepted primitive `int(1) >> int(-1)`
   returns `1`, because the core applies `Int.toNat` to the negative count.
   BitVec's `sshiftRight'` reads the count's word as `2^256-1` and returns
   `0`. The file contains a minimal inequality `example`. Solidity does
   not admit a signed count; the primitive's admission/type representation
   permits this extra case. This is not a claim that a valid Solidity
   program with an unsigned count misexecutes.

### Core changes wanted

- Decide whether explicit `checked` mode must panic on every arithmetic
  overflow. If so, power needs a guard before primitive evaluation,
  including before an overflowing narrow intermediate; merely checking the
  destination afterward cannot repair the demonstrated case.
- Represent the shift count independently from the left operand's type:
  reject signed counts while admitting the unsigned count of a signed
  arithmetic right shift. The current homogeneous `BinOp.evalT` signature
  and `BinOp.accepts` cannot express that distinction.

No core file or root dependency manifest was changed. Missing all-width
proofs above remain Bridge proof work, not an assertion that changing the
core is logically necessary to prove every true correspondence.
