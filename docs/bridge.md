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

## Loom

The adapter uses upstream Loom commit
`78928abc9054b31d0bea85985496490baae95244`, which already pins Lean and
Mathlib 4.24.0. The WP/VC-generator import closure is vendored
under `Bridge/vendor/Loom` (provenance, exclusions, and file hashes in its
`VENDOR.md`). Two CCPO instances receive explicit upstream names so editor
checks agree with the build under the vendored path; no proof body changes.
It needs no toolchain backport, lean-auto, Velvet, or SMT backend.
The bridge gate verifies those hashes. The root dependency manifest and
the `Solidity/` import graph remain independent of Loom.

`Bridge/SolidityBridge/Loom.lean` selects Loom's `MAlgExcept` algebra for
`ExceptT THalt Id`, definitionally the actual `TRes`. A Solidity program is
the Kleisli arrow `fun σ => Prog.runFrames σ P κ`; the contexts may change,
and the runner itself retains the heap-extension evidence until projecting
the returned state. No `StateT` or alternative interpreter is introduced.
`loomWp_iff_afterRunTR` proves Loom's WP equals the core reading, and
`loomWp_eq_wp` identifies the resulting transformer with the existing
bridge WP. `loomWp_bind` is derived from `wp_comp`, without another
operational proof.

| Halt | Box accepts | Diamond accepts |
|---|---|---|
| `revert` | yes | no |
| `revertWith data` | yes | no |
| `diverge` | yes | no |
| `exhausted` | yes | yes |
| `panic` | no | no |

`Modality.onTHalt` alone accepts panic for box; the separate panic exclusion
in `afterRunTR` is part of the selected handler. Loom's base `MAlgOrdered`
does not demand preservation of top or arbitrary infima, so it fits this
policy. There is deliberately no `NoFailure` instance for either modality:
`wp_top` is unavailable (box of top is precisely panic freedom). The
existing nonempty intersection and binary meet laws remain applicable;
empty intersection preservation and unconditional box/diamond duality
are not claimed. Loom's CCPO-based loop rules and partial/total algebra
instances are not supplied for this adapter; Solidity loops use the
existing core loop taclets (including `whileInvariantBox`) and their
existing soundness proofs.

`Bridge/SolidityBridge/LoomRules.lean` defines `Premise.toLoom` once and
proves `Premise.toLoom_sound` once from `Stmt.sound`, `holds_modal`, and
the WP correspondence. It does not inspect statements or premises.
`generator` packages `Fml.Leads`; `stepsGenerator` uses `Fml.Steps.sound`;
`symexGenerator` uses the existing bounded strategy and its certificate.
These are **sufficient preconditions**, in the `Leads` direction. The
strategy's last line is not asserted to be weakest.

At this milestone the strategy post is restricted to `holds · ψ` for
`ψ : Fml C Γ₀`. A `Post C Γ₀` additionally carries the no-fresh-name and
inactive evidence used to step around an opaque post. Loom's actual
`WPGen.get` must accept every Lean predicate, so the fixed-post generator
uses Loom's own `WPGen.spec_triple`: its VC is the last line together with
entailment from the fixed deep post to the requested continuation. At the
same deep post, `generator_get` proves the VC is exactly the last line.
General direct generation for arbitrary Lean posts requires the separately
approved `Fml.pred` change; it has not been made at this milestone.

The read-only finder/skeptic review confirmed that execution and rule
soundness are reused, that all five halt cases agree with `afterRunTR`,
and that the generator's fixed-post restriction and sufficient direction
are stated accurately. The confirmed wording fix describes the existing
core loop taclets generally, rather than implying only box invariants
are supported. The skeptic also verified that the two vendor patches
only make existing instance names explicit; no types or proof bodies change.

Per-file Lean MCP diagnostics pass for both adapter modules and all fifteen
vendored modules. Six imported `#guard_msgs` axiom audits allow only
`propext`, `Classical.choice`, and `Quot.sound`. Building the existing WP
laws exposed a missing `Solidity.Syntax.Splice` import for their `sol[...]`
regression; the bridge import is corrected without changing those laws.
`Bridge/SolidityBridge/Arith/Power.lean` needed the same notation-import fix
for its existing `sol{...}` regressions; no arithmetic statement changes.
The full bridge gate also exposed a missing divergence alternative in
`Bridge/SolidityBridge/Evm.lean`'s existing `compile_trace_complete` proof.
The added case contradicts its successful-run hypothesis; its statement
and compiler correspondence are unchanged.
`Bridge/SolidityBridge/Arith/Lowering.lean`'s `narrowCheck_guard` equation
also omitted the current core's self-frame panic-data branch when overflow
mode is unset. Its right-hand side now includes `panicStmt 17` in that
case, as the existing source does; no hypothesis or execution definition
changes.

Integration with master `c7e634f5` accounts for its new `CallMemo` layer in
`ElabM`: `ctx_run`, `nctx_run`, and the two narrow-check equations return
`pure` in the cache state monad, preserving any incoming cache. The cast
capture and guard proofs quantify that cache and unfold the existing
transformers; no elaborator implementation is copied or changed.

Final validation for phases 0–2: `./scripts/check-bridge.sh` passes
(1,624 jobs), including both vendor hash manifests and the imported axiom
pins; the final log contains no errors. Per-file Lean MCP diagnostics also
pass for the root, `Checks`, both adapters, and all repaired bridge files.
The core source, root dependency manifest, both toolchains, and `AGENTS.md`
are unchanged, so the phase-3-only core checks were not run.

Phase 3 remains gated on explicit user approval. Adding `Fml.pred` gives
every recursion over `Fml` another case; the import-fanout tool reports
453 dependent modules above `Calculus.Fml`, with bridge consumers also
needing rebuilding. `git log -S` searches for predicate/atom/pure
constructors and a typed-state predicate field found no earlier removal
of a comparable constructor for speed in the inspected formula histories.

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

### B1: arithmetic, widths, and exact failure policies

`Bridge/SolidityBridge/Arith.lean` imports the family files below and preserves
the original public theorem names. The numeric bridges cover every admitted
integer operator and every legal Solidity width (8, 16, …, 256). Most width
lemmas are stronger: unsigned `n ≤ 256`, signed `0 < n ≤ 256`.
`unsignedN`/`signedN` embed **every** `BitVec n` value into the actual core
primitive type; no overflow or operation-success assumption excludes inputs.

The unqualified requested milestone is **not all green**: universal panic
behavior and word-valued signed shift counts have the counterexamples in
“Discrepancies”. The true equations and those findings are both retained.

| Files under `Bridge/SolidityBridge/Arith/` | Proved behavior |
|---|---|
| `Bridge/SolidityBridge/Arith/Basic.lean`, `Bridge/SolidityBridge/Arith/Checked.lean` | Actual 256-bit range checks and checked unsigned/signed `+ - *`, signed negation, and unsigned power. Acceptance is exactly equality of the mathematical integer with its decoded BitVec word. |
| `Bridge/SolidityBridge/Arith/Wrapping.lean`, `Bridge/SolidityBridge/Arith/SignedWrapping.lean`, `Bridge/SolidityBridge/Arith/NarrowWrapping.lean` | Unsigned wrapping `+ - * **`; signed wrapping `+ - * **` and negation, including width 256. All-width equations evaluate actual typed primitive/cast/cut compositions. `cutUInt`/`cutInt` are the terms checked from `lowBits`/`signedAt`. Any operand error is preserved. Signed power has an unsigned exponent; exponents retain their full value. Primitive unsigned wrapping operations also agree with ZMod. |
| `Bridge/SolidityBridge/Arith/Division.lean`, `Bridge/SolidityBridge/Arith/NarrowDivision.lean`, `Bridge/SolidityBridge/Arith/SignedDivision.lean` | Unsigned division/remainder and signed truncation-toward-zero division/remainder at every width, with zero failures explicit. The signed remainder reference is `srem`. Checked signed division includes its width predicate; wrapping division proves the narrow quotient/cast and full-width conditional-denominator/modular-sign strategies, including minimum signed value divided by `-1`. |
| `Bridge/SolidityBridge/Arith/Comparison.lean` | All six signed/unsigned comparisons and equality tests on arbitrary words at every width. |
| `Bridge/SolidityBridge/Arith/Bitwise.lean`, `Bridge/SolidityBridge/Arith/NarrowBitwise.lean` | Signed/unsigned AND, OR, XOR at every width; unsigned complement, including the narrow source's `maxN -% x` lowering. Signed proofs use sign extension and establish the returned integer, not merely its low-bit projection. |
| `Bridge/SolidityBridge/Arith/Shifts.lean`, `Bridge/SolidityBridge/Arith/NarrowShifts.lean` | Unsigned left/right shifts at every width and unsigned count, preserving the full count independently of base width. Left shift evaluates the actual width-cut term. Signed arithmetic right shift agrees with `sshiftRight count.toNat` at every width; the stronger word-count claim is refuted below. |
| `Bridge/SolidityBridge/Arith/Casts.lean`, `Bridge/SolidityBridge/Arith/Widths.lean` | Actual word conversions; all target-width unsigned truncation and signed interpretation; signed-to-unsigned, signed-to-signed, and unsigned-to-signed templates; same-sign widening for arbitrary valid source-width words. `lowBits_from_correct`/`signedAt_from_correct` connect the real source checker to evaluation of arbitrary typed operands, preserving their failures. |
| `Bridge/SolidityBridge/Arith/NarrowChecked.lean`, `Bridge/SolidityBridge/Arith/OverflowGuards.lean`, `Bridge/SolidityBridge/Arith/CheckedExecution.lean` | Actual `inTyCond` checker equations and assert/require runners; actual full-width `Checked.rangeU`/`rangeI`/`negRange` guards, including multiplication's protected intermediates. The explicit checking-mode pipeline (core value preguard, primitive, width predicate) panics exactly when `+ - *` or signed negation/division changes the bounded result; zero division reverts. Power's separate equation retains primitive revert before the destination guard. |
| `Bridge/SolidityBridge/Arith/Modular.lean` | Actual `addmod`/`mulmod` against ZMod, with wide intermediates and explicit zero-modulus failure, for every core unsigned operand/modulus, hence every valid narrow operand too. |
| `Bridge/SolidityBridge/Arith/Signature.lean` | Actual `Op1`/`Op2` signature evaluators call the same primitive operators. Signature `Op1.toInt` widens uint to unbounded KeY `kint`; it is distinguished from signed word cast `UnOp.toInt`. |
| `Bridge/SolidityBridge/Arith/Lowering.lean` | Exact source equations for wrapping rewrites, signed division's two strategies, unsigned complement/left shift, negative-literal addition/subtraction, and literal power bases. `castCapture_factor` retains the real checker/fresh capture continuation and their errors; `castCapture_typed` selects identity or conversion. `narrowCheck_guard` identifies the emitted statement, including default require, explicit checking, self-call panic data, and ignoring mode; `narrowCheck_full` proves the full-width no-op. |

`PrimTy` contains uint256/int256/bool; narrow widths are metadata carried by
`intTyOf` and the cast/cut/guard lowerings. `intTyOf_head` demonstrates any
width on an ordinary local. Division and comparisons use genuine width-sized
words, not arbitrary 256-bit states with an assumed width label. Counts and
exponents are never truncated to the base width.

`*_checked_all_widths` in `Bridge/SolidityBridge/Arith/NarrowChecked.lean` composes primitive evaluation
**then** a width check. Primitive `none` becomes revert through `TRes.ofOpt`;
the width-check failure is separate. These equations alone do not describe
explicit `checked` blocks. `*_explicit_checked_all_widths` in
`Bridge/SolidityBridge/Arith/CheckedExecution.lean` adds the actual value preguard first. Its numeric
operands are arbitrary core values embedded as pure typed terms.
`guardedValue_assert_then` connects that prefix to the actual `Stmt.assert`
runner followed by evaluation in its returned state. The
checker/template and source-action equations provide separate compositional
links; this is not a universal correctness theorem for the whole frontend.
In particular signed division's raw source branch and numeric primitive
pipeline are both proved, without claiming one combined theorem for
checking/evaluating that entire raw template.

`narrowWrap_uint`/`narrowWrap_int` describe nonliteral operands; separate
negative-literal and literal-power equations cover those signed
optimizations. Their fit hypotheses are actual source admission checks,
not assumptions that an operation's result fits. `negative_literal_add` and
`negative_literal_sub` prove the optimizations retain the same mathematical
operation. `castCapture_factor` also retains literal fit failures. A
whole-frontend theorem covering every expression, capture, and side effect
is outside these operator bridges.

Signed left shift, signed complement, and checked signed power are rejected
by the primitive admission table. No evaluator is fabricated for those
combinations. The extra homogeneous signed right-shift count is discussed
below.

Read-only finder/skeptic review confirmed nonvacuous width embeddings and
numeric coverage. It identified the need to separate primitive postchecks
from explicit preguards and expose literal source branches; both are now
represented in the proofs and these claims. No heartbeat limit was raised.
Some arithmetic/source modules increase recursion depth for the existing
256-bit representations. Final validation and independent statement/doc
review are recorded below.

### B2: lattice laws and the two wp readings

`Bridge/SolidityBridge/WeakestPreLaws.lean` is imported by the package root.
It uses Mathlib's `Set` predicate lattice (`Monotone`, `⊓`, `⊤`, and order
homomorphisms) on the actual core predicates. There are no termination,
success, panic-freedom, or postcondition-consistency assumptions in the
monotonicity, binary-conjunction, or sequencing laws.

- For the actual modality transformer `Bridge.wp`, `wp_mono`/`wpOrderHom`
  were already present; `wp_inf` and `wp_comp` add binary conjunction and
  sequencing for arbitrary result-valued functions with the exact
  `Modality.afterRunTR` halt policy.
- `stepWp` observes states returned by a core `TStep`. `stepWp_mono` and
  `stepWp_inf` lift the lattice laws; `stepWp_seq` proves composition for
  the real `TRun.seq`, including its heap-extension evidence;
  `stepWp_prog_cons` specializes it to the real program constructor.
- `valid_modal_iff_wp_top` identifies `Fml.Valid` of a framed modality with
  the top precondition; `proves_modal_wp_top` uses `Proves.fmlValid`.
  `proves_spec_box_wp_top` separately uses `Proves.valid` at its actual
  `Spec.box`/`Spec.toFml` types.
- The closer's helper `Modality.wp` in `Solidity/Calculus/CloseLemmas.lean`
  is a different reading: it treats every error as `onHalt`. `rawWp`
  embeds exactly that helper into the same lattice. `rawWp_mono`,
  `rawWpOrderHom`, `rawWp_inf`, `rawWp_box_top`, and `rawWp_comp` prove its
  four requested laws, with top preservation stated for box.
- `wp_eq_rawWp` proves the precise relation between the readings for
  arbitrary runs: actual wp is `(raw wp OR exhaustion) AND not panic`.
  The helper's top law therefore cannot establish top preservation for
  the actual box.

The requested **unconditional top-preservation law for the actual box is
false**, so B2 is not fully green as requested. `wp_box_top_iff` classifies
the exact obstruction, without replacing the original statement by a
restricted one. `assert_false_box_not_valid` and a minimal Lean `example`
refute `[assert(false)] true`; another `example` refutes top preservation
on the inhabited `Unit` state type. No postcondition or impossible input
hypothesis makes those counterexamples disappear.

B3 is not started: its explicit B0–B2-green prerequisite is not met.
Optional B4 is not attempted. The existing compiler and loop adapters
remain the baseline results described above.

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

3. **Actual box does not preserve top.** `assert(false)` panics; the
   actual box rejects panic even when its postcondition is true. This
   agrees with the core's documented partial-correctness policy. The
   simpler closer wp helper does preserve top under box, but differs on
   both panic and exhaustion. The B2 file checks both readings explicitly.

### Core changes wanted

- Decide whether explicit `checked` mode must panic on every arithmetic
  overflow. If so, power needs a guard before primitive evaluation,
  including before an overflowing narrow intermediate; merely checking the
  destination afterward cannot repair the demonstrated case.
- Represent the shift count independently from the left operand's type:
  reject signed counts while admitting the unsigned count of a signed
  arithmetic right shift. The current homogeneous `BinOp.evalT` signature
  and `BinOp.accepts` cannot express that distinction.

- Preserve or explicitly reconsider the deliberate panic-rejecting box
  policy before requesting its unconditional top-preservation law. The
  bridge does not propose silently changing that policy to force a lattice
  theorem. The closer helper and actual modality should continue to be
  distinguished in any public wp API.

No core file or root dependency manifest was changed. The discrepancies
are findings; no numeric statement was weakened to conceal them.

### Final bridge-theorems validation

`./run-lean.sh --bridge` passes under Lean 4.24.0: the core default targets,
the separate TestSuite target, the Bridge build (1,547 jobs), vendor hashes,
and the frozen SolKey check (377 taclets, 131 read-bearing annotations).
All 179 printed Bridge axiom audits, including 162 arithmetic audits,
contain only `propext`, `Classical.choice`, and `Quot.sound`. Arithmetic
source checks find no `sorry`, new axiom/opaque declaration, unrestricted
simp, untyped `have`, or heartbeat-limit change. New arithmetic modules
build without warnings. Whitespace and changed-path scope checks pass;
the root still has zero dependency declarations and no core source diff.

Independent read-only finder/skeptic passes confirm the arithmetic operand
domains, multiplication guard protection, source-link boundaries, and the
wp/validity statements. The final separate reviewer found no actionable theorem/doc mismatch or
vacuous hypothesis and confirmed real numeric coverage of every legal width
and admitted operator family. It confirmed the stated frontend boundaries
and that the refuted laws keep B3 gated. The prose-path script still reports
13 pre-existing missing upstream/vendor references; no reference in this
updated document is missing. No unrelated path or core file was changed.
