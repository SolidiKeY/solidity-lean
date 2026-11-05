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

The root imports `Bridge/SolidityBridge/Checks.lean` (regressions and pinned
axiom audits: only `propext`, `Classical.choice`, `Quot.sound`). The
Plausible rule checker (`lake exe rulecheck`,
`Bridge/SolidityBridge/PropertyChecks.lean`) is described in
[rule-repair.md](rule-repair.md); it runs a fixed-seed corpus on a fresh
build, rejects a deliberate bad assignment, and no test result is installed
as a theorem.

## Loom

The adapter uses upstream Loom commit
`78928abc9054b31d0bea85985496490baae95244`, which already pins Lean and
Mathlib 4.24.0. The WP/VC-generator import closure is vendored
under `Bridge/vendor/Loom` (provenance, exclusions, and file hashes in its
`VENDOR.md`). Two CCPO instances receive explicit upstream names so editor
checks agree with the build under the vendored path; no proof body changes.
The adapter needs no toolchain backport, lean-auto, Velvet, or SMT backend;
Velvet, vendored beside it ("Velvet" below), adds lean-auto to Bridge.
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

The strategy post is restricted to `holds · ψ` for
`ψ : Fml C Γ₀`. A `Post C Γ₀` additionally carries the no-fresh-name and
inactive evidence used to step around an opaque post. Loom's actual
`WPGen.get` must accept every Lean predicate, so the fixed-post generator
uses Loom's own `WPGen.spec_triple`: its VC is the last line together with
entailment from the fixed deep post to the requested continuation. At the
same deep post, `generator_get` proves the VC is exactly the last line.
`Bridge/SolidityBridge/LoomVCGen.lean` supplies `runWithPost` and one
`@[loomSpec]` generator for all programs. The annotation exposes the deep
post and VC budget to Loom's specification lookup; its execution is
definitionally `Prog.runFrames`. `runWithPost_wp` also identifies its WP
with the existing bridge WP. The budget bounds symbolic execution only:
exhausting it leaves a modal obligation, without changing program execution.
Loom's `mwp` combines this generator with its own bind, pure and conditional
generators. `runWithPostGenerator_get` exposes the core strategy leaf and
the explicit continuation entailment.

Direct automatic generation against an uninterpreted Lean parameter
`Q : State C Γ₀ → Prop`, without a deep post or an entailment proof, is
outside this interface. Existing taclets transform `Fml`, which cannot
contain that parameter. Users instead choose an existing deep `ψ` and
prove `∀ τ, holds τ ψ → Q τ` when composing the Solidity step. Ordinary
Lean continuations may use arbitrary predicates; this obligation records
exactly what the fixed Solidity specification supplies. The core formula
language is retained without an opaque predicate constructor.

`Bridge/SolidityBridge/LoomExamples.lean` (imported by the root and the
regression module) exercises the real VCG rather than calling the bridge
soundness theorem directly:

| Example | Checked behavior |
|---|---|
| `straight_via_loom` | `mwp` selects the registered Solidity generator; `sol_decide` closes its core strategy leaf. A `#wp` output pin and `straight_vc_is_wp_leaf` identify that leaf exactly. |
| `mixed_via_loom` | An ordinary Lean bind, a Solidity `seven()` call, and a Lean conditional compose through Loom's bind/pure/if generators. The deep post `x = 7` supplies the fact needed to prove the Lean result is `8`. `mixed_returns` also checks actual successful execution at the initial state, excluding a vacuous box specification. |
| `panic_rejected`, `revert_accepted` | The actual `assert(false)` is rejected with a true deep post; the actual revert is accepted even with a false deep post. |
| `invariant_via_loom` | The counting loop uses its core invariant taclet, pinned by `#step` as `whileInvariantBox`. Its generated quantified leaf is normalized and closed by `sol_close`; no Loom loop rule is applied to Solidity code. This is box partial correctness, not a termination claim. |

## Velvet

Velvet, the Dafny-style verifier built on Loom, is vendored beside it under
`Bridge/vendor/CaseStudies` (provenance, the files kept and checksums in
`Bridge/vendor/CaseStudies/VENDOR.md`). It is the Loom-based Velvet of Loom's
commit `2c7dbe71`, on Lean and Mathlib 4.24, like the rest of Bridge; the
current Velvet (<https://github.com/verse-lab/velvet>) moved to Lean 4.35 and
Lean's own VC generator and does not build on this toolchain. Velvet needs
seven more Loom modules (`Bridge/vendor/Loom/VENDOR.md`) and, for
`Loom.SMT`, lean-auto, which `Bridge/lakefile.toml` requires at Loom's
manifest revision. The z3/cvc5 binaries Loom's Lake file downloads are not
fetched: `loom_solve` runs its default solver, `grind`, and the four
upstream examples kept are the ones that close with it.

Three libraries are default targets of Bridge: `Velvet` (the front end:
`method`, `prove_correct`, `loom_solve`), `VelvetExamples` (four of
upstream's examples) and `SolidityVelvet` (`Bridge/SolidityVelvet.lean`).
The last writes its examples as Solidity, not as Velvet's `do` notation:
`contract C { … }` (`Bridge/SolidityVelvet/Contract.lean`) reads a whole
contract, its storage and its functions with their `ensures` and loop
`invariant`s, and states each function as the Velvet method `C.f`, which
`prove_correct C.f by loom_solve` proves. A function takes the storage it
mentions (as `mut` parameters when it writes them), then `msg.sender`, then
its arguments; `uint` is `Nat`, a `mapping` a `Mapping` (unwritten keys read
zero, `@[grind =]` on its read-over-write), and Solidity's reverts (a
`require`, overflow and underflow, an index past the length, a division by
zero) are Loom `assume`s, so an `ensures` speaks of the calls that do not
revert. `Bridge/SolidityVelvet/TestSuite.lean` is solkey's `TestSuite.sol` read
this way: 83 of its functions, under their names, in one contract, each
stating with `assert` what holds after the feature it tests, all proved by
`prove_contract TestSuite by loom_solve`; those that need structs, aliases,
memory, calls, `break`/`continue` or effects inside expressions are left
out. The other contracts are three Solidity programs of the core (the counting
loop of `LoomExamples`, a scan for the largest balance, ERC20's `transfer`),
a bank (`Bridge/SolidityVelvet/Bank.lean`), an ERC20 token's `mint`,
`transfer`, `approve` and `transferFrom` (`Bridge/SolidityVelvet/Token.lean`)
and loops over storage arrays with their invariants
(`Bridge/SolidityVelvet/Loops.lean`). They are Lean programs and are not
related to `Stmt.run`; the theorems about Solidity's own semantics are the
Loom adapter's above. `SolidityVelvet` imports Velvet alone and nothing
imports it, so Velvet's keywords (`method`, `require`, `ensures`,
`invariant`), the contract grammar's (`contract`, `function`, `mapping`) and
Velvet's global `grind` attributes do not reach `SolidityBridge`.

To build only Velvet, from `Bridge/`:

```sh
lake exe cache get
lake build Velvet VelvetExamples SolidityVelvet
```

These examples are also on the examples site (`docs/site.md`).

## Results by file

| Direction | Checked result | Scope |
|---|---|---|
| Arithmetic against other implementations | `Bridge/SolidityBridge/Arith.lean`: checked add/subtract/multiply return the mathematical result exactly in range at both primitive numeric types; unsigned wrapping add/multiply agree with `BitVec`; unsigned wrapping add/subtract/multiply agree with `ZMod`. | The actual `BinOp.evalT` and `PrimTy.ofInt?`, not detached arithmetic formulas. Narrow source types are elaborator lowerings and are not covered by a blanket all-width theorem. |
| Independent EVM model | `Bridge/SolidityBridge/ExternalEvm.lean`: exact word encodings, numeric stack-step agreement, a CSLib `Simulation` on the projected arithmetic stack LTS, and `upstream_step` against EVMYulLean's actual `execBinOp` transformer. | `ADD`, `SUB`, `MUL`, `DIV`, `MOD`, `AND`, `OR`, `XOR`, arbitrary operand words and numeric stack tails. Upstream stack underflow is checked; its other state is framed. Bytecode dispatch, gas, symbolic slots, jumps, account state and `CALL` remain outside the correspondence. |
| Bounded EVM byte memory | `Bridge/SolidityBridge/ExternalEvm/MemoryRefinement.lean` and `Bridge/SolidityBridge/ExternalEvm/MemoryComposition.lean`: persistent word-cell/32-byte correspondence through actual core instructions and upstream macros. | All four load/store forms on preallocated numeric cells; aligned in-bounds windows, nonwrapping extent and the explicit unproved `PaddingCorrect` contract. No raw-memory Solidity admission or gas/bytecode claim. |
| Compiler traces | `Bridge/SolidityBridge/Evm.lean`: successful instruction traces reflect source runs; payment-free successful source runs produce traces; successful termination is equivalent. | The existing compiler's `inFragP`, representation and array-bound hypotheses remain explicit. Calls are included when admitted by that fragment. This reuses core compiler correctness. |
| Weakest preconditions | `Bridge/SolidityBridge/WeakestPre.lean`: predicate transformer as a Mathlib order homomorphism, weakest sufficient precondition, nonempty intersection preservation and guarded duality. | Reads the actual modality and frame execution. Panic is rejected by both modalities; exhaustion is accepted by both. Box of top is panic freedom. Thus arbitrary empty-infimum preservation and unconditional box/diamond duality would be false. |
| Independent loop rules | `Bridge/SolidityBridge/Loop.lean`: invariants from Mathlib's `PFun.fixInduction`; definedness from `WellFounded` or a natural variant; total correctness combining both. | Proved through the bridge's first-return-map correspondence, without invoking the core's loop invariant/variant rules. Terminal errors are outcomes; the chosen postcondition must reject them if successful termination is required. |
| Adversarial reentrancy | `Bridge/SolidityBridge/Adversary.lean`: independently defined yield/resume and contract/callee LTSs; exact outcome correspondence with transfer semantics; `holdsC_iff_all_policies` and `holdsC_iff_all_callees`. | Callback-enabled transfer boundaries, including exit invariant violations and payment halts. A callee has arbitrary control/label types, entry/return relations and an LTS; `CallTr` executes its transitions. Safety covers finite completed traces **assuming invariant-preserving returns**, matching the core: violating returns cannot resume and infinite runs are not completed outcomes. Instantiating a callee with concrete Solidity callback bodies remains a correspondence obligation. |
| First-order compactness | `FO.finite_support` in `Bridge/SolidityBridge/ModelTheory.lean`. | Semantic entailment from `SolTheory` has a finite supporting subtheory. This does not establish calculus completeness or finite support of arbitrary dynamic-logic proofs. |


### Arithmetic at every width (`Arith/`)

`Bridge/SolidityBridge/Arith.lean` imports the family files below. The
numeric bridges cover every admitted integer operator and every legal
Solidity width (8, 16, …, 256); `unsignedN`/`signedN` embed **every**
`BitVec n` value into the core primitive type, with no overflow or
success assumption. Two universal claims are false (see "Discrepancies").

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

The generic synthesis/checking helpers in `Arith/Widths.lean` require
`p = .int → op ≠ .shr`: signed right shift takes its count from an unsigned
operand. `Bridge/SolidityBridge/Arith/WidthsSignedShift.lean` proves that separate source-checking path;
`Bridge/SolidityBridge/Arith/WidthsObstructions.lean` retains kernel-checked counterexamples to the old
generic statement. `Bridge/SolidityBridge/Arith/WidthsSyntax.lean` supplies structural checker facts
without depending on generated equation numbers.

`narrowCheck_guard` retains panic data when either `selfFrame` or
`retainFailureData` is set. `Bridge/SolidityBridge/Arith/LoweringObstructions.lean` refutes the earlier
statement that tested only `selfFrame`; `Bridge/SolidityBridge/Arith/GuardRetentionExamples.lean`
checks all flag combinations in default, checking and ignoring modes. These
repairs change Bridge statements and proofs, preserving source execution,
the concrete width results and proof resource limits.

The shared arithmetic repair (2026-10-29) passed the complete optional Bridge
build, its pinned axiom checks and the rule checker (seed 42, 1,000 samples
per case), with explicit `-j1` under a 12 GiB/no-swap scope. Per-file Lean MCP
diagnostics, trust, import-layer and orphan checks passed. Independent
read-only finder and skeptic reviews found no confirmed defects. The prose
path check adds no missing reference; its 46 pre-existing failures are outside
this change. The separate `Derived17` performance repair is still pending.

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

### Lattice laws and the two wp readings (`WeakestPreLaws.lean`)

Mathlib's `Set` predicate lattice on the actual core predicates, with no
termination, success, panic-freedom or consistency assumptions:

- For the actual modality transformer `Bridge.wp`, `wp_mono`/`wpOrderHom`,
  `wp_inf` and `wp_comp`: monotonicity, binary conjunction and
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
  four laws, with top preservation stated for box.
- `wp_eq_rawWp` proves the precise relation between the readings for
  arbitrary runs: actual wp is `(raw wp OR exhaustion) AND not panic`.
  The helper's top law therefore cannot establish top preservation for
  the actual box.

The **unconditional top-preservation law for the actual box is false**:
`wp_box_top_iff` classifies the obstruction, and `assert_false_box_not_valid`
refutes `[assert(false)] true`.

### Independent checks

- `Bridge/SolidityBridge/ExternalEvm/Environment.lean` relates SELFBALANCE
  to EvmYul's actual account-map lookup and its `stateOp` transformer,
  including absent accounts. ADDRESS, CALLER, CALLVALUE and TIMESTAMP
  agree on shared observations as well. `referenceMachine_agrees` gives a
  representing machine for every upstream state, so the relation does not
  assume zero balances or equal caller/executing addresses. Each opcode
  theorem also preserves that shared-state relation after execution. This extends
  the eight existing binary-word comparisons; it does not establish every
  instruction, gas, byte memory, account-changing CALL or bytecode dispatch.
- `Bridge/SolidityBridge/CompilerSimulation.lean` supplies CSLib
  `IsBisimulation`, `Simulation` and `TraceEq` for successful program
  boundaries. Each target transition contains an actual instruction trace
  in `Evm.lts`; labels retain the typed source program. Traces compose over
  any number of admitted, payment-free programs, including inlined calls.
  Fragment admission and local-space bounds remain explicit. Instruction
  labels are grouped into those boundary transitions; failure and divergence
  are outside this successful-execution LTS. The existing trace-completeness
  proof now handles the core theorem's divergence alternative explicitly.
- `Bridge/SolidityBridge/LoopFixpoint.lean` identifies `OrderHom.lfp` of
  the one-iteration outcome transformer with Mathlib's `PFun.fix` outcomes.
  Well-founded induction gives total correctness with decreases required
  only on invariant states. The postcondition chooses whether terminal
  errors are acceptable. This argument invokes no core loop rule.
- `Bridge/SolidityBridge/AdversaryPolicy.lean` proves that each fixed
  operational callee has exactly the completed outcomes of its reachable
  return policy. Internal callee labels are retained when lifting traces.
  This strengthens the existing theorem quantifying over all callees;
  returns must still preserve the assumed invariant, and infinite callee
  runs are not completed outcomes.
- `FO.finite_storage_support` in `Bridge/SolidityBridge/ModelTheory.lean`
  applies compactness to the contract theory together with supplied
  first-order storage facts. It extracts a finite subset of the supplied
  facts while leaving the contract theory available in full. This is
  semantic entailment, without a calculus-completeness claim.

### Model theory and callback traces

`Bridge/SolidityBridge/ModelTheory/LowenheimSkolem.lean` adds:

- `FO.solTheory_compact`: `SolTheory C ∪ facts` is satisfiable exactly when
  every finite subset of `facts` is satisfiable together with the whole theory.
- `FO.solTheory_models_of_card`: a model at every infinite cardinal at least
  the language cardinal. The proof supplies the concrete state's infinite
  logical-integer carrier, rather than assuming an infinite model exists.
- `FO.solTheory_elementary_submodel`: downward Löwenheim–Skolem with explicit
  language, parameter-set and ambient-model cardinal bounds, retaining the
  parameters and every contract axiom.
- `FO.holds_iff_submodel_realize`: an elementary submodel of a concrete state
  preserves each translated closed first-order leaf, including leaves that
  are not valid in every state.

The cardinality results concern abstract first-order models. They assert
neither that these models are concrete Solidity states nor that the entire
Solidity signature is countable.

`Bridge/SolidityBridge/CallbackTrace.lean` labels completed outcomes with the
full returned state. `holdsC_iff_weakObservable_traces` identifies the transfer
callback modality with safety on every callee's observable traces. CSLib
saturation treats internal computation as silent:
`weakTraceEq_callSafe` and `weakBisim_callSafe` preserve every postcondition,
even when callees perform different amounts of internal work.
`holdsC_iff_weakTraceEquivalent_callee` permits replacing the universal callee
by an implementation with the same weak traces. Strong trace/bisimulation
versions are provided too; those count internal transitions.

`Bridge/SolidityBridge/CallbackModalTrace.lean` supplies `holdsC_iff_traceSafe`,
`traceEq_holdsC` and `bisim_holdsC` for every program, frame stack and modality.
Its LTS reuses `ExecP` and `ExecF`: it is an adapter establishing CSLib
invariance, rather than an independent implementation of callback execution.
The separate operational callee correspondence concerns one transfer boundary.
Both results cover finite completed outcomes under invariant-preserving
returns; even diamond safety does not assert termination of an arbitrary callee.

### Independent EVM opcodes (`ExternalEvm/`)

The vendor holds the import closure of the pinned upstream primitive and
full EVM dispatchers, with two Lean 4.24 compatibility patches (a `UInt256`
annotation, JSON); original and patched checksums are in its `VENDOR.md`.

`Bridge/SolidityBridge/ExternalEvm/Dispatch.lean` connects the core's actual
instruction steps to `EvmYul.EVM.step` on all numeric represented stacks for
18 binary and two unary word operators, the five account/transaction
observations, numeric PUSH and POP. The binary/unary/POP correspondences
include stack underflow. `Bridge/SolidityBridge/ExternalEvm/StackOps.lean`
compares legal DUP1–DUP16 and SWAP1–SWAP16 with explicit stack-depth premises.
Signed division/remainder and exponentiation are proved against the upstream
implementations, including exponentiation by squaring, zero divisors, and
signed-minimum division by minus one.

These are projected opcode proofs. The shared relation observes the numeric
stack and account/transaction fields, balances modulo `2^256`, and 160-bit
account addresses. It does not equate memory, storage, PC, code, exact
unbounded balances or gas. The dispatcher is supplied its opcode/immediate
with positive evaluator fuel and zero charged gas; instruction fetching and
the gas/stack-limit/static-mode checks in the upstream `X` driver are not
verified by these theorems.

The full instruction correspondence is **not complete**. Status and remaining boundaries:

| Core instructions | Status or remaining obligation |
|---|---|
| `keccakMap`, `keccakArr`, `sload`, `sstore` | Bounded finite-observation macro refinement below, under explicit setup and alias assumptions. Unrestricted layout remains excluded. |
| `mload`, `mstore`, `mloadAt`, `mstoreAt` | [Bounded preallocated refinement](#bounded-memory-refinement-compiler10-2026-10-29) is proved under the explicit padding contract. Discharging that external contract, memory growth, instruction fetching and gas/bytecode equivalence remain outside the result. |
| `jump`, `jumpi`, `loop` | General fetched-run simulation and automatic recursive certificates for accepted layouts; certified scanner destinations and charged X continuation refinement with explicit readiness/terminal gates. See below. |
| `call` | Seven-operand ABI, account/code execution, address truncation, balance bounds and callee behavior corresponding to `accepts`. |
| `revert` | Return-data operands and the driver's halting relation. |

#### Bounded memory refinement (compiler10, 2026-10-29)

`Bridge/SolidityBridge/ExternalEvm/Memory.lean` supplies actual
`EvmYul.EVM.step` MLOAD/MSTORE equations, fixed-cell PUSH32 macros, and
stack-cell PUSH32(32)/MUL macros. The runner supplies opcodes with positive
fuel and zero charged gas. Returned states retain the actual PC,
execution-length, gas preparation and active-memory updates; this is not an
instruction-fetching or gas-checking driver theorem. Existing same-stack
counterexamples in `Obstructions` are unchanged.

`Bridge/SolidityBridge/ExternalEvm/MemoryBytes.lean` proves a pure 32-byte
big-endian `encoding`, its exact length and decoder roundtrip. `serialize_eq`
connects the actual upstream `UInt256.toByteArray` to this encoding under the
explicit named hypothesis `PaddingCorrect bound`, with `32 ≤ bound`.
The hypothesis specifies only the opaque zero allocator, not serialization,
reads, writes, simulation or their desired conclusions. No new axiom is
installed and **no inhabitant of this external contract is claimed**.

The trust boundary is concrete. Upstream `ffi.ByteArray.zeroes` has no stated
source body or correctness specification and names the native `memset_zero`
implementation. Inspection of the actual Lean declaration reports no axioms;
its elaborator-generated opaque value is `fun n => default`, not a checked
zero-padding implementation. Native allocator correctness is therefore an
external representation assumption, not established by an axiom audit or by
sampled execution. These theorems do not verify or replace that primitive.

`write_inbounds` normalizes the actual `ByteArray.write` definition.
`write_size`, `write_get_same`, `write_get_frame`, `read_inbounds`, `readback`
and `write_readback` derive size, exact written bytes, padded-read reduction,
readback and the frame on every existing byte outside `[a,a+32)`. They require
a full 32-byte source and `a+32 ≤ dest.size`; only the length-zero allocator
contract is needed for these in-bounds byte operations. They do not assume
readback or frame conclusions. No write-growth or partially allocated read is
covered. Source arrays are immutable mathematical byte arrays, so the laws do
not assume a mutable buffer aliasing implementation.

`Bridge/SolidityBridge/ExternalEvm/MemoryRefinement.lean` defines the persistent
`Represents cells m s` relation independently of upstream reads: physical size
is `32*cells`, `activeWords.toNat = cells`, and every cell below capacity is a
numeric core word with all 32 physical bytes equal to its pure encoding.
`Bounded cells` requires `32*cells < 2^256` and `< 2^64`. Thus cell scaling and
`activeWords*32` do not wrap, and the accessed windows fit before the upstream
`USize` conversions. Serialization padding lengths are at most 32 (also valid
on a 32-bit platform). Symbolic words, cells outside capacity and memory
expansion remain outside this relation.

`load_state_frame` proves the actual upstream load leaves the full memory-machine
state unchanged within capacity. `store_lookup_same` and `store_lookup_other`
state actual upstream readback and distinct-cell read framing directly for
arbitrary represented memory and every numeric word. These are derived from
the persistent relation, not assumed read equations.

`lookup_represents` derives actual upstream read agreement from these bytes;
it does not assume `ReadAgrees`. `load_preserves` and `store_preserves` prove
the persistent postrelation for the actual upstream memory transformers.
`load_refines`, `store_refines`, `loadAt_refines` and `storeAt_refines` relate
the actual core steps to the actual upstream macros, with equal numeric
stacks **and the whole persistent postrelation**. Every access requires its
word-cell index below capacity. Distinct aligned cells have disjoint windows;
the store proof uses the written-byte law at its cell and the physical-byte
frame at every other cell. Loads read before expanding active memory; the
preallocated active capacity makes that update stable.

`control_represents` proves an inhabited two-cell input independently of the
FFI hypothesis. Fixed/dynamic controls cover either valid boundary and all
numeric stored values. `roundtrip_control` proves actual upstream store/load
readback and the other-cell zero frame; `fixed_roundtrip` composes actual core
store/load steps and actual macros, deriving the load from the store's proved
postrelation and an exact final one-word stack. These evaluator claims remain
conditional on the explicit allocator contract. The contract itself is not
claimed inhabited. Under the same allocator contract, the new actual unaligned-store counterexample shows a
store of one at byte 1 changes byte 32 of the next cell. Existing underflow,
address-wrap, active-extent-wrap and same-stack obstructions remain; the
access premise excludes the first out-of-capacity index; this is not an executable
refusal. `capacity_load_counterexample` separately proves that an actual load
at that index expands activeWords to 3 with physical size still 64, losing
the original two-cell relation, independently of the FFI contract.

The separate native regression `scripts/check-external-memory.sh` compiles only
the verbatim `memset_zero` function from already-pinned EVMYulLean commit
`047f63070309f436b66c61e276ab3b6d1169265a`, plus the ABI wrapper generated by
the unchanged vendored FFI declaration and pinned Lean compiler.
`Bridge/tests/memory-zeroes.provenance.json` records the full upstream source
hash and verbatim function-body hash; the script verifies the copied fixture's
checksum. It loads the memory symbol into Lean's interpreter and runs
`Bridge/tests/MemoryObserve.lean`: 28 actual core/upstream fixed/dynamic
store-load pairs, at cells 0 and 1, with values 0, 1, 255, 256, `2^248`, `2^255`
and `2^256-1`. It checks numeric stacks, physical encoding, size, active extent,
other-cell read frame, 33 zero-allocator samples and six boundary/error
observations. No hashing libraries are linked. These are runtime observations,
not kernel proof of the allocator contract, a Solidity source-admission test,
or gas/bytecode equivalence. No reference Lean definition is replaced. The final native run passed in
5 seconds at 275,124,224 bytes peak aggregate cgroup memory, with no OOM.
The active-wrap observation starts from the nonzero unaligned-write state,
so its expected zero is discriminating.

All 20 new guarded headline axiom audits report only `propext`,
`Classical.choice` and `Quot.sound`; the original eleven remain. Focused byte
checking passed in 4 seconds at 297,611,264 bytes peak aggregate cgroup memory;
focused refinement checking passed in 12 seconds at 318,484,480 bytes. A
projection-normalization repair resolved the initial store proof's default
heartbeat stop without changing budgets or claims. Independent read-only finder/skeptic reviews found no remaining proof defect.
Their confirmed capacity-wording issue and nondiscriminating native active-wrap
control were corrected; neither reviewer used a Lean server. New/existing
ExternalEvm targets and the 36-case × 1,000-sample rule checker passed.
Orphan/layer/strict automatic/trust gates and the trust regression passed.
TestSuite's complete 564-row check passed with the repository's existing pinned
snapshot (552 derived, 11 refuted, one excluded, zero pending; two skip).
The incomplete setup snapshot first failed for a missing sibling pin file;
no pin or source was changed to repair it. Before the master refresh, documentation paths failed
with the same 20 missing references as the initial baseline, not new memory-reference failures.
After refreshing only the task branch from published master `127c2ee5`, the
cold `timeout --signal=TERM --kill-after=15s 7200 bash ./run-lean.sh` reached
its aggregate 7,200-second limit after 699/703 default jobs. That attempt is
**BLOCKED**, not passed. There was no theorem error or OOM. The same serialized
group's optional umbrella failed in `Arith/Widths.lean` at lines 21, 47, 79,
111 and 501 (438 seconds); all new/existing ExternalEvm targets, native memory
observations and the rule checker passed. The group took 7,659 seconds, peaked
at its hard 12 GiB cap, and recorded 51 cgroup limit events but zero OOM events.

The concrete repair for the cold aggregate timeout was to build the remaining
`Solidity.Examples.DecisionMemory` and `Solidity.Examples.DecisionKInt` targets
separately using the retained cache (84 seconds), then rerun the **unchanged**
7,200-second full command. It passed in 1,104 seconds: 703 default jobs, all
262 TestSuite jobs and the actual SolKey annotation check, with no skip.
The 28 explicit axiom audits present at that milestone passed in 5 seconds;
three direct read/frame laws were then added and individually kernel-checked.
The successful staged group took 1,193 seconds at 11,587,039,232 bytes peak
aggregate cgroup memory, with no limit or OOM events. No statement, expected
observation, proof/search budget or timeout was changed to obtain these passes. The final
optional-memory check then passed the affected targets (12 seconds), all 31
explicit axiom audits (5 seconds), native observations (4 seconds), complete
TestSuite/static gates and diff check. Its only failing check was the historical
documentation-path gate. That group took 29 seconds at 353,624,064 bytes peak
aggregate memory, with no limit or OOM events. Final independent finder/skeptic
reviews found no remaining proof obligation within this explicitly conditional,
preallocated fragment; the conflicting present-tense documentation-debt count
was corrected.

A subsequent whole-scope review identified a weakness in the controls: the
original zero-filled neighbor could not detect accidental zeroing, and the
explicit composed witness covered only fixed store/fixed load.
`Bridge/SolidityBridge/ExternalEvm/MemoryComposition.lean` now provides a pure,
allocator-independent two-cell initializer for arbitrary words and proves all
four fixed/dynamic store/load compositions against the actual core runner and
upstream evaluator runner. Dynamic source reads include an actual index PUSH;
no stack is injected between the store and load. The theorem retains the
persistent byte relation, exact value and arbitrary stack tail, and the other
cell's specified original value. The allocator hypothesis remains explicit and
unproved; neither the populated initializer nor native execution proves it.
Eight additional native cases use distinct nonzero initial cells, zero and
maximum-word writes, and the sentinel tail `[7, 9]`, checking the neighbor's
bytes as well as its read. All original controls and expected values remain.
The new module checked in 5 seconds at 360,980,480 bytes peak; the native group
passed in 10 seconds at 488,419,328 bytes, with 12 GiB/no-swap limits and no
limit or OOM events. Five new guarded audits report only `propext`,
`Classical.choice` and `Quot.sound`, bringing the explicit audit total to 36.

The populated-composition final group passed affected targets, all 36 explicit
axiom audits, native controls, complete TestSuite/static checks, orphan/layer,
strict automatic and trust gates. It took 19 seconds at 279,638,016 bytes peak,
with no memory-limit or OOM events. Its documentation-path check remains red
with exactly the previous finding set (46 missing, 16 ambiguous). Independent
read-only finder and skeptic reviews confirmed the two control gaps above are
repaired and found no further independent obligation within this bounded
conditional memory fragment. Neither used a Lean server. At that checkpoint, published master
`cc155f36` had no relevant Bridge, source-syntax or core-run changes relative
to the validation base; the shared Widths prerequisite was still unpublished.

At the earlier published base `127c2ee5`, the documentation checker failed
with 46 missing and 16 ambiguous references. A read-only reconstruction of
that exact base yielded the identical finding set, with no task-introduced
findings. The earlier 20-missing result belongs to the pre-refresh base and
remains recorded in its logs.

The earlier checkpoint `200153d3` and every subsequent export are retained.
Their failed Widths gates and cold aggregate timeouts remain failed historical
attempts, not passes. The coordinator's published prerequisite
`040e59d30a6726fa4f9fee831695eeaa4027ede1` was verified as an ancestor of fetched
master and merged into this same task branch at `57d53308`. No unpublished
sibling work was imported and this task made no arithmetic repair.

On that merged source, the full optional Bridge command passed in 1,042 seconds
(2,021 jobs), including the original pinned `SolidityBridge.Checks`. All
new/existing affected ExternalEvm targets passed, as did the original native
controls plus eight populated compositions, all 36 memory axiom audits, and
the 36-case × 1,000-sample rule checker at seed 42. Orphan/layer, strict
automatic, complete TestSuite/static, trust and trust-regression gates passed.
The first unchanged 7,200-second full core command passed all 738 default targets
and TestSuite through Derived19, including Derived17 (154 seconds), then hit
its aggregate timeout. This is **BLOCKED**, not a pass. The group took 8,271
seconds at its 12 GiB hard cap, with 1,773 limit events and zero OOM events.
Its original container continued across a managed-runtime reconnect; the
terminal resource report was recovered verbatim from retained Docker stdout.

The concrete repair was to stage the two remaining cold targets, Derived20 and
Derived21, under the same 7,200-second timeout and 12 GiB/no-swap limit. Both
passed (223 seconds combined). The identical full `./run-lean.sh` command then
passed in 43 seconds: all 738 default jobs, all 262 TestSuite jobs and the
actual pinned SolKey annotation check, with no skip. A separate annotation
check and all 36 audits also passed. That staged group took 271 seconds at
5,986,820,096 bytes peak, with no limit or OOM events. No source statement,
expected observation, proof/search budget or timeout was changed. Derived17
required no repair on this task branch. These passing gates do not establish
the unproved `PaddingCorrect` contract or an unconditional FFI theorem.

The final documentation-path gate remains **FAIL**: 46 missing and 24 ambiguous
references. A separate detached read-only checkout of exactly `040e59d3`
produces the identical 70 findings, with no memory-task regressions or resolved
historical references. The 16-ambiguity count above belongs to the older base.
Final complete TestSuite/static, orphan/layer, strict automatic, trust and diff
checks passed. That final static group took 13 seconds at 173,125,632 bytes
peak, with no limit or OOM events; its documentation checks remain red.
Independent read-only finder and skeptic reviews found no remaining obligation
within this explicitly conditional bounded fragment. Their confirmed
current-base ambiguity-count finding was corrected; neither used a Lean
server. The original assignment's bounded refinement is complete under its
stated external contract, while no unconditional FFI, raw-source admission,
gas or bytecode claim is made.

This optional refinement admits no raw-memory/assembly Solidity source shape,
changes no source compiler, inventory target or exclusion, and claims no gas
or bytecode equivalence. Consequently no legacy/viaIR/optimizer source-admission
fixture is added or promoted. Numeric storage hashing and jump/PC assembly
remain outside this memory task.

The arithmetic dispatcher above excludes symbolic-slot PUSH/ADD and DUP/SWAP
depths outside 1–16. The optional finite storage lowering below admits
symbolic-slot PUSH; symbolic offset ADD and those extra depths remain outside
its fragment. `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean`
proves concrete disagreements for same-stack CALL/REVERT/JUMP/JUMPI and fixed
memory opcodes, non-wrapping symbolic offsets, and impossibility of a globally
injective encoding of all symbolic slots into finite EVM words. These results
rule out an unrestricted one-opcode identity theorem; they do not rule out
verified macro lowerings under explicit representation assumptions.

`Bridge/SolidityBridge/ExternalEvm/FiniteStorage.lean` supplies a proved
finite-observation representation lemma for the storage-slot refinement work.
`Represents` allows numeric aliases with equal reads. `write_iff` proves the
exact condition for a numeric write to implement a symbolic write on that
observed domain: each distinct observed alias must already contain the value
being written. It covers zero writes and writes outside the observed domain,
without assuming hash injectivity or collision freedom. Two distinct roots
(`0` and `2^256`) provide positive zero-alias and negative nonzero-write controls.
This finite-observation lemma alone does not connect to upstream account-map
SSTORE or hashing. Those connections are supplied by the bounded adapter below;
source coverage is not expanded.

On the task VM (2026-10-28), the isolated optional target passed kernel checking
(exit 0; 17 jobs; 1.61 s; 1,055,711,232 bytes sampled aggregate peak RSS).
Its axiom audit reports `[propext]` for `write_iff` and
`[propext, Quot.sound]` for the concrete refusal control. Independent read-only
finder and skeptic reviews found no confirmed defect. Checks used the
coordinator's measured VM guard: 12 GiB per-process address-space limit,
10 GiB sampled process-group RSS stop and 12 GiB whole-VM-current stop, on an
existing 16 GiB VM cgroup with actual swap disabled. This is not a claim that
a writable 12 GiB cgroup or `MemorySwapMax=0` was set. Reproduce with the
matching toolchain and `lake build SolidityBridge.ExternalEvm.FiniteStorage`;
the task additionally supplied `-j1` in an untracked Lake configuration.

`Bridge/SolidityBridge/ExternalEvm/RBMapErase.lean` proves the missing
lookup-after-erase law for the pinned Batteries map used by upstream storage.
The raw-tree theorem assumes actual orderedness, a transitive comparator and
a strict cut; the map theorem obtains orderedness from RBMap's own invariant.
It preserves nonmatching entries and removes matching entries, including absent
keys, without requiring comparator equality to imply propositional key equality.
No vendor code changes. This supplies the zero-write dependency; it does not
by itself prove SSTORE refinement. Its isolated target passed with exit 0
(28 jobs; 2.73 s; 874,049,536 bytes sampled aggregate peak RSS), and both audited
headlines use only `[propext, Quot.sound]`. Finder and skeptic read-only reviews
found no confirmed defects. Earlier append proof attempts hit the unchanged
200,000-heartbeat limit; small equation lemmas and constructive propositional
proofs repaired that cost, without increasing any limit. The same measured VM
guard and single-thread configuration described above were used.

`Bridge/SolidityBridge/ExternalEvm/StorageAccounts.lean` connects these map
laws to the actual upstream `Account.updateStorage`, `State.sstore` and
`State.sload`. `storage_read_write` covers arbitrary initial storage and all
word values, including zero erasure. Its explicit semantic premise is that the
executing account exists. `account_after_sstore` preserves that premise, so the
law applies after previous writes and clears. Refund/access-list effects remain
in the evaluator, but are unobserved by this storage relation. No hash-separation,
original-transaction-storage or other-account restrictions are assumed.
The isolated account target passed (exit 0; 1041 jobs; 2.72 s;
1,652,953,088 bytes sampled aggregate peak RSS). Both headline axiom audits are
`[propext, Classical.choice, Quot.sound]`. Independent finder and skeptic reviews
found no confirmed defects. Driver gas/static-mode checks and source physical
layout remain outside this optional adapter.


### Finite storage macros

The storage row now has an optional, conditional compiler refinement in
`Bridge/SolidityBridge/ExternalEvm/StorageSlots.lean`, imported with its
regressions by `Bridge/SolidityBridge/Checks.lean`. It does not lift excluded source physical-layout
or assembly semantics.

- `StorageAddresses.lean` interprets roots modulo `2^256`, recursively hashes
  mapping/array parents, and wraps offsets. Hashes use actual upstream
  `MachineState.keccak256` on concrete scratch states built by upstream
  `mstore`. There is no hash injectivity or collision-freedom premise.
- `StorageOpcode.lean` proves small actual `EvmYul.EVM.step` steps.
  `StorageMacros.lean` composes them: array hashing executes
  `PUSH 0; MSTORE; PUSH 32; PUSH 0; KECCAK256`; mapping hashing writes the key
  at zero and parent at 32, then hashes 64 bytes. `ArraySetup`/`MapSetup`
  constrain only the bytes read after those actual writes. Both are inhabited
  for arbitrary operands from empty memory. No sibling byte-memory or
  assembler API is required.
- `Agrees` observes a represented stack and a finite list of symbolic storage
  cells in a present executing account. `WriteCompatible` is the exact alias
  condition from `write_iff`: every distinct observed numeric alias already
  contains the written value. Initial storage and collisions may otherwise be
  arbitrary. Actual SLOAD and nonzero/zero-erasing SSTORE preserve the relation
  under explicit membership, account and alias premises.
- `step_refines` and `bounded_refinement` establish successful actual symbolic
  instruction execution, partial lowering, upstream macro execution and
  preservation of `Agrees`. `Ready` records stack/setup/alias premises along a
  finite instruction list; it does not assume successful executions exist.
  Joint `Agrees` and `Ready` witnesses establish nonvacuity.

`StorageSlotExamples.lean` kernel-checks scoped source observations and exact
compiler output: scalar write/read gives 7, clearing gives 0, and
`balances[7] = 5` gives 5 in both `Prog.runFrames` and actual upstream
execution of its lowering. Arbitrary mapping/array hash-to-write controls use
nonempty observation domains. Controls refuse absent accounts, incompatible
numeric root aliases, underflow, unsupported CALL, and the existing compiled
source-array read (which needs bounds/control-flow/element arithmetic outside
this partial lowering). `Obstructions.lean` is unchanged, including its
impossibility of a globally injective encoding of all symbolic slots.

The relation does not observe PC, gas, refunds/access warmth, other accounts,
whole byte memory or unbounded physical layout. As in the dispatcher adapter,
supplied instructions use evaluator fuel 1 and charged gas 0; instruction
fetch and upstream driver checks are outside the theorem. Upstream
`ffi.ByteArray.zeroes` and `ffi.keccak256` (called by `ffi.KEC`) remain
opaque evaluator operations. Agreement with those operations does not certify
canonical serialization, cryptographic correctness or external FFI execution.
Symbolic offset ADD and general source-array compilation remain refused.
No source inventory category is promoted. The fixtures use scoped source and
the existing intrinsic compiler; no solc pipeline reader or optimizer mode was
changed by this optional lowering.

Pinned headline and example audits report only
`[propext, Classical.choice, Quot.sound]`; no new axiom declarations were
added. Independent read-only finder and skeptic reviews confirmed preparation,
finite aliases, arbitrary-account storage, joint witnesses and source/compiled
observations, with no confirmed semantic defect remaining. Earlier requests
for source hashing/reads, joint witnesses and pinned audits were implemented.
Neither reviewer used a Lean server or build.

A monolithic concrete-macro proof was **BLOCKED** by the RSS guard (91.65 s;
10,789,376,000 bytes peak). Small opcode lemmas and composition repaired that
cost without raising limits. A scalar read example then hit the unchanged
200,000-heartbeat limit; splitting symbolic execution with `run_append_ok`
repaired it. The final affected target passed (exit 0; 1133 jobs; 8.97 s;
1,867,120,640 bytes sampled aggregate peak RSS). All accepted Lean validation
uses the measured guard described above, `LEAN_NUM_THREADS=1`, and explicit
`-j1` in temporary untracked Lake configurations.

The first full-package attempt lost its guard during executor reconnection
(observed defunct guard with wait status 9 and no resource result). It remains
**BLOCKED**, with no successful terminal exit or invented aggregate peak.
The remaining workload group was stopped. The retry launches the unchanged guard in a detached session; its inherited
12 GiB address-space limit was verified on the Lake process before continuing
from disk caches. Earlier failures and interruptions remain in the exported evidence.


The final direct storage regressions and unchanged Obstructions target passed
(exit 0; 1152 cached jobs; 1.11 s; 406,573,056 bytes peak RSS). The fixed-seed
rule checker passed 36 rule cases × 1000 samples (seed 42; exit 0; 72.85 s;
1,113,563,136 bytes peak). Orphan, layer, strict automation, core trust, trust
script tests and a separate trust scan of all eight task modules passed.

**Historical checkpoint 658fe793 (superseded by the resumed diagnosis below).**
Full validation was blocked by an unchanged dependency. The first
completed default-package run failed (exit 1; 1228.59 s; 4,158,939,136 bytes
peak): Arith/Widths proof errors and a TermSize thread-creation abort (134).
An isolated core TermSize run with MALLOC_ARENA_MAX=2 passed under the same
limits (27.74 s; 1,360,445,440 bytes). The subsequent full run failed only
SolidityBridge.Arith.Widths (exit 1; 27.63 s; 1,950,683,136 bytes).
An isolated Widths target reproduced its five errors (exit 1; 7.97 s;
1,810,821,120 bytes). Its generated synth.eq_N anchors are stale at lines
21, 47, 79, 111 and 501. Both independent reviewers verified that Widths is
unchanged from the recorded base and imports none of the storage-task modules;
at that checkpoint, repair was outside the storage assignment. The continuation
below explicitly authorizes narrow Widths maintenance. Its failed recovery
audits containing sorryAx are not accepted certificates. A freshly fetched
master at 638c9b68b37d8a6a15630eac9885e2d873040eb1 still has the identical
Widths file. No unrelated proof repair or upstream branch was imported here.
The maximal independent storage increment is proved; original-assignment
completion is not claimed while the mandatory full gate is blocked.

The global documentation-path gate also remains failed (exit 1; 20 unresolved
references in unchanged files). Source blob comparisons establish that debt;
it is separate from the new owning documentation and is not reported as passed.
Full logs, exact guard reports, configurations, reviews and checksums accompany
the task handoff. Reproduce the affected optional targets from `Bridge/`:

```sh
lake build SolidityBridge.ExternalEvm.StorageSlotExamples \
  SolidityBridge.ExternalEvm.Obstructions
```

The task's exact guarded commands and temporary single-thread configurations
are retained in its evidence.


### Resumed Widths prerequisite (checkpoint d44a19bf; superseded below)

The continuation authorizes narrow shared proof maintenance in
`Bridge/SolidityBridge/Arith/Widths.lean`. The initial resumed fetch was
`638c9b68b37d8a6a15630eac9885e2d873040eb1`. A final fetch reached
`c30efa3d8786cede97a8d4f1e9b90629724e5cd4`; the Widths blob is still
`339457565926f36fb8af144bc5957280d8f387f2`. No upstream changes were imported.

`Bridge/SolidityBridge/Arith/WidthsSyntax.lean` supplies stable structural name/unary facts.
`synth_word`, `synth_head` and `synth_unary` retain their original
statements and now use those named facts. Negative-numeric-literal overlap is
excluded from the generic unary clause using the existing premises: numeric
synthesis returns uint, while negation requires int. Abstracting the monadic
literal result and transporting inequality avoids kernel deep recursion
without changing any limit. The new module passed under its default recursion
limit (exit 0; 3.33 s; 1,126,162,432 bytes peak RSS). All three repaired
headline audits report only `[propext, Quot.sound]`. All 38 existing public
theorem headers and the existing `maxRecDepth 4096` option are unchanged.

**A semantic decision is required for the two binary helper contracts.**
This is not merely historical anchor debt. `Bridge/SolidityBridge/Arith/WidthsObstructions.lean`
kernel-checks negations of the exact original generic schemas:

- With the concrete empty contract and local `x : int`, every original
  `synth_binary` premise holds for `x >> x`. Current synthesis checks the
  right operand as uint and refuses the expression, contradicting the claimed
  successful intrinsic syntax.
- For `x : int >> 257`, every original literal-helper premise holds.
  Synthesis produces the saturated intrinsic count 256; the original
  `synth_bin_literal` conclusion contains 257. The theorem asserts syntax
  equality, even if the resulting shifts may evaluate alike.

`OldSynthBinary` and `OldSynthBinLiteral` reproduce those original contracts
without importing the failing Widths module. Their negations, jointly inhabited
premises and concrete evaluator observations have pinned audits with only
`[propext, Quot.sound]`. Positive controls retain unsigned count 257,
8-bit modulo reduction, the full-word signed cast, and the negative-literal
clause. No operator semantics, expected observation, theorem statement,
fixture, exclusion or proof/search budget has changed.

The combined obstruction/storage/counterexample target passed (exit 0;
5.44 s; 1,141,514,240 bytes peak). The focused check including signed wrapping,
casts and the unchanged ExternalEvm Obstructions also passed (exit 0; 7.26 s;
1,162,199,040 bytes peak). The independent positive-control target passed
(exit 0; 6.76 s; 1,153,908,736 bytes peak). The isolated Widths target remains
failed at only the two binary proof sites (exit 1; 6.95 s;
1,765,376,000 bytes peak); the three statement-preserving repairs and their
guards no longer fail.

The requested decision is whether to correct the generic binary/check-helper
contracts to exclude or describe the signed-right-shift special case, while
preserving the current source/operator semantics and all width/cast result
statements. For example, an explicit exclusion `p = .int → op ≠ .shr`
would retain the cases used by the unsigned width proofs. No such premise has
been added. The request is pending; elapsed time is not authorization.

Original-assignment completion and a passing full Bridge gate are **not**
claimed. The full gate cannot be made sound with both refuted contracts
unchanged. The original storage commits/export remain intact; the cumulative
resumed handoff retains the exact counterexamples and all failed/successful
proof and resource reports. The unchanged documentation-path debt remains red.

The fresh final full Bridge gate failed only Widths (exit 1; 9.17 s;
1,669,246,976 bytes peak group RSS). Independent storage, unchanged global
Obstructions, the new syntax/obstruction modules, signed wrapping and casts
passed (exit 0; 1.21 s; 395,571,200 bytes). The actual fixed-seed executable
passed 36 cases × 1000 samples, seed 42 (exit 0; 2.22 s;
463,720,448 bytes peak group RSS). An invalid nonexistent Counter target
and an executable invocation from the wrong package failed first; their logs
are retained, and only the corrected commands are passes.

**The full core TestSuite also remains resource blocked.** Its static complete
parity/trust check passed against the existing repository pin (564 cases:
552 derived, 11 refuted, 1 excluded; no repin). The first guarded build stopped
at the whole-VM limit. Allocator collection/segment reuse then allowed Derived7
to pass (177.11 s; 2,955,022,336 bytes peak); a subsequent full run passed
Derived15 but failed Derived17 and Derived21 (exit 1; 523.49 s;
5,866,684,416 bytes peak). Enabling small arenas allowed Derived21 to pass
individually (126 s), but the combined run was stopped during Derived17
(exit 75; 251.54 s; 7,523,086,336 bytes peak group RSS).

The installed allocator parses `MIMALLOC_ARENA_RESERVE=65536` as **64 KiB**,
not the initially intended 64 MiB. Verbose logs verify the actual setting.
Small initial arenas and experimental segment targets are not hard caps.
Clean file-cache advice retained every cache file on disk but did not complete
Derived17: its isolated retry stopped at the whole-VM limit (exit 75;
109.76 s; 8,138,121,216 bytes peak). Disabling large/transparent huge pages
for the process then reached the aggregate RSS stop (exit 75; 132.84 s;
10,744,573,952 bytes peak). Restoring the published default asynchronous
elaboration schedule under `-j1` instead failed with `bad_alloc` (underlying
Lean 134, Lake 1; 104.42 s; 8,904,433,664 bytes peak). Profiling and all
terminal resource reports are retained. No identical failed configuration was
rerun as a purported repair. None of these stopped runs is a pass.

The tested allocator combination uses `MALLOC_ARENA_MAX=2`,
`MIMALLOC_PURGE_DELAY=0`, `MIMALLOC_TARGET_SEGMENTS_PER_THREAD=16`,
`MIMALLOC_MAX_SEGMENT_RECLAIM=100` and `MIMALLOC_GENERIC_COLLECT=100`;
arena/large-page variants and synchronous/default-schedule configurations
are preserved verbatim in evidence. Individual flag causality is not proved.
All runs retain the installed per-process AS bound of 12 GiB, sampled group
RSS stop of 10 GiB, whole-VM-current stop of 12 GiB, actual 16 GiB VM cgroup
and disabled swap. This is not a 12 GiB cgroup guarantee.

No core loop/closer proof, fixture, expected observation or proof budget was
changed. The next proposed investigation is source-level profiling of Derived17
by its loop/closer owner under these bounds; this storage task does not take over the
excluded loop work. The semantic Widths decision is independently necessary.
The original-assignment completion decision remains **blocked**, not complete.

### Human-approved signed-SHR maintenance (2026-10-29)

The human explicitly approved the exact exception
`p = .int → op ≠ .shr` for the four internal generic Widths synth/check
helpers, and required a separate signed-SHR proof. This resolves the earlier
Widths decision; it authorizes no other weakening. The four helpers now have
that premise. All 34 other original Widths theorem statements, all 21
NarrowChecked statements and all 19 Lowering statements remain unchanged.
NarrowChecked's callers discharge the new premise trivially. Stable structural
unfolding also repairs its negative-literal anchor. Existing width/cast results
are kernel checked again (isolated Widths: exit 0; 9.77 s; 1,738,887,168-byte
peak group RSS; NarrowChecked: exit 0; 8.15 s; 1,730,707,456 bytes).

`Bridge/SolidityBridge/Arith/WidthsSignedShift.lean` separately proves the actual
source checker branches. Both check the count as uint. A literal count uses
`min n 256`; a nonliteral count is compared with uint 256 before conversion
to int. The theorems retain explicit successful checker/literal setup premises.
A concrete empty contract inhabits checked inputs at counts 0, 255, 256 and
257, as well as the nonliteral cast-count branch. The old unrestricted-helper
counterexamples in `Bridge/SolidityBridge/Arith/WidthsObstructions.lean` remain
unchanged. The separate branch laws and controls passed at the default recursion
limit (exit 0; 3.82 s; 1,675,149,312 bytes); their pinned axiom audits contain
only `[propext, Quot.sound]`. These are source-checker syntax laws, not a new
universal source-arithmetic or physical-layout refinement claim.

#### Retained-failure-data guard decision

Full Bridge reached a further false contract in
`Bridge/SolidityBridge/Arith/Lowering.lean`: `narrowCheck_guard` describes its
RHS using `scope.selfFrame` alone. Current source lowering uses
`scope.selfFrame || scope.retainFailureData` in both the explicit-overflow and
default guard branches. The new
`Bridge/SolidityBridge/Arith/LoweringObstructions.lean` proves the actual
source equation and negates the exact old unrestricted schema. Its concrete
empty contract, uint8 local, `selfFrame=false`, `retainFailureData=true`,
default overflow mode and empty memo satisfy every old premise. Actual lowering
emits a panic-data guard; the old RHS emits an ordinary require. A typed
statement observation distinguishes the results. The actual equation, setup,
concrete counterexample and exact-schema negation passed (exit 0; 3.02 s;
1,689,808,896-byte peak group RSS), with only `[propext, Quot.sound]`.

The exact proposed correction is to use the OR of the two flags in both RHS
positions. A separate human decision has been requested; the signed-SHR
approval does not authorize it. The old Lowering contract has not been changed.
The independent local-type and Boolean simplification proof repairs retain
those statements. Original-assignment completion and a green full Bridge gate
are not claimed while this contract is pending.

#### Primary cgroup validation

After resuming this same saved VM, its local Docker daemon could enforce the
original primary policy. The task's directory-only carrier mounts the existing
published runtime read-only and the existing workspace read/write; it downloads
no image/toolchain/source environment. Workspace device/inode and actual
Lean 4.24.0 / Lake 5.0.0 output match the outer executor. The runtime mounts for
the Derived17 check are `/usr`, `/bin`, `/lib` and `/lib64`; core validation
additionally mounts `/opt` for the published Node runtime.

Actual kernel files verify the workload's hard 12 GiB memory limit and zero
swap allowance. A read-only ancestor inspection verifies the same VM's hard
16 GiB ancestor. Executor and Docker workload cgroups are siblings beneath that
ancestor, not a direct parent/child pair. This is the approved primary cgroup
policy, with no per-process address-space limit; it is not a passing fallback
AS/RSS-guard run. The earlier fallback stops remain failed.

The exact original Derived17 Lake target passed unchanged: exit 0; 201.34 s;
10,977,157,120-byte sampled aggregate RSS; 10,909,995,008-byte peak charged
cgroup memory; no max/OOM/OOM-kill events. No fixture, proof, sharding, tactic
step, heartbeat, search or test budget changed. The first eight unchanged
proofs had separately passed at 2,225,348,608-byte peak RSS; the isolated
1024-step nested-return proof exceeded the fallback's 10 GiB RSS stop. Splitting at existing theorem boundaries did not remove that measured
individual-proof peak; this does not rule out other proof factoring. No core
loop/closer work was taken over.

The original `./run-lean.sh` core/TestSuite/sort command runs under the same
primary bounds with explicit Lean `-j1` and `LEAN_NUM_THREADS=1`. An initial
carrier invocation failed before validation because Node was absent from PATH;
that failed log is retained. The corrected run reached 526 build jobs without
proof errors but hit its 1800-second timeout (exit 75; 7,889,965,056-byte sampled
RSS; 8,189,521,920-byte charged cgroup peak). It is not a pass. The next attempt
restores the published CLI asynchronous-elaboration default, retains all numeric
proof/search/test budgets and the same timeout/hard resource bounds, and reuses
the completed disk caches. Its terminal result must be recorded separately.

All logs, primary/fallback policy scopes, exact configuration snapshots, human
approval, failed commands and read-only review outcomes accompany the cumulative
handoff. No source support inventory is promoted by this optional finite-model
compiler refinement or by internal proof maintenance. The original global
storage-encoding obstruction and the physical-layout/assembly exclusions remain.

The published-default-schedule full-script attempt also timed out (exit 75;
1800.07 s; 5,947,494,400-byte sampled RSS; 5,283,250,176-byte charged peak),
after 577 jobs and without proof errors. A bounded library prerequisite then
timed out in OpenLoops (exit 75; 600.01 s; 6,750,101,504-byte sampled RSS;
5,792,980,992-byte charged peak). Both remain failed. Isolating the exact
OpenLoops module within the existing 1800-second maximum passed unchanged
(exit 0; 750.89 s; 9,120,841,728-byte sampled RSS; 8,168,312,832-byte charged
peak; no OOM events). No allocator-cadence change was needed for that isolated pass. Subsequent cold
library validation timed out again (600.01 s; sampled RSS 3,967,377,408 bytes;
charged peak 3,049,177,088 bytes), after 608 jobs without proof errors. The next
library attempt restores only the documented default collection cadence of
10000 from 100, under the same limits and proof budgets; its outcome remains
pending. Separate library/executable/TestSuite prerequisites and the original
full-script confirmation still require their own terminal outcomes.

The preserved primary runner V1 had an exceptional-path reporting defect:
a missing executable produced a CLI success with a null underlying exit code.
This was reproduced as an explicitly labeled negative control, not a passing
command. Historical successful checks retain valid underlying child exit 0
and completed-build output; their results do not rely on that error path.
V2 fails closed on launcher/monitor exceptions and passed both the missing-command
(exit 75) and normal-success (exit 0) controls. V1 and its exact historical
reports remain preserved; subsequent checks use V2. The installed fallback
`bounded.py` was not modified.

The latest independent affected-target check passed the current Widths,
separate signed-shift, counterexample, narrow, finite-storage and unchanged
global-obstruction targets. The fixed-seed executable again passed 36 cases
× 1000 samples, seed 42. Broad local-type simplification initially hit the
existing 200000-heartbeat limit; the proof now matches the current three-field
`LocalTy.val` equation directly and rewrites the known head lookup. This removed
that error without raising the limit. The isolated Lowering module now fails
only at the unchanged, separately unapproved guard contract.

The latest fresh affected-target check passed (exit 0; 26.14 s; sampled RSS
1,740,263,424 bytes; charged peak 374,431,744 bytes), including every new
independent source-checker/counterexample module, narrow laws, finite-storage
controls and unchanged global obstruction. The fixed-seed executable passed
(exit 0; 2.52 s; sampled RSS 462,655,488 bytes; charged peak 245,403,648 bytes).
The current isolated Lowering gate reports only the original false guard
contract (exit 1; 6.65 s); failed recovery audits are not certificates.

Independent read-only finder and skeptic reviews found no new soundness or
scope defect, confirmed the exact four approved premise changes and unchanged
other headers, and verified the concrete retained-data obstruction. Neither
used Lean tools, a Lean server or a build. Their requested qualifications about
proof factoring, primary-policy scope and historical runner reports are retained
here. This local proof checkpoint is not original-assignment completion: the
full core script and full Bridge gate are still pending/red as described above.

#### Assembly layout and conditional control-flow simulation

`Bridge/SolidityBridge/ExternalEvm/Assembly/CodeLayout.lean` resolves labels in the
existing `List Instr`; it introduces no source intermediate language. A label
is a `Fin (code.length + 1)`, including the continuation. `Relocation` retains
both `target = origin + 1 + offset` and the exact absolute word address.
Resolution refuses offsets beyond the continuation, unsupported prefixes, and
word-address overflow. Numeric PUSH, POP, relative JUMP/JUMPI and nested LOOP
have executable byte emission; other instructions have no assembly layout here.

Every core boundary receives a `0x5b` byte. Branch macros use fixed PUSH32
immediates followed by JUMP/JUMPI. Loop emission uses a header, condition,
ISZERO/conditional exit, body and absolute back edge. Its body begins at
`base + conditionSpan + 37`; its continuation is at
`base + conditionSpan + bodySpan + 72`. `assemble` returns a proof-carrying
`Image` only after checking total length, word-address bounds, boundary bytes,
and all nested branch-reference bytes. PUSH32 accepts `Fin W`, so its encoder
cannot silently truncate an out-of-range input.

`Image` alone is a raw-byte layout certificate, not an execution certificate.
`Bridge/SolidityBridge/ExternalEvm/Assembly/Placement.lean` now proves that an actually placed image's labels decode as
upstream JUMPDESTs, and that the target frame preserves its code slice. This
direct decoding fact is distinct from scanner membership: placing the image
after a PUSH32 opcode can put its first byte inside the preceding immediate.
The general simulation below therefore requires actual decoder and address
certificates. The automatic linker described below constructs these by finite
checking rather than inferring them from raw boundary bytes alone. The existing
same-stack JUMP/JUMPI obstructions are unchanged. Source assembly remains excluded. No Solidity frontend admission changed,
and the legacy/viaIR/optimizer fixture matrix and source-feature inventory
are not promoted by this optional instruction-level refinement.

`Bridge/SolidityBridge/ExternalEvm/Assembly/LayoutChecks.lean` checks taken and
untaken core branches, zero offsets, exact continuation targets, too-large
offsets, nested-loop edges, unsupported instructions and word-PC boundaries.
These are layout/core-run controls, not source-versus-upstream agreement.
Per-file Lean checks used Lean 4.24.0 with `-j1`: layout 1.815 s / 720,998,400
bytes peak sampled group RSS; controls 1.208 s / 693,436,416 bytes. The managed
VM policy was an existing 16 GiB cgroup with no actual swap, a hard inherited
12 GiB per-process address-space limit, sampled 10 GiB workload RSS stop and
12 GiB whole-VM-current stop. No writable 12 GiB cgroup limit was set.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Control.lean` proves actual
upstream PUSH32/JUMP and PUSH32/JUMPI macro equations for arbitrary target
states and numeric stack tails, including conditional underflow. `jump_pc`
retains the exact resolved natural address; the jump/frame lemmas preserve
account/environment state and target memory. `fetched_jump_trace` and
`fetched_jumpi_trace` use actual dispatcher steps with explicit packet-fetch
assumptions. Positive evaluator fuel and zero charged gas remain explicit.
The `sequence` helper composes separately supplied source successes and target
traces; it is not a general sequence simulation or boundary-relation theorem.

`Bridge/SolidityBridge/ExternalEvm/Assembly/ControlChecks.lean` pairs core runs
with fetched upstream observations of taken/untaken branches, numeric PUSH32
including the maximum word, and a terminating loop. It instantiates the general
fetched-JUMP theorem at an inhabited actual code/state and proves the target
byte decodes as JUMPDEST. Actual upstream `X` controls reject invalid taken
JUMP/JUMPI destinations and accept an untaken JUMPI with an invalid destination;
these use fixed, explicit driver resources, not a new source gas model.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Loop.lean` links the emitted
constant-true loop bytes to a universal ten-step fetched cycle. The cycle
preserves the stack and account/environment state, returns to the header,
and increases `execLength` by ten. `trueLoop_prefixes` proves actual counted
prefixes for every number of turns. `trueLoop_core` retains the core's semantic
`.fault` classification for a loop with no terminating turn. This does not
identify `.fault` with a finite-fuel `X` result, prove driver divergence, or
establish arbitrary structured-loop assembly correctness.

The focused targets `SolidityBridge.ExternalEvm.Assembly.LayoutChecks`,
`SolidityBridge.ExternalEvm.Assembly.ControlChecks` and
`SolidityBridge.ExternalEvm.Assembly.Loop` pass (exit 0), including all paired
observations and headline axiom audits. Their actual axiom union is
`propext`, `Classical.choice`, `Quot.sound`. The prior milestone's pinned warm check took 6.956 s
at 1,788,063,744 bytes peak sampled group RSS. Loop checking took 17.019 s at
3,387,580,416 bytes. Direct ten-step elaboration had hit the existing 200,000
heartbeat limit; separate closed decoder proofs and step equations repaired
checking without raising any limit. Validation used temporary untracked Lake
copies with package/library `weakLeanArgs = ["-j1"]`, `LEAN_NUM_THREADS=1`, and
the workload guard described above; the copies and exact commands are retained
in the delivered evidence.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Composition.lean` introduces `Boundary`: a bounded source label,
its exact absolute PC, numeric stack interpretation, and upstream account,
environment and memory frame. `exec_simulation` inducts over the actual core
runner, carrying pending skips through source suffixes without executing their
bytes. `PrimitiveLayout` contains actual packet decodings and address equations,
not target execution premises. The primitive boundary lemmas derive fetched
executions from those facts; `decoded_run_simulation` composes numeric PUSH,
POP and forward branches. `Bridge/SolidityBridge/ExternalEvm/Assembly/CompositionChecks.lean` supplies an inhabited image
at PC 5 with boundaries 5/40/74/108. Its simulation is universal over conditions
and stack tails, with actual taken/untaken observations (five/seven steps),
scanner controls, and valid/invalid destination-set controls against `X`.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Structured.lean` proves general loop composition. `LoopLayout`
contains actual decoder/address facts for the nested condition/body slices,
four-step guard and backedge. `decoded_loop_turn` obtains condition/body runs
from their own refinements, then composes the routing macros. It does not
assume a whole-loop target trace. Successful core loops cannot export a pending
skip. Mutually indexed `DecodedCode`/`DecodedSite` proof certificates follow the
existing instructions and support arbitrary nested loops; they are not another
executable source language. `certified_run_simulation` proves a general successful
core-run versus actual fetched-run correspondence under these certificates.
`decoded_loop_divergence_prefixes` maps every still-running source prefix to
an actual target prefix of at least that length, retaining the core's divergent
`.fault` classification. It does not equate that classification with a driver
failure or claim finite-fuel, gas-checking `X` divergence.

`Bridge/SolidityBridge/ExternalEvm/Assembly/StackLoopChecks.lean` inhabits the recursive loop certificate for a
nonconstant stack-consuming loop. Any finite list of nonzero numeric conditions
followed by zero terminates at PC 72, preserving the remaining stack and account/environment state.
This is a kernel theorem for variable-length input, not only a sampled run.
Executable controls cover zero continuing turns and three continuing turns (29 fetched
steps), source fault/target underflow on empty input, and actual scanner output.

The upstream scanner API itself is opaque: a retained negative API probe
prints `D_J_aux` as `opaque`, rejects `D_J_aux.eq_def` as unknown, and cannot
unfold its recursive equation with `rfl`. This is evidence of the available
API boundary, not a scanner-correctness theorem. The concrete PUSH32-prefix
control directly decodes JUMPDEST while the actual scanner excludes it.

At checkpoint `c956244263fa03edc6cec17725b75987bb3d05a7`, automatic
certificate construction and scanner/driver refinement were still open; the
continuation below adds them for accepted checked layouts. The raw `assemble`
API still returns `Image`. The successful-run
theorem covers the supported numeric instruction fragment and explicit local
layout assumptions; it is not universal Solidity source coverage or a theorem
for faults/reverts outside that fragment. Positive one-step evaluator fuel and
zero charged gas are unchanged. No proof/search/fuel budget was raised.

The complete focused proof closure passes with pinned actual axiom union `propext`,
`Classical.choice`, `Quot.sound`: rebuilding the new proof closure took
18.126 s at 2,096,726,016 bytes peak sampled group RSS. A warm check,
including the negative PUSH-prefix scanner control, passed in 6.548 s at
2,126,405,632 bytes. Adding an exact kernel `StackUnderflow` control then
passed the focused closure in 5.945 s at 2,044,481,536 bytes. Independent read-only finder and
skeptic reviews found no defect in the general conditional theorem, its
inhabited branch/variable-loop instances, placement proof or prefix claims;
both explicitly retained the certificate-generation/scanner/driver limitations.
Layer, strict automatic, trust and core orphan gates pass. A separate optional
import/trust check confirms every new module is reachable from the Bridge root,
no import cycle or forbidden proof/budget token was introduced, and Widths does
not import the task modules. The prose-path gate still exits 1 for exactly the
20 historical missing references; its diagnostic log and cited files match the
previous milestone/base.

The original full default Bridge attempt remains **failed**, exit 75 at
1,200.115 s / 2,400,370,688 bytes. Its log accounts for 1,176.664 s across 384
completed cold jobs, rather than identifying one hung dependency. Azure cache
requests returned proxy HTTP 403. Staging the cached ModelTheory closure passed
in 3.625 s; staging the Bridge root then exposed unchanged `Arith.Widths` proof
failures and a `TermSize` thread-creation crash (exit 1 overall, 844.709 s /
3,955,150,848 bytes). The root dependency had initially bypassed the temporary
`-j1` config. Untracked manifest overrides now select single-thread configs for
transitive packages too. Explicit `-j1` alone still crashed `TermSize`; serial
elaboration (`-DElab.async=false`) passed in 27.974 s / 1,435,271,168 bytes,
without changing its source, stack size, proof limits or observations. The
repaired full build also checked it successfully. `Arith.Widths` is identical
to the recorded base and still fails at stale `synth.eq_3` rewrites; it is not
modified by this assignment. The repaired full default command finished with exit 1 in 556.431 s at
2,396,921,856 bytes; its only failing target was unchanged `Arith.Widths`.
The documented Plausible runner passed 36 rule cases × 1,000 samples
(seed 42), exit 0 in 70.142 s at 1,102,626,816 bytes. All terminal results
are recorded in the task handoff; no failing gate is a pass. The final existing
`scripts/check-bridge.sh` run, using a Lake wrapper only to select the temporary
resource configs, exited 1 in 8.053 s / 1,814,028,288 bytes on that checkpoint’s
proof sources; its sole failing
target was unchanged `Arith.Widths`, and all vendor checks passed. This checkpoint was incomplete. The continuation below adds automatic
certificates and scanner/driver relations; a required full Bridge failure
still prevents declaring the original assignment complete.

### Automatic certificates, scanner and charged driver

`Bridge/SolidityBridge/ExternalEvm/Assembly/Static.lean` and
`Bridge/SolidityBridge/ExternalEvm/Assembly/StaticLoop.lean` derive the universal
primitive/loop layout obligations from finite source lookup, arithmetic and
actual decoder checks. `Bridge/SolidityBridge/ExternalEvm/Assembly/Automatic.lean`
recursively constructs `DecodedCode` for accepted placed images. Recursion is
by the existing instruction/list size, without semantic fuel or an untyped IR.
`assembleChecked` returns the image, placement and execution certificate;
`assembleChecked_simulation` consumes that result and the actual successful
core run. Unsupported instructions and failed placement/offset checks return
`none`. Acceptance completeness for all valid layouts is not claimed.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Scanner.lean` certifies a walk of
actual upstream `parseInstr` and `N`, skipping PUSH payloads. Its destination
list contains only actually decoded JUMPDESTs; `scanFrom_success` proves
availability when code size plus 33 fits the word address space. No equality
to opaque `D_J_aux` is assumed or proved. The certified list's array is passed
explicitly to actual upstream `X`.
`Bridge/SolidityBridge/ExternalEvm/Assembly/Scanned.lean` checks every label in
every recursive image, each atomic relocation and loop entry/exit.
`Bridge/SolidityBridge/ExternalEvm/Assembly/Linked.lean` stores that certificate
and its exact erasure to the execution certificate. Thus nested destinations
are not justified merely by root metadata. `linkChecked` rejects prefixes
that swallow required boundaries inside PUSH data; a complete aligned PUSH
prefix remains accepted.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Driver.lean` proves `X_unfold` by
`rfl` against the pinned driver, retaining all its gas, stack, destination,
static and other exceptional checks. `fetchedSteps_driver` inductively lifts
an arbitrary successful fetched prefix to equality of actual charged `X`
continuations. The retained state relation omits exactly gas and execution
count; world/environment, PC, stack, memory, active words, return data and
H_return agree. `LinkedProgram.driver_simulation` composes it with the general
source simulation. `DriverReady` explicitly checks positive finite dispatcher
fuel, the emitted opcode fragment and the original driver gates along charged
states. `checkReady` produces its proof. It does not assume an `X` outcome:
a possible step-error branch is accepted by readiness and ruled out by the
successful fetched trace and opcode congruence theorem. No source gas model
or unconditional gas-sufficiency claim is introduced.

`X_stop` and `X_destination_stop` separately prove successful halting at the
final JUMPDEST followed by STOP under the two exact terminal gates and positive
fuel. They retain upstream STOP's PC and clearing of returnData. The general
prefix theorem is continuation equality; successful halting additionally uses
these terminal checks. Arbitrarily long structured-loop fetched prefixes
remain the divergence result; no finite-fuel/gas `X` divergence is asserted.
Faults/reverts outside the supported successful fragment retain their named
refusals and existing obstruction proofs.

`Bridge/SolidityBridge/ExternalEvm/Assembly/AutoChecks.lean` kernel-inhabits
automatically generated branch and multi-turn loop certificates.
`Bridge/SolidityBridge/ExternalEvm/Assembly/LinkedChecks.lean` kernel-inhabits
the recursive scanned loop and driver readiness, and kernel-checks actual
`X 24` on conditions `[1,2,0]`, leaving `[9]` at STOP PC 73. Its live nested
control executes both loop bodies and reaches PC 179 with `[9]`; an explicit
kernel core-run proof uses the same `[1,1,0,0]` input and result. Other controls
cover hidden/aligned PUSH prefixes, corrupt placement, unsupported instructions,
invalid offsets, missing destinations, insufficient fuel and zero gas. The
original same-stack jump obstructions and offset/invalid-destination controls
remain unchanged. These optional instruction-level results do not promote
frontend coverage or require a Solidity source-mode fixture change.

The new headline and inhabited-proof axiom audit reports exactly `propext`,
`Classical.choice`, `Quot.sound`; source assertions pin the driver-prefix and
readiness results. Independent read-only finder and skeptic reviews found no
concrete defect and explicitly retained the readiness, terminal and opaque
scanner qualifications. No Lean server was used. The focused new closure
passed in 13.888 s at 2,428,465,152 bytes sampled group RSS before the final
axiom assertions; final command results and all failed development probes are
retained in the cumulative task handoff. The final unchanged full
`scripts/check-bridge.sh` (including vendor hashes) exited 1 in 36.880 s at
2,430,226,432 bytes, solely on unchanged `Arith.Widths`; all new assembly
modules built. That blocker is also unchanged on fetched published master
`b6bc41d47632335dea8bf34a6fc550aee66c99cf`. It remains another owner's area.
The paired nested proof then passed in 14.897 s at 2,428,059,648 bytes; the
final unchanged full script on those exact proof sources again exited 1,
solely on Widths, in 8.271 s at 1,809,760,256 bytes. The rule runner passed
36 cases × 1,000 samples (seed 42), exit 0 in 2.521 s at 487,870,464 bytes.
Layer, strict automatic, trust and orphan checks pass; the documentation-path
gate still fails with exactly the previous historical diagnostic log.
The original 1,200.115-second exit-75 attempt remains failed, not superseded
by a pass. Measurements use the existing 16 GiB
VM/no swap, hard 12 GiB per-process address-space limit and sampled 10 GiB group
RSS/12 GiB VM-current stops, not a writable 12 GiB cgroup guarantee.

### Scanner-consuming success and nested divergence

The continuation after `e9aaa5d34ee257b3564bc24503f1d2957626d28c` closes
integration gaps found by independent whole-scope review. At that checkpoint,
the historical Widths failure did not block these independent proofs; the
published repair and final combined validation are recorded below.

`Bridge/SolidityBridge/ExternalEvm/Assembly/Termination.lean` checks an
`ExitLayout`: the actual linked end-label JUMPDEST, a nonwrapping next PC and
an actual STOP at that PC. `TerminalGates` and its checker retain the two
original terminal resource gates. `SuccessBoundary` relates the final numeric
stack, world/environment and memory to the source result/frame, records the
exact STOP PC and clearing of returnData. `LinkedProgram.success_simulation`
now composes general source success, charged-prefix refinement and terminal
halting into actual `X.success`, rather than ending at continuation equality.
It still requires finite readiness and terminal gates; no X result is a premise.

The existing prefix theorem is preserved. Its new exact helper exposes
`driverSteps`, the counted actual charged prefix endpoint. This adapter is
related to `X` only for the certified pure fragment under positive readiness;
no off-fragment equivalence is asserted. The shared success helper uses that
endpoint equality to attach executable terminal witnesses without inspecting
classical source-loop witnesses. `Bridge/SolidityBridge/ExternalEvm/Assembly/PureFetched.lean`
proves frame preservation by induction.
`Bridge/SolidityBridge/ExternalEvm/Assembly/TerminationChecks.lean` kernel-inhabits
the actual 21-step/three-turn loop prefix, readiness, terminal gates and the
shared success proof on `[1,2,0,9]`, returning `[9]` with `X 24`. A separate
inhabited application exercises the compiler-facing count existential; the
control does not claim to identify its classical witness. Prefix readiness
at fuel 22 remains insufficient to execute the terminal JD and STOP.

`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeTrace.lean` annotates each actual
fetched microstep with its decoded pure packet and scanner justification for
its jump target. `SafeTrace.jump_checks` derives the original upstream
`X.notIn` check at every reached branch. The stronger compiled invariant also
validates untaken conditional targets; the existing upstream counterexample
accepting an untaken invalid destination remains unchanged.
`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeComposition.lean`,
`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeLocal.lean` and
`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeStructured.lean` carry that
annotation through the existing source sequence, relative-branch and loop
inductions. `ScannedCode.safe_refinement` consumes the same stored atomic
relocations and nested loop entry/exit memberships used by its erasure;
scanner safety is no longer merely a parallel metadata fact.

`Bridge/SolidityBridge/ExternalEvm/Assembly/ResourceReady.lean` removes real-array
destination validity from readiness premises. Its resource adapter invokes
the unchanged driver gate with the current operand as a singleton array;
`resourceGate_eq` proves equality to the real-array gate from compiled
`JumpSafe`. All original gas, stack, static and other checks remain intact.
`ResourceReady` contains no real destination array and no X outcome.
`SafeTrace.driver_ready` derives the original full readiness using the safe
trace and retained-state congruence. `LinkedProgram.resource_success_simulation`
therefore obtains actual X success from scanner-certified source execution,
resource-only readiness and the exact terminal gates. This is an adapter for
upstream checks, not a source gas semantics or universal gas-sufficiency claim.
`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeFetched.lean` separately checks
finite microstep safety for executable controls.
`Bridge/SolidityBridge/ExternalEvm/Assembly/ResourceChecks.lean` kernel-inhabits
the resource-only shared success path on the same multi-turn input, and both
taken/untaken relocated source branches. Missing destinations, zero gas and
insufficient fuel remain negative controls. Direct X observations accompany
the general proof path rather than replacing it.

`Bridge/SolidityBridge/ExternalEvm/Assembly/NestedDivergence.lean` adds proof
relations indexed by the existing instructions and machines, not a new source
IR. A witness ultimately contains a genuinely forever-running loop; successful
prefixes, divergent conditions/bodies and finite completed outer turns may
precede it. `BlockDiverges.source_fault` derives the unchanged core fault
classification. `BlockDiverges.compiled` enters an infinite inner loop without
assuming that an outer turn completes.
`Bridge/SolidityBridge/ExternalEvm/Assembly/SafeDivergence.lean` strengthens this
to arbitrarily long nonhalting, scanner-safe fetched traces, including sequence
prefixes with pending skips and later nested divergence after finite outer
turns. No finite-fuel/gas X divergence or equivalence with ordinary faults is
claimed.

`Bridge/SolidityBridge/ExternalEvm/Assembly/NestedDivergenceChecks.lean` stages
automatic recursive certification for an outer body containing an infinite
inner loop. `Bridge/SolidityBridge/ExternalEvm/Assembly/SafeDivergenceChecks.lean`
kernel-inhabits the recursively scanned certificate, actual scanner walk and
linked program, then applies the general safe-divergence theorem. The source
fault proof and 15-step target observation (inner header PC 37, empty stack)
exercise entry before any completed outer turn. A distinct later-entry case
uses `[loop [] [jumpi 1, loop [push 1] []]]` on `[1,1,1,0]`: a kernel source
witness completes one outer turn before inner divergence, while executable
link acceptance and 19 fetched steps reach PC 72 with an empty stack. That
later case is a source witness plus executable target regression, not a second
kernel-instantiated safe-divergence certificate. Independent review found the
general checked `afterTurns` induction and existing inhabited certificate
adequate; no per-constructor universal coverage claim is made.
`Bridge/SolidityBridge/ExternalEvm/Assembly/LayoutFacts.lean` supplies image-data
uniqueness and acceptance of already proved images by the raw layout validator;
it does not assert syntactic or semantic checker completeness.

The new complete control closure passed in 13.604 s at 2,346,885,120 bytes
sampled group RSS. The automatic scanner-safe nested control passed in 19.576 s
at 2,737,020,928 bytes. A closed endpoint proof initially hit the unchanged
10 GiB group-RSS guard (exit 75, 51.083 s / 10,765,037,568 bytes; further failed
attempts/probes are retained). Declaration isolation located repeated
normalization of whole 21-step EVM states in boundary conversion. Checked
endpoint equations, inductive frame preservation and elaboration-abstract
endpoint definitions repaired it: the same complete success control passed in
18.936 s at 2,358,882,304 bytes. No observation, fuel, proof/search limit or
resource ceiling was changed. Longer scanner walks similarly use factored
literal PCs and kernel-checked closed parser facts instead of raising recursion
depth. All failed resource terminals remain BLOCKED evidence.

The final closure, including pinned axiom assertions, passed in 31.409 s at
2,732,032,000 bytes sampled group RSS (exit 0).

`Bridge/SolidityBridge/ExternalEvm/Assembly/PopChecks.lean` closes the final
review's supported-POP validation omission: an automatic atomic certificate
and general kernel simulation pair `[push 1, pop, push 9]` with `[9]`, fetched
PC 70 and actual `X 9` STOP PC 71. A kernel safe-POP instance exercises the
scanner-consuming atomic path. Empty-stack source POP faults, exactly two
fetched steps produce StackUnderflow, and resource readiness refuses it.
The fixture passed in 5.643 s at 1,912,508,416 bytes sampled group RSS.

The actual new axiom union remains `propext`, `Classical.choice`, `Quot.sound`
(`Image.unique` uses only `propext`, `Quot.sound`). General success and safe
nested-divergence headlines and their inhabited controls pin actual axioms.
Independent read-only finder and skeptic reviews found no remaining semantic
integration gap within this accepted numeric fragment, and retained the opaque
D_J, acceptance-completeness, resource/terminal and unsuccessful-source limits.

The earlier compatibility check against published
`2abccb7044a4c6eb33a816cee7e862927e499cff` and its unchanged Widths failure
remain historical evidence. The approved prerequisite
`040e59d30a6726fa4f9fee831695eeaa4027ede1` was fetched, verified as an ancestor
and merged into the existing task branch at
`d011a0dba731756c16db8f390cde5c1dc2bbe6d4`. No assembly source changed in that
merge; the same-stack JUMP/JUMPI obstruction proofs remain unchanged. The old
Widths failure is no longer a blocker.

### Final published-prerequisite validation

The original complete `scripts/check-bridge.sh` gate, including all three
vendor hash sets, passed (exit 0) in 193.879 s at
3,384,856,576 bytes sampled aggregate RSS. This builds all default
optional targets and the complete registered assembly regression closure.
The fresh 18-headline/inhabited-instance axiom audit passed in
4.741 s at 1,619,939,328 bytes; its actual union remains
`propext`, `Classical.choice`, `Quot.sound`. Rulecheck passed all 36 cases,
1,000 samples each, seed 42 (exit 0, 11.132 s,
1,101,221,888 bytes). Layers, strict automatic, trust and orphan
checks passed. The documentation-path check retains the exact published
prerequisite's historical failures; it is not reported as passed.

The first post-merge full attempt stopped at the unchanged 600-second guard
(exit 75, 600.042 s, 2,189,041,664 bytes), after 64 successful new jobs. A
bounded syntax/elaboration cache stage passed in 101.987 s at 1,371,729,920
bytes. The next full attempt also timed out (exit 75, 600.068 s,
3,832,205,312 bytes), after another 89 successful jobs including the repaired
Widths/guard closure. Its terminal setup files identified the unfinished
`Solidity.Calculus.TermAgree` dependency. Staging that dependency passed in
31.476 s at 1,478,217,728 bytes before the final full run. These are cache and
scheduling repairs; no proof, source observation, fuel, timing or resource
budget was raised. Both timeouts and the original 1200.115-second timeout
remain failed evidence in the cumulative archive.

The first complete post-prerequisite umbrella passed 2,052 jobs in 439.456 s
at 2,355,208,192 bytes. A fresh comparison with the published documentation
baseline then found one new basename ambiguity: the added layout module made
an existing storage note's short citation ambiguous. The repair stays entirely
within this task: `CodeLayout.lean` has byte-identical contents to the former
layout file, with three own imports and two owning-document references updated.
No other batch's storage note was edited. The full post-rename pass is the
193.879-second result above.

The post-rename standalone axiom probe initially exited 1 because Lake restored
only the cached module's ILean into its ordinary build directory. Lake's actual
build had resolved the OLean directly from its artifact cache. Inspection of
`Module.restoreArtifacts` identified the loader-path distinction. A bounded
per-file kernel check materialized the unchanged layout OLean in 2.518 s at
1,066,070,016 bytes; the subsequent ordinary-path axiom audit passed. The failed
probe remains in the archive; no proof statement, dependency or trust premise
changed and no cache was deleted.

All heavy operations used the existing writer lock, one Lean thread, explicit
`-j1`, no Lean server, and the coordinator's measured workload guard: actual
16 GiB hard VM cgroup with disabled swap, inherited 12 GiB per-process address
space, sampled 10 GiB aggregate-RSS stop and 12 GiB VM-current stop. No writable
12 GiB cgroup or `MemorySwapMax=0` was set. Disk caches remain available.

Fresh independent read-only finder and skeptic reviews of the whole original
automatic layout/scanner/certificate/driver obligation found no remaining
own-scope gap or integration regression. No source-assembly admission,
feature inventory, intrinsic core representation or upstream pin changed.
The optional umbrella pass is build/regression evidence, not an unconditional
source-language or all-EVM soundness theorem. Explicit layout, numeric
representation, frame, scanner, fuel/resource and terminal assumptions remain;
upstream FFI or padding assumptions (including `PaddingCorrect` wherever such
an external claim requires it) are not discharged by this control-flow work.
No finite-gas divergence, opaque scanner equivalence, or acceptance-completeness
claim is added.

To build the independent targets alone, from `Bridge/`:

```sh
lake build SolidityBridge.ModelTheory.LowenheimSkolem \
  SolidityBridge.CallbackTrace SolidityBridge.CallbackModalTrace \
  SolidityBridge.ExternalEvm.StackOps SolidityBridge.ExternalEvm.Obstructions \
  SolidityBridge.ExternalEvm.StorageSlotExamples \
  SolidityBridge.ExternalEvm.Memory SolidityBridge.ExternalEvm.MemoryBytes \
  SolidityBridge.ExternalEvm.MemoryRefinement SolidityBridge.ExternalEvm.MemoryComposition \
  SolidityBridge.CompilerSimulation SolidityBridge.LoopFixpoint \
  SolidityBridge.AdversaryPolicy rulecheck
lake exe rulecheck --seed 42 --samples 1000
```

## Discrepancies

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
   both panic and exhaustion. `WeakestPreLaws.lean` checks both readings.

## Core changes wanted

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

Actual pinned-EVM MSTORE/decoder/step components: [proofs and remaining byte/source/resource laws](feature-work/diamond-try-evm-memory.md). Source/native12/8 strictEXIT1 and P4/P5b/P8 remain open; no vendor interface or admission adoption.

### Historical cumulative validation checkpoint ce54e121 (2026-10-29)

The four approved Widths helper contracts and separate signed-SHR laws are
committed in `c7a45cd0e3660dbbea2e541251419d59b5629d28`. The earlier Widths
decision and TestSuite 17 resource blocker are resolved as described above.
The separately kernel-refuted `narrowCheck_guard` contract still requires its
own human decision; the signed-SHR approval does not authorize changing it.
Its original statement remains unchanged, and the exact old-schema negation
and inhabited counterexample remain in
`Bridge/SolidityBridge/Arith/LoweringObstructions.lean`.

Library prerequisite 4 timed out at 600.005 s (exit 75), after kernel-building
DecisionHashes in 324 s. It is a blocked group, not a pass. Its completed cache
was retained. The fresh original, unmodified `./run-lean.sh` passed:
exit 0 (underlying 0), 741.357 s, sampled aggregate peak RSS 5,530,206,208 bytes
and charged cgroup peak 4,188,057,600 bytes. The timeout remains the original 1800 s. The command
selects only the temporary explicit `-j1` Lake configuration and existing frozen
SolKey rule snapshot. It completed 685 core jobs, 259 TestSuite jobs, and
matched all 131 read-bearing sort annotations. No source fixture, expected observation, proof/search
budget, toolchain or dependency pin changed.

The fresh full Bridge check after the final statement-preserving intTyOf_head
proof repair reports exit 1 (underlying 1), 7.060 s, sampled aggregate peak RSS 1,703,419,904 bytes
and charged cgroup peak 321,679,360 bytes. The unchanged guard contract
is its semantic blocker. Full Bridge and original-assignment completion are
not claimed. The affected storage/Widths/countercontrol targets and fixed-seed
rulecheck (36 cases × 1,000 samples, seed 42) pass in the terminal logs recorded above.

The current static orphan, layer, strict automatic, trust, trust-test, complete
TestSuite parity and diff checks pass. Documentation-path checking remains red
at the same 20 historical missing references; its corrected output is byte-for-byte
identical to the earlier debt log. An initial carrier docs command had raw exit 0
while reporting missing awk; that result is INVALID, not a passed gate. The
operational repair read-only mounts this same VM's existing /etc/alternatives,
resolving /usr/bin/awk without installing another runtime or changing source.

All current heavyweight checks use the verified primary hard 12 GiB workload
cgroup with `swap.max=0` and actual disabled swap, `LEAN_NUM_THREADS=1` and explicit
Lean `-j1`, one group under the checkout writer lock. The resumed allocator trial
restored shipped collect 10000 and purge delay 10 defaults; it establishes no
individual-flag speedup. Exact launches, reports, zero OOM event deltas where
applicable, invalid/blocked historical runs and actual configs are preserved.
Temporary configs and tracked manifest changes are removed after snapshotting;
all proof caches remain on disk.

Independent read-only finder and skeptic reviews found no new source defect
and confirmed the exact four approved header changes, unchanged other public
headers, explicit storage representation limits and separate guard decision.
Neither used Lean/server/builds or wrote files. Their export review identified
and corrected snapshot races, task-identity drift and overly broad completion
logic before creating the successor cumulative export. R1–R3 remain preserved;
the new handoff includes all task commits from the original base, full logs,
resource reports, human approval, reviews and checksummed patch/bundle/archive.


### Approved guard correction and final finite-storage validation (2026-10-29)

The human separately approved exactly both RHS flag tests of
`Solidity.Bridge.Arith.narrowCheck_guard` to use
`scope.selfFrame || scope.retainFailureData`. Commit
`d6c67b075dcd53ccc0c3381ec40955c4e90a46c5` applies only that conclusion correction;
all premises, other theorem statements, public width/cast results, actual source
behavior, source/compiled observations, exclusions and budgets are unchanged.
The preceding pending-decision checkpoints are historical and resolved.

The corrected public contract kernel-checks. Additive
`Bridge/SolidityBridge/Arith/GuardRetentionExamples.lean` applies it to an inhabited
uint8 local for all 12 combinations of self/retain flags and ordinary/checking/
ignoring overflow modes. In particular retained failure data without a self-call
selects the panic guard. Pinned audits for the helper, matrix and retained-panic
control use only `propext` and `Quot.sound`. Both `retained_data_counterexample`
and `not_old_narrow_guard` remain byte-identical and kernel-checked, refuting the
old conclusion. The global symbolic-slot injection obstruction is unchanged.

| Final check | Exit | Seconds | Sampled aggregate peak RSS (bytes) | Kernel cgroup peak (bytes) |
|---|---:|---:|---:|---:|
| Focused guard/storage/countercontrols | 0 | 10.198 | 1,714,331,648 | 335,499,264 |
| Full Bridge umbrella (2023 jobs) | 0 | 8.362 | 2,287,788,032 | 547,061,760 |
| Rulecheck (36 × 1000, seed 42) | 0 | 2.315 | 467,128,320 | 107,278,336 |
| Original full core/TestSuite/sort script (warm cache) | 0 | 2.118 | 216,403,968 | 375,488,512 |
| Original combined script with Bridge and vendor checks (warm cache) | 0 | 2.518 | 406,814,720 | 375,627,776 |

These are actual terminal results, not inferred cache or environment readiness.
Warm-cache confirmations do not replace the preserved 741.357-second core run or
establish a cold-build speedup. The original combined script checks 685 core jobs,
259 TestSuite jobs, all three vendor checksum manifests, 2023 optional Bridge
jobs and all 131 read-bearing sort annotations. Every final heavy check uses the
same saved VM, published Lean/Lake runtime, hard 12 GiB workload cgroup,
`swap.max=0`, actual disabled swap, `LEAN_NUM_THREADS=1` and explicit Lean `-j1`.
There are no OOM-event deltas. Timeouts, earlier failures and the invalid
missing-awk docs run remain preserved and are not promoted to passes.

The result remains an optional compiler refinement of the existing finite
storage model under the stated setup, finite-alias compatibility and actual
upstream-evaluator representation assumptions. It makes no hash-injectivity,
collision-freedom or unbounded physical-layout claim and does not enable excluded
source assembly/layout semantics. Existing source-run/compiled-run observations,
positive controls, collision refusals and kernel simulations remain checked by
the full Bridge umbrella. No source-coverage inventory promotion is warranted.

Independent read-only finder and skeptic reviews found no defect and confirmed
the exact approval boundary, inhabited controls and retained obstructions. Neither
used a Lean server/build or wrote files. The final static gates and their exact
HEAD are retained in the successor handoff. The historical 20 missing doc-path
references remain red and unchanged; they are separate documentation debt.
Current operational configs are snapshotted before removal/restoration; proof
caches stay on disk. The cumulative export preserves R1–R4 and includes both
human approvals, every task commit, full logs, resource reports and reviews.

### External memory integration gate repair (2026-10-30)

Combined validation of candidate `35ccc2d2411625a7a42f1748a1dac4d55c3e8899`
against base `204eb1545cbf57e436196e4cba346075515b7279` stopped at
`scripts/check-external-memory.sh`: the retained attempt-2 gate-14 log reports
`lake: command not found` (exit 127), after the allocator checksum passed.
The script now prepends `$HOME/.elan/bin` to PATH, matching
`scripts/check-bridge.sh`, so both Lake and `lean --print-prefix` resolve the
pinned toolchain. No Lean source, observation, proof budget or gate was changed.

The focused repaired gate passed (exit 0) from an initial `PATH=/usr/bin:/bin`:
28 store/load pairs, 33 allocator samples, six boundary/negative observations
and eight populated cases. An original-script control under the same restricted
PATH reproduced exit 127. The repaired run took 4.005 seconds, with sampled
aggregate RSS 2,267,680,768 bytes and scope memory peak 1,219,211,264 bytes.
The existing controller systemd scope reported `memory.max=12884901888`,
`memory.swap.max=0`, zero swap usage and zero OOM/kill events before and after.
The available-host guard retained a 12 GiB reserve. Host swap was enabled;
the no-swap claim applies to this workload scope.

Checks ran sequentially with `LEAN_NUM_THREADS=1`. A test-only Bash adapter
selected a temporary Bridge config adding explicit Lean `-j1` for the build;
the final `exec lake` used the normal config and its existing explicit `-j1`.
The temporary config was removed after checking. Full logs, settings snapshot,
source hashes and resource counters are retained in this integration checkout
under `.lake/external-memory-repair/`. Shell syntax and diff whitespace checks
passed. The documentation-path gate still exits 1 with 46 missing references;
replaying the pre-repair document produced byte-identical findings.
Independent read-only finder and skeptic reviews found no blocking
issue; neither used the Lean server. No Lean file was edited, so per-file MCP
diagnostics were unnecessary. This focused result does not replace the required
combined rerun or prove the explicit `PaddingCorrect` contract.

### Integration merge review (2026-10-29)

The merge of `109ba72ac8cf62f4aa4c13ae5590802244400bd0` into
`c8fd7b7ce6276497229b3aae8a65c27ef7cc78ed` retains all four arithmetic
regression imports and `ExternalEvm.StorageSlotExamples` in `Bridge/SolidityBridge/Checks.lean`.
The resolved file is byte-identical to the latter parent. Independent read-only
finder and skeptic reviews found no lost declarations, audits or import cycle;
neither used the Lean server. Focused whitespace and conflict-marker checks pass.
Per-file MCP diagnostics remain blocked: both configured endpoints use the core
package search path and report `unknown module prefix 'SolidityBridge'`; this
checkout also lacks `Bridge/.lake`. No Lean pass or combined-build result is
claimed by this merge repair. The coordinator must validate the Bridge package
and run the required combined gates before publication.

### Control-flow integration merge review (2026-10-30)

The pending merge of `7bb843729b9c9dacb3ad70dd439e553c004612f2` into
`204eb1545cbf57e436196e4cba346075515b7279` resolves the shared insertion point
above by retaining both complete documentation blocks verbatim: storage and
arithmetic evidence first, then assembly and control-flow evidence. The
automatically merged module map is retained. Every staged Lean file remains
byte-identical to the incoming branch, and the umbrella retains both parents'
imports. No proof, observation, resource claim or budget is changed by this
documentation repair; historical primary-cgroup and fallback reports retain
their respective scopes.

Conflict-marker, whitespace, qualified incoming module-path and local Markdown
link checks pass. The repository-wide documentation-path check exits 1 with 46
missing references, all independently reproduced against the pre-merge HEAD;
their citing files are unchanged. Neither merged document has a missing Lean
file reference. Independent read-only finder and skeptic dispatches both failed
before review because the agent service reported `no rollout found for thread
id`. These reviews remain pending for the coordinator. No Lean server or build
was run for this repair, and no combined validation pass is claimed. The merge
is left staged and uncommitted for the coordinator's reviews and combined gates.


### Fresh-master memory/control-flow merge repair (2026-10-31)

The pending merge of `89ce50152255d6dc82ab733cecacb903b91e948e` into
`376727392c6a4886783eaf03912ca4ec8d1cbb37` retains the exact union of both
parents' 38 umbrella imports and every conflicting module-map entry. The
instruction-status table keeps the bounded preallocated memory result and its
explicit padding-contract boundary from the memory branch, together with the
published-master fetched-run/control-flow result and its readiness/terminal
gates. Both detailed evidence sections remain. The other 222 staged Lean
files are byte-identical to their pre-repair index content; no theorem,
observation, target, invariant or budget was changed.

Focused import-union, module-path, local Markdown-link, conflict-marker and
whitespace checks pass. The repository-wide documentation-path check exits 1:
46 missing references are independently reproduced in unchanged HEAD files;
two more are independently reproduced in the unchanged incoming
[inline-assembly roadmap](feature-work/inline-assembly.md#groups), which cites
the planned Y01 syntax and SolcJson admission modules. Those incoming roadmap
references remain baseline documentation findings. This merge-review paragraph
originally repeated both absent paths, introducing the two additional findings
repaired below. A whole-index whitespace check also reports existing staged
issues outside these three files
(`ExprExamples`, `Infer`, `Horizon`, `TrustAudit` and `ParseCorpus`); those files
were preserved. The focused three-file whitespace check passes.

Per-file MCP diagnostics were attempted sequentially on the umbrella through
both configured endpoints. Both fail at line 2 with `unknown module prefix
'SolidityBridge'`, using the core package's search path. This is blocked
validation, not a Lean pass. Independent read-only finder and skeptic dispatches
both failed before review with `no rollout found for thread id`; those reviews
remain pending. No full build ran. The coordinator must run Bridge-context
diagnostics, independent reviews and all required combined gates. This repair
is left staged and uncommitted; no publication or combined-validation pass is
claimed. Historical primary-cgroup and fallback evidence retains its original
scope and rejection history.

### Documentation regression repair (2026-10-31)

Attempt 7 validated candidate `d7bbf532c7adc2e8a1f3ec28c1c0ff7519eb58e6`
against base `89ce50152255d6dc82ab733cecacb903b91e948e`: all 14 executable
gates exited 0, but the documentation comparison found two new missing-path
references in the merge-review paragraph above. That paragraph now links to
the existing Y01 roadmap instead of repeating its absent planned module paths,
and corrects its earlier claim that it introduced no findings.

The unchanged `scripts/check-doc-paths.sh` exits 1 with 48 missing and 37
ambiguous references, exactly the retained baseline finding set; only output
ordering differs. Both candidate-only findings are removed, with no baseline
finding removed or added. The local roadmap link and its `groups` anchor
resolve, and `git diff --check` passes. Focused logs and the baseline comparison
are retained under `.lake/doc-path-repair-20261031/`. This documentation-only
repair requires no Lean diagnostics. The coordinator must rerun combined
validation on the repaired tree; the retained executable results belong to
the earlier candidate. Historical resource failures and scope claims above
are preserved.

Independent read-only finder and skeptic reviews found no confirmed defect
in this documentation repair; neither used the Lean server.
