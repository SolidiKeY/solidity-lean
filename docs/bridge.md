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
| `mload`, `mstore`, `mloadAt`, `mstoreAt` | Word-cell to byte-memory relation, address scaling and macro expansion for fixed addresses. |
| `jump`, `jumpi`, `loop` | Assembler from relative/structured control flow to absolute PC and valid jump destinations. |
| `call` | Seven-operand ABI, account/code execution, address truncation, balance bounds and callee behavior corresponding to `accepts`. |
| `revert` | Return-data operands and the driver's halting relation. |

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

To build the independent targets alone, from `Bridge/`:

```sh
lake build SolidityBridge.ModelTheory.LowenheimSkolem \
  SolidityBridge.CallbackTrace SolidityBridge.CallbackModalTrace \
  SolidityBridge.ExternalEvm.StackOps SolidityBridge.ExternalEvm.Obstructions \
  SolidityBridge.ExternalEvm.StorageSlotExamples \
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
