# Impact of the 2026-10-29 scope decisions

This audit lists what each
[user decision](../solidity-scope.md#user-decisions-2026-10-29) affects in
the repository. That covers Lean definitions and theorems, calculus rules,
examples and TestSuite expectations, scripts, documents, and the Codex lanes
whose assumptions change. For each item it says what happens to the existing
proofs and which [roadmap](../coverage-plan.md) group owns the change. It
reopens no decision. It changes no Lean.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285` ("Record
  resource and environment decisions"). Every `file:line` refers to it.
- **Method:** four read-only searches, one per decision cluster: hashes;
  environment and payments; resources; pins, settings and observations.
  Each used `grep`/`sed` only, and no Lean server. Every cited line was then
  re-read at the base, and the claims marked F were checked against the
  refuting theorem.
- **Companion:** the compiler restriction ledger
  [roadmap-g04-restrictions.md](roadmap-g04-restrictions.md). Its R32–R36 and
  its [§8](roadmap-g04-restrictions.md#8-decision-follow-up-2026-10-29) carry
  the decided premise forms. This document does not repeat R-rows; it cites
  them.

**Verdict key.** Every Lean theorem cited stays kernel-checked. A decision
changes which theorems count as evidence for the public claim.

| Mark | Meaning |
|---|---|
| **V** | Valid as a statement about a narrower environment, such as a history-free oracle, the no-callback reading, the gasless machine or a source with a depth cutoff. It may become a special case or corollary of the final theorem. |
| **R** | The definition or statement must change shape to meet the decision. The existing theorem stays true of the old definition, but is not the required statement. |
| **F** | The claim it carries is false under the decided environment: a theorem used as a verdict there is refuted, or a document asserts the opposite of the decision. |
| **U** | Unaffected, or already consistent with the decision. |

## 1. Summary

| Decision | Existing proofs | Main owners | Codex lanes whose assumptions change |
|---|---|---|---|
| G00 Q1 — 30 exclusions approved | U. The ledger and status wording are stale. | G00 | none |
| G00 Q2 — abstract premises | V for every payment and callback result. R for `worldAssumptions` and the acceptance boolean. | S04.03, G22, G43, G47, G51 | diamond-payments, diamond-try |
| G00 Q3 — Osaka | V for the Cancun vector evidence, which must be re-run | G06, G05 | evm-* (vendored EVM pinned to Cancun) |
| G00 Q4 — eight `EvalOrder` combinations, solc 0.8.38 | U for the compiler (it works on elaborated `Prog`). R for the frontend settings. | G05, G13, G53 | none |
| G00 Q5 — `creationCode`/`runtimeCode` | F for reading solc's bytes as the source meaning | G01, G44, G05 | abi-lazy-calldata (none directly) |
| G00 Q6 — fixed point | R: manifest scope and admission | G00, S00, G15, G16/G25 | none |
| G01 Q1 — idealized source | U for the decision itself; R for the "open question" wording | G01 | none |
| G01 Q2 + follow-ups — resource failures | V for the gasless machine and the cutoff source. F for the 1024-frame source cutoff and for "exhaustion ends the session". | G01, S03.03/S03.04, G37.02, G47, G51 | evm-control-flow, memory-loops, memory-internal-calls, revert-outcome-specs, readonly-external, diamond-try |
| G01 Q3 / G04 Q1 — per-run hash premise | V for the symbolic machine and the per-goal calculus premise. R for `Slot`, `PublicCorrectness`. | G27.05, G46.03/G46.05, G01, G51 | evm-storage-slots, evm-byte-memory |
| G01 Q4 — history-dependent callees | V for every no-callback and fixed-table result. F for three public `⊨ᶠ` verdicts. | S04.02/S04.03, G22.02, G42.03, G51 | diamond-payments, diamond-try, readonly-external, revert-outcome-specs |
| G01 Q5 — full observation | V for the bytes-less machine revert. R for the source halt classes. | G38, G21, S04.02 | revert-outcome-specs, abi-lazy-calldata |
| G01 Q6 — `decode` export | R for `PublicCorrectness` | G01, G06 | none |
| G01 Q7 — answers regardless of gas | F for the 2300-gas justification of the no-callback reading | G51.02, G43, G47 | diamond-payments |
| G01 Q8 — whole input | R for `validateSettings` and the open-question wording | G05, G44.02, G01, G42.04 | none |
| G04 Q2 — dangling aliases | V for the compiler's refusal. F for the source's `push(v)` over a recycled slot. | G28, G30, S04.01 | evm-storage-slots, memory-storage-copy |
| G04 Q3 — payments any outcome | V for every payment theorem (history-free table) | G43, G47, S04.03 | diamond-payments |
| Follow-up — sender funds | R for transaction entry | S04.04, G22.05, G50.02 | none |
| Follow-up — precompiles | R for calls to precompile addresses (read from the table) | G23, G31, G47 | readonly-external |

## 2. Per decision

### 2.1 G00 Q1 — the 30 exclusions

| `file:line` | Item | Verdict | Owner |
|---|---|---|---|
| `Solidity/Language/Features.lean:1771` | `Unmodelled` (22 constructors; `blockField` covers 9 fields, so 30 rows) | U | G00 |
| `Features.lean:1880`, `:1910`, `:1936` | `outsideScope`, `Unmodelled.excluded`, `Feature.exclusion_complete`: classification, not approval | U | G00 |
| `scripts/roadmap-g00-scope.py:11`, `:35`, `:337` | `EXCLUSION_EVIDENCE`, `g00_status`: `exclude` still maps to `unresolved` | R (an evidence entry naming the decision) | G00 (g00-manifest-rev) |
| `docs/feature-work/roadmap-g00-scope.md:18–24`, `:563–587` | "30 unresolved" wording, superseded by its own note at `:25` | R | G00 |
| `docs/coverage-plan.md:172` | G00 row: "Unconfirmed exclusions remain unresolved work" | R (none remain unconfirmed) | G00 |

**Events and logs do not conflict.** `logs` stays excluded (`eventLog`,
`Features.lean:1478`). The `Event` of G01 Q5 is the session-event type of the
contracts (`Solidity/Roadmap/Contracts.lean:258`: deployment, call, answer,
transaction), not an `emit` log. `Contracts.lean:241` and
[roadmap-g01-interfaces.md](roadmap-g01-interfaces.md) already say logs are
excluded observations. `emit` keeps evaluating its arguments and erasing the
log (`Features.lean:654–656`).

### 2.2 G00 Q2, G01 Q4, G04 Q3, G01 Q7 — environment, callees and payments

These four decisions act together. Callees and payment recipients outside
the system follow history-dependent strategies with unbounded reentrancy.
Recipients inside the system run their own code. Answers range over all
outcomes whatever gas is forwarded. The no-callback reading must be a proved
special case. Neither `worldAssumptions` nor a payment-acceptance boolean is
an approved premise.

**Source environment**

| `file:line` | Declaration | What it assumes | Verdict | Owner |
|---|---|---|---|---|
| `Solidity/Language/Features.lean:220`, `:1373` | `worldAssumptions` row | the premise G00 Q2 did not approve | R (replace or propose again) | G00 → S04.03, G22, G47 |
| `Features.lean:1183` | `callbackSemantics` row | the modality is chosen by option | R (callbacks become the default, no-callback a lemma) | G00 |
| `Solidity/Semantics/State.lean:110` | `TTx.ext` | a fixed per-transaction table: identical calls read one entry, with no history, and a callback leaves `tx` unchanged | R (a history-dependent strategy) | S04.02/S04.03, G22.02 |
| `Solidity/Semantics.lean:111` | `sendKey` | a payment answer depends on address and amount only | R | S04.03 |
| `Solidity/Semantics/Run.lean:164` | `State.canPay` | funds plus a table lookup; no entry means accept | R (any outcome, history-dependent) | G22.02, G43 |
| `Run.lean:877` | `TRun.tryCall` | address `0` reverts (kept by G01 Q4); every other receiver, precompiles included, is read from the table | R for precompiles and history; U for address `0` | G22.01, G23 |
| `Solidity/Semantics/Callback.lean:153` | `StateInv.pay` | the no-callback switch as a premise | R (a proved special case) | G22.02, G51 |
| `Callback.lean:493–542` | `ExecS` transfer and send constructors | invariant havoc for the callee; `tx` fixed | V for the box; under unbounded reentrancy the invariant `J` must be a proved contract invariant | G22.02, G42.03 |
| `Callback.lean:1259`, `:1282`, `:1504` | `Prog.exec_run`, `Frames.exec_run`, `ExecP.eq_run` | the deterministic run over the fixed table | V, and the seed of the "no-callback is a special case" lemma | G51.01 |
| `Solidity/Semantics/RunFrame.lean:1158` | `State.havoc` | own balance arbitrary, not tied to the ledger | V (a sound over-approximation, too loose for diamonds under the ledger reading) | G22.02 |

**Compiler and machine** (G04 R32, R33)

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Evm/Machine.lean:336`, `:574` | `Machine.accepts`, the `CALL` step | R (account execution or a shared history-dependent strategy) | G43, G47 |
| `Machine.lean:346` | `Machine.init` (every payment accepted) | V | G47 |
| `Solidity/Evm/Sim.lean:223`, `:226` | `funds`, `oracle` fields | R (a joint world/payment relation) | G43 |
| `Solidity/Evm/Stmt.lean:892` | `transfer_sim` | V | G43 |
| `Solidity/Evm/Correct.lean:1089`, `:1181`, `:1197` | `compile_correct`, `Sim.init`, `compile_storage` | V. The R32 disjunct is still to discharge. | G43, G49 |
| `Bridge/SolidityBridge/Evm.lean:154`, `:172`; `Bridge/SolidityBridge/CompilerSimulation.lean:28` | Bridge results under `Prog.pays P = false` | V | G43, G47 |
| `Solidity/Evm/Examples.lean:268` | `transfer_refused`, under a hand-written `accepts` | R when `accepts` goes | G47 |

**Calculus and examples**

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Calculus/CallbackHolds.lean:153` | `TransferSem`: its docstring justifies no-callback by the 2300-gas stipend | F for the justification under G01 Q7. The definition is U. | G51.02 |
| `CallbackHolds.lean:174`, `:329`, `:334` | `validT_noCallback`, `validC_false_iff`, `validT_noCallback_iff` | V | G51 |
| `Solidity/Calculus/Rules.lean:735`, `:746`, `:754`, `:899` | `transferNoCallbackBox`, `sendNoCallbackBox`, `sendNoCallbackDiamond`, `tryCallNoCallbackBox` | V (sound for `holds`, the reading where callees keep the state) | G51.01 |
| `Rules.lean:1026`, `:1063` | `tryCallDiamond`, `transferDiamond` (close to `false`) | U (conservative) | G51; lanes diamond-try, diamond-payments |
| `Solidity/Calculus/CallbackRules.lean:25` | `CallbackTaclet` | V (fixed table); `transferWithCallbackDiamond` stays unclaimed | G51.01 |
| `Solidity/Calculus/CallbackSound/Rules.lean:485`, `:522`, `:565`, `:728`, `:841` | `holdsC_transferCb`, `holdsC_sendCb`, `holdsC_tryCb`, `holdsC_trySelfCb`, `holdsC_sendDet` | V | G51.01 |
| `Solidity/Examples/Tactics/Callback.lean:112`, `:120` | `withdrawUnsafe_valid` (`⊨ᶠ`), `withdrawUnsafe_noCallback` | F as a verdict for the decided environment: `withdrawUnsafe_withCallback` (`:252`) refutes it under callbacks | G51 |
| `Callback.lean:287` | `withdrawCall_valid` (`⊨ᶠ`, callee keeps the state) | F as a public verdict | G51 |
| `Solidity/Examples/Tactics/TryCatch.lean:269` | `selfCall_valid` (`⊨ᶠ`) | F as a public verdict: `selfCall_noCallback` (`:288`) refutes even the no-callback reading | G51 |
| `Solidity/Frontend/Testing.lean:226` | TestSuite obligations stated as `ValidT` with an explicit `TransferSem` | V; restate at the callback reading | G53, G51 |
| `Solidity/Examples/Tactics/SelfCall.lean:155` | `noCodeAtZero` | U (assumption kept) | — |

**Documents:** [options.md](../options.md) O1/O7 (the stipend justification),
[correctness.md](../correctness.md) "Payments" (table acceptance),
[function-specs.md](../function-specs.md) (invariant only at `withCallback`).
Each is R under these decisions, owned by G51/G43. None is edited here; the
§4 payment-wording fix in options.md O4 is a different, factual correction.

### 2.3 Follow-ups — sender funds, precompiles, `this` and own balance

| `file:line` | Declaration | What it assumes | Verdict | Owner |
|---|---|---|---|---|
| `Solidity/Semantics/Lifetime.lean:50` | `World.enter` | credits `msg.value` with no sender ledger | R (an unaffordable transaction is invalid and never executes) | S04.04, G50.02 |
| `Solidity/Semantics/ContractWorld.lean:134` | `World.enter` | an unaffordable transaction gives `.error .revert` | R (invalid, not a revert) | S04.04, G22.05 |
| `Solidity/Semantics/Deploy.lean:22` | fresh deployment state | `selfBalance := tx.msgValue` | R (own balance follows the ledger, prefunded addresses included) | G44.03 |
| `Lifetime.lean:79` | `World.accepts` (`selfAddress = s.address`) | `this` from deployment | U | — |
| `Run.lean:877` | `TRun.tryCall` (see §2.2) | precompile addresses answered from the table | R (their EVM definitions; the crypto ones through the fixed functions) | G23, G31, G47 |
| `Solidity/AST.lean:933` | `HashKind` (`sha256`, `ripemd160`, `ecrecover` builtins) | fixed functions | U | — |
| `Solidity/Roadmap/Contracts.lean:263` | `Event.call` ("outside the system") | precompile calls would be environment events | R (precompiles are not environment code) | G01 |

[lifetime.md](../lifetime.md) and [semantic-gaps.md](../semantic-gaps.md)
(the precompile note) are R; the address-0 assumption there is U.

### 2.4 G01 Q1, Q2 and the resource follow-ups

The source is idealized: unbounded fuel and recursion. Running out of gas,
including the 1024 call-depth limit and gas exhaustion inside a callback, is
a failure the source allows. A nested external frame may revert to its
caller, which continues. A transaction may revert, and the session continues
with the next one. Today every resource stop (`exhausted`, the recursion
bottom, a push at `2^256`, the machine's `.fault`) is a halt that ends a
prefix and that both modalities accept.

| `file:line` | Declaration | What it assumes | Verdict | Owner |
|---|---|---|---|---|
| `Solidity/Roadmap/Contracts.lean:240` | outcome-section docstring: "Exhaustion of excluded resources is not an observation (it ends a prefix)" | exhaustion ends the session | F for gas and call depth | G01 (g01-contracts-rev) |
| `Contracts.lean:104–112` | `Lang` (`Res`, `Admissible`, `sem`) | one resource bound per session | R. Allowed failures must enter through `Env` (or `sem` becomes a relation), because `sem` is a function. | G01, G06 |
| `Contracts.lean:302`, `:319` | `SourceSpec.Idealized`, `SourceSpec.NonVacuous` | `Idealized` is decided (drop "open question"); a revert witness becomes trivial once any transaction may revert | R | G01, G07, S05 |
| `Contracts.lean:382` | `EvmSpec` (resources "gas, memory, stack and code size") | code size is a resource | R (drop code size: EIP-170/EIP-3860 idealization) | G01, G06 |
| `Contracts.lean:455` | `typedRunPrefixes` | `.exhausted` completes as an error | R (a frame or transaction revert) | G01, S03.04 |
| `Solidity/Syntax/Scoped.lean:469` | `recDepth := 1024` with `recUnroll`, `Prog.recBase` | internal recursion cut at 1024 frames | F under G01 Q1/Q2: frames live in memory and only gas bounds depth | S03.03/S03.04, G37.02 |
| `Solidity/Semantics/Run.lean:58` | `THalt` (`exhausted`) | a halt both modalities accept | R (a failure the caller sees) | S03.04, G38 |
| `Run.lean:876` | `TRun.tryCall` docstring: "one that exhausts or diverges halts the caller alike" | a nested exhaustion is not caught | F under the nested-frame follow-up: the caller sees a revert and continues | G22, G42, S03 |
| `Solidity/Semantics/Callback.lean:1119` | `ExecS.trySelfHalt` use | as above | F (same) | G22, G42 |
| `Solidity/Semantics/Storage/Ops.lean:916` | `Storage.full` (push at `2^256` → `exhausted`) | a length cap as a resource stop | V; the transaction-level reading becomes an allowed revert | S04.01, G30 |
| `Solidity/Semantics/RunFrame.lean:34` | `Modality.onTHalt` (the diamond accepts `exhausted`) | decision 15 of [intrinsic.md](../intrinsic.md) | V for the intrinsic run; the completion transfer of G51 must exclude it | G51 |
| `Solidity/Calculus/Recursion.lean:163` | the bottom frame meets every contract | the 1024-frame unrolling | R (no bottom once the cutoff goes) | G51, S03.04 |
| `Solidity/Examples/Tactics/Recursion.lean:301` | the countdown diamond, true because of the bottom frame | the cutoff | R (needs a termination argument) | G51, G53 |
| `tests/upstream/RecursionResource.lean:12` | `bottom_exhausted` | the cutoff exists | F once the cutoff is removed (obsolete) | S03, G52 |
| `Solidity/Tools/Upstream.lean:296` | `exhausted` reported as blocked, never as an EVM failure | — | R (may match an empty-data revert) | G52, G53 |
| `Solidity/Evm/Machine.lean:359` | `Out` (`.fault` for divergence); no gas | the gasless machine | V | G45–G47 |
| `Solidity/Evm/Compile.lean:298` | `assumeFalse ⇒ none` | exhaustion outside the fragment | V | S03.04 |
| `Solidity/Evm/MemoryCompile.lean:51` | `frameNeedProg` | frames in memory | U (consistent with G01 Q2) | G32, G37.01 |
| `Solidity/Language/Features.lean:1483` | `machineResources` row text | exhaustion ends a prefix | R | G00 |

G04 rows: R08 becomes F at the source (the cutoff), R27, R38 and R39 are R,
and R25's capacity premise can be discharged as an allowed out-of-gas
revert. R24 (`Panic(0x41)` at `2^64`) is U.

**Documents:** the "Recursion depth" row of
[solc-alignment.md](../solc-alignment.md#where-the-interpreter-follows-solc-not-key)
is F (it states a 1024-frame source bound). Its "Gas" and "Array lengths"
deltas, [lifetime.md](../lifetime.md), [kernel-port.md](../kernel-port.md)
"Recursion", and decision 15 of [intrinsic.md](../intrinsic.md) are R. The
G01 Q1/Q2/Q7 text of [roadmap-g01-interfaces.md](roadmap-g01-interfaces.md)
is R for its owner. None is edited here, because each rewrite depends on the
G01/S03 restatement.
`scripts/evm-reference/README.md` already disables the code-size caps
(U).

### 2.5 G01 Q3 / G04 Q1 and G00 Q2 — hashes

The source already treats hashes as fixed functions, not environment
inputs (`keccakBytes`, `HashKind.apply`, `Solidity/Semantics/Heap.lean:466–530`).
No `Function.Injective` hypothesis on a hash exists anywhere. The decision
falls on the machine, the contracts and the calculus bridge.

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Evm/Machine.lean:99`, `:106` | `Slot`, `Slot.add`: global injectivity and no wrap, built into the type | R (numeric slots under the per-run premise) | G46.03, G46.05, G27.05 |
| `Solidity/Evm/Layout.lean:212`, `:310` | `Slot.add_inj`, `occ_entries_disjoint` | V on the symbolic machine; on words, a lemma under the per-run premise | G27.02, G27.05 |
| `Solidity/Evm/Repr.lean:85`, `:805` | `ReprAt.map`, `OccAt.kind_unique` | R with `Slot` | G27.02, G27.05 |
| `Solidity/Evm/Correct.lean:1089` | `compile_correct` (symbolic machine) | V; the G46 bridge carries the premise | G46.03, G49 |
| `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean:15`, `:65` | `no_injective_slot_encoding`, `slot_add_wrap_mismatch` | U (the evidence that no global premise is possible) | G46.05 |
| `Solidity/Calculus/HashPremise.lean:87`, `:117` | `Fml.HashFree`, `Fml.ValidH`: a per-goal premise over the formula's own hashes | V. It is not the per-run premise; specification transfer must bridge the two. | G51.02 |
| `Solidity/Calculus/Decision.lean:724`; `Solidity/Calculus/HashSwap.lean:828` | `decideHashK_sound`, `Fml.swPrefix_validH` | V (verdicts are `ValidH`) | G51.01/G51.02 |
| `Solidity/Roadmap/Contracts.lean:410`, `:423`, `:435` | `PublicCorrectness`, `SpecTransfer`, `PublicCorrectness.transfer`: no hash premise | R (add the per-run premise; re-prove `.transfer`) | G01 (g01-contracts-rev) |
| `Solidity/Language/Features.lean:998` | `keccakBuiltin` row (`abstract`) | U in substance; "abstract" now means a fixed parameter | G00 |
| `Solidity/Keccak.lean`, `Solidity/Hashes.lean`, `Solidity/Secp256k1.lean` | the fixed functions | U (the approved instantiation) | — |

The random-oracle bound has no Lean artifact. It is this batch's
hash-collision-bound task. The per-run predicate has no artifact either; it
is G01's (statement) and G27.05/G46.05's (use). Documents to restate for
their owners: [roadmap-g01-interfaces.md](roadmap-g01-interfaces.md) ("no
hash-injectivity premise") and [bridge.md](../bridge.md) (§ on injective
encodings). [compiler-verification.md](../compiler-verification.md) now
points at the decision (§4 below).

### 2.6 G00 Q3 — Osaka

| Location | Pin | Verdict | Owner |
|---|---|---|---|
| `Bridge/vendor/EvmYul/Wheels.lean:148` | `TargetSchedule := "Cancun"`; the vendored EVM has no `CLZ` (EIP-7939) | R; the Bridge word lemmas do not depend on the fork (U) | G06 (g06-osaka-repin) |
| `scripts/check-abi-vectors.mjs`, `check-call-exception-vectors.mjs`, `check-modifier-frames.mjs`, `check-recursive-types.mjs`, `check-self-power-data.mjs`, `check-operator-aliases.mjs`, `check-slice-copies.mjs`, `check-public-getters.mjs`, `check-transient-world-vectors.mjs`, `check-transient-vectors.mjs`, `check-source-admission.mjs`, `check-abi-hex-call.mjs` | `evmVersion: 'cancun'` and `Hardfork.Cancun` | V as Cancun evidence; re-run on Osaka | G06 (g06-osaka-repin), G05 |
| fixtures under `tests/solc/`, `tests/upstream/` | `"evmVersion": "cancun"` records | R (regenerate) | G05 |
| `Solidity/Frontend/Source.lean:169` | `validateSettings` accepts every listed EVM target | R (narrow to Osaka for the public profile) | G05 |
| `scripts/solidity-upstream.mjs`, `scripts/evm-reference/replay.mjs` | already Osaka | U | — |

### 2.7 G00 Q4 — `EvalOrder` and the solc pin

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Syntax/Raw.lean:392` | `EvalOrder` (three flags, eight combinations) | U | S02/S03 |
| `Solidity/Frontend/Import.lean:666` | `legacyOrderOverride`; modern imports reach only two combinations | R (settings must express all eight) | G05, G13 |
| `Solidity/Evm/Correct.lean:1089` | `compile_correct` over elaborated `Prog` | U (holds for every order) | G26 |
| `Solidity/Frontend/Source.lean:154` | `parseCompiler` with the 0.8.34 and 0.8.38 pins | R (0.8.34 for SolKey compatibility only) | G05, G53 |
| `scripts/solc-ast.mjs`, `scripts/solc-unit.mjs`, `.github/workflows/lean.yml` | 0.8.34 defaults | R | G05, G53 |

### 2.8 G00 Q5 — `creationCode`/`runtimeCode`

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Frontend/Source.lean:359` | `readCompilerCode`: solc's `bytecode`/`deployedBytecode` from the fixture | F (the decision makes these this compiler's bytes) | G44.02, S04.02 |
| `Source.lean:287` | `requireCompilerCode`; the elaborator inlines the bytes as a literal | R (the source takes the `Artifact` table as a parameter) | G44.02, G07 |
| `Solidity/Roadmap/Contracts.lean:373`, `:281` | `Artifact` exists; `SourceSpec` has no `Artifact` parameter | R | G01 (g01-contracts-rev) |

### 2.9 G00 Q6 — fixed point

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Language/Features.lean:1488` | `fixedPoint`, scoped `upstream` | R (manifest change; the 174 in-profile count changes) | G00 (g00-manifest-rev) |
| `Solidity/Frontend/SolcJson/Admission.lean:159` | fixed types classified and refused | R | S00, G15 |
| — | reference semantics beyond solc 0.8.38 | missing (this batch's fixed-point-semantics task) | S02, G16, G25 |

### 2.10 G01 Q5, Q6, Q8 — observation, state transfer, system boundary

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Roadmap/Contracts.lean:245`, `:258` | `Outcome` (revert bytes), `Event` | U | G01 |
| `Solidity/Evm/Machine.lean:359` | `Out.revert` without bytes | V (coarser than the decided observation) | G38 (revert-outcome-specs) |
| `Solidity/Semantics/Run.lean:58` | `THalt`: panics 0x11/0x12/0x31/0x32 collapse to `.revert` | R | S04.02, G21 |
| `Solidity/RevertBytes.lean` | selectors and `Panic` encoding | U (reusable) | S04.02 |
| `Contracts.lean:410` | `PublicCorrectness`: no `decode` conjunct; `EvmSpec` has no world type | R | G01, G06 |
| `Solidity/Frontend/Source.lean:183` | `validateSettings`: "library linking is not in this source boundary" | R (G00 disagreement 6) | G05, G44.02 |
| `docs/solidity-features.json` | `externalLibraryCalls` (abstract) | R (linked libraries are in the system) | G00, G42.04 |

### 2.11 G04 Q2 — dangling aliases

| `file:line` | Declaration | Verdict | Owner |
|---|---|---|---|
| `Solidity/Evm/Compile.lean:87`, `:161` | `Frag.dropFragile`, `bindFl` (R36) | V (a refusal to remove) | G28, G30 |
| `Solidity/Evm/Sim.lean:216` | `Sim.fragile` (live elements only) | V | G28 |
| `Solidity/Semantics/Storage/Ops.lean:782` | `pushSlot`: an empty push exposes the recycled slot as solc leaves it | U | S04.01 |
| `docs/solc-alignment.md` "`push` over a recycled slot" | `push(v)` lays a struct or array on fresh slots (`SVal.strip`), dropping what solc keeps | F (a source/solc delta now in profile) | S04.01, G30 |
| `Solidity/Calculus/Rules.lean:704`, `:708` | `storagePopSave`, `storagePopSaveMappingElement` | U | G51 |
| `Solidity/Examples/Tactics/StorageDangling.lean`, `Solidity/Examples/Tactics/Dangling.lean` | dangling-survives theorems; docstrings say "undefined" | V; reword docstrings | G53 |

[solc-alignment.md](../solc-alignment.md#arrays-past-their-end) still
classifies the dangling writes as compiler-specific migration cases. That
wording is R for S04.01; it is not edited here, because the
`push(v)` delta must be fixed first.

## 3. Codex lanes whose assumptions change

| Lane | Assumption that no longer holds |
|---|---|
| diamond-payments | Acceptance is a history-free table or boolean (`canPay`, `Sim.oracle`, `Machine.accepts`); `transferDiamond`'s rationale; the R32 disjunct |
| diamond-try | A self-call that exhausts halts the caller; `holdsC_tryCb`/`holdsC_trySelfCb` read a fixed table |
| readonly-external | External frames cannot fail on resources; precompile addresses answered by the table |
| revert-outcome-specs | Gas and call-depth failures are reverts the caller sees; answers are history-dependent; panic codes must be kept |
| evm-control-flow | `.fault` stands for divergence; on Osaka a non-terminating transaction is an out-of-gas revert and the session continues (R38) |
| evm-storage-slots | Symbolic slots with global injectivity (R34); must not add a global encoding; dangling aliases in profile (R36) |
| evm-byte-memory | `KECCAK256` from the stack (R35); Osaka fork |
| memory-loops | Divergence/prefix correspondence (R38) under per-transaction revert |
| memory-internal-calls | Frames in memory with no depth cutoff (G01 Q2) |
| memory-storage-copy | `occ_*_disjoint` holds only on symbolic slots |
| abi-lazy-calldata | Exact ABI bytes are the observation (G01 Q5) |
| function-ref-args | Recursion through function values has no cutoff |

## 4. Stale documentation

Fixed here, in Markdown outside `Solidity/Evm/**` (G04 §4):

- [compiler-verification.md](../compiler-verification.md):
  - the `compile_storage` block now has disjunct (iv) and the `Fin W`/`hbalance` signature;
  - `compile_net` quantifies over `Fin W`;
  - the payment disjunct is described as a stale weakening no proof reaches;
  - loops are admitted (`LOOP`), and copy loops are simply not emitted;
  - the loop-payment refusal is explained by `TurnRel`;
  - the slot and `accepts` bullets point at the decisions.
- [assurance.md](../assurance.md): the per-allocation premise is
  distinguished from the public `AllocationInput` premise.
- [solc-alignment.md](../solc-alignment.md#where-the-interpreter-follows-solc-not-key):
  the `transfer` row now says both sides revert on refusal.
- [options.md](../options.md) O4: the `transfer` diamond rationale no longer
  says the run books a refused payment.

**Child obligations: Lean docstrings** (left to their owners):

| Location | Stale text | Owner |
|---|---|---|
| `Solidity/Evm/Compile.lean:25–26` | "no `send`/`try`/loop" (loops are admitted at `:307`) | Evm owners (G24) |
| `Solidity/Evm/Compile.lean:228` | `Stmt.pushes`: "since the fragment has no loop" | Evm owners |
| `Solidity/Evm/Stmt.lean:889–891`; `Solidity/Evm/Correct.lean:976–981` | `transfer_sim`; `stmt_sim` (`Correct.lean:984`): "the machine alone reverts" on refusal | Evm owners, G43 |
| `Solidity/Evm/Correct.lean:1077–1081`, `:1185–1192` | `compile_correct`, `compile_storage` docstrings, same | Evm owners, G43 |
| `Solidity/Evm/Repr.lean:771` | cites `TyCtx.dropFragile`; the definition is `Frag.dropFragile` | Evm owners |
| `Solidity/Theorems.lean:264` | `compiler_correct` docstring, same payment wording | G43 / G55 |
| `Solidity/Calculus/Rules.lean:1061–1062` | `transferDiamond` rationale: "reverts the machine alone" | G51 (diamond-payments) |

## 5. Questions

None. Every decision can be met as stated. Two choices are design work for
the owners, not scope questions:

- how allowed resource failures enter `Lang` (through `Env`, or `sem` as a
  relation): G01;
- how `ValidH` (per goal) relates to the per-run premise in specification
  transfer: G51.02.

## 6. Handoff

- **Base:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`.
- **Done:**
  - this audit;
  - the G04 ledger update (R32–R36, §6 answers, §8);
  - the Markdown fixes of §4.
- **Checked:**
  - every cited line re-read at the base;
  - the F verdicts against their refuting theorems (`withdrawUnsafe_withCallback`, `selfCall_noCallback`) or decision text;
  - `scripts/check-doc-paths.sh` (no new missing reference).
- **Lean:** none changed, no Lean server used, no build.
- **Child obligations:**
  - every R and F row above, by its owner;
  - the docstring table of §4;
  - the G04 §8 handoff.
