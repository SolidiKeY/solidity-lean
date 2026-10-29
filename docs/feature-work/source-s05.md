# Source semantics S05: composition, ledger, controls

Lane V04, checkpoint 5 (roadmap row S05 in [coverage-plan.md](../coverage-plan.md)).
It composes S00–S04 into G01's interface (`Solidity/Roadmap/Contracts.lean`)
and records the reviews and the handoff of the whole lane. The earlier
checkpoints are in [source-s02.md](source-s02.md), [source-s03.md](source-s03.md)
and [source-s04-state.md](source-s04-state.md#s0404-transactions).

## Modules

| Module | Content |
|---|---|
| `Solidity/Source/Semantics.lean` | `SrcProg`, `sessionGo`, `sessionFrom`, `sessionAt`, `sessionAt_consistent`, `sourceLang` |
| `Solidity/Source/Ledger.lean` | `semExprCoverage`, `semStmtCoverage` and their theorems |
| `Solidity/Source/SemanticsExamples.lean` | Every control of the lane |

## Composition

`SrcProg` is a program at the source: an elaborated `Program`, the
pipeline, the fixed parameters and the deployed contract.

`sessionFrom P env addr n` runs a session at horizon `n`:

1. It deploys the main contract at `addr` (S04.04), at the least
   completing horizon up to `n`.
2. It then runs up to `n` environment actions. Credits are recorded and
   credited to instances. Requests are transactions, each at its least
   completing horizon.
3. It returns G01's `Prefix`:
   - **events**: the deployment, then the events of each completed
     transaction;
   - **final observation**: the last outcome, once the environment has no
     more actions.

`sessionAt` takes `addr` to be the creation address
`Fixed.createAddress deployer deployNonce`. Each transaction's new events
are appended to the session's own record, so the record only grows by
construction.

`sessionGo_mono` proves that a larger horizon extends the prefix and that
a completed prefix is final. `sessionAt_consistent` is therefore G01's
`Prefixes.Consistent`, and `sourceLang E : Lang Event Outcome` has:

| Field | Value |
|---|---|
| `Prog` | `SrcProg E` |
| `Env` | `SessionEnv` |
| `Res` | `Nat`, the horizon |
| `Allowed` | `SessionEnv.Allowed` |
| `Admissible` | trivial |

What `sourceLang` does not give G01 (also under `limitations:`):

- **Failure points.** Resources are horizons only. The user decisions
  require that any external frame or transaction may fail (gas, the depth
  limit apart from 1024 frames), and G01's `Failures` and `withFailures`
  need them. They are not modelled.
- **Stuck runs.** A `stuck` run shows as an unfinished prefix,
  indistinguishable from divergence. A progress theorem would rule it out.
- **Events of unfinished transactions.** A transaction that never
  completes (an endless reentrancy loop, say) shows none of its events.
  Showing them needs horizon monotonicity of the events, which is not
  proved.
- **Request validity.** `Lang.Affordable` (unaffordable requests are
  dropped) and `Lang.PrecompilesFixed` (precompile addresses are not
  environment accounts) are not met.
- **`SourceSpec`.** It is not instantiated: `Parses` is lanes V05 and
  V06, `meaning` needs an elaborator from `Resolution` to `Program`, and
  `stipendFits` is G06 Q3.

## Ledger

`Ledger.lean` checks the full source-constructor ledger against S01's
coverage, which classifies every `Syn` expression and statement
constructor without a wildcard and gives each typed one a derivation
(`TypingExamples.exprCoverage_typed`):

- `semExprCoverage_total` and `semStmtCoverage_total`: every expression
  and statement constructor has a semantic status;
- `semExprCoverage_of_typed` and `semStmtCoverage_of_typed`: every
  constructor S01 types is `evaluated`. Its derivations elaborate to
  `RExpr`/`RStmt`, and the interpreter has an arm for every constructor of
  those (no wildcard; Lean's exhaustiveness check);
- `semExprGaps_spec`: the gaps (`slice`, `callOptions` beyond `value`,
  `metaType`, `new`, `inlineArray`, `elemType`) are exactly the
  constructors S01 defers;
- among statements, `declTuple` and `try` are gaps, and `assembly` is
  excluded apart from the canonical rethrow.

"Evaluated" is a classification, not progress. An arm can be `stuck` on
some inputs:

- dynamic ABI decoding;
- calldata references;
- `fallback` with parameters;
- nested-array copies;
- the ABI of user-defined value types and external function types;
- function-typed defaults.

These are recorded in [source-s02.md](source-s02.md#what-s02-does-not-do)
and [source-s03.md](source-s03.md#what-s03-does-not-do).

## Well-formedness and progress interfaces

Well-formedness of the state is intrinsic:

- values carry their ranges, enum bounds and locations (`Val`, S04.01);
- storage is typed by its layout (`Storage D L`);
- memory writes keep each object's type (`Heap.write_ty`);
- every interpreter step builds values only through these types, so
  preservation holds by construction.

What is not intrinsic is checked at run time and fails as `stuck`. That
covers layout agreement (`Env.cellTy` against a path's static type), memory
object types, and frame shapes.

No progress theorem is proved, so the absence of `stuck` is an obligation:
for a well-formed elaborated program, no horizon ends `stuck`. The controls
show non-stuck completion on each program they run.

## Controls

All controls are in `Solidity/Source/SemanticsExamples.lean` and are
checked by kernel evaluation (`decide`, `decide +kernel`). Each comes with
the wrong result it excludes.

The required behaviour controls:

| Theorem | Statement |
|---|---|
| `reentrant_callback`, `no_callback` | a reentrant callback |
| `revert_rolls_back`, `revert_rolls_back_transient`, `transient_cleared` | a revert rolling back storage and transient state |
| `modifier_twice_legacy`, `modifier_twice_viaIR`, `modifier_once` | a modifier with two placeholders |

Further controls:

| Theorem | Statement |
|---|---|
| `outside_revert_rolls_back` | a call out answered with a revert undoes its successful callback's write; the events stay |
| `static_callback_refused` | a callback during a static call cannot write |
| `ctor_order_legacy`, `ctor_order_viaIR` | constructor order per pipeline |
| `session_runs` | a full session: deployment then `g()`, two events, final outcome `12`; nothing at horizon 2 |
| `horizon_stable`, `horizon_short` | the same outcome at horizons 20 and 40; none at 3 |

The S02 controls are in [source-s02.md](source-s02.md#controls-soliditysourcesemanticsexampleslean).

### Upstream evidence

The modifier controls reproduce the pinned semantic tests
`test/libsolidity/semanticTests/modifiers/function_modifier_multi_invocation.sol`
(legacy: `f(true) -> 2`, `f(false) -> 1`) and `…_viair.sol` (via IR: `1`
and `1`) from `tests/upstream/solidity-0.8.38.tar.gz`.

## Review

A read-only finder and a separate read-only skeptic reviewed checkpoints
1–5 together, after the first complete version (commit `3419665`).
Neither used the Lean server.

### Confirmed and fixed

| Finding | Fix |
|---|---|
| A call out answered with a revert kept its debit and its callbacks' writes (finder 1) | `callAddr` marks the journal before the call and rolls back on a revert answer; `outside_revert_rolls_back` |
| Legacy evaluated base-constructor arguments before the initializers (finder 2, skeptic 13) | Legacy runs the initializers, then collects the arguments, then the bodies; via IR collects the arguments first |
| No `extcodesize` check; short return data and short call data read as zeros (finder 3, 10; skeptic 8) | `extCall` reverts on a codeless non-instance target and on return data shorter than its static returns; `dispatch` reverts on short call data |
| A callback during a static call could write (finder 4, skeptic 10) | `envLoop` carries the pending call's static flag into callbacks; `static_callback_refused` |
| A non-`payable` `fallback` accepted value (finder 5) | `Decl.specialPayable` |
| Modifiers were not dispatched virtually (finder 6) | `Glob.dispatchMod` |
| `transfer` discarded the callee's revert data (finder 8) | It forwards the data |
| `bytes` to `bytesN` was stuck (finder 9) | `convExplicitRV` reads the bytes and cuts or pads them |
| `St.fnLocals` was not restored after a caught halt (finder 12) | `runMods` restores it before re-raising |
| Callbacks ran one frame too shallow (finder 16, skeptic 15) | Callbacks run at the pending call's depth + 1, i.e. two below the caller |
| Code was installed before construction (finder 17) | The code is set after a successful construction; a deployment adds to an existing balance (finder 20) |
| A self-call with value skipped the balance check (finder 21) | Checked |
| Docstrings overclaimed: "instantiates G01's Lang", horizon independence, a "canonical choice" (skeptic 2, 4, 6) | The docstrings, [source-s02.md](source-s02.md) and the coverage-plan status now state the limits |
| The ledger's wording overclaimed and used an unrestricted `simp` (skeptic 12) | "Evaluated" is defined as a classification; `semExprGaps_spec` is now a `rfl` check |
| No non-vacuity control for sessions (skeptic 14) | `session_runs` |
| `source-s05.md` was missing (skeptic 16) | This document |

### Recorded, not fixed

These are listed under `limitations:`.

- **Typing.** Derivation uniqueness, and an elaborator from `Resolution`
  to `Program` (skeptic 6, finder 13): `Elaborated` constrains only the
  carried bodies. Constructors, initializers, constants, base arguments
  and modifier invocations are resolved data without a derivation link.
  Q1 asks about the literal typing.
- **`sourceLang` against G01** (skeptic 1, 2, 3, 5, finder 14, 23): no
  failure points (gas, frame failures), the stipend rule, sender-funds
  validity, precompile addresses, stuck runs read as divergence, and no
  events from unfinished transactions.
- **Horizon independence** (skeptic 4): not proved.
- **Getters** (skeptic 7): public state-variable getters are not
  dispatched; a call to one reaches `fallback` or reverts.
- **ABI** (finder 7, 11; skeptic 11): struct parameters' signatures,
  user-defined value types and external function types, dynamic
  parameters and returns, and coder v1 under legacy.
- **Constructors** (finder 5): `deploy` does not refuse value to a
  non-`payable` constructor.
- **Legacy `addmod`/`mulmod`** (finder 15): the zero-modulus check runs
  after all three arguments.
- **Static frames** (skeptic 10): `emit` is allowed; value in a static
  frame returns a revert to the caller instead of failing the frame.
- **Smaller items**: function-typed defaults (finder 19), log topics
  (finder 24), the value of `s = m` for a storage reference (finder 25),
  and a credit's event recorded even when the credit fails (skeptic 15).
- **Not connected to the journal laws** (skeptic 17):
  `rollback_run` and `undoN_run` are not linked to `enterInstance` in a
  theorem. The rollback controls check them on runs.
- **Negative controls not added** (skeptic 14): the depth limit,
  `send`/`transfer`, `receive`/`fallback`, a via-IR parameter restart,
  base arguments, and return decoding.

### Answered

- `reentrant_callback` is a genuine callback through `envLoop` and
  `enterInstance`; the skeptic confirmed it.
- The modifier semantics matches upstream (both reviews).
- The [solc-alignment.md](../solc-alignment.md#modifier-placeholder-frames)
  wording "incoming return slots are passed" disagrees with upstream
  `function_modifier_multi_invocation_viair.sol`, which the lane follows.
  It is flagged for that document's owner, not edited here.

## Handoff (S05)

**Checkpoint status.**

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 | partial | `Elaborated`, `RBody.ofDerivation_typed`, `Env.fieldTy?_of_fieldAt`, the closed typing gaps; uniqueness not proved (Q1) |
| 2 | done, with the gaps listed | `wrapBits_mem`, `intRes_overflow`, `intRes_unchecked`, `intBin_divZero`; controls `add_overflow_*`, `div_by_zero`, `order_*`, `short_circuit` |
| 3 | done, with the gaps listed | `firstDone_mono`, `firstDone_spec`, `firstDone_none_iff`; controls `modifier_*`, `ctor_order_*`, `horizon_*` |
| 4 | done, with the gaps listed | controls `revert_rolls_back*`, `commit_keeps_storage`, `transient_cleared`, `reentrant_callback`, `outside_revert_rolls_back`, `static_callback_refused` |
| 5 | partial | `sessionGo_mono`, `sessionAt_consistent`, `sourceLang`, `semExprCoverage_of_typed`, `semStmtCoverage_of_typed`, `semExprGaps_spec`, `session_runs`; progress and `SourceSpec` open |

**Gates.**

- Lean diagnostics are clean on every touched Lean file.
- No `sorry`, new axioms, `native_decide`, `implemented_by` or
  `maxHeartbeats` changes. The pins in `SemanticsExamples.lean` are
  recorded with `node scripts/check-axiom-pins.mjs --write`.
- `TrustAudit.lean` has a source-semantics block (21 theorems).
- `node scripts/check-g07.mjs --log` over a full `./run-lean.sh` (head
  `6269063`) reports 0 new failures:
  - check-trust: 0 findings.
  - check-layers: 0 modules reach the elaborator.
  - check-orphans: 0 orphaned (790 reachable).
  - check-noncircular: 0 violations (23 source modules).
  - check-axiom-pins: 497 pins, 0 errors.
  - check-source-grammar and `source-ctors --check`: clean.
  - Script tests: pass.
  - check-doc-paths: 46 missing, which is the baseline.
  - G03 ledger: 0 errors.
  - The build: "Build completed successfully (775 jobs)" and "(262 jobs)".
  - check-solkey: 37 mismatches, which is the baseline.
  - An earlier run on `3419665` hit the baselined `Derived17` out-of-memory
    kill; the final run did not.

**Elaboration times** (`./run-lean.sh`, warm):

| Module | Time |
|---|---|
| `Solidity.Source.SemanticsExamples` | about 7 s |
| `Solidity.Source.Eval` | built within the run, no outlier |

The kernel controls need transaction horizons of 20–30. A
`String`-valued signature was not reducible in the kernel, so signatures
are character lists (`sigOf`).

**For integration.**

- The sibling lanes read the new `Typed`/`RExpr` constructors and the
  `DecidableEq STy` instance.
- G13's checker must produce the new derivations.
- G15's admission needs an elaborator `Resolution → Program` to give
  `SourceSpec.meaning`.
- G46 needs the failure points and the events of unfinished
  transactions before refinement can be stated against this semantics.
