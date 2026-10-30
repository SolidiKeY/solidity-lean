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
- **Stuck runs.** A `stuck` run shows as an unfinished prefix, like
  divergence. It is not a lack of horizon: a transaction stuck at one
  horizon is stuck at every larger one (`runTx_stuck_stable`,
  [Horizons](#horizon-independence)), so the two differ in the model even
  (`txFate`, `stuck_not_diverges`) though G01's `Prefix` shows them alike.
  Unmodelled features also halt `stuck` (a `string` getter, see
  [Well-formedness](#well-formedness-and-progress-interfaces)), so progress
  holds at best for a modelled fragment; it is not proved.
- **Events of unfinished transactions.** `sourceLang` (`sessionAt`) shows
  none of the events of a transaction that never completes.
  `sourceLangEvents` (`sessionAtEvents`, `Solidity/Source/Session.lean`)
  shows them and is consistent; see
  [Events of unfinished transactions](#events-of-unfinished-transactions).
  An unfinished deployment shows its run's events too (`deployRun_events_mono`,
  from `deploy_approx` in `HorizonDeploy.lean`).
- **Request validity.** `Lang.Affordable` (unaffordable requests are
  dropped) and `Lang.PrecompilesFixed` (precompile addresses are not
  environment accounts) are not met.
- **`SourceSpec`.** It is not instantiated: `Parses` is lanes V05 and
  V06, `stipendFits` is G06 Q3, `hashed`/`slotHashed` need the semantics to
  record every preimage it hashes, and `Failures` needs the failure points.
  `meaning` now has its elaborator (`elaborate`, item 1b).

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

## Horizon independence

`Solidity/Source/Horizon.lean` proves that the interpreter is monotone in
its horizon. `Below m m'` says that on every state `m` either times out or
runs exactly as `m'`.

| Theorem | Statement |
|---|---|
| `belowAt G n` | every interpreter function at horizon `n` is `Below` itself at `n + 1` (`evalE` … `dispatch`, by induction on `n`) |
| `deploy_below`, `runTx_below` | so are a deployment and a transaction |
| `runTx_stable`, `deploy_stable` | a result that completes at horizon `k` is the result at every `k' ≥ k` |
| `firstDone_runTx` | what `firstDone` finds is the run at every larger horizon: the least completing horizon is not a choice |
| `runTx_stuck_stable` | a transaction stuck at `k` is stuck at every `k' ≥ k` |

The proof is one step theorem per function (`evalE_step`, …), each over
the hypothesis `BelowAt G n` for all functions, so each stays within the
default heartbeats; `below_go` walks the two copies of a body (binds,
`attempt`s, `match`es, `if`s). Three interpreter matches were restructured
for it, with the same meaning: `evalBuiltin` matches the builtin, then its
arguments one level at a time; `abi.encodeWithSelector` reads the selector
with `Val.bytesOf`; `assignCopy` copies through `copyInto`.

## Events of unfinished transactions

`Horizon.lean` also proves that the interpreter only appends events and
that a run that times out shows a prefix of the events at every larger
horizon:

| Theorem | Statement |
|---|---|
| `growAt G n` | every interpreter function only appends events (`Grow`) |
| `approxAt G n` | every interpreter function at `n` approximates itself at `n + 1` (`Approx`: both grow; on every state the first times out with events the second extends, or the two agree) |
| `runTx_events_mono` | a transaction not completed at `k` shows a prefix of its events at every `k' ≥ k` |

`sessionGoEvents` (`Session.lean`) is `sessionGo` except at a transaction
that completes within no horizon up to `n`: the prefix ends with the events
its run at `n` produced, or a `stuck` run's events. `sessionAtEvents` is
consistent (`sessionAtEvents_consistent`), so `sourceLangEvents E` has the
type of G01's `Lang Event Outcome` with the same fields as `sourceLang`.
The control (`SessionExamples.lean`, `#guard`) runs a function that loops
forever calling out: at horizon 30 `sessionFrom` shows only the deployment,
`sessionFromEvents` the calls and answers as well, and more at horizon 60.

Helpers keep the events (`Const`, every helper but `emitEvent`), so their
`Approx` lemmas come from the `Below` ones (`Approx.of_below`). Large
bodies are split across declarations to stay within the default heartbeats
(`evalE_apart_*` by constructor index, `evalBuiltin_apart_*` by builtin,
`dispatch_apart_*` by what the call data selects); two interpreter pieces
were named for this with the same meaning (`Glob.pickFn`,
`Glob.pickGetter`, `extReturn`), and `fieldsOf` and `decodeArg` were rewritten as single-level exhaustive matches.

`HorizonDeploy.lean` proves the same for deployments
(`deploy_approx`, from `construct_approx` and the `_grow`/`_approx`
lemmas of initializers, base arguments and constructor bodies;
`deploy_events_mono` states the prefix), and `sessionFromEvents` shows an
unfinished deployment's events at `n` (a halted one's when halted) instead
of none (`deployRun_events_mono`). The control does not pin the
still-running branch apart from a later halt, and no control reaches the
halted-deployment branch. The control (`SessionExamples.lean`)
deploys a constructor that loops calling out: events at horizon 30, more at
60, no final observation.

The prefix of an unfinished transaction holds its `.call`, `.answer` and `.reenter` events but no `.tx` event (`runTx` emits it when it ends). That `sessionAtEvents` agrees with `sessionAt` when every transaction completes holds by the definition, not by a theorem.

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

No progress theorem is proved, and as worded for every elaborated program
it is false: unmodelled features halt `stuck` too (the getter of a
`string` state variable, `Eval.lean`'s getter branch, elaborates and is
not refused by the profile). The absence of `stuck` is an obligation for
a modelled fragment, which is not yet delimited (by a hypothesis or by
profile exclusions of the unmodelled features). The controls other than
the stuck one below complete without `stuck`.

**Stuck is not divergence** (`Session.lean`). `txFate G q s n` is a
transaction's fate within horizon `n`: `done o`, `halted h` or `pending`.

| Theorem | Statement |
|---|---|
| `txFate_mono` | a fate that is not `pending` is the fate at every larger horizon |
| `txFate_pending_iff` | `pending` within `n` iff the run times out at every horizon up to `n` |
| `txFate_of_done` | a run done at some `k ≤ n` gives the fate within `n` |
| `diverges_iff` | `Diverges` (pending at every horizon) iff the run times out at every horizon |
| `stuck_iff` | `Stuck` (halted `stuck` within some horizon) iff the run is stuck at some horizon |
| `stuck_not_diverges` | a stuck transaction does not diverge |
| `stuck_stable` | a stuck fate stays the same halt at every larger horizon |
| `stuck_eventually` | a stuck transaction has, from some horizon on, the same `stuck` fate at every horizon |

`stuck_not_diverges` itself is shallow (a stuck run is not a timeout); the
content is in `stuck_iff`'s converse and `txFate_of_done`, which use
`runTx_stable` so that the least completing horizon has the run's result.
`txFate_mono`, `stuck_stable` and `stuck_eventually` follow from how
`firstDone` is built.

Skeptic review (read-only, no Lean server), fixed:

- the doc called progress for every elaborated program open; the `string`
  getter control refutes it, so the doc now asks for a modelled fragment;
- the `Failures` paragraph named depth and stipend as its content; it now
  names G06's failure points;
- the control checks the deployment and the stuck message;
- `stuck_not_diverges`' docstring claimed a dependency on stability that the
  proof does not have; `stuck_eventually` states the stronger fact.

**Semantic fix: callbacks at the depth limit and from static frames.**
Callbacks entered through `envLoop` (`Eval.lean`) did not apply
`callAddr`'s checks. A callback from the environment frame at depth 1024,
or with value while the pending call is static (EIP-214), now fails with
empty data (`.reenter`, then `.reentered (.revert [])`) without entering.
The controls (`SessionExamples.lean`) call back `x()` at depths 1024
(reverts), 1023 and 3 (return `3`), and with value from a static frame
(reverts). `Horizon.lean`'s proofs go through unchanged. The EVM side's
bridge must record a refused callback the same way.

Finder/skeptic review of the deployment events and the callback fix
(read-only, no Lean server), fixed: the static-value check above; a
depth-1023 control; `deploy_events_mono`'s unused hypothesis dropped and
the session citations moved to `deployRun_events_mono`/`deploy_approx`;
"stuck" wording for any halt; citation placement.

So a reader of fates can tell a stuck run (a modelling gap or ill-formed
program, observable at a finite horizon) from a divergent one. The session
prefix (G01's `Prefix Event Outcome`) cannot carry the distinction, since
both end non-final; `txFate` is the observation to read alongside it. The
control (`SessionExamples.lean`) has `s()` on a `string public s` stuck at
horizons 40 and 80, and `spin` pending at both. Progress itself (no
modelled program is ever stuck) is still open, and needs the modelled
fragment delimited first.

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
- **Horizon independence** (skeptic 4): proved after S05 (`runTx_stable`, `firstDone_runTx`, below).
- **Getters** (skeptic 7): value-type getters are dispatched after S05
  ([source-s03.md](source-s03.md#item-3-gaps-closed-after-s05)); struct,
  `bytes` and `string` getters are not.
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

**Checkpoint status** (after the continuation of 2026-10-30).

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 | done | `Typed.unique`, `StmtD.unique`, `ItemsD.unique`, `RBody.ofDerivation_unique` (Q1, solc literal typing); `Typed.infer`/`StmtD.infer`, `elaborate`, `Elaborated` coherence for every part (item 1b) |
| 2 | done, with the gaps listed | as before; dynamic ABI arguments decoded (`decodeArgs`) |
| 3 | done, with the gaps listed | as before; `runTx_stable`, `deploy_stable`, `firstDone_runTx`, `runTx_stuck_stable` (horizon independence); getters, static `emit`, constructor value |
| 4 | done, with the gaps listed | as before |
| 5 | partial | `sessionAt_consistent`, `sourceLang`; `sessionAtEvents_consistent`, `sourceLangEvents` (events of unfinished transactions, from `growAt`, `approxAt`, `runTx_events_mono`); `txFate`, `stuck_not_diverges` (stuck is not divergence); progress, failure points and `SourceSpec` open |

**Gates** (head `1917b60` and its doc follow-up).

- Lean diagnostics clean on every touched file; a full `./run-lean.sh`:
  "Build completed successfully (783 jobs)" and "(262 jobs)".
- No `sorry`, new axioms, `native_decide`, `implemented_by` or
  `maxHeartbeats` changes. Large proofs are split across declarations
  instead (see [Events of unfinished transactions](#events-of-unfinished-transactions)).
- Pins recorded with `node scripts/check-axiom-pins.mjs --write` (512 pins,
  0 errors); `TrustAudit.lean`'s source-semantics block lists the new
  headline theorems.
- `node scripts/check-g07.mjs --log`: 0 new failures; check-solkey 37
  mismatches (baseline).

**Elaboration.** `Solidity/Source/Horizon.lean` is the slowest new module
(a few minutes in a full build); its step theorems each stay within the
default heartbeats.

**For integration.**

- G13's checker must follow the `Typed`/`StmtD` rule changes recorded in
  [source-s02.md](source-s02.md#typed-rules-changed-for-g13s-checker),
  including `StmtD.rethrow`'s premise `rethrowVar? body = some d`.
- G15's `SourceSpec.meaning` can use `elaborate`.
- G46 can read `sourceLangEvents`; it still needs failure points.

**G13 checker on master (`fb379ae`, `Solidity/Frontend/Static/Infer*.lean`).**
It is written against S01's typing before this lane's changes (master's
`Typing.lean` has none of the S02 constructors). Do not merge master into
this branch; at integration these parts of the checker break:

| Checker file | What breaks | Cause on this branch |
|---|---|---|
| `Infer.lean` `constRes` (l. 121–123) | builds `.const hq ha` | `Typed.const` has a third premise, `e.hexLen? = none` |
| `Infer.lean` `litRes` (l. 138) | builds `.litBytes (h := h) hf` from `fitsBytes` | `Typed.litBytes` takes `hexLen? = some len` and has type `hexConst n.value len` |
| `Infer.lean` `binPair` shift/exp (l. 219–229) | premises on `τa.mobile`, result at `τa` | `Typed.shift`/`exp` read `τa.shiftTy` and type the result `τa.shiftTy` |
| `Infer.lean` arith/bit/order/eq (`common?`) | still compiles; results change | `STy.common?` refuses a constant against a constant or a `bytesN` and uses the mobile type |
| `Infer.lean` (all arms) | no arms for the new rules | new `Typed` constructors `member`, `structNew`, `extCall`, `extCallValue`, `transfer`, `send`, `abiEncode`, `assignCopy`, and `LVal.member` |
| `Static/InferStmt` (master) l. 71 | builds `.expr p.2` | `StmtD.expr` has the premise `(C.inModifier && e.isUnderscore) = false` |
| `Static/InferStmt` (master) l. 118 | builds `.retTuple p.2 q.2 hf` | `StmtD.retTuple` has the premise `σs ≠ []` |
| `Static/InferStmt` (master) `rethrowRes` (l. 143–152) | builds `.rethrow hb hr ht hp` from `Syn.paths` | `StmtD.rethrow`'s last premise is `rethrowVar? body = some d` |
| `Static/InferComplete` (master) `const_mem`, `litBytes_mem` (l. 65, 143), the main match (l. 543–544, 589–593), `shift_pair`, `exp_pair` (l. 245–253) | the same signature changes | as above; the main match also lacks the new constructors |
| `Static/InferStmtComplete` (master) l. 87–91, 186–189, 210–213 | `.expr`, `.retTuple`, `.rethrow` cases | as above |
| `Static/InferExamples` (master) `zero_types` (l. 75) | expects 33 types for `0x00` | `0x00` now has one type, `hexConst 0 1` (solc's literal typing, Q1) |

This branch's `Typed.infer` (`Solidity/Source/Infer.lean`) follows the new
rules and returns one derivation per expression; by `Typed.unique` that is
enough for meaning, but it is not the checker's list-of-all-derivations
interface and has no completeness proof.

**Why `SourceSpec` and `Failures` stay open.** `SourceSpec`
(`Solidity/Roadmap/Contracts.lean`) needs, beyond `sourceLangEvents`:

- `hashed`, the preimages a prefix hashes, prefix-monotone in the bound.
  `St` records no preimages, and adding a field changes every interpreter
  step that `Horizon.lean` walks (`belowAt`, `growAt`, `approxAt`), so it is
  a change to `Machine.lean`/`Eval.lean` plus a re-proof of those theorems
  with one more monotone component.
- `Failures`/`withFailures`/`NoFail` over `lang.Res`. The bound is a bare
  horizon (`Res := Nat`). G06's failure points let each request be
  dropped or run with its post-fee balance, and any external frame fail
  at a chosen point; the semantics has no such choice (only the depth
  limit fails a call, `Eval.lean`, and the stipend rule `stipendFits` has
  no source counterpart), so the bound must first carry failure points
  and every call site consult them.
- `Parses`/`Resolves` relations over an `Input`, which belong to S00/S01's
  front end (`Frontend/`, not this lane's files).

A placeholder instance (`Failures := Unit`, `hashed := []`) would type-check
but would make `forward_iff`/`guard_iff` vacuous, so none is given.

**Open** (also under `limitations:`): a progress theorem for a modelled
fragment, which must first be delimited (`stuck` is told apart from
divergence by `txFate`, `stuck_not_diverges`, but not ruled out); gas/frame failure points and G01's `Failures`;
`SourceSpec` (needs `Parses`, recorded preimages for `hashed`, the stipend
rule); calldata references, `abi.decode`, `new`, slices, inline arrays,
`try`, tuple declarations, `fallback` with parameters; dynamic-length
`Panic(0x41)`; user-defined value types in the decoder.
