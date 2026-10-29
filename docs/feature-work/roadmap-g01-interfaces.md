# Roadmap G01: interfaces and the six final theorem contracts

Group G01 of the [roadmap](../coverage-plan.md), wave 0. This document fixes the
types, observations, state and world relations and refinement notion of the
six final proof obligations, the shape of a compositional pass certificate,
and the frontend, backend and EVM proof boundaries. It proves none of the
obligations. The first version was pinned to revision
`127c2ee59de16971e45b08a2def54f4e5fae8e2a`; this revision applies the
[user decisions of 2026-10-29](../solidity-scope.md#user-decisions-2026-10-29)
on top of `caf52ecd4dde5d37cbc0098d47de1a01aa218285`.

The contracts are stated in Lean, as definitions only, in
`Solidity/Roadmap/Contracts.lean` (namespace `Solidity.Roadmap`). The module
imports `Solidity.Keccak` (the fixed hash) and `Solidity.Syntax.Raw` (for
`EvalOrder`) only, so it is below the elaborator and below the compiler:
`scripts/check-layers.mjs` lists `Solidity.Roadmap.*` in its core. The plug of
the existing typed run, `typedRunPrefixes`, moved to
`Solidity/Roadmap/TypedRun.lean`, so that a source semantics may import the
contracts (for `Artifact`) without reaching the intrinsic run. Neither module
contains a `sorry` or an axiom. The lemmas check the shape of the contracts
and nothing more: the order is a preorder, refinement composes and transfers
safety, completion and divergence, the allowed environments contain the
no-callback ones, and neither a never-compiling nor an always-reverting
compiler satisfies the public contract. They are not final theorems.

With this revision every question G01 raised is decided and implemented in
the statements; G01's interfaces are frozen at this revision. The
[decisions table](#decisions-applied) maps each decision to its declaration.

## Contents

1. [Decisions applied](#decisions-applied)
2. [Layers and interface types](#layers-and-interface-types)
3. [Common semantic notions](#common-semantic-notions)
4. [The six contracts](#the-six-contracts)
5. [Pass certificates and proof boundaries](#pass-certificates-and-proof-boundaries)
6. [Reuse map](#reuse-map)
7. [Scope questions and their decisions](#scope-questions-and-their-decisions)
8. [Child obligations](#child-obligations)
9. [Handoff](#handoff)
10. [Review](#review)

## Decisions applied

Each row is a decision of
[solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29) or an
item of its follow-up list, and where `Contracts.lean` implements it.

| Decision | Implemented by |
|---|---|
| G01 Q3 / G04 Q1: a per-run hash premise, never global injectivity | `CollisionFree f xs` (equal outputs imply equal inputs over `xs`); `EvmSpec.hashed` (the `KECCAK256` preimages of a prefix, consistent along the horizon) and `EvmSpec.guard`; the premise `EvmSpec.RunCollisionFree V p e r`; `RefinesUnder`, refinement under that premise, in `PublicCorrectness.refines` and `SpecTransfer`. The hash is a fixed parameter (`Fixed.hash`, shared by `SourceSpec.fixed` and `EvmSpec.fixed`), Keccak-256 by `EvmSpec.Approved` (`keccakWord`), not an environment input. `CollisionFree.singleton` shows the premise never asks for injectivity. |
| G01 Q6: export `decode : EvmWorld → Option IntrinsicWorld` | `StateExport` (`lowering`, `decode`, `envAbs`); `EvmSpec.World`, `worlds`, `resume`; `IntrinsicSpec.worlds`; the fields `decode_reach` and `decode_commutes` of `PublicCorrectness`. |
| G00 Q5: `creationCode`/`runtimeCode` from the whole-input `Artifact` table, a parameter of the source semantics | `SourceSpec.meaning : … → Artifact → lang.Prog`; `Lowering.lower` takes the table; `PublicCorrectness.refines` instantiates it with the compiler's output. The [gate](#non-circularity-as-a-checkable-gate) explains why this parameter is not circular. |
| G01 Q2 and the follow-up rows on nested frames and the block gas limit | `Lang.Res` is a horizon with resource choices; running out of gas is a revert and the session continues. `SourceSpec.Exhaust`/`never`/`exhaust`/`withExhaust` (every frame and transaction may fail); `EvmSpec.gas`/`withGas` (a gas schedule per frame); code size, stack and memory are not EVM resources (`EvmSpec` docstring). |
| G01 Q4, G04 Q3 and the follow-up rows on sender funds and precompiles | `SessionEnv` (requests and a history-dependent `Strategy` of `Move`s, with `Event.reenter`/`reentered` for unbounded reentrancy); `SessionEnv.Allowed` (`Affordable` against the `Ledger`, `ZeroHasNoCode`); `SessionEnv.NoCallback` and `SessionEnv.Allowed.withoutCallbacks` (the no-callback reading is a special case); `Lang.PrecompilesFixed`; `PublicCorrectness.session` (source and EVM read one environment). |
| G00 Q4: all eight `EvalOrder` combinations | `SourceSpec.order`/`setOrder`/`order_set`; `SourceSpec.AllOrders` as the field `PublicCorrectness.orders`; `evalOrders` and `mem_evalOrders`; `PublicCorrectness.allOrders`. |
| G01 Q1: idealized source | `SourceSpec.Idealized`, part of `SourceSpec.Approved`. |
| G01 Q5: the full event list with exact bytes | `Outcome`, `Event` (unchanged observations, plus the callback events and the target of `Event.tx`). |
| G01 Q7: callee answers regardless of forwarded gas | `Strategy` takes the history only, not the gas. |
| G01 Q8: the whole input is the system | `Event` docstring; `Artifact`, `CodeUnit.links`. |
| Integration review leftovers | Addresses and values are `Address := Fin (2^160)` and `Word := Fin (2^256)` (`Fin Evm.W`), not `Nat`; the unused imports (`Semantics.Lifetime`, `Evm.Machine`) are gone; `Solidity.Roadmap.*` is in `CORE`; the "open question" and "proposed default" wording is gone. |

The public names `Lang`, `Pass`, `Cert`, `SourceSpec`, `EvmSpec`,
`Admission`, `PublicCorrectness` and `SpecTransfer` are kept. Their
signatures changed as follows, which a citing sibling must follow:

- `Lang` has a new field `Guard` with the default `True`.
- `Cert.need_ok` and `Cert.back` are guarded by the target's `Guard`;
  `Cert.refines` gives `RefinesUnder`; `Cert.comp` takes the premise
  `mid : ∀ p e r, L₂.Guard p e r` (the middle language has no premise).
- `Refines.completes`, `Refines.sound`, `Refines.diverges` and
  `Refines.safety` are kept; `RefinesUnder.*` are their forms under a
  per-run premise, and `Refines.under` and `RefinesUnder.refines` convert.
- `SourceSpec` and `EvmSpec` have new fields; `SourceSpec.meaning` and
  `Lowering.lower` take an `Artifact`.
- `Event` addresses and values are `Address`/`Word`; `Event.tx` gained its
  `target`; `Event.reenter` and `Event.reentered` are new.
- `PublicCorrectness` is a `structure … : Prop` with named fields and an
  extra argument `X : StateExport S I V`.

## Layers and interface types

Each layer is an intrinsic type. No layer is an untyped intermediate
representation, which follows [intrinsic.md](../intrinsic.md). The
`Contracts.lean` name for each layer is given in the type column.

| # | Layer | Type | Owner |
|---|---|---|---|
| L0 | Raw compilation input: named source units, the selected unit and the settings, its `EvalOrder` among them | `SourceSpec.Input`, `SourceSpec.order`, `setOrder` | G00 (pins), G12 (units) |
| L1 | Source syntax under the pinned grammar | `SourceSpec.Syntax`, judgment `Parses : Input → Syntax → Prop` | S00 |
| L2 | Resolved, typed declaration graph | `SourceSpec.Resolved`, judgments `Resolves`, `WellFormed` | S01 |
| L3 | Approved profile | `SourceSpec.InProfile : Resolved → Prop` | G00, G15 |
| L4 | Source meaning: deployment and transaction sessions, for a given artifact table | `SourceSpec.lang : Lang Event Outcome`, `meaning` | S02–S05 |
| L5 | Intrinsic typed contract world: `Contract`, `Prog C Γ Γ'`, `State C Γ` and a world of typed instances | `IntrinsicSpec.World`, `IntrinsicSpec.lang`, `worlds` | G16–G24 (see the [reuse map](#reuse-map)) |
| L6 | Backend languages chosen by the compiler, one per pass | any `Lang Event Outcome` | G24–G44 |
| L7 | Assembly: instruction lists with labels | `Lang Event Outcome` with programs over instructions | G45 |
| L8 | Bytecode artifacts | `Artifact`: a table of `CodeUnit`s (`initcode`, `runtime : Bytes`, library link sites), one per contract and library, and the selected one | G44, G45 |
| L9 | Pinned Osaka EVM: accounts with code, executing transactions, the outside world played by the session environment | `EvmSpec.lang`, `EvmSpec.load`, `EvmSpec.World` | G06, G46, G47 |

The judgments at L1 and L2 are relations defined from the pinned grammar and
type rules. They are not the parser and not the elaborator. The frontend is a
function that contract 1 relates to them.

## Common semantic notions

All declarations named in this section are in `Solidity/Roadmap/Contracts.lean`.

### Words and addresses

Values are `Word := Fin (2 ^ 256)`, which is `Fin Evm.W` for the constant
`Evm.W` of `Solidity/Evm/Machine.lean`, and addresses are
`Address := Fin (2 ^ 160)`; bytes are `Bytes := List UInt8`. They are bounded
types, so no event carries a number the EVM cannot hold. The module does not
import `Solidity.Evm.Machine`; it restates the bound, which keeps the
contracts outside the compiler's import closure.

### Executions as consistent families of finite prefixes

A `Prefix E O` is what a finite execution prefix shows: `events : List E` and
`final : Option O`. A prefix whose `final` is `none` is still running at its
horizon. One execution is `Prefixes R E O := R → Prefix E O`, a prefix at each
resource bound `r : R`. Every language's semantics is consistent,
`Prefixes.Consistent`: a larger bound extends the events, and a completed
prefix stays the same. This is a field of `Lang` (`consistent`, with the
order `resLE` on bounds), so a semantics that completes with a success at
one bound and with a revert at a larger one is not a language. Under this
reading:

- an execution **completes** with `o` when some bound completes it
  (`Prefixes.Completes`);
- an execution **diverges** at the bounds `A` when no bound in `A` completes
  it (`Prefixes.Diverges`).

The divergence claim is about a consistent family of finite prefixes. It
never says that one finite-gas EVM transaction diverges.

The prefix order `Prefix.Le` says that `a` is below `b` when `a`'s events
are a prefix of `b`'s and, if `a` completed, `b = a`. It is a preorder
(`Prefix.Le.refl`, `Prefix.Le.trans`), and a completed prefix is below only
itself (`Prefix.Le.final_eq`).

### Resources: horizons, exhaustion and gas

A bound `r : Lang.Res` is a **horizon** (how far the prefix looks) together
with the layer's **resource choices**. Running out of gas is never the end
of a session ([G01 Q2](#q2-fixed-evm-limits) and the follow-up rows of the
decisions):

- **Any frame may fail.** A frame of the system that runs out of gas, and an
  external call refused at the 1024 call-depth limit, ends with a revert
  with empty data that its caller sees; the caller continues. This covers
  our own code running out of forwarded gas inside a callback, and calls
  between two instances of the system.
- **Any transaction may fail.** A transaction that runs out of gas reverts,
  and the session continues with the next request.

On the source this is an exhaustion choice in the bound: `SourceSpec.Exhaust`
(the choices: which frames fail as if out of gas), `exhaust r` (the choice of
a bound), `withExhaust r x` with `exhaust_with`, and `never`, the run without
failures (`SourceSpec.NoExhaust`). On the EVM it is the gas schedule of the
bound: `EvmSpec.gas r h`, the gas of the frame the system starts after the
history `h` (a transaction's gas limit, or what the environment forwards
into a callback), with `withGas` and `gas_with`.

Refinement then reads naturally (next section): soundness is "for every gas
schedule there are exhaustion choices", adequacy is "for every exhaustion
choice, `never` included, there is a gas schedule". A source loop that does
not terminate has, at `never`, prefixes that never complete; its compiled
transaction runs out of every finite gas and reverts, which the source
allows by an exhaustion choice.

Code size is not an EVM resource: the EIP-170 and EIP-3860 limits are a
recorded idealization, so the theorem assumes any code size deploys. Nor are
stack and memory: internal calls keep their frames in memory, so internal
recursion is bounded only by gas, and that compiled code stays within the
1024-word stack is a compiler obligation (G32, G37, G45). `EvmSpec.Approved`
makes every horizon and gas schedule admissible; the per-transaction gas cap
and the block gas limit restrict real runs, which the soundness half covers,
and are lifted only in the adequacy half (a recorded reading; see the
[handoff](#handoff)).

### The per-run hash premise

`CollisionFree f xs` says that `f` does not collide on the members of `xs`:
equal outputs imply equal inputs. The hash-collision-bound task defines the
same shape as `Solidity.Hash.CollisionFree`; the two are to be unified at
integration. `CollisionFree.nil`, `CollisionFree.of_prefix` and
`CollisionFree.singleton` check its shape; the last shows that the premise
holds of every function on one preimage, so it never asks for injectivity.

The EVM exposes the `KECCAK256` preimages a prefix hashes, in order
(`EvmSpec.hashed`, consistent along the bounds by `hashed_consistent`). The
premise is `EvmSpec.RunCollisionFree V p e r := CollisionFree V.fixed.hash
(V.hashed p e r)`: the preimages hashed by this execution prefix do not
collide ([G01 Q3](#q3-hash-collisions)). That is the name the
hash-collision-bound task bounds the probability of (about q²/2²⁵⁷ for q
hashes). It is the EVM language's `Guard` (`EvmSpec.guard`).

The hash is a **fixed parameter**, not an environment input: `Fixed.hash`,
read by both sides (`SourceSpec.fixed`, `EvmSpec.fixed`,
`PublicCorrectness.fixed`) and instantiated by Keccak-256 (`keccakWord`, from
`Solidity.Keccak.keccak256Nat`) in `EvmSpec.Approved`.

### Refinement

`Lang E O` is a language at one layer. It has programs, environments, a
bound type `Res` with an order `resLE`, `Allowed : Env → Prop`, `Admissible :
Res → Prop`, `sem : Prog → Env → Prefixes Res E O`, the proof `consistent`,
and a per-run premise `Guard : Prog → Env → Res → Prop` that defaults to
`True`; only the EVM has a nontrivial one.

`Refines AS AT s t` is two-sided:

1. **Forward (resource adequacy).** Every admissible source prefix is below
   some admissible target prefix.
2. **Backward (soundness).** Every admissible target prefix is below some
   admissible source prefix.

`RefinesUnder AS AT G s t` is the same under a per-run premise `G` on the
target bound: the forward direction names a target bound that is above the
source prefix if it satisfies `G`, and the backward direction holds of
target bounds that satisfy `G`. The premise cannot make the forward
direction vacuous in practice: the target bound is chosen before the
premise is checked, and refuting the premise at it means exhibiting a
Keccak collision among the run's own preimages. `Refines.under` and
`RefinesUnder.refines` convert between the two. Proved consequences:

- **Completion transfers** (`RefinesUnder.completes`, `Refines.completes`).
  A source prefix that completes with `o` at an admissible bound gives an
  admissible target bound at which, under the premise, the target completes
  with the same observation and the same events.
- **Nothing is invented** (`RefinesUnder.sound`, `Refines.sound`).
- **Divergence transfers** (`RefinesUnder.diverges`, `Refines.diverges`).
- **Safety transfers** (`RefinesUnder.safety`, `Refines.safety`): any
  downward-closed prefix property.
- `Refines.trans` composes.

Adequacy is the explicit bound function `Cert.need` of each pass
certificate (below), never the assumption that the target already has the
desired result. That the final `need` is a definition without choice is
checked on the final theorems' definitions and axioms (G49.03, G54).

### The session environment

Every layer reads one environment type, `SessionEnv`
([G01 Q4](#q4-environment-model)):

- the deployment: `deployer`, `deployNonce`, `deployValue`, `deployArgs`.
  `this` is the address the deployment produces from them, reported by
  `Event.deploy`; it is not a free input;
- `balance`, the opening balances. The system's own balance is the ledger's
  (`Ledger`, G03's fixed definition, `Fixed.ledger`), from these balances and
  the history;
- `requests : List Event → Option Request`, the next transaction request
  after a history (`none` ends the session);
- `callee : Strategy`, where `Strategy := List Event → Move`: while a call
  of the system is pending, the environment answers it (`Move.answer`) or
  calls back into the system (`Move.reenter`). The strategy depends on the
  whole history, may call back at any depth, and answers regardless of the
  gas the system forwards ([G01 Q7](#q7-gas-dependent-environment-behaviour)).
  A payment to an untyped recipient is a call the strategy may accept or
  refuse ([G04 Q3](../solidity-scope.md#user-decisions-2026-10-29)).

`SessionEnv.Allowed F e` is the conjunction of:

- `Affordable`: the deployment value and every request's `msg.value` are at
  most the sender's ledger balance; a request the sender cannot afford is
  invalid and never runs;
- `ZeroHasNoCode`: a call to address 0 is answered at once with success and
  no data (the recorded assumption that address 0 has no code).

Nothing else restricts the strategy. `SourceSpec` and `EvmSpec` each read
their environments as session environments (`session`, `ofSession`,
`session_of`) and allow exactly the allowed ones (`allowed_iff`); the public
contract requires the source environment to be the EVM's
(`PublicCorrectness.session`), so `envAbs` cannot choose an environment in
which nothing happens. `PublicCorrectness.allowed_iff` derives that the two
sides allow the same environments.

The **no-callback reading** (`transferSemantics:noCallback`) is
`SessionEnv.NoCallback`: the strategy never calls back.
`SessionEnv.withoutCallbacks` replaces every callback by a refusal;
`SessionEnv.withoutCallbacks_noCallback` and
`SessionEnv.Allowed.withoutCallbacks` show that the allowed environments
contain the no-callback ones. A statement over every allowed environment
therefore holds of them: it is a special case, never a premise. The calculus
side (soundness of `ProvesC I false` against sessions with no-callback
strategies) is G51's.

**Precompiles** are fixed functions: `Lang.PrecompilesFixed L` says no event
of `L` calls an `Address.Precompile` (the Osaka addresses `0x01`–`0x11` and
P256VERIFY at `0x100`), so a call to one is computed inside the semantics,
the cryptographic ones through the approved fixed functions, and never
consults the strategy. Both `SourceSpec.Approved` and `EvmSpec.Approved`
require it.

The EVM plays every account outside the system by the strategy. A concrete
Osaka world with arbitrary external code is one such strategy for a fixed
artifact (its code may read our code and balances, which are fixed or
ledger-determined along the history); that simulation is a G06/G47
obligation.

### Shared observations

The observation types are fixed once for every layer, so no pass can pick a
weaker observation ([G01 Q5](#q5-observation-granularity)).

- **`Outcome`**: `success (returnData)` or `revert (revertData)`, as ABI
  bytes. A panic is a revert with `Panic(uint256)` data. A custom error is a
  revert with its selector and arguments. `Error(string)` is a revert with
  its encoding. The empty revert, also what a frame out of gas or refused at
  the call-depth limit shows, is `revert []`.
- **`Event`**:
  - the deployment of the selected contract with its outcome and address
    (`deploy`);
  - outgoing typed external calls and payments to accounts outside the
    system (`call`, with callee, value, ABI input and the static flag);
  - creations (`create`), naming the created contract by its position in
    the compilation input, a source identity;
  - the `answer` to the newest pending call, or a creation's address;
  - a session's completed transactions (`tx`, with sender, target, value,
    timestamp, input and outcome);
  - callbacks (`reenter`, with target, sender, value and input) and their
    outcomes (`reentered`).

  The **compiled system** is every contract and linked library of the
  compilation input ([G01 Q8](#q8-system-boundary-libraries-and-created-contracts)).
  A call between its instances, a linked library call (which runs on the
  caller's storage) and a call to a precompile are internal to the
  semantics, not events.

The recorded exclusions are omitted on purpose: logs, gas, raw layout,
`selfdestruct`, raw calldata and the extra block fields
([solidity-scope.md](../solidity-scope.md)). Event (log) arguments still
execute, with their effects and failures, inside the semantics.

### State and world relations

The refinement contracts relate observations over sessions; a
compiler-chosen representation (any storage packing, any memory layout)
is allowed, and a trivial representation gains nothing because the
observations stay fixed. The proofs need these relations as internal
lemmas, owned as follows:

| Relation | Between | Owner |
|---|---|---|
| `R_low` | source world (S04.03: accounts, typed persistent and transient stores, balances, time) and intrinsic world | G16–G23 |
| `R_rep` | intrinsic world and backend states: storage representation (G27), memory and frames (G32), calldata (G35, G40), world and payments (G42–G44) | G24–G44 |
| `R_evm` | the assembly machine and the pinned EVM state: byte memory, real `KECCAK256` slots, stack, accounts and code | G46, G47 |

The public theorem also **exports a decoding** of EVM worlds to intrinsic
worlds ([G01 Q6](#q6-state-level-transfer)), as a function, so that it cannot
be a trivial relation. `StateExport S I V` holds the `lowering : Lowering S
I` whose worlds are meant, `decode : V.World → Option I.World` and the
environment map `envAbs` to the intrinsic layer. Two fields of
`PublicCorrectness` constrain it, for every compiled input, allowed EVM
environment and admissible bound:

- `decode_reach`: under the per-run hash premise, the EVM worlds the prefix
  reaches at its transaction boundaries (`EvmSpec.worlds`) decode, in order,
  to exactly the intrinsic worlds the lowered program reaches at some
  admissible intrinsic bound (`IntrinsicSpec.worlds`). A storage invariant
  proved of every intrinsic world the lowered program reaches therefore
  holds of every decoded EVM world.
- `decode_commutes`: **decoding commutes with the observations.** For every
  reached EVM world `ω` decoding to `ω'`, the sessions continued from `ω`
  (`EvmSpec.resume`) refine and are refined by the intrinsic sessions from
  `ω'` (`IntrinsicSpec.ofWorld`), at every allowed environment, under the
  per-run hash premise.

`PublicCorrectness.envAbs_agrees` ties the intrinsic environment map to the
public one through the lowering's own map.

## The six contracts

`SourceSpec` bundles the independent source side: `Input`, `Syntax`,
`Resolved`, the judgments `Parses`, `Resolves`, `WellFormed`, `InProfile`,
the session language `lang`, `meaning : (r : Resolved) → WellFormed r →
InProfile r → Artifact → lang.Prog`, the settings (`order`, `setOrder`), the
fixed parameters, the session environment and the exhaustion choices.
`meaning` is total on admitted input because its proofs are arguments, and
it takes the artifact table as a parameter (G00 Q5).

### 1. Source admission and parsing — `Admission`, `CheckedFrontend`

**Types.** `Admission S` has `frontend : S.Input → Option S.Resolved` and
two fields:

- `sound`: an accepted input is `S.Admitted`, meaning it parses under
  `Parses`, resolves under `Resolves`, is `WellFormed` and is `InProfile`;
- `complete`: every admitted input is accepted with exactly its resolution.

For a proof-producing frontend, `CheckedFrontend S` splits `frontend` into
`produce` and a Lean `check`, with three fields:

- `checked`: acceptance by the checker implies admission;
- `accepted`: what is produced passes the checker;
- `complete`: every admitted input produces its resolution with some
  certificate.

`SourceSpec.Unambiguous` requires `Parses` and `Resolves` to be functional,
which `complete` needs to be meaningful. It is an S00/S01 obligation.

**Observation.** Acceptance with the resolved graph, or rejection.
Rejection is exact by `complete`.

**Premises.** The settings, the evaluation order among them, and
compilation-unit identity are part of `Input` (G00 and G12). There are no
other premises.

**Non-circular because** `Parses` and `Resolves` are relations from the pinned
grammar and type rules (S00/S01), not the frontend's code. A solc JSON AST,
a digest or `ScopeScan.within` (`Solidity/Frontend/Source.lean`)
instantiates neither: the last certifies only a feature list.

**Vacuity is excluded.** A frontend that rejects everything fails `complete`
on any admitted input. One that accepts everything fails `sound`.

### 2. Lowering — `Lowering`

**Types.** `IntrinsicSpec` is the intrinsic world type, its session
language, `ofWorld` and `worlds`. `Lowering S I` has:

- `lower : (r : S.Resolved) → S.WellFormed r → S.InProfile r → Artifact →
  I.World`, total by its type, for every artifact table.
- A pass `S.lang → I.lang` whose domain contains every source meaning (`dom`)
  and whose output is `ofWorld (lower …)` (`agrees`).
- Its certificate `cert : Cert pass`.

**Observation and relation.** The shared `Event` and `Outcome`. The
certificate gives refinement in both directions at every allowed environment
(`Cert.refines`). The intrinsic language has no per-run premise, so this is
plain refinement (`RefinesUnder.refines`). Typing preservation is in the
target type itself, since `lower` produces intrinsic `Prog C Γ Γ'`.

**Premises.** Only the approved environment set `I.lang.Allowed` and its
resources.

**Non-circular because** `S.lang` and `S.meaning` come from S02–S05 without
the lowering; the [gate](#non-circularity-as-a-checkable-gate) enforces it.
An always-reverting or erased lowering fails `Refines.completes` on any
source program that completes with a success (G07 control).

### 3. Compilation — `Compilation`

**Types.** `Compilation I Asm` has `compile : I.World → Asm.Prog`, total, a
pass whose domain contains every lowered world (`dom`), `agrees`, and
`cert`. Its pass is the composition of all backend passes (G24–G44) by
`Cert.comp`. Calls, deployment, runtime dispatch and linking are passes like
any other: dispatch on the ABI selector, receive and fallback (G40) and
constructor/initcode generation (G44) produce the session behaviour that
`Event.deploy` and `Event.tx` observe, and linking is the `CodeUnit.links`
table of the `Artifact` that contract 4 resolves.

**Premises.** None beyond allowed environments. Fragment predicates may be
the `Dom` of an inner pass. The closure hypothesis of `Pass.comp` and the
`dom` field ensure no such predicate survives into contract 3.

**Vacuity is excluded** for the same reason as contract 2.

### 4. EVM execution — `Execution`

**Types.** `Execution Asm V` has `assemble : Asm.Prog → Artifact`, total, and
a certified pass `Asm → V.lang` whose output is `V.load (assemble a)`. The
pass composes:

- instruction selection, stack lowering, labels and loops, assembly and byte
  encoding (G45);
- jump and `JUMPDEST` realization of structured control (G45.03);
- the bridges to the pinned EVM: numeric, byte memory and calldata, storage
  with real hashing, transient storage (`TLOAD`/`TSTORE`, reset at the end
  of the transaction), environment, hash, call/create/return with returndata
  and revert bytes, and rollback of persistent and transient state and of
  balances on revert, and the transaction (G46, G47).

Its certificate is guarded by the EVM's `Guard`, the per-run hash premise:
`need_ok` holds at the named bound if that bound's preimages do not collide,
and `back` at every bound whose preimages do not collide. This is where real
`KECCAK256` storage slots meet the compiler's collision-free slot terms.

`EvmSpec` is the pinned Osaka EVM as a `Lang`, with `load` installing an
artifact and running a session, its fixed parameters, the session
environment, the gas schedule, the hash preimages and the worlds
([G00 Q3](../solidity-scope.md#user-decisions-2026-10-29)). Its `Allowed` is
fixed by `allowed_iff`, never chosen by the compiler, so it cannot leave out
malformed calldata, value sent to a non-payable function or hostile callees.

**Non-circular because** `EvmSpec` is the pinned EVM semantics from G06, not
the compiler's own machine, and `load` must decode bytes by the pinned EVM's
own decoder, never by an inverse of `assemble` (gate, part 3). The current
`Evm.Machine` is at most an inner language here (see the
[reuse map](#reuse-map)).

### 5. Composition: the public theorem — `PublicCorrectness`

`PublicCorrectness S V compiler envAbs X` is a structure in `Prop` with
these fields:

1. `coverage`: the compiler returns an artifact exactly when the input is
   admitted.
2. `orders`: `S.AllOrders`, every admitted input stays admitted under each
   of the eight `EvalOrder` combinations (`evalOrders`, `mem_evalOrders`).
   With `coverage`, every admitted input compiles under each of them
   (`PublicCorrectness.allOrders`). Six of the eight have no solc setting;
   `Input` carries the order itself.
3. `envOnto`: every allowed source environment is the abstraction of an
   allowed EVM environment.
4. `fixed` and `session`: both sides read the same hash and ledger, and the
   source environment is the EVM's session environment.
5. `envAbs_agrees`: the state export's environment map agrees with
   `envAbs` through the lowering.
6. `refines`: for every admitted input, artifact the compiler returns and
   allowed EVM environment `e`, `envAbs e` is allowed and the source meaning
   **at that artifact table** refines the artifact's EVM sessions at `e`,
   under the per-run hash premise (`RefinesUnder … (V.RunCollisionFree
   (V.load art) e)`).
7. `decode_reach` and `decode_commutes`: the state export (above).

The final public statement is the conjunction of:

- `PublicCorrectness` with `compiler` the concrete pipeline definition, the
  composition of the frontend and of contracts 2–4, computable and run on
  G07's controls, and `X` its lowering and decoding;
- `SourceSpec.Approved` (idealized source, precompiles fixed) and
  `EvmSpec.Approved` (Keccak-256, every horizon and gas schedule admissible,
  precompiles fixed);
- `SourceSpec.NonVacuous`: admitted inputs whose meanings, at allowed
  environments and without exhaustion (`NoExhaust`), complete with a
  success with data, complete with a revert, and diverge, for every artifact
  table.

The roadmap's obligations read off this contract as follows:

- **Success and failure are preserved.** `Outcome` is part of the final
  observation (`RefinesUnder.completes`, `RefinesUnder.sound`).
- **No never-compiling compiler.** `PublicCorrectness.compiles`: with a
  non-vacuous source, the compiler returns an artifact.
- **No always-revert compiler.** `PublicCorrectness.succeeds` turns the
  source's success witness into an EVM success under the per-run premise,
  and `PublicCorrectness.not_alwaysRevert` refutes any compiler whose bytes
  never complete with a success on collision-free runs (say, runs that hash
  nothing).
- **Divergence** is matched by `RefinesUnder.diverges` and the forward
  direction; a diverging source transaction is, on the EVM, a transaction
  that runs out of gas, which the source allows by an exhaustion choice.
- **No fixed fuel.** Fuel is part of a bound of a consistent family, not a
  premise.
- **Resources.** Exhaustion is a revert the source allows; adequacy is the
  composed `need`.

**Premises.** The allowed environments, the admissible bounds (both fixed
by the decisions, not by the compiler) and the per-run hash premise. There
is no global hash injectivity.

### 6. Verification and trust — `SpecTransfer`

`SpecTransfer S V compiler envAbs` says that for every admitted input and
allowed EVM environment, two kinds of source specification hold of the
bytes under the per-run hash premise:

- **Safety (box-like).** A downward-closed prefix property that holds at
  every admissible source prefix holds at every admissible EVM prefix whose
  preimages do not collide.
- **Completion (diamond-like).** A source completion at an admissible bound
  gives an admissible EVM bound at which, if its preimages do not collide,
  the bytes complete with the same outcome.

The semantic half is proved from contract 5 (`PublicCorrectness.transfer`,
no axioms, pinned by `#guard_msgs`). The rest of contract 6 is meta-level and
owned by G51, G54 and G55:

- **Rule soundness.** Every added calculus rule is sound. `Proves.valid`
  (`Solidity/Calculus/Sound.lean`) is the existing form, on the intrinsic
  typed run.
- **The bridge from `⊨` to these prefix properties**, on the intrinsic
  language: the box's acceptance of revert and divergence read as a
  downward-closed property; a diamond's completion read at `never`
  exhaustion; then contracts 2–5. The no-callback calculus is the special
  case of no-callback strategies.
- **Trust.** No `sorry`, no new axioms and a reproducible kernel check
  (`scripts/check-trust.sh`, `TrustAudit.lean`,
  [assurance.md](../assurance.md)).
- **Automatic search is separate.** `SpecTransfer` transfers whatever is
  proved; it does not ask any tactic to find the proof (G51.02).

### Non-circularity as a checkable gate

The gate G07 implements has four parts:

1. **Import whitelist.** The modules defining the source semantics (S00–S05)
   and instantiating `SourceSpec` may import only an explicit whitelist:
   Lean's prelude, the new source modules, named datatype modules (such as
   the one defining `Ty`), each with its S05 correspondence theorem, and
   `Solidity.Roadmap.Contracts` itself, whose closure is `Solidity.Keccak`
   and `Solidity.Syntax.Raw` and their imports. In particular they reach
   neither `Solidity.Syntax.Scoped` (the intrinsic programs) nor
   `Solidity.Semantics.Run` (their run), nor `Solidity.Roadmap.TypedRun`,
   `Solidity.Evm.*`, `Solidity.Frontend.*` or `Solidity.Syntax.Elab*`. A
   blacklist would not do: an S04 module could define its own `toIntrinsic :
   Resolved → Prog …` and set `meaning := Prog.run ∘ toIntrinsic`, and
   `Lowering.lower := toIntrinsic` would make contract 2 an identity. This is
   a mechanical check in the style of `scripts/check-layers.mjs`.
2. **No `meaning` through the pipeline, checked both ways.** `S.meaning` must
   not mention `I.lang`, `lower` or a later layer (enforced by (1)), and the
   constants `Lowering.lower` unfolds to include no constant of the source
   closure other than the whitelisted datatypes and the judgments it
   consumes.
3. **The EVM end too.** The module instantiating `EvmSpec` imports the pinned
   EVM (G06: the core interface, or the external adapter in `Bridge/`) and no
   compiler module, so `load` cannot decode an artifact by the inverse of
   `assemble`.
4. **The artifact table is a variable of the source.** `meaning` takes the
   table as an argument and may use only the `Artifact` and `CodeUnit`
   datatypes, never a compiler definition (enforced by (1): the source
   closure contains no `Solidity.Evm.*` module, and `Contracts.lean` defines
   no compiler). It reads the table only as the byte values of
   `type(C).creationCode` and `type(C).runtimeCode`.

**Why a compiler-output parameter is not circular.** Circularity would mean
the source's meaning is defined by what the compiler does, so that the
compiler is correct by construction. Here:

- The source semantics is defined uniformly for **every** table, before any
  compiler exists; the compiler cannot change it, only choose which table the
  theorem instantiates it with (its own output, `PublicCorrectness.refines`).
- The table enters the source as **data**: the bytes a `creationCode` or
  `runtimeCode` expression evaluates to. The source never executes those
  bytes (executing arbitrary bytecode is a recorded exclusion), and `new C`
  runs the source meaning of `C`, not the table's bytes. So a table cannot
  make wrong code look right: if the bytes for `C` were wrong, the EVM's
  `new C` would execute them and its observations would differ from the
  source's.
- The decision fixes these expressions' value as "the bytes this compiler
  produces" ([G00 Q5](../solidity-scope.md#user-decisions-2026-10-29)); the
  parameter is the only way to state that value without a fixed compiler
  inside the source. Every other observation is still checked against the
  compiler-independent semantics, and the success, revert and divergence
  witnesses of `SourceSpec.NonVacuous` must hold for every table.
- The composed pipeline must output a table consistent with itself (a
  contract embedding `C`'s bytes embeds the bytes the table holds for `C`).
  solc rejects cyclic creation dependencies, so this is a well-founded
  construction (G44), not a fixed point the theorem assumes.

## Pass certificates and proof boundaries

### Certificate shape

A pass `π : Pass L₁ L₂` has an input domain `Dom`, a function `run` on that
domain and `envAbs`. A **certificate** `Cert π` is data. Its fields are:

- `envSound` and `envOnto`;
- `need : (p : L₁.Prog) → π.Dom p → L₂.Env → L₁.Res → L₂.Res`, the
  constructive resource bound (on the EVM, a gas schedule);
- `need_ok`: at every allowed target environment and admissible source
  bound, `need` is admissible and, under the target's `Guard`, the source
  prefix is below the target prefix there;
- `back`: every admissible target prefix satisfying the `Guard` is below an
  admissible source prefix.

`Cert.refines` turns a certificate into `RefinesUnder` for one program and
environment.

### Composition lemma

`Pass.comp π₁ π₂ closed` needs `closed : ∀ p h, π₂.Dom (π₁.run p h)`, so a
domain cannot remain a restriction of the composed pass. Its statement:

```lean
def Cert.comp (c₁ : Cert π₁) (c₂ : Cert π₂) (closed : ∀ p h, π₂.Dom (π₁.run p h))
    (mid : ∀ p e r, L₂.Guard p e r) : Cert (π₁.comp π₂ closed)
```

`mid` says the middle language has no per-run premise; only the EVM, the
last language, has one, so every composition of the pipeline meets it. The
lemma is proved in `Contracts.lean` and depends on `propext` only, pinned by
`#guard_msgs`. The composed bound is `need₂ ∘ need₁`; the backward direction
chains the two `back` fields.

Mixed programs (G24) are handled by passes whose domain is all intrinsic
programs. A per-feature compiler is an inner component, and its fragment
predicate is discharged inside the pass, not exported.

### Boundaries

| Boundary | From → to | Contract | Trusted base on each side |
|---|---|---|---|
| Frontend | L0 → L2 | 1 (`Admission` or `CheckedFrontend`) | Source: the pinned grammar and type rules as Lean relations. External: solc only as an untrusted certificate producer. |
| Lowering | L2/L4 → L5 | 2 | Source semantics S02–S05; the intrinsic world's semantics |
| Backend | L5 → L7 | 3 | Composed `Cert`s of compiler passes; no fragment predicate in the final `dom` |
| EVM | L7 → L8 → L9 | 4 | The pinned Osaka EVM semantics (G06). The core states the interface; an external implementation (EVMYulLean) stays in `Bridge/`. |

No boundary uses the next layer's semantics to define the previous one, and
each is a `Cert`, so the four compose by `Cert.comp`. Contract 1 supplies the
admitted inputs.

## Reuse map

How each existing type or theorem plugs in, or exactly why it cannot.
Locations are at the base revision. The in-flight Codex lanes
(`evm-byte-memory`, `evm-storage-slots`, `evm-control-flow`,
`memory-*`, `revert-outcome-specs`, `abi-lazy-calldata`, `diamond-*`,
`function-ref-args`, `readonly-external`) are likely to change the rows
marked †.

### Source side

| Existing | Location | Plugs in as | Why not directly |
|---|---|---|---|
| solc JSON import, `solc_import` | `Solidity/Frontend/Import.lean` | At most an untrusted `CheckedFrontend.produce` (G15) | Parsing and resolution are solc's. The AST is printed to `sol` text and elaborated by the macros, so there is no `Parses`/`Resolves` relation to be sound against. |
| `Source.Provenance`, `ScopeScan`, `ScopeScan.within` | `Solidity/Frontend/Source.lean:117`, `:271`, `:299` | Pins of `Input` (G00); feature evidence toward `InProfile` | They certify the identity of the input and the extracted feature list. They say nothing of source correspondence or extraction completeness (the docstring at `Source.lean:269`). |
| Source premise `address(this) < 2^160` | [source-inputs.md](../source-inputs.md), `Solidity/Frontend/Problems.lean:89` | A conjunct of the EVM `Allowed` environment set | — (an existing environment premise; it is listed for G00 to confirm) |
| Elaborated `Prog C Γ Γ'` via `Prog.run` | `Solidity/Semantics/Run.lean:1153` | **Not** the source semantics | Defining the source as `Prog.run ∘ lower` would make contract 2 true by construction. It is the intrinsic layer (below). |

### Intrinsic layer (L5)

| Existing | Location | Plugs in as | Why not directly, and what remains |
|---|---|---|---|
| `Contract`, `Stmt`, `Prog`, `State`, `TTx` | `Solidity/Syntax/Raw.lean:404`, `Solidity/Syntax/Scoped.lean:335`, `:445`, `Solidity/Semantics/State.lean:115`, `:105` | Components of `IntrinsicSpec.World` and its states | (a) Function bodies live inside call statements (an inductive-inductive contract is avoided, [intrinsic.md](../intrinsic.md), "What stays extrinsic"). (b) A recursive call is unrolled to `recDepth = 1024` frames whose bottom is `exhausted` (`Stmt.callRec`, `Scoped.lean:429`; `Prog.recBase`, `:455`; `recDepth`, `:469`). Under the decided `Idealized` source ([Q1](#q1-source-resources)) this is a cutoff that G37 must remove. (c) `TTx.ext` is a static response table keyed by call: two identical calls read the same entry, while the decided environment is a history-dependent `Strategy` ([Q4](#q4-environment-model)). |
| `THalt`, `TRes`, `Prog.run` | `Solidity/Semantics/Run.lean:58`, `:79`, `:1153` | The final value of an intrinsic prefix, after mapping to `Outcome` | `THalt` erases error classes. A failing `assert` is `.panic` without its code; `.revertWith d` keeps revert data where the run has it, but overflow, bounds, empty `pop` and division by zero are plain `.revert` and lose their `Panic` codes, as do `Error(string)` and the distinction of empty data ([solc-alignment.md](../solc-alignment.md), "Remaining deltas", first item). Mapping to `Outcome` needs `Prog.withPanics` (`Solidity/Syntax/Checked.lean:587`) or the G38 revision. `.exhausted` must become a frame failure the source allows (a revert with empty data under an exhaustion choice, `SourceSpec.Exhaust`), never an observation of its own. |
| `TLoop.run` (classical, divergence by `Classical.choose`) | `Solidity/Semantics/Run.lean:565` | The limit of a prefix family | It is not itself a resourced family. |
| `Prog.runF` (loop fuel) and `Prog.runF_approx` | `Solidity/Semantics/RunFuel.lean:319`, `:449` | The intrinsic family indexed by loop fuel; `Roadmap.typedRunPrefixes` (`Solidity/Roadmap/TypedRun.lean`) is the plug | `Prefixes.Consistent` (fuel monotonicity) is not proved yet: a child obligation of G24. There are no events; external calls are a table lookup, not an `Event`. |
| Push at `2^256 - 1` elements is `exhausted` (decision 15) | [intrinsic.md](../intrinsic.md), decision 15 | A gas-exhaustion failure (revert with empty data) the source allows | solc panics with `0x41` at length `2^64` ([solc-alignment.md](../solc-alignment.md), "No bound on a dynamic array's length"). The pinned language is solc's, so S04 must define the `0x41` panic, and the intrinsic run then deviates from the source. G23/G30 must close the gap through `R_low`; it is not an exclusion. |
| `Contract.deployT`, `State.deploy` | `Solidity/Semantics/Deploy.lean:28`, `:20` | The deployment step of an intrinsic session | Only the single contract; value refusal as solc's creation code. |
| `Lifetime.World`, `System`, `System.run`, `System.Init`, `Reachable` | `Solidity/Semantics/Lifetime.lean:25`, `:87`, `:97`, `:124`, `:162` | A candidate intrinsic session semantics (deploy, then calls) | Deterministic and without callbacks ("not a realization of callback havoc"). The entry interface `System` is supplied by the model, since visibility is not retained by `Contract`, so G20/G40 must produce it from source. Divergence and exhaustion have no transition, so a prefix family per transaction is still to be added. |
| `ContractWorld.World`, `Context`, `Entry`, `Operation`, `Operation.run`, `Step`, `Reachable` | `Solidity/Semantics/ContractWorld.lean:52`, `:91`, `:122`, `:392`, `:407`, `:431`, `:443` | The multi-instance intrinsic world: typed storage per instance, 160-bit addresses, explicit funds, creation, libraries, rollback | "Static frames conservatively accept empty-body observations only" (module docstring, line 19); bodies and payable metadata are supplied by the model; there is no general world-aware statement lowering ([contract-world.md](contract-world.md)). It is the best base for `IntrinsicSpec.World` once events and prefix families are added (G22, G24). |

### Backend and EVM

| Existing | Location | Plugs in as | Why not directly, and what remains |
|---|---|---|---|
| `Evm.Machine`, `Instr`, `Out`, `run`, `loopRun`, `Slot`, `Word` † | `Solidity/Evm/Machine.lean:323`, `:185`, `:359`, `:611`, `:435`, `:99`, `:165` | An inner backend `Lang` (a symbolic-slot, word-addressed stack machine with a structured `LOOP`) | It is not the pinned EVM: slots are terms (keccak never collides), memory is word-addressed, `LOOP` is structured, there is no gas and no stack limit, and `CALL` runs no callee code ([compiler-verification.md](../compiler-verification.md), "The machine"). Contract 4 needs passes from it to bytes (G45) and to the pinned EVM (G46). `loopRun` is classical (a fault on divergence), so its prefix family needs a step-indexed run. |
| `Compiler.compile`, `Compilation`, `Input`, `Rep`, `Agrees`, `correct` † | `Solidity/Evm/Compiler.lean:21`, `:17`, `:44`, `:63`, `:74`, `:86` | Seed of the statement-level `need_ok`/`back` of a backend `Cert` | (a) **Partial.** `compile` returns `Option`: `inFragP` (`Solidity/Evm/Compile.lean:321`) or the memory compiler decides. Contract 3 needs totality on lowered worlds. (b) **Panic and payment.** The second disjunct maps a source `.panic` (a failing `assert`) to a machine `revert` with no data, which loses `Panic(0x01)` under the fixed `Outcome` (G38). The third disjunct of `Agrees` (source `ok`, machine `revert` when `Prog.pays`) violates `Refines.completes`; G43 must remove it, not export it. (c) **Divergence.** The fourth disjunct (source `diverge`, machine `fault` or payment revert) fits `final = none` only after the payment case is removed. (d) **Capacity premises.** The `Input` premises `L + Prog.pushes P ≤ Lmax`, `b + Memory.frameNeedProg P ≤ frame` and `Memory.AllocationInput` (`Solidity/Evm/MemoryGrowResult.lean:36`) are theorem premises. They must become a proved `need` or a runtime check (G30, G33). (e) **One program, not sessions.** It relates one run, not deployment and transaction sessions. |
| `compile_correct`, `compile_exact`, `compile_box`, `compile_net`, `compile_storage`, `Sim`, `Sim.init`, `loop_sim` † | `Solidity/Evm/Correct.lean:1089`, `:1115`, `:1137`, `:1157`, `:1197`, `Solidity/Evm/Sim.lean:574`, `Correct.lean:1181`, `:296` | Lemmas inside the G24–G26 certificates. `Sim` is an instance of `R_rep` for the core path. | The same restrictions as above: the `inFrag` fragment (no pushing, paying or shrinking loop bodies; `uint`-keyed mappings only), fragile aliases, a push bound of `2^64`, inlined calls. |
| `Memory.CompiledProg`, `Memory.compile_correct`, `Memory.StateRepr` † | `Solidity/Evm/MemoryCompile.lean:377`, `:1245`, `Solidity/Evm/MemorySource.lean:26` | `R_rep` for memory (G32) | A whole-program selection between the core and memory paths ([compiler-verification.md](../compiler-verification.md), "Memory operations"). G24 must make mixed programs compose. |
| `Main.compiler_checked`, `compiler_correct`, `compiler_net` | `Solidity/Theorems.lean:297`, `:269`, `:285` | Public restatements of the above | The same restrictions. They are not instances of contract 5. |
| `Compiler.bisimulation`, `trace_equivalence` (Bridge) | `Bridge/SolidityBridge/CompilerSimulation.lean:45`, `:67` | Lemmas about successful steps | Only successful program boundaries are transitions; payment freedom (`Prog.pays P = false`) is a premise of both `Transition` constructors (`CompilerSimulation.lean:24`); halting and diverging runs are not transitions. As a contract-5 notion it would erase failure observations, so it cannot be the public refinement. |
| `Evm.lts`, `compile_trace_sound`, `compile_trace_complete` (Bridge) | `Bridge/SolidityBridge/Evm.lean:39`, `:144`, `:153` | Step-level traces of the inner machine: the basis of its prefix family | The same machine as above; `compile_trace_complete` needs `Prog.pays P = false`. |
| `ExternalEvm.simulation` and the word lemmas (Bridge) | `Bridge/SolidityBridge/ExternalEvm.lean:198` | A seed of G46.01 (the numeric EVM bridge, against EVMYulLean) | Arithmetic stack operations only. Symbolic slots, gas, absolute jumps, accounts and calls are outside it (its module docstring). |

### Calculus and trust

| Existing | Location | Plugs in as | Why not directly |
|---|---|---|---|
| `Proves.valid`, `Spec.sat` | `Solidity/Calculus/Sound.lean:38`, [correctness.md](../correctness.md) | The intrinsic end of contract 6 | Reads `Prog.run`, not sessions or prefixes. The bridge to `SpecTransfer` is G51.02 (see contract 6). |
| `scripts/check-trust.sh`, `TrustAudit.lean` | [assurance.md](../assurance.md), "M1 · Trust gates and non-vacuity" | The trust half of contract 6 | Must be extended to the final theorems (G54). |

## Scope questions and their decisions

<a id="open-scope-questions"></a>
G01 asked eight scope questions; the user decided all of them on 2026-10-29
([decisions](../solidity-scope.md#user-decisions-2026-10-29)). Each is kept
here with its decision and the declarations that implement it.

### Q1. Source resources

*Asked:* an idealized source, or a source-side resource such as recursion
depth? *Evidence:* the intrinsic run cuts recursion at 1024 frames
(`recDepth`, `Solidity/Syntax/Scoped.lean`); the roadmap forbids a call-depth
cutoff in the final semantics (G37).

*Decided:* idealized, unbounded fuel and recursion: `SourceSpec.Idealized`,
in `SourceSpec.Approved`. The compiler realizes deep recursion with frames
in memory, bounded only by gas.

### Q2. Fixed EVM limits

*Asked:* which EVM resource profile? *Evidence:* the 1024-word stack and
1024 call depth, the block gas limit, and the code-size limits (EIP-170,
EIP-3860) can make the forward direction false for in-profile programs.

*Decided:* exhaustion is a failure the source allows, not an observation;
internal calls keep their frames in memory; the code-size limits are a
recorded idealization; any external frame may fail with a revert its caller
sees; any transaction may revert from gas exhaustion and the session
continues. Implemented by the [resource reading](#resources-horizons-exhaustion-and-gas):
`SourceSpec.Exhaust`, `EvmSpec.gas`, `EvmSpec.Approved`.

### Q3. Hash collisions

*Asked:* may contract 5 carry a premise about `KECCAK256`? *Evidence:* the
scope forbids global injectivity; the current machine makes collision
freedom structural (`Slot` terms).

*Decided:* a per-run premise that the preimages hashed by the execution
prefix do not collide, with a random-oracle bound on its failure:
`CollisionFree`, `EvmSpec.RunCollisionFree`, `RefinesUnder`. The bound is the
hash-collision-bound task's.

### Q4. Environment model

*Asked:* history-dependent callees or the static `TTx.ext` table; callback
depth; the no-callback reading as a premise or a case; address 0; sender
funds and precompiles. *Evidence:* `envOnto` makes a narrow source
environment set force a narrow EVM one.

*Decided:* history-dependent strategies with unbounded reentrancy; the
no-callback reading a special case; address 0 without code an assumption;
`msg.value` bounded by the sender's ledger balance; precompiles fixed
functions; `this` from deployment and the own balance from the ledger.
Implemented by [the session environment](#the-session-environment).

### Q5. Observation granularity

*Asked:* is the external `Event` list the right observation?

*Decided:* the full `Event` list with exact ABI and revert bytes, `Panic`
codes included: `Outcome`, `Event`. G38 must preserve `Panic` codes
([solc-alignment.md](../solc-alignment.md), "Remaining deltas").

### Q6. State-level transfer

*Asked:* must the public theorem export a functional decoding of EVM state?

*Decided:* it exports `decode : EvmWorld → Option IntrinsicWorld`:
`StateExport`, `PublicCorrectness.decode_reach` and `decode_commutes`
([state and world relations](#state-and-world-relations)).

### Q7. Gas-dependent environment behaviour

*Asked:* one gas bound per session or per request; gas-shaped callee
answers. *Evidence:* a call forwards at most 63/64 of the remaining gas,
`transfer` and `send` a 2300 stipend.

*Decided:* over-approximation: callee answers range over all outcomes
regardless of forwarded gas (`Strategy` reads the history, not the gas).
Gas is per frame (`EvmSpec.gas`), so per request.

### Q8. System boundary: libraries and created contracts

*Asked:* is the whole input, every contract and linked library, the
compiled system?

*Decided:* yes. Calls among its instances and linked library calls are
internal; `Event.create` names a contract by its position in the input;
`Artifact` is the whole-input table, which the source reads for
`creationCode`/`runtimeCode` (G00 Q5).

## Child obligations

Every field of the contracts has an owner.

| Field | Obligation | Owner |
|---|---|---|
| `SourceSpec.Parses`, `Unambiguous` (parse) | The pinned grammar as a relation; unambiguity | S00 |
| `Resolves`, `WellFormed`, `Unambiguous` (resolution) | Static semantics as relations; functionality | S01 |
| `InProfile` | Profile and combination predicate, with exclusion evidence | G00, G15 |
| `order`, `setOrder`, `AllOrders` | Settings carrying any of the eight `EvalOrder` combinations, each admitted | G00, S01, G12 |
| `lang`, `meaning`, `inhabited` | Session semantics with events and outcomes, parametric in the artifact table, consistent prefix families, nontrivial allowed environments | S02–S04, S05 |
| `Exhaust`, `never`, `exhaust`, `withExhaust` | Exhaustion choices at event granularity: every frame of the system (a transaction, a callback, a call between instances) may fail with `revert []` before its next event, its caller continuing; `never` is the unexhausted meaning | S03.04 |
| `fixed`, `session`, `allowed_iff` (both specs) | The shared environment and fixed parameters; the `Ledger` | S03, G03, G06 |
| `Approved` (both specs) | Idealized source; Keccak-256; every gas schedule admissible; precompiles fixed | S03.04, G06 |
| `Admission` or `CheckedFrontend` | Sound and complete frontend | G05 (interface), G08–G15 |
| `IntrinsicSpec` (`worlds` included) | The intrinsic world with events, prefix families and boundary worlds; fuel monotonicity of `Prog.runF`; panic codes; no recursion cutoff | G22–G24, G37, G38 |
| `Lowering` (`lower`, `dom`, `agrees`, `cert`) | Total lowering for every table and its certificate | G16–G23, G48 |
| `Compilation` | Total backend; composed `Cert`s; removal of the payment asymmetry and of the capacity premises; stack use within 1024 words | G24–G44, G49.01 |
| `Execution`, `EvmSpec` (`hashed`, `guard`, `gas`, `World`, `worlds`, `resume`) | Assembly, encoding and pinned Osaka EVM bridges under the per-run hash premise; the outside world as a strategy (a concrete world is simulated by one) | G06, G45–G47, G49.02 |
| `StateExport`, `decode_reach`, `decode_commutes` | The decoding of EVM worlds and its two obligations | G27, G32, G46, G49.03 |
| `PublicCorrectness` | The composed public theorem with deployment and sessions; the self-consistent artifact table | G44, G49.03, G50 |
| `RunCollisionFree` | The probability bound on its failure; unification of `CollisionFree` with `Solidity.Hash.CollisionFree` | hash-collision-bound task, integration |
| `SpecTransfer` and its calculus bridge | `⊨`-to-prefix bridge; rule soundness; the no-callback calculus as the no-callback case | G51 |
| Non-circularity gate | The four parts above, mechanically | G07 |
| Always-revert and erased-observation controls | Instances of `PublicCorrectness.not_alwaysRevert` and `Refines.completes` on inhabited programs | G07, G49.03 |
| Trust | Axiom inventory of the final theorems | G54, G55 |
| `Lang.consistent` for every layer | Consistency of each prefix family along the horizon | S03.04, G24, G45, G46.06 |
| `SourceSpec.NonVacuous` | Success-with-data, revert and divergence witnesses at `never`, for every table | S05, G07 |
| Concrete `compiler`, computable `need` | The public theorem instantiated with the actual pipeline; no choice in `need` | G49.03, G54 |

Not done here: no instance of any contract is constructed, and no existing
theorem is restated against them.

## Handoff

### This revision (contracts match the decisions)

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`.
- **Done:** every item of the decisions' G01 follow-up (the
  [decisions table](#decisions-applied)): the per-run hash premise over a
  fixed hash instantiated by Keccak-256, the `decode` export, the artifact
  table as a parameter of the source semantics with the extended gate, the
  resource reading (no code size, frames and transactions may fail, no
  session end at gas exhaustion, recursion bounded by gas), the session
  environment, the eight evaluation orders, bounded words and addresses,
  dropped imports, `Solidity.Roadmap.*` in `CORE`, and the "open question"
  wording removed. `typedRunPrefixes` moved to
  `Solidity/Roadmap/TypedRun.lean`.
- **New lemmas:** `CollisionFree.nil`, `of_prefix`, `singleton`;
  `Refines.under`; `RefinesUnder.refines`, `completes`, `sound`, `diverges`,
  `safety`; `SessionEnv.withoutCallbacks_noCallback`,
  `SessionEnv.Allowed.withoutCallbacks`; `mem_evalOrders`;
  `PublicCorrectness.allOrders`, `compiles`, `succeeds`, `not_alwaysRevert`,
  `allowed_iff`.
- **Recorded readings** (consequences of the decisions, for the user to
  confirm; see the batch handoff's questions):
  - the adequacy half lifts the per-transaction gas cap (EIP-7825) and the
    block gas limit: `EvmSpec.Approved` admits every gas schedule; without
    that, no compiler satisfies adequacy for a transaction that needs more
    gas than the cap;
  - the own balance follows the ledger; balance the system receives without
    running (as a `SELFDESTRUCT` beneficiary under EIP-6780, a withdrawal or
    a priority fee) has no `Move` and is not modelled.

### First version

- **Base revision:** `127c2ee59de16971e45b08a2def54f4e5fae8e2a`.
- **Checked:** `lean_diagnostic_messages` clean; `check-layers` (155 core
  modules), `check-orphans` and `check-trust` passing; `./run-lean.sh` built
  704 and 262 jobs, its last step `check-solkey.sh` reporting 37 mismatches
  that predate G01. Elapsed about 1 h 15 min.

## Review

### This revision

Findings of the read-only finder and skeptic reviews of this revision are
recorded below.

REVIEW_PLACEHOLDER

### First version

Two read-only reviews were run on the first pushed version, neither using the
Lean server.

**Finder** (citations and claims against the source). Confirmed and fixed:

1. `Prog.withPanics` is at `Solidity/Syntax/Checked.lean:587`, not `:568`
   (that line is `Stmt.withPanics`).
2. The `Lang` docstring named Q3 for the EVM resource profile; it is Q2.
3. The handoff misattributed which axiom results are pinned by
   `#guard_msgs`. The pinned ones are `Cert.comp` and
   `PublicCorrectness.transfer`.
4. Parts of the roadmap's obligations were not addressed: runtime dispatch
   and linking (obligation 3), jumps, rollback and transient state
   (obligation 4), and the separation of automatic search (obligation 6).
   Added to contracts 3, 4 and 6.
5. The reuse map missed `Agrees`' second disjunct (a source panic becomes a
   machine revert without `Panic(0x01)` data) and the
   `b + Memory.frameNeedProg P ≤ frame` premise. Both added.
6. In `CompilerSimulation`, payment freedom is a premise of the `Transition`
   constructors, not of the labels. Corrected.
7. `THalt` keeps `revertWith` data. The text now says exactly what is lost.
8. The `EvmSpec` docstring now lists code size, as the document does.
9. The `ContractWorld` static-frame claim now quotes its docstring.

**Skeptic** (adversarial reading of the contracts). Confirmed and fixed:

1. **Blocking: the non-circularity gate could be bypassed** by a source
   module defining its own lowering to `Prog` and running `Prog.run`. The gate
   is now a whitelist, with a converse check on `Lowering.lower` and a gate
   on `EvmSpec`.
2. **Vacuous endpoints.** Added `SourceSpec.NonVacuous` (success with data,
   revert and divergence witnesses). `EvmSpec.Allowed` is fixed as the
   pinned environment set less approved premises, and `load` may not decode
   by the compiler's inverse.
3. **Consistency was only prose.** `Lang` now has `resLE` and `consistent`.
4. **`need` was called constructive without enforcement.** The wording is
   corrected; computability of the final `need` is a child obligation
   (G49.03, G54).
5. **Gas-dependent environment behaviour and per-transaction gas** were
   decided silently. They became scope question Q7.
6. **Observation gaps.**
   - There was no deployment observation: added `Event.deploy`.
   - Created code was named by a compiler-chosen number: now a source
     identity, read off `Artifact.contracts`.
   - Linked libraries were environment events: the compiled system now
     includes them, and `Artifact` carries link sites. The boundary became
     scope question Q8.
7. **An arbitrary `compiler` parameter** does not make output executable.
   The final statement uses the concrete, computable pipeline run on G07's
   controls. The unused `Prefixes.Emits` was removed.

Not changed: the skeptic's "already acknowledged" items (Q1–Q5, G51's meta
half, `Prog.runF` monotonicity, now covered by the `Lang.consistent` row).
