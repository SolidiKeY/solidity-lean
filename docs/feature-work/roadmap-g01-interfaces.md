# Roadmap G01: interfaces and the six final theorem contracts

Group G01 of the [roadmap](../coverage-plan.md), wave 0. This document fixes the
types, observations, state and world relations and refinement notion of the
six final proof obligations, the shape of a compositional pass certificate,
and the frontend, backend and EVM proof boundaries. It proves none of the
obligations. The first version was pinned to revision
`127c2ee59de16971e45b08a2def54f4e5fae8e2a`; this revision applies the
[user decisions of 2026-10-29](../solidity-scope.md#user-decisions-2026-10-29)
on top of `caf52ecd4dde5d37cbc0098d47de1a01aa218285`, merged with master
`77f8878f` (the integrated wave-0 groups) for the second integration round.

The contracts are stated in Lean, as definitions only, in
`Solidity/Roadmap/Contracts.lean` (namespace `Solidity.Roadmap`). The module
imports `Solidity.Hash.CollisionBound` (the hash premises) and
`Solidity.Roadmap.Evm` (G06's EVM interface) only, whose closure adds
`Solidity.Keccak` and nothing else, so it is below the elaborator and below
the compiler:
`scripts/check-layers.mjs` lists `Solidity.Roadmap.*` in its core. The plug of
the existing typed run, `typedRunPrefixes`, moved to
`Solidity/Roadmap/TypedRun.lean`, with `Pipeline.order` and
`SourceSpec.order` (which read the raw syntax's `EvalOrder`), so that a
source semantics may import the contracts (for `Artifact`) without reaching
the intrinsic run or the raw syntax. Neither module
contains a `sorry` or an axiom. The lemmas check the shape of the contracts
and nothing more: the order is a preorder, refinement composes and transfers
safety, completion and divergence, the allowed environments contain the
no-callback ones, and neither a never-compiling nor an always-reverting
compiler satisfies the public contract. They are not final theorems.

With this revision every question G01 raised is decided and implemented in
the statements, together with the second-round decisions, G06's findings
F1–F8 and the integration reviews. The [decisions table](#decisions-applied)
maps each to its declaration. Integration review decides whether it is
accepted.

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
[solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29) (first
round, its follow-up list, and the section "Second round (2026-10-29)") or
a finding of the integration review and of G06
([roadmap-g06-evm.md](roadmap-g06-evm.md), §5), and where `Contracts.lean`
implements it.

| Decision | Implemented by |
|---|---|
| G01 Q3 / G04 Q1: a per-run hash premise, never global injectivity; G06 F7: over the preimages the source determines | `SourceSpec.hashed` (the preimages a source prefix determines: `keccak256` arguments and slot preimages under the pinned layout), `SourceSpec.guard_iff`; `HashPremise F xs ys` = `Solidity.Hash.CollisionFree` on all preimages ∧ `Solidity.Hash.RegionsDisjoint` on the slot preimages (`SourceSpec.slotHashed`); `RefinesUnder`, refinement with the forward direction under the source's premise and the backward direction under the target run's own (`EvmSpec.hashed`, `slotHashed`, `guard_iff`), in `PublicCorrectness.refines`, `Cert` and `SpecTransfer`; `PublicCorrectness.hashes_source` (the bytes hash only source-determined preimages and address storage only by the source's slot preimages). `CollisionFree` is an alias of `Solidity.Hash.CollisionFree`; `CollisionFree.singleton` shows the premise never asks for injectivity. |
| Second round: hashed regions of length at most L overlap neither each other nor a root | `Fixed.regionLen` (L), `Fixed.rootSlots`, `Fixed.Sane` (1 ≤ L ≤ 2^128, at most 2^128 roots; in both `Approved` predicates and `Fixed.Keccak`), `HashPremise`, `HashPremise.nil`, `HashPremise.of_prefix`. |
| The hash is a fixed parameter instantiated by Keccak, not an environment input; G06 F5 | `Fixed.evm : Evm.Fixed` (G06's hash, precompiles and precompile gas), `Fixed.hash`, shared by `SourceSpec.fixed` and `EvmSpec.fixed` (`PublicCorrectness.fixed`); `Fixed.Keccak` instantiates it with G06's `Evm.keccakWord`. |
| G01 Q6: export `decode : EvmWorld → Option IntrinsicWorld` | `StateExport` (`lowering`, `decode`, given the run's preimages, `envAbs`); `EvmSpec.World`, `worlds`, `balances`, `resume`; `IntrinsicSpec.worlds`; the fields `decode_reach` and `decode_commutes` of `PublicCorrectness`. |
| G00 Q5: `creationCode`/`runtimeCode` from the whole-input `Artifact` table, a parameter of the source semantics | `SourceSpec.meaning : … → Artifact → lang.Prog`; `Lowering.lower` takes the table; `PublicCorrectness.refines` instantiates it with the compiler's output; `PublicCorrectness.creates_table` makes `new C` run the table's bytes. The [gate](#non-circularity-as-a-checkable-gate) explains why this parameter is not circular. |
| G01 Q2, the follow-up rows on nested frames and gas exhaustion; G06 F1, F2, F4 | `Lang.Res` is a horizon with resource choices; running out of gas is a revert and the session continues. `SourceSpec.Failures`/`failures`/`withFailures`/`NoFail` (G06's `FailurePoints`: each request dropped or run with its post-fee sender balance and a failure point, each frame's failure point); `EvmSpec.gas`/`withGas`; `Lang.Forward` with `SourceSpec.forward_iff` (adequacy at no failure and fewer than `hashBound` source hashes); code size, stack and memory are not EVM resources. |
| Second round: the per-transaction cap (EIP-7825) and the block gas limit are a recorded idealization | `EvmSpec.Approved` admits every gas schedule (`EvmSpec` docstring). |
| G01 Q4, G04 Q3, the follow-up rows on sender funds and precompiles; G06 F6 | `SessionEnv` (requests by index, a history-dependent `Strategy` of `Move`s, `Event.reenter` with its static flag and `reentered` for unbounded reentrancy, `hasCode`); `SessionEnv.Allowed` (`ZeroHasNoCode`, `CodelessSucceeds`); `Lang.Affordable` (no transaction runs with a value above its sender's ledger balance); `Lang.ThisFromDeployment` with `Fixed.createAddress`; `Lang.PrecompilesFixed` with `Address.Precompile` (G06's `Evm.Precompile` table); `SessionEnv.NoCallback`, `SessionEnv.Allowed.withoutCallbacks` (the no-callback reading is a special case); `PublicCorrectness.session`, `envAbs_eq` (source and EVM read one environment). |
| Second round: forced ether | `Event.credit`; `Move.credit` (during a pending call); `Action.credit` (between transactions); the `Ledger` reads the history, credits included. |
| Second round: the stipend rule | `SourceSpec.stipendFits`, a field of the compiler-independent source (G06's `StipendRule`). |
| G00 Q4, revised in the second round: solc's two pipelines; G05's per-unit coder (`Pipeline`, `AbiCoder` correspond to `Solidity.Frontend.Source.Pipeline`/`AbiCoder`, `Pipeline.order` to G05's `Roadmap.Frontend.defaultOrder`, the per-unit `coder` to G05's `CoderMode.coderOf`; the contracts restate them because the source whitelist excludes `Solidity.Frontend.*`) | `Pipeline`, `AbiCoder`, `pipelines`, `mem_pipelines`; `SourceSpec.pipeline`/`setPipeline`/`pipeline_set`, per-unit `pragmaCoder` and `coder` with `coder_legacy`/`coder_viaIR`, `pipelineOf`/`coderOf` with `SettingsResolved`; `SourceSpec.AllPipelines` as `PublicCorrectness.bothPipelines`; `PublicCorrectness.allPipelines`; `Pipeline.order` and `SourceSpec.order` in `TypedRun.lean`. |
| Second round: empty library link map only | `SourceSpec.linkMap`, `SourceSpec.NoLinkMap`, part of `SourceSpec.Approved`. |
| G06 F8: the public theorem fixes the pin | `EvmSpec.pin`, `EvmSpec.Approved` (`V.pin = Evm.pinned`). |
| G01 Q1: idealized source | `SourceSpec.Idealized`, part of `SourceSpec.Approved`. |
| G01 Q5: the full event list with exact bytes | `Outcome`, `Event`. |
| G01 Q7: callee answers regardless of forwarded gas | `Strategy` takes the history only, not the gas. |
| G01 Q8: the whole input is the system | `Event` docstring; `Artifact`, `CodeUnit.links`. |
| First integration review | `Address := Fin (2^160)`, `Word := Fin (2^256)` (`Fin Evm.W`), a 64-bit nonce; no unused imports; `Solidity.Roadmap.*` in `CORE`; no "open question" or "proposed default" wording. |

The public names `Lang`, `Pass`, `Cert`, `SourceSpec`, `EvmSpec`,
`Admission`, `PublicCorrectness` and `SpecTransfer` are kept. Their
signatures changed as follows, which a citing sibling must follow:

- `Lang` has new fields `Forward` and `Guard`, both defaulting to `True`.
- `Cert.need_ok` assumes the source bound in the source's `Forward` and
  `Guard` and yields a target bound in the target's; `Cert.back` assumes
  the target's `Guard` and yields a source bound meeting the source's;
  `Cert.refines` gives `RefinesUnder`; `Cert.comp` takes no extra premise.
- `Refines.completes`, `Refines.sound`, `Refines.diverges` and
  `Refines.safety` are kept; `RefinesUnder AS AT FS GS GT` (source forward
  bounds `FS`, source premise `GS`, target premise `GT`) is the guarded
  form, with `RefinesUnder.*` its lemmas (`sound`, `diverges` and `safety`
  take `GT`), and `Refines.under` and `RefinesUnder.refines` convert.
- `IntrinsicSpec` has `worlds`, `fixed`, the session-environment fields,
  `NoFail`, `hashed`, `slotHashed`, `forward_iff` and `guard_iff`;
  `EvmSpec` has `slotHashed` and `guard_iff`; `PublicCorrectness` has
  `ifixed` and `isession`.
- `SourceSpec` and `EvmSpec` have new fields; `SourceSpec.meaning` and
  `Lowering.lower` take an `Artifact`.
- `Event` addresses and values are `Address`/`Word`; `Event.tx` gained its
  `target`; `Event.reenter` (with its static flag), `Event.reentered` and
  `Event.credit` are new.
- `PublicCorrectness` is a `structure … : Prop` with named fields and an
  extra argument `X : StateExport S I V`.

## Layers and interface types

Each layer is an intrinsic type. No layer is an untyped intermediate
representation, which follows [intrinsic.md](../intrinsic.md). The
`Contracts.lean` name for each layer is given in the type column.

| # | Layer | Type | Owner |
|---|---|---|---|
| L0 | Raw compilation input: named source units, the selected unit and the settings, its pipeline, ABI coder and (empty) link map among them | `SourceSpec.Input`, `pipeline`, `setPipeline`, `coder`, `linkMap` | G00 (pins), G12 (units) |
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

### Resources: horizons, failures and gas

A bound `r : Lang.Res` is a **horizon** (how far the prefix looks) together
with the layer's **resource choices**. Running out of gas is never the end
of a session ([G01 Q2](#q2-fixed-evm-limits) and the follow-up rows of the
decisions):

- **Any frame may fail.** A frame of the system that runs out of gas ends
  with a revert with empty data that its caller sees; the caller continues.
  This covers our own code running out of forwarded gas inside a callback,
  and calls between two instances of the system.
- **Any transaction may fail.** A transaction that runs out of gas reverts,
  and the session continues with the next request.

On the source these are the bound's resource failures (G06 F1, F4):
`SourceSpec.Failures` (G06's `FailurePoints`: each request's fate, dropped
as invalid or run with its post-fee sender balance and an optional failure
point, and each external frame's failure point), `failures r`,
`withFailures r x` with `failures_with`, and `NoFail`, the choices without a
failure (`SourceSpec.NoFailure`). Which requests are dropped, the post-fee
balance and where gas runs out depend on the compiled code, so they are
resources, chosen per execution, never environment inputs. Failures the EVM
forces whatever the gas are source semantics in every choice: external calls
at the 1024 call-depth limit, and payments whose `receive`/fallback body the
stipend rule rejects. On the EVM the resource is the gas schedule:
`EvmSpec.gas r h`, the gas of the frame the system starts after the history
`h`, with `withGas` and `gas_with`.

Refinement then reads (next section): soundness is "for every gas schedule
there are failure choices", adequacy is "without failures there is a gas
schedule" (`Lang.Forward`, `SourceSpec.forward_iff`). Adequacy does not
range over the other choices: one that fails a call between two instances
while a later, expensive sibling call succeeds has no gas schedule, because
a call forwards all but 1/64 of the caller's gas. The failures are a
soundness allowance (the decision), not something the compiled code must
reproduce.

**Divergence** (G06 F2). With a gas schedule in the bound, every EVM
transaction ends, so no EVM execution diverges at every admissible bound,
and `Refines.diverges` says nothing at the EVM. Divergence is read as: the
source never completes without failures (`SourceSpec.NonVacuous`'s third
witness, at `NoFailure`), and every EVM completion is a gas failure that
`back` maps to a failure choice.

Code size is not an EVM resource: the EIP-170 and EIP-3860 limits are a
recorded idealization. Nor are stack and memory: internal calls keep their
frames in memory, so internal recursion is bounded only by gas, and that
compiled code stays within the 1024-word stack is a compiler obligation
(G32, G37, G45). `EvmSpec.Approved` makes every horizon and gas schedule
admissible: the per-transaction gas cap (EIP-7825) and the block gas limit
are a recorded idealization (second round). Real, capped runs are among the
admissible ones, so the soundness half covers them; the adequacy half may
use more gas than the caps. Consequently a compiler that is correct only
with very large gas (say above 2^100) and reverts or takes a catch path
below it satisfies the contracts; a quantitative bound on `need` is not part
of them. In particular a contract that bricks itself permanently after a
transaction run with `gasleft()` below some threshold `X` is not refuted
(`gasleft` is excluded from the profile, but compiled code may still branch
on the gas it has): adequacy can always choose a schedule above `X`, and
soundness accepts the failure choices. This gas-triggered bricking gap is
the same idealization.

A `transfer` or `send` to an instance of the system forwards the 2300-gas
stipend. Whether the receiving body fits is decided by a compiler-independent
source cost rule with cold (EIP-2929) costs, `SourceSpec.stipendFits`
(second round); the compiled body must fit every body the rule admits and
fail for every other (G43, G47).

### The per-run hash premise

The premise reads the preimages the **source** run determines (G06 F7):
`SourceSpec.hashed p e r`, the `keccak256` arguments and the slot preimages
of the source prefix's storage accesses under the pinned storage layout, in
order (`hashed_consistent`). Every layer's `Guard` is the same premise on
the preimages **its own** run hashed: the source's on `SourceSpec.hashed`
(`SourceSpec.guard_iff`), the intrinsic layer's on `IntrinsicSpec.hashed`,
the EVM's on `EvmSpec.hashed` and `slotHashed` (`EvmSpec.guard_iff`):

```lean
def HashPremise (F : Fixed) (xs ys : List Bytes) : Prop :=
  Solidity.Hash.CollisionFree F.hash xs ∧
    Solidity.Hash.RegionsDisjoint (2 ^ 256) F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) ys
```

applied to a run's preimages (`xs`) and its slot preimages (`ys`:
`SourceSpec.slotHashed` with `slotHashed_sub`; on the EVM the preimages
whose hash addresses storage). The region conjunct reads only slot
preimages: code and initcode hashes are of bytes the compiler chooses,
which it could grind against the regions. The region rule is conservative:
two single-slot values whose hashes lie within `L` slots of each other count
as overlapping, though neither region is used beyond its first slot.

The first conjunct is G01 Q3: the preimages do not collide. The second is
the second-round extension: the regions of `regionLen` slots their hashes
start (an array's elements, a struct's fields) overlap neither each other
nor a root slot below `rootSlots`. Both are the hash-collision-bound task's
predicates (`Solidity/Hash/CollisionBound.lean`), which bound their failure
probability (about q²/2²⁵⁷ for q preimages, plus the region terms in
`q·L`); `CollisionFree` here is an alias of `Solidity.Hash.CollisionFree`.
G06's `Evm.Fixed.NoCollision` and `Evm.Fixed.NoOverlap` state the same
premises with a root count; that they agree with `HashPremise` on
`Fixed.evm` is an integration lemma (G06/G46).

**Which run's premise.** Forward (adequacy) is guarded by the *source*
run's premise: the source bound is universally quantified, so no choice of
the prover can make it fail. Backward (soundness) is guarded by the
*target* run's own premise: a violation excuses only a target run that
really hashed the colliding or overlapping preimages. Two earlier designs
failed here. A premise on the bytes' own hashes, with no restriction on what
they hash, let the compiler falsify it (a known Keccak collision pair,
`2^256` repeated hashes). A backward escape borrowed from the source let a
source run through a loop the target never executed (`f(2^191)`, or
`h = keccak(h)`) excuse everything after it. Now the bytes may hash only
preimages the source determines and address storage only by the source's
slot preimages (`PublicCorrectness.hashes_source`, per preimage), so the
compiler cannot choose what the EVM's premise reads; this also makes the
compiler use the pinned layout's slot preimages (G27, "solc's slot
behaviour" of G04 Q2). A correct compiler still has the escape where it is
needed: a target that really runs the long loop hashes those preimages
itself, and a real collision (`m[k1]` written, colliding `m[k2]` read, after
an out-of-gas transaction or not) is among the target's own hashes.

Two parameters bound the premise:

- **`hashBound = 2^128`.** Adequacy speaks only of source prefixes without
  resource failures hashing fewer than `2^128` distinct preimages
  (`SourceSpec.forward_iff`, with `distinctCount`, the length of
  `Solidity.Hash.dedup` computed without choice); below that no collision
  and no overlap is forced by counting. One request suffices to cross it
  (`f(2^130)` writing `m[i]` in a loop); such a prefix is outside adequacy,
  and the bound is compiler-independent. The bound is **not** part of the
  premise. Counting does force a violation of `HashPremise` once a run
  hashes more than about `2^256/L` distinct slot preimages (about `2^190`
  for `L ≈ 2^66`); since soundness reads the target's own premise, that
  excuses only a target that itself hashed that many.
- **`Fixed.Sane`**: `1 ≤ regionLen ≤ 2^128` and `rootSlots ≤ 2^128`, a
  sanity bound only: the final statement uses the concrete `S.fixed` of
  the S05-validated source, whose `regionLen` is the profile's largest
  region (about `2^66` slots) and `rootSlots` its static layout. Without
  it `rootSlots ≥ 2^256` would fail the premise on every hashing run and
  `regionLen = 0` would drop the region premise. Both `Approved` predicates
  and `Fixed.Keccak` require it. The caps leave room for in-profile storage
  (a dynamic array of structs may span `2^66` slots); with `q` preimages the
  region bound stays about `q²·L/2^256`. That every region of the profile
  fits `regionLen` and the static layout `rootSlots` is a G27 obligation.

The hash is a **fixed parameter**, not an environment input: `Fixed.hash`
reads `Fixed.evm.keccak` (G06's `Evm.Fixed`, shared through
`PublicCorrectness.fixed`). The final statement quantifies over the fixed
functions and instantiates them with `Fixed.Keccak` (G06's `Evm.keccakWord`,
sane regions). Not yet pinned in Lean, because the constants do not exist:
`precompileGas` to Osaka's gas table (F5), the non-cryptographic precompiles
(identity, modexp) to their EVM definitions, and `Fixed.ledger` to G03's
ledger; each is a child obligation (G03, G06), and until then the final
statement must add them as conjuncts.

### Refinement

`Lang E O` is a language at one layer. It has programs, environments, a
bound type `Res` with an order `resLE`, `Allowed : Env → Prop`, `Admissible :
Res → Prop`, `sem : Prog → Env → Prefixes Res E O`, the proof `consistent`,
and two predicates on bounds that default to `True`: `Forward`, the bounds
adequacy speaks of, and `Guard`, the per-run premise on the preimages this
layer's run hashed. At the source and the intrinsic layer both are fixed by
`forward_iff` and `guard_iff`, at the EVM `Guard` by `guard_iff` and
`Forward` is trivial (`EvmSpec.Approved`).

`Refines AS AT s t` is two-sided:

1. **Forward (resource adequacy).** Every admissible source prefix is below
   some admissible target prefix.
2. **Backward (soundness).** Every admissible target prefix is below some
   admissible source prefix.

`RefinesUnder AS AT FS GS GT s t` reads each premise on its own side:

1. **Forward.** Every admissible source bound in `FS` meeting the source's
   premise `GS` names an admissible target bound above it.
2. **Backward.** Every admissible target prefix meeting the target's own
   premise `GT` is below an admissible source prefix.

`Refines.under` and `RefinesUnder.refines` convert. Proved consequences:

- **Completion transfers** (`RefinesUnder.completes`, `Refines.completes`).
  A source completion at an admissible bound in `FS` satisfying `G` is a
  target completion with the same observation and events.
- **Nothing is invented** (`RefinesUnder.sound`, `Refines.sound`) by a
  target prefix meeting its premise.
- **Divergence transfers** (`RefinesUnder.diverges`, `Refines.diverges`).
- **Safety transfers** (`RefinesUnder.safety`, `Refines.safety`): any
  downward-closed prefix property, to target prefixes meeting their
  premise.
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
- `hasCode`, whether an account outside the system has code after a history
  (what `extcodesize` reads);
- `requests : List Event → Nat → Option Action`, the `i`-th action after a
  history, counting every action issued (a dropped request leaves the
  history unchanged): a transaction `request` or a `credit` (`none` ends the
  session);
- `callee : Strategy`, where `Strategy := List Event → Move`: while a call
  of the system is pending, the environment answers it (`Move.answer`) or
  calls back into the system (`Move.reenter`, with its static flag: G06 F6)
  or credits an account
  (`Move.credit`, a foreign `SELFDESTRUCT`). The strategy depends on the
  whole history, may call back at any depth, and answers regardless of the
  gas the system forwards ([G01 Q7](#q7-gas-dependent-environment-behaviour)).
  A payment to an untyped recipient is a call the strategy may accept or
  refuse ([G04 Q3](../solidity-scope.md#user-decisions-2026-10-29)).
- **Forced ether** (second round): the environment may credit any account,
  the system's own included, without running its code: between transactions
  (`Action.credit`: a block beneficiary's fee, a withdrawal) and during a
  pending call (`Move.credit`: a foreign `SELFDESTRUCT`). Each credit is an
  `Event.credit`, so the ledger, which reads the history, records it.

`SessionEnv.Allowed e` is the conjunction of:

- `PrecompilesHaveNoCode`: `extcodesize` reads 0 at a precompile;
- `ZeroHasNoCode`: address 0 has no code (`hasCode h 0 = false`, the
  recorded assumption);
- `CodelessSucceeds`: a call to an account without code runs nothing and
  succeeds at once with no data, as on the EVM. `SessionEnv.hasCode` is what
  `extcodesize` reads, so solc's code-existence check before a typed call
  reads the same answer on both sides. Accounts with code may accept or
  refuse any call or payment.

**Sender funds.** A request whose value exceeds its sender's ledger balance
is invalid and never runs: `Lang.Affordable` (in both `Approved`
predicates) says no `Event.tx` carries a value above the sender's balance
after the history before it. Which requests are dropped for fees depends on
the compiled code's gas, so that is a resource failure (G06 F1), not an
environment restriction; unaffordable requests are therefore allowed and
dropped, not excluded. The `Ledger` gives external accounts' balances: they
move only by events (payments, values sent, credits). Value moved between
instances of the system is internal; the system's own balances are part of
each side's worlds, from the deployment value, the events and those
transfers.

Nothing else restricts the strategy. `SourceSpec` and `EvmSpec` each read
their environments as session environments, exactly (`session`,
`ofSession`, `session_of`, `of_session`: each environment type is equivalent
to `SessionEnv`), and allow exactly the allowed ones (`allowed_iff`); the
public contract requires the source environment to be the EVM's
(`PublicCorrectness.session`), so `envAbs` is forced
(`PublicCorrectness.envAbs_eq`) and cannot choose an environment in which
nothing happens. `PublicCorrectness.allowed_iff` derives that the two
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
require it, and both sides read the same functions, `Fixed.evm.precompile`
and `precompileGas` (G06's `Evm.Fixed`, shared through
`PublicCorrectness.fixed`; G06 pins the gas to Osaka's, F5).
`Address.Precompile` reads G06's address table (`Evm.Precompile.ofAddress?`).

**`this` comes from the deployment**: `Lang.ThisFromDeployment` says every
`Event.deploy` reports the address `Fixed.createAddress` computes from the
session's `deployer` and `deployNonce` (a 64-bit nonce); both `Approved`
predicates require it.

The EVM plays every account outside the system by the strategy. A concrete
Osaka world with arbitrary external code is one such strategy for a fixed
artifact (its code may read our code and balances, which are fixed or
ledger-determined along the history); that simulation is G06's certificate
(`Evm.Certificate`). Environment code realizes every finite strategy prefix
but not every strategy, and its state inside a reverted frame is rolled
back, so its moves depend on committed history only (G06 F3). The
contracts quantify over all strategies, a superset; `envOnto` is trivial
here because both sides read one `SessionEnv`, and G06's finitary
`Certificate.forth` carries the realizability to the external EVM. The
restriction to committed history is **not** expressed in `SessionEnv`: a
`Strategy` may read events of reverted frames, so `Certificate.forth` must
either realize such strategies only on their finite, committed parts or the
strategy type must be narrowed (G06). Also not expressed, and recorded as
G06 idealizations to settle there: creation at an occupied address
(EIP-684, EIP-7610), requests from a sender with code (EIP-3607), and the
addresses at which the session deploys the input's libraries (G05 Q1 says
the session deploys and links them; the convention, deployer nonces after
`deployNonce` or creations by `this`, is G05/G44's and must be the same on
both sides).

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
    outcomes (`reentered`);
  - credits without a call (`credit`).

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
I` whose worlds are meant, `decode : List Bytes → V.World → Option I.World`
and the environment map `envAbs` to the intrinsic layer. `decode` is given
the preimages the run has hashed (`EvmSpec.hashed`): a world alone cannot
determine which key a hashed slot belongs to, since two keys may collide in
another run, and decoding must never invert the hash. Two fields of
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
  `ω'` (`IntrinsicSpec.ofWorld`), at every allowed environment whose opening
  balances are `ω`'s (`EvmSpec.balances`): forward under the intrinsic
  run's own premise, which covers the keys the world `ω'` stores, backward
  under the EVM premise over the prefix's preimages followed by the
  continuation's (a later key may collide with an earlier one).

Both are stated for EVM prefixes meeting the EVM's own premise
(`V.lang.Guard`). Since the bytes hash only source-determined preimages
(`hashes_source`), the compiler cannot choose what that premise reads: a
violation means the run really hashed colliding or overlapping source
preimages. The intrinsic layer reads the same environment and fixed
parameters (`PublicCorrectness.ifixed`, `isession`) and its `Forward` and
`Guard` are pinned like the source's (`IntrinsicSpec.forward_iff`,
`guard_iff`), so `decode_commutes` cannot be made vacuous by the intrinsic
layer's predicates.

Both compare intrinsic worlds by equality, so the intrinsic world must be a
canonical representation (G22, G24). The final statement must name the
concrete typed intrinsic layer (G24) for `I`: `Contracts.lean` cannot
import it, and with a freely chosen `I` (a copy of the EVM) the export
would say nothing.

`PublicCorrectness.envAbs_agrees` ties the intrinsic environment map to the
public one through the lowering's own map.

## The six contracts

`SourceSpec` bundles the independent source side: `Input`, `Syntax`,
`Resolved`, the judgments `Parses`, `Resolves`, `WellFormed`, `InProfile`,
the session language `lang`, `meaning : (r : Resolved) → WellFormed r →
InProfile r → Artifact → lang.Prog`, the settings (`pipeline`, `coder`, `linkMap`), the stipend cost rule, the
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
(`Cert.refines`), forward under the source's premise and backward under
the intrinsic run's own. The intrinsic language's `Forward` and `Guard` are
pinned (`IntrinsicSpec.forward_iff`, `guard_iff`), and the certificate must
establish them at `need` and carry the premise back (`Cert.back`), so
neither can be chosen to make the contract vacuous. Typing preservation is in the
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

Its certificate is guarded by the assembly language's `Guard`: the premise
on the source-determined preimages, carried down to the assembly program.
This is where real `KECCAK256` storage slots meet the compiler's
collision-free slot terms: the bridge proves that bytes meeting the premise
on those preimages behave as the assembly program.

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
2. `bothPipelines`: `S.AllPipelines`, every admitted input stays admitted
   under both pipelines (`pipelines`, `mem_pipelines`), legacy with its
   pragma's ABI coder and via-IR with v2, each with its `EvalOrder`
   (`Pipeline.order`). With `coverage`, every admitted input compiles under
   both (`PublicCorrectness.allPipelines`).
3. `envOnto`: every allowed source environment is the abstraction of an
   allowed EVM environment.
4. `fixed` and `session`: both sides read the same fixed functions, and the
   source environment is the EVM's session environment
   (`PublicCorrectness.envAbs_eq`: `envAbs` is forced).
5. `envAbs_agrees`: the state export's environment map agrees with
   `envAbs` through the lowering.
6. `creates_table`: the artifact's units have prefix-free creation bytes
   (`Artifact.PrefixFree`), and every `CREATE` the EVM runs
   (`EvmSpec.created`) executes the table's creation bytes for the contract
   its `Event.create` names, followed by the constructor arguments
   (`createsOf`, `Artifact.initcode`). So `type(C).creationCode`, read from
   the table, is what `new C` deploys.
7. `hashes_source`: every preimage the bytes hash is one the source run
   determines at some admissible bound (G06 F7), each on its own: a
   transaction that fails from gas may hash before it fails, and the source
   run where it fails does not.
8. `refines`: for every admitted input, artifact the compiler returns and
   allowed EVM environment `e`, `envAbs e` is allowed and the source meaning
   **at that artifact table** refines the artifact's EVM sessions at `e`,
   forward under the source's `Forward` and `Guard`, backward under the
   EVM run's own `Guard` (`RefinesUnder`).
9. `decode_reach` and `decode_commutes`: the state export (above).

The final public statement is the conjunction of:

- `PublicCorrectness` with `compiler` the concrete pipeline definition, the
  composition of the frontend and of contracts 2–4, computable and run on
  G07's controls, and `X` its lowering and decoding;
- `SourceSpec.Approved` (idealized source, precompiles fixed, `this` from
  the deployment, values affordable, settings recorded, empty link map,
  sane regions) and `EvmSpec.Approved` (the Osaka pin `Evm.pinned`, every
  horizon and gas schedule admissible, no premise of its own, precompiles
  fixed, `this` from the deployment, values affordable, sane regions), for
  all fixed functions `S.fixed = V.fixed` with `Fixed.Keccak` (Keccak-256,
  sane regions), plus the pins listed under [the per-run hash
  premise](#the-per-run-hash-premise) that have no Lean constant yet
  (Osaka's precompile gas, the non-cryptographic precompiles, G03's
  ledger);
- `I` the concrete typed intrinsic layer (G24): with a freely chosen `I`
  the state export would say nothing;
- `SourceSpec.NonVacuous`: admitted inputs whose meanings, at allowed
  environments, in the forward bounds and under the premise, complete with
  a success with data, with a success after hashing (a nonempty
  `SourceSpec.hashed`; `PublicCorrectness.succeeds_hashing` then refutes a
  compiler that reverts whenever the source hashes, without any fact about
  Keccak's values), and with a revert, and one whose single request
  diverges without failures, for every artifact table.

The roadmap's obligations read off this contract as follows:

- **Success and failure are preserved.** `Outcome` is part of the final
  observation (`RefinesUnder.completes`, `RefinesUnder.sound`).
- **No never-compiling compiler.** `PublicCorrectness.compiles`: with a
  non-vacuous source, the compiler returns an artifact.
- **No always-revert compiler.** `PublicCorrectness.succeeds` turns the
  source's success witness into an EVM success, with no premise on the
  bytes' own hashes, and `PublicCorrectness.not_alwaysRevert` refutes every
  compiler whose compiled bytes never complete with a success, whatever
  they hash and whatever the region parameters.
- **Divergence** is matched by the forward direction (prefixes of growing
  events) and by `back`: a diverging source transaction is, on the EVM, a
  transaction that runs out of gas, which the source allows by a failure
  choice ([resources](#resources-horizons-failures-and-gas)).
- **No fixed fuel.** Fuel is part of a bound of a consistent family, not a
  premise.
- **Resources.** Exhaustion is a revert the source allows; adequacy is the
  composed `need`.

**Premises.** The allowed environments, the admissible bounds (both fixed
by the decisions, not by the compiler) and the per-run hash premise on the
source's preimages. There is no global hash injectivity.

### 6. Verification and trust — `SpecTransfer`

`SpecTransfer S V compiler envAbs` says that for every admitted input and
allowed EVM environment, two kinds of source specification hold of the
bytes:

- **Safety (box-like).** A downward-closed prefix property that holds at
  every admissible source prefix holds at every admissible EVM prefix
  meeting the EVM run's own premise.
- **Completion (diamond-like).** A source completion at an admissible bound
  without failures, below `hashBound` and under the premise gives an
  admissible EVM bound at which the bytes complete with the same outcome.

The semantic half is proved from contract 5 (`PublicCorrectness.transfer`,
no axioms, pinned by `#guard_msgs`). The rest of contract 6 is meta-level and
owned by G51, G54 and G55:

- **Rule soundness.** Every added calculus rule is sound. `Proves.valid`
  (`Solidity/Calculus/Sound.lean`) is the existing form, on the intrinsic
  typed run.
- **The bridge from `⊨` to these prefix properties**, on the intrinsic
  language: the box's acceptance of revert and divergence read as a
  downward-closed property; a diamond's completion read without resource
  failures; then contracts 2–5. The no-callback calculus is the special
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
   `Solidity.Roadmap.Contracts` itself, whose closure is
   `Solidity.Hash.CollisionBound`, `Solidity.Roadmap.Evm` and
   `Solidity.Keccak`: interface and hash modules without a compiler,
   intrinsic program or `Lean` import. In particular they reach
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
  make wrong code look right: `PublicCorrectness.creates_table` makes the
  EVM's `new C` execute exactly the table's bytes for `C`, so if they were
  wrong its observations would differ from the source's.
- The decision fixes these expressions' value as "the bytes this compiler
  produces" ([G00 Q5](../solidity-scope.md#user-decisions-2026-10-29)); the
  parameter is the only way to state that value without a fixed compiler
  inside the source. Every other observation is still checked against the
  compiler-independent semantics, and the success, revert and divergence
  witnesses of `SourceSpec.NonVacuous` must hold for every table.
- The composed pipeline must output a table consistent with itself (a
  contract embedding `C`'s bytes embeds the bytes the table holds for `C`).
  solc rejects cyclic creation dependencies, so this is a well-founded
  construction (G44), not a fixed point the theorem assumes. `PublicCorrectness`
  does not check that `compiler i` is the pipeline run on the same table;
  that is part of the concrete pipeline's definition (G44, G49.03).

## Pass certificates and proof boundaries

### Certificate shape

A pass `π : Pass L₁ L₂` has an input domain `Dom`, a function `run` on that
domain and `envAbs`. A **certificate** `Cert π` is data. Its fields are:

- `envSound` and `envOnto`;
- `need : (p : L₁.Prog) → π.Dom p → L₂.Env → L₁.Res → L₂.Res`, the
  constructive resource bound (on the EVM, a gas schedule);
- `need_ok`: at every allowed target environment and admissible source
  bound in the source's `Forward` satisfying its `Guard`, `need` is
  admissible, in the target's `Forward`, satisfies the target's `Guard`
  (the pass carries the preimages down), and the source prefix is below the
  target prefix there;
- `back`: every admissible target prefix meeting the target's `Guard` is
  below an admissible source prefix meeting the source's (the pass carries
  the preimages back up).

`Cert.refines` turns a certificate into `RefinesUnder` for one program and
environment.

### Composition lemma

`Pass.comp π₁ π₂ closed` needs `closed : ∀ p h, π₂.Dom (π₁.run p h)`, so a
domain cannot remain a restriction of the composed pass. Its statement:

```lean
def Cert.comp (c₁ : Cert π₁) (c₂ : Cert π₂) (closed : ∀ p h, π₂.Dom (π₁.run p h)) :
    Cert (π₁.comp π₂ closed)
```

The lemma is proved in `Contracts.lean` and depends on `propext` only,
pinned by `#guard_msgs`. The composed bound is `need₂ ∘ need₁`, with the
forward bounds and premises carried through the middle language. The
backward direction chains the two `back` fields, the middle prefix meeting
its premise.

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
| Source premise `address(this) < 2^160` | [source-inputs.md](../source-inputs.md), `Solidity/Frontend/Problems.lean:89` | Discharged by the type: `Address := Fin (2^160)`, and `this` comes from the deployment (`Lang.ThisFromDeployment`) | — |
| Elaborated `Prog C Γ Γ'` via `Prog.run` | `Solidity/Semantics/Run.lean:1153` | **Not** the source semantics | Defining the source as `Prog.run ∘ lower` would make contract 2 true by construction. It is the intrinsic layer (below). |

### Intrinsic layer (L5)

| Existing | Location | Plugs in as | Why not directly, and what remains |
|---|---|---|---|
| `Contract`, `Stmt`, `Prog`, `State`, `TTx` | `Solidity/Syntax/Raw.lean:404`, `Solidity/Syntax/Scoped.lean:335`, `:445`, `Solidity/Semantics/State.lean:115`, `:105` | Components of `IntrinsicSpec.World` and its states | (a) Function bodies live inside call statements (an inductive-inductive contract is avoided, [intrinsic.md](../intrinsic.md), "What stays extrinsic"). (b) A recursive call is unrolled to `recDepth = 1024` frames whose bottom is `exhausted` (`Stmt.callRec`, `Scoped.lean:429`; `Prog.recBase`, `:455`; `recDepth`, `:469`). Under the decided `Idealized` source ([Q1](#q1-source-resources)) this is a cutoff that G37 must remove. (c) `TTx.ext` is a static response table keyed by call: two identical calls read the same entry, while the decided environment is a history-dependent `Strategy` ([Q4](#q4-environment-model)). |
| `THalt`, `TRes`, `Prog.run` | `Solidity/Semantics/Run.lean:58`, `:79`, `:1153` | The final value of an intrinsic prefix, after mapping to `Outcome` | `THalt` erases error classes. A failing `assert` is `.panic` without its code; `.revertWith d` keeps revert data where the run has it, but overflow, bounds, empty `pop` and division by zero are plain `.revert` and lose their `Panic` codes, as do `Error(string)` and the distinction of empty data ([solc-alignment.md](../solc-alignment.md), "Remaining deltas", first item). Mapping to `Outcome` needs `Prog.withPanics` (`Solidity/Syntax/Checked.lean:587`) or the G38 revision. `.exhausted` must become a frame failure the source allows (a revert with empty data under a failure choice, `SourceSpec.Failures`), never an observation of its own. |
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
continues. Implemented by the [resource reading](#resources-horizons-failures-and-gas):
`SourceSpec.Failures`, `EvmSpec.gas`, `EvmSpec.Approved`.

### Q3. Hash collisions

*Asked:* may contract 5 carry a premise about `KECCAK256`? *Evidence:* the
scope forbids global injectivity; the current machine makes collision
freedom structural (`Slot` terms).

*Decided:* a per-run premise that the preimages hashed by the execution
prefix do not collide, with a random-oracle bound on its failure; the
second round extends it to hashed regions. Implemented over the
source-determined preimages: `HashPremise`, `SourceSpec.hashed`,
`SourceSpec.guard_iff`, `RefinesUnder` ([the per-run hash
premise](#the-per-run-hash-premise)). The bound is
`Solidity/Hash/CollisionBound.lean`'s.

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
| `pipeline`, `setPipeline`, `coder`, `AllPipelines` | Settings for the two pipelines and their ABI coders, both admitted | G00, S01, G12 |
| `linkMap`, `NoLinkMap` | Only the empty library link map; the session deploys and links the input's libraries at addresses fixed by one convention on both sides | G00, G05, G44 |
| `stipendFits` | The compiler-independent stipend cost rule, and compiled `receive`/fallback bodies that agree with it | S04, G43, G47 |
| `Fixed.regionLen`, `Fixed.rootSlots` | Static layout below `rootSlots`, hashed regions within `regionLen` | G27 |
| `Fixed.ledger`, `Fixed.evm` (`precompile`, `precompileGas`) | The G03 ledger, the Osaka precompile functions and gas, pinned in the final statement | G03, G06 |
| `SourceSpec.Failures`, `NoFail`, `hashed` pinned | `Failures` as G06's `FailurePoints` with `NoFail` (no drop, no failure point, the sender balance the EVM computes) and `hashed` defined from the run, in the concrete source named by the final statement | S03.04, S05 |
| `creationCode` fidelity | Each successful creation from a unit's creation bytes installs that unit's runtime bytes, linked, and deploying a unit's creation bytes refines the source's `new C` (an `EvmSpec` code reader is needed) | G44, G47 |
| Committed-history strategies; EIP-684/7610 and EIP-3607 | Narrow `Strategy` or show `Evm.Certificate.forth` realizes it on committed history; settle the two EIPs as idealizations | G06 |
| `Fixed.evm` against G06 | `HashPremise` agrees with `Evm.Fixed.NoCollision`/`NoOverlap`; `Fixed.hash` with `Evm.Fixed.keccak` (definitional) | G06, G46 |
| `Lang.resLE`, `Failures` (meaning) | Bounds ordered by horizon only; a failure choice only turns a frame into `revert []` (or drops a request) at some point after its last event, the run agreeing with a no-failure choice before | S03.04, S05 |
| `hashed` granularity | For every source bound there is one with the same events whose `hashed` includes every hash the run makes before its next event (so an event-granular failure choice cannot hide the hashes of a failing frame from `hashes_source`) | S03.04, S05 |
| `SourceSpec.slotHashed` | The layout's slot preimages among `hashed` | S04, G27 |
| `SourceSpec.hashed` | Every hash the source evaluates (`keccak256`, run-time selectors, indexed dynamic event arguments) and the layout's slot preimages of every storage object it touches; the compiled bytes hash only those (`hashes_source`) | S04, G27 |
| `SessionEnv.hasCode`, `EvmSpec.balances`, `EvmSpec.created` | The EVM's code existence, world balances and `CREATE` bytes, read off the pinned EVM | G06, G47 |
| Canonical `IntrinsicSpec.World`; concrete `I` in the final statement | Decoded worlds compared by equality; the typed intrinsic layer named for `I` | G22, G24, G49.03 |
| `lang`, `meaning`, `inhabited` | Session semantics with events and outcomes, parametric in the artifact table, consistent prefix families, nontrivial allowed environments | S02–S04, S05 |
| `Failures`, `NoFail`, `failures`, `withFailures`, `forward_iff`, `guard_iff` | G06's `FailurePoints` at event granularity: every frame of the system (a transaction, a callback, a call between instances) may fail with `revert []` before its next event, its caller continuing, and every request may be dropped; `NoFail` is the unexhausted meaning, with call-depth and stipend failures forced | S03.04 |
| `fixed`, `session`, `allowed_iff` (both specs) | The shared environment and fixed parameters; the `Ledger` | S03, G03, G06 |
| `Approved` (both specs), `Fixed.Keccak` | Idealized source; the Osaka pin; every gas schedule admissible; precompiles fixed; `this` from the deployment; values affordable; Keccak-256 and sane regions | S03.04, G06 |
| `Admission` or `CheckedFrontend` | Sound and complete frontend | G05 (interface), G08–G15 |
| `IntrinsicSpec` (`worlds`, `NoFail`, `hashed` included) | The intrinsic world with events, prefix families and boundary worlds; its failures and preimages (a resumed run's include the world's stored keys); fuel monotonicity of `Prog.runF`; panic codes; no recursion cutoff | G22–G24, G37, G38 |
| `Lowering` (`lower`, `dom`, `agrees`, `cert`) | Total lowering for every table and its certificate | G16–G23, G48 |
| `Compilation` | Total backend; composed `Cert`s; removal of the payment asymmetry and of the capacity premises; stack use within 1024 words | G24–G44, G49.01 |
| `Execution`, `EvmSpec` (`pin`, `hashed`, `gas`, `created`, `World`, `worlds`, `balances`, `resume`) | Assembly, encoding and pinned Osaka EVM bridges under the per-run hash premise carried down from the source; the outside world as a strategy (a concrete world is simulated by one, `Evm.Certificate`) | G06, G45–G47, G49.02 |
| `StateExport`, `decode_reach`, `decode_commutes` | The decoding of EVM worlds and its two obligations | G27, G32, G46, G49.03 |
| `PublicCorrectness` | The composed public theorem with deployment and sessions; the self-consistent artifact table | G44, G49.03, G50 |
| `HashPremise` | The probability bound on its failure (`Solidity/Hash/CollisionBound.lean`, collisions and regions) | hash-collision-bound task |
| `SpecTransfer` and its calculus bridge | `⊨`-to-prefix bridge; rule soundness; the no-callback calculus as the no-callback case | G51 |
| Non-circularity gate | The four parts above, mechanically | G07 |
| Always-revert and erased-observation controls | Instances of `PublicCorrectness.not_alwaysRevert` and `Refines.completes` on inhabited programs | G07, G49.03 |
| Trust | Axiom inventory of the final theorems | G54, G55 |
| `Lang.consistent` for every layer | Consistency of each prefix family along the horizon | S03.04, G24, G45, G46.06 |
| `SourceSpec.NonVacuous` | Success-with-data and revert witnesses in the forward bounds under the premise, a divergence witness without failures, for every table | S05, G07 |
| Concrete `compiler`, computable `need` | The public theorem instantiated with the actual pipeline; no choice in `need` | G49.03, G54 |

Not done here: no instance of any contract is constructed, and no existing
theorem is restated against them.

## Handoff

### This revision (contracts match the decisions)

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`, merged with
  master `77f8878f` (the integrated wave-0 branches) for the second
  integration round.
- **Done:** every item of the decisions' G01 follow-up (the
  [decisions table](#decisions-applied)): the per-run hash premise over a
  fixed hash instantiated by Keccak-256, the `decode` export, the artifact
  table as a parameter of the source semantics with the extended gate, the
  resource reading (no code size, frames and transactions may fail, no
  session end at gas exhaustion, recursion bounded by gas), the session
  environment, the two pipelines, bounded words and addresses,
  dropped imports, `Solidity.Roadmap.*` in `CORE`, and the "open question"
  wording removed; and the six second-round decisions (two pipelines, gas
  caps idealized, forced ether, the stipend cost rule, hashed regions, empty
  link map). `typedRunPrefixes` moved to `Solidity/Roadmap/TypedRun.lean`.
  After integration held the revision back: the premise on the source's
  preimages with `hashBound` on the source side, `Fixed.Sane`, the hash
  premises unified with `Solidity/Hash/CollisionBound.lean`, `Fixed.evm` as
  G06's `Evm.Fixed`, and G06's findings F1–F8 (see the
  [review](#review)).
- **New lemmas:** `CollisionFree.singleton`; `HashPremise.nil`,
  `HashPremise.of_prefix`; `Refines.under`; `RefinesUnder.refines`,
  `completes`, `sound`, `diverges`, `safety`; `SessionEnv.withoutCallbacks_noCallback`,
  `SessionEnv.Allowed.withoutCallbacks`; `mem_pipelines`;
  `PublicCorrectness.allPipelines`, `compiles`, `succeeds`,
  `not_alwaysRevert`, `allowed_iff`, `envAbs_eq`.

- **Checked:**
  - `lean_diagnostic_messages` on `Contracts.lean` and `TypedRun.lean`: no
    messages; the `#guard_msgs` pins hold (`Cert.comp`: `propext`;
    `PublicCorrectness.transfer`: no axioms). No `sorry`, axiom,
    `native_decide`, `implemented_by` or `maxHeartbeats` change.
  - `node scripts/check-layers.mjs`: 157 core modules (160 after the merge
    with master), 0 reach the
    elaborator; `node scripts/check-orphans.mjs`: 0 orphaned;
    `bash scripts/check-trust.sh`: 0 findings;
    `bash scripts/check-doc-paths.sh`: 46 missing references, as at the base.
  - `./run-lean.sh`: `lake build` "Build completed successfully (719 jobs)";
    `lake build SolkeyTestSuite` lost `TestSuite.Derived17` to exit 137
    (memory) on the first run and built it on the warm re-run ("Build
    completed successfully (262 jobs)"); `check-solkey.sh` reports
    "37 mismatch(es)", the count at the base.
- **Checked after the integration rounds** (head after the merge with
  `77f8878f`): `lean_diagnostic_messages` clean on both modules with the
  pins holding; `check-layers` 160 core modules, 0 reach the elaborator;
  `check-orphans` 0 orphaned; `check-trust` 0 findings; `check-doc-paths`
  46 missing, unchanged; `./run-lean.sh`: "Build completed successfully
  (723 jobs)", SolkeyTestSuite "(262 jobs)", `check-solkey.sh`
  "37 mismatch(es)" (baseline).
- **Checked after the second hold** (master `2abccb70` merged): diagnostics
  clean with the pins; `check-layers` 160 core modules, 0 reach the
  elaborator; `check-orphans` 0 orphaned; `check-trust` 0 findings;
  `check-doc-paths` 46 missing, unchanged; `roadmap-g03-ledger.py --check`
  0 errors; `./run-lean.sh`: "Build completed successfully (728 jobs)",
  SolkeyTestSuite lost `TestSuite.Derived17` to exit 137 (memory) on the
  first run and built "(262 jobs)" on the warm re-run, `check-solkey.sh`
  "37 mismatch(es)" (baseline).
- **Checked after the third hold** (master `040e59d` merged): diagnostics
  clean with the pins; `check-layers` 168 core modules, 0 reach the
  elaborator; `check-orphans` 0 orphaned; `check-trust` 0 findings;
  `check-doc-paths` 46 missing, unchanged; `roadmap-g03-ledger.py --write`
  and `--check` 0 errors; `./run-lean.sh`: "Build completed successfully
  (739 jobs)", SolkeyTestSuite "(262 jobs)", `check-solkey.sh`
  "37 mismatch(es)" (baseline).
- **Elapsed:** about 4 h in all (12:55–17:00 UTC); before the second hold
  about 2 h 25 min (12:55–15:20 UTC); the first part
  below took about 1 h 15 min (12:55–14:10 UTC, 2026-10-29), of which the
  cold build took 59 min (151 min user CPU) and the final builds 11 and
  4 min. Peak memory was not measured (`/usr/bin/time` is absent).

### First version

- **Base revision:** `127c2ee59de16971e45b08a2def54f4e5fae8e2a`.
- **Checked:** `lean_diagnostic_messages` clean; `check-layers` (155 core
  modules), `check-orphans` and `check-trust` passing; `./run-lean.sh` built
  704 and 262 jobs, its last step `check-solkey.sh` reporting 37 mismatches
  that predate G01. Elapsed about 1 h 15 min.

## Review

### Sixth round: fourth integration hold (design change)

Master `9b6d1c29` merged. Fixed:

1. *Confirmed, blocking: B1 at a higher threshold.* The region conjunct
   fails by counting past about `2^256/L` distinct slot preimages, so a
   source run through `f(2^191)` (or `h = keccak(h)`) violated the premise
   right after the history before the request, and `Collided` freed the
   rest of the session, though the target never ran that loop. Design
   change: each layer's `Guard` reads its own run's preimages; backward
   soundness is guarded by the **target's** premise
   (`RefinesUnder AS AT FS GS GT`), forward by the source's; `Collided`,
   `NoCollisionUpTo`, `Cert.reflect` and `Matched` are gone; `Cert.back`
   carries the premise back; `EvmSpec.slotHashed` and `EvmSpec.guard_iff`
   are new; `hashes_source` also restricts the EVM's slot preimages to the
   source's, so the compiler cannot choose what the EVM premise reads. The
   correct compiler keeps the escape where needed: a target that really
   runs the long loop, or reads a key colliding with one it wrote (after an
   out-of-gas transaction or not), hashed those preimages itself, so the
   second and fourth rejections stay closed.
2. *Doc*: the counting threshold is about `2^256/L`, not the count of
   `hashBound`; the conservative region rule (two single-slot values within
   `L` count as overlapping) is stated.
3. *Recorded*: the gas-triggered bricking gap (see the
   [resources](#resources-horizons-failures-and-gas)).

### Fifth round: third integration hold

Master `040e59d` merged. Fixed:

1. *Confirmed, blocking: the count in the premise opened the escape on one
   request.* `f(2^130)` makes the idealized source hash `2^128` distinct
   preimages within one transaction, so `¬Guard` held right after its
   events and `Collided` freed it and every later transaction (and
   `NoCollisionUpTo`, `Matched`). The bound is back in `Forward`
   (`forward_iff`: no failure and fewer than `hashBound` distinct
   preimages), `Guard` is `HashPremise` only (`guard_iff`), for both
   `SourceSpec` and `IntrinsicSpec`; `Collided` still ignores `Forward`, so
   the fourth round's fix stays.
2. *The region conjunct read compiler-chosen code hashes.* `HashPremise`
   takes the slot preimages separately (`SourceSpec.slotHashed`,
   `IntrinsicSpec.slotHashed`).
3. *`regionLen` up to `2^128`.* `Fixed.Sane` stays a sanity bound; the doc
   states that the final statement uses the concrete `S.fixed`, with the
   profile's largest region.
4. *`hashed` granularity*: a named child obligation (S03.04, S05).

### Fourth round: second integration hold

Integration review held the revision back a second time; master `2abccb70`
is merged. Fixed:

1. *Confirmed: `refines` unmeetable through the backward escape.*
   `Collided` required the source prefix to be in `FS` (no failure, below
   `hashBound`), so a real collision after an out-of-gas transaction had
   no escape. The bound moved into the premise (reverted in the fifth
   round, which keeps the rest), `Forward` was only "no resource failure",
   and `Collided`,
   `NoCollisionUpTo`, `Cert.back`/`reflect`, `Cert.comp` and `SpecTransfer`
   no longer mention `FS`. The intrinsic layer's `forward_iff`/`guard_iff`
   follow.
2. *Plausible: no hashing witness.* `SourceSpec.NonVacuous` has a success
   witness whose run hashes; `PublicCorrectness.succeeds_hashing` carries it
   to the bytes.
3. *Doc:* the `Fixed.Sane` cap in the decisions table is `2^128`.
4. *G03 ledger:* `MODULES["G01"]` lists `Solidity.Roadmap.TypedRun`, D08
   cites `typedRunPrefixes` in `TypedRun.lean`; the acknowledgements naming
   G01 for `Solidity.Evm.Machine` and `Solidity.Semantics.Deploy` no longer
   do, because `Contracts.lean` imports neither any more (the checker
   flagged them); those for RevertData, RevertBytes, Heap, Storage, Checked
   and the `G01 <- G24.04` inversion stay. `roadmap-g03-ledger.py --write`
   and `--check` pass (0 errors).

### Third round: finder and skeptic on the second integration round

A read-only finder and skeptic (neither using the Lean server) reviewed the
merged head. Fixed:

1. *Blocking (finder, skeptic): the state export kept an EVM-side guard*
   (a bound on the bytes' own hash count and premise), which bytes hashing
   one preimage `2^128` times made vacuous. `decode_reach` and
   `decode_commutes` now assume `Matched`: the EVM prefix lies below a
   source prefix in the forward bounds that meets the premise.
2. *Blocking (skeptic): `hashes_source` was unprovable*: a transaction that
   fails from gas hashes before failing, and no single source bound contains
   both that hash and the later session's. It is now per preimage.
3. *Blocking (finder): `decode_commutes` read the intrinsic layer's
   unconstrained `Forward`/`Guard`.* `IntrinsicSpec` now reads the session
   environment exactly and pins `Forward`/`Guard` (`forward_iff`,
   `guard_iff`); `PublicCorrectness.ifixed`/`isession` tie it to the EVM.
4. *Duplicates counted toward `hashBound`* (skeptic): the bound counts
   distinct preimages (`distinctCount`).
5. *`Fixed.Sane` too small for in-profile storage* (skeptic): raised to
   `2^128`, and part of `EvmSpec.Approved` too (finder: the doc claimed it).
6. *`PrefixFree` failed on interfaces' empty creation bytes* (skeptic): it
   ranges over nonempty units.
7. *The divergence witness was trivial for a never-ending session*
   (skeptic): it now has a single request (`SessionEnv.OneRequest`).
8. *Precompiles' code existence was free* (skeptic):
   `SessionEnv.PrecompilesHaveNoCode`.
9. *`not_alwaysRevert` ranged over every environment and bound* (finder):
   now over allowed environments and admissible bounds.
10. *Doc errors* (finder): the module's imports, "frozen" wording, the core
    count, `NoExhaust` renamed `NoFailure`, `Solidity.Evm.W`, the
    correspondence of `Pipeline`/`AbiCoder` with G05's types, the claim that
    precompile gas is pinned (now a listed child obligation), the base
    revision in the introduction.

Recorded, not changed (child obligations above or limitations): the pins
without Lean constants (Osaka precompile gas, non-cryptographic
precompiles, G03's ledger); `Failures`/`NoFail`/`hashed` pinned only in the
concrete source; runtime-code fidelity of `creationCode`/`runtimeCode`; the
committed-history restriction on strategies; EIP-684/7610 and EIP-3607;
the library deployment convention; the acknowledged gas-threshold, logs,
post-bound and post-collision freedoms; `Cert.comp` was checked correct.

### Second integration round

Integration review held the revision back. Its points and what was done:

1. *Confirmed: `refines` could not be met for long sessions*: the
   `2^128` bound restricted only the EVM's hashes, while adequacy ranged
   over every source bound without failures. The bound is now on the
   source (then `SourceSpec.forward_iff`: no failure and fewer than `hashBound`
   source-determined preimages), compiler-independent; the EVM has no
   forward restriction (`EvmSpec.Approved`), and `Cert` carries the source's
   `Forward` to each target.
2. *Confirmed: unconstrained `regionLen`/`rootSlots`.* `Fixed.Sane`
   (then `1 ≤ regionLen ≤ 2^64`, `rootSlots ≤ 2^64`; raised to `2^128` in
   the third round) is part of both `Approved`
   predicates and `Fixed.Keccak`. `not_alwaysRevert` no longer assumes
   anything about the bytes' hashes: the premise is on the source, and
   `NonVacuous`'s success witness meets it.
3. *Plausible: bytes hashing a known collision pair falsify the guard.*
   Adopted G06's F7: the premise reads the preimages the source run
   determines (`SourceSpec.hashed`, `guard_iff`), `RefinesUnder` guards the
   source bound, and `hashes_source` makes the bytes hash only
   source-determined preimages; the state export is guarded by `Matched`,
   a source-side premise (third round).
4. *Unification with `Solidity.Hash.CollisionBound`.* `CollisionFree` is an
   alias of `Solidity.Hash.CollisionFree`; `HashPremise` is by definition
   `Hash.CollisionFree ∧ Hash.RegionsDisjoint`. The claims that the sibling
   bounds `RunCollisionFree` are gone (that predicate is gone).
5. *G06's findings F1–F8 and G05's per-unit coder*: all absorbed (see the
   [decisions table](#decisions-applied)): F1 failures and dropped requests
   as resources (`SourceSpec.Failures`, `Lang.Affordable`, requests indexed
   by count); F2 divergence read without failures ([resources](#resources-horizons-failures-and-gas));
   F3 finitary realizability left to `Evm.Certificate` ([the session
   environment](#the-session-environment)); F4 forced failures in the source
   semantics; F5 `Fixed.evm : Evm.Fixed` shared by both sides; F6 the static
   flag on `Event.reenter`/`Move.reenter`; F7 above; F8 `EvmSpec.pin` with
   `V.pin = Evm.pinned`. The ABI coder is per unit (`pragmaCoder`, `coder`,
   `coderOf` take the unit's index).
6. *Frozen wording* withdrawn until integration accepts the revision.
7. *Duplicated `docs/README.md` row*: only the new row is kept.

### This revision

A read-only finder and a separate skeptic reviewed the first push of this
revision, neither using the Lean server. Their findings and what was done
(superseded in part by the later rounds: the bound and the premise moved to
the source, the intermediate languages' premises are carried and pinned,
`never` became `NoFail`, and the closure of `Contracts.lean` is no longer
`Solidity.Keccak` alone; names below are as they were then):

**Fixed** (all in `Contracts.lean` and this document):

1. *Blocking (finder): the hash premise could make the public contract
   vacuous.* Bytes hashing more than `2^256` preimages violate the premise
   by counting at every large bound, so the guarded forward direction held
   vacuously. Adequacy now names only bounds in the EVM's `Forward`, runs
   hashing fewer than `hashBound = 2^128` preimages (`Lang.Forward`,
   `EvmSpec.forward_iff`, `RefinesUnder`'s `FT`). The false claim that
   refuting the premise needs an exhibited collision is corrected.
2. *Blocking (finder, skeptic): adequacy over every exhaustion choice was
   unsatisfiable* (63/64 forwarding; the 1024 call-depth limit). Adequacy
   now ranges over the source's `Forward` bounds, `never` only
   (`SourceSpec.forward_iff`, `RefinesUnder`'s `FS`, `Cert.need_ok`), and
   `never` includes the deterministic call-depth failures.
3. *Blocking (skeptic): `decode` of a world alone and `decode_commutes`' guard
   over the continuation only* were false for mappings with colliding keys.
   `decode` now takes the run's preimages, and the continuation's guard is
   the premise over the prefix's preimages followed by its own.
4. *`creationCode` was not tied to what `new C` deploys* (skeptic). Added
   `EvmSpec.created`, `Artifact.initcode`, `Artifact.PrefixFree`, `createsOf`
   and the field `PublicCorrectness.creates_table`.
5. *The non-session part of an environment was free* (skeptic). Added
   `of_session` to both specs; `PublicCorrectness.envAbs_eq` shows `envAbs`
   is forced.
6. *Intermediate languages could set `Guard := False`* (finder). Added
   `IntrinsicSpec.guard_trivial` and `Compilation.asm_guard`.
7. *Settings were not tied to the meaning* (finder, skeptic). Added
   `SourceSpec.pipelineOf`, `coderOf` and `SettingsResolved` (in
   `SourceSpec.Approved`); `PublicCorrectness.allPipelines` no longer takes
   an unused membership hypothesis.
8. *Precompile functions not shared; code existence not in the environment;
   resumed sessions' balances unrelated to the world* (skeptic). Added
   `Fixed.precompile`, `SessionEnv.hasCode` with `CodelessSucceeds`,
   `EvmSpec.balances` and the balance premise of `decode_commutes`.
9. *`not_alwaysRevert`'s hypothesis ranged over every artifact* (finder);
   it now ranges over compiled artifacts and bounds below `hashBound`.
10. *Remaining `Nat` values; `this` only in prose* (finder). `Ledger` returns
    `Word`, `deployNonce` is 64-bit; `Fixed.createAddress` and
    `Lang.ThisFromDeployment` (in both `Approved`) tie `this` to the
    deployment.
11. *Gate text* (finder): `Contracts.lean` no longer imports
    `Solidity.Syntax.Raw` (`Pipeline.order` and `SourceSpec.order` moved to
    `TypedRun.lean`), so its closure is `Solidity.Keccak`, which has no
    imports.
12. *Stale wording* (finder): the reuse-map row for `address(this) < 2^160`,
    the `PublicCorrectness` docstring on Keccak, the `docs/README.md` row,
    the "for the user to confirm" readings (removed when the second-round
    decisions settled them).
13. *Solc-style layout not covered by the premise* (skeptic): already
    covered by the second-round regions (`RegionsDisjoint`).

**Recorded, not changed:**

- *Ledger not pinned; exhaustion choices and the bound order uninterpreted;
  intrinsic worlds compared by equality; the intrinsic layer `I` free*
  (skeptic): child obligations in the table above (G03/G06 pins, S03.04,
  S05, G22/G24, G49.03). The final statement must name the concrete
  intrinsic layer.
- *Gas thresholds* (skeptic): with every gas schedule admissible, a
  compiler correct only above huge gas satisfies the contracts; stated under
  [resources](#resources-horizons-failures-and-gas).
- *The table fixed point* (skeptic): not checked by `PublicCorrectness`;
  stated in the gate.
- *Outside this task's files* (finder): `docs/solidity-scope.md` still says
  "none is done yet" for the follow-up list, and `docs/parallelism.md`'s
  family list of the core does not name `Roadmap`; both are for the
  integrator.

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
