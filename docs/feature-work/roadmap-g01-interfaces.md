# Roadmap G01: interfaces and the six final theorem contracts

Group G01 of the [roadmap](../coverage-plan.md), wave 0. This document fixes the
types, observations, state and world relations and refinement notion of the
six final proof obligations, the shape of a compositional pass certificate,
and the frontend, backend and EVM proof boundaries. It proves none of the
obligations. Facts about existing code are pinned to the base revision
`127c2ee59de16971e45b08a2def54f4e5fae8e2a`.

The contracts are also stated in Lean, as definitions only:
`Solidity/Roadmap/Contracts.lean` (namespace `Solidity.Roadmap`). The module
is dependency-free and below the elaborator: it imports
`Solidity.Semantics.RunFuel`, `Solidity.Semantics.Lifetime` and
`Solidity.Evm.Machine` only. It contains no `sorry` and no axiom. Its few
lemmas check the shape of the contracts and nothing more: the order is a
preorder, refinement composes, and refinement transfers safety, completion
and divergence. They are not final theorems.

Nothing here is frozen where a user decision is needed. Those points are
listed under [open scope questions](#open-scope-questions).

## Contents

1. [Layers and interface types](#layers-and-interface-types)
2. [Common semantic notions](#common-semantic-notions)
3. [The six contracts](#the-six-contracts)
4. [Pass certificates and proof boundaries](#pass-certificates-and-proof-boundaries)
5. [Reuse map](#reuse-map)
6. [Open scope questions](#open-scope-questions)
7. [Child obligations](#child-obligations)
8. [Handoff](#handoff)
9. [Review](#review)

## Layers and interface types

Each layer is an intrinsic type. No layer is an untyped intermediate
representation, which follows [intrinsic.md](../intrinsic.md). The
`Contracts.lean` name for each layer is given in brackets.

| # | Layer | Type | Owner |
|---|---|---|---|
| L0 | Raw compilation input: named source units, the selected unit and pinned settings | `SourceSpec.Input` | G00 (pins), G12 (units) |
| L1 | Source syntax under the pinned grammar | `SourceSpec.Syntax`, judgment `Parses : Input → Syntax → Prop` | S00 |
| L2 | Resolved, typed declaration graph | `SourceSpec.Resolved`, judgments `Resolves`, `WellFormed` | S01 |
| L3 | Approved profile | `SourceSpec.InProfile : Resolved → Prop` | G00, G15 |
| L4 | Source meaning: deployment and transaction sessions | `SourceSpec.lang : Lang Event Outcome`, `meaning` | S02–S05 |
| L5 | Intrinsic typed contract world: `Contract`, `Prog C Γ Γ'`, `State C Γ` and a world of typed instances | `IntrinsicSpec.World`, `IntrinsicSpec.lang` | G16–G24 (see the [reuse map](#reuse-map)) |
| L6 | Backend languages chosen by the compiler, one per pass | any `Lang Event Outcome` | G24–G44 |
| L7 | Assembly: instruction lists with labels | `Lang Event Outcome` with programs over instructions | G45 |
| L8 | Bytecode artifacts | `Artifact`: a table of `CodeUnit`s (`initcode`, `runtime : List UInt8`, library link sites), one per contract and library, and the selected one | G44, G45 |
| L9 | Pinned EVM: accounts with code, executing transactions | `EvmSpec.lang`, `EvmSpec.load` | G06, G46, G47 |

The judgments at L1 and L2 are relations defined from the pinned grammar and
type rules. They are not the parser and not the elaborator. The frontend is a
function that contract 1 relates to them.

## Common semantic notions

All declarations named in this section are in `Solidity/Roadmap/Contracts.lean`.

### Executions as consistent families of resourced finite prefixes

A `Prefix E O` (line 51) is what a finite execution prefix shows: `events :
List E` and `final : Option O`. A prefix whose `final` is `none` is still
running or has run out of resources. Running out of an excluded resource is
therefore **not an observation**: it ends a prefix without a final value.
This applies to the compiled system's own resources. A callee outside the
system that runs out of gas is an environment answer (a revert), and how gas
the system forwards shapes such answers is open scope question
[Q7](#q7-gas-dependent-environment-behaviour).

One execution is `Prefixes R E O := R → Prefix E O` (line 81), a prefix at
each resource bound `r : R`. Every language's semantics is consistent,
`Prefixes.Consistent` (line 85): more resources extend the events, and a
completed prefix stays the same. This is a field of `Lang` (`consistent`,
with the order `resLE` on resources), so a semantics that completes with a
success at one bound and with a revert at a larger one is not a language. Under this reading:

- an execution **completes** with `o` when some bound completes it
  (`Prefixes.Completes`, line 89);
- an execution **diverges** at the admitted bounds when no admitted bound
  completes it (`Prefixes.Diverges`, line 94).

The divergence claim is therefore about a consistent family of finite
prefixes. It never says that one finite-gas EVM transaction diverges. A
source with an unbounded loop has prefixes at every fuel, none completed.
Its target has prefixes at every gas bound, none completed: they end out of
gas, or their events keep growing.

The prefix order `Prefix.Le` (line 57) says that `a` is below `b` when `a`'s
events are a prefix of `b`'s and, if `a` completed, `b = a`. It is a preorder
(`Prefix.Le.refl`, `Prefix.Le.trans`). A completed prefix is below only
itself (`Prefix.Le.final_eq`, line 74).

### Refinement, resources and the resource abstraction

`Lang E O` (line 104) is a language at one layer. It has programs,
environments, a resource type `Res` with an order `resLE`, `Allowed : Env →
Prop`, `Admissible : Res → Prop`, `sem : Prog → Env → Prefixes Res E O` and
the proof `consistent` that every execution is a consistent family.

`Refines AS AT s t` (line 115) is two-sided:

1. **Forward (resource adequacy).** Every admissible source prefix is below
   some admissible target prefix.
2. **Backward (functional soundness).** Every admissible target prefix is
   below some admissible source prefix.

It is transitive (`Refines.trans`, line 120). Three consequences are proved
in the module:

- **Completion transfers** (`Refines.completes`, line 135). A source prefix
  that completes with `o` at an admissible bound gives an admissible target
  prefix with the same final observation and the same events.
- **Nothing is invented** (`Refines.sound`, line 145). A target completion is
  a source completion with the same events.
- **Divergence transfers** (`Refines.diverges`, line 155). A source that never
  completes at admissible bounds has a target that never completes at
  admissible bounds.

`Refines.safety` (line 169) transfers any downward-closed prefix property
from source to target.

The resource abstraction is `Lang.Admissible`, chosen per layer, plus the
explicit bound function `Cert.need` of each pass certificate (below). `need`
maps each admissible source bound to an admissible target bound at which the
target prefix lies above the source prefix. So resource adequacy is a
function proved correct, never the assumption that the target execution
already has the desired result. The type does not force `need` to be
computable: a `need` defined by `Classical.choose` would only restate the
forward direction. That the final bound is a definition without choice
(constructive, or a proved closed-form bound) is checked on the final
theorems' definitions and axioms (G49.03, G54).

At the ends of the pipeline:

- **Source.** The proposed default is `SourceSpec.Idealized` (line 302):
  every fuel bound is admissible, so the source's prefixes are all of its
  behaviour.
- **EVM.** `Admissible` is the set of gas/memory/stack/code resources the
  approved profile permits. It is open scope question [Q2](#q2-fixed-evm-limits)
  and must not silently idealize the EVM.

### Nondeterministic environment quantification

The environment is everything the program does not determine: the
transaction requests (sender, value, timestamp, calldata), callee and
callback behaviour, payment acceptance, the funds of other accounts and
creation results. Each semantics is deterministic given its environment.

A pass maps target environments to source environments (`Pass.envAbs`).
Its certificate requires two things:

- `envSound`: every allowed target environment maps to an allowed source
  environment;
- `envOnto`: every allowed source environment is reached.

Correctness holds for **every** allowed target environment. No source
environment can be dropped by realizing only environments in which nothing
happens. Adversarial interaction (G50) is part of this quantification: a
session's request sequence and every callee strategy are part of the
environment.

### Shared observations

The observation types are fixed once for every layer, so no pass can pick a
weaker observation.

- **`Outcome`** (line 245): `success (returnData)` or `revert (revertData)`,
  as ABI bytes. A panic is a revert with `Panic(uint256)` data. A custom error
  is a revert with its selector and arguments. `Error(string)` is a revert
  with its encoding. The empty revert is `revert []`.
- **`Event`** (line 258): what the compiled system asks of the environment
  and what the environment answers:
  - the deployment of the selected contract with its outcome and address
    (`deploy`), so a failed deployment is not hidden behind later empty
    successes;
  - outgoing typed external calls and payments to accounts outside the
    system (`call`, with callee, value, ABI input and the static flag);
  - creations (`create`), naming the created contract by its position in
    the compilation input, a source identity, so neither side numbers code;
  - the environment's `answer` (an outcome, or the created address);
  - a session's completed transactions (`tx`, with request and outcome).

  The **compiled system** is every contract and linked library of the
  compilation input. A call between its instances, and a linked library
  call (which runs on the caller's storage), is internal to the semantics,
  not an event. Whether this is the approved boundary is open scope question
  [Q8](#q8-system-boundary-libraries-and-created-contracts).

The recorded exclusions are omitted on purpose: logs, gas, raw layout,
`selfdestruct`, raw calldata and the extra block fields
([solidity-scope.md](../solidity-scope.md)). Event (log) arguments still
execute, with their effects and failures, inside the semantics.

### State and world relations

The public contracts do not expose a state relation. They relate
observations over sessions. Persistent state is observed through later
transactions of the same session, so a compiler-chosen representation (any
storage packing, any memory layout) is allowed. A trivial or erased
representation relation gains nothing, because the observations stay fixed.

The proofs still need these relations as internal lemmas, and the owning
groups must state them:

| Relation | Between | Owner |
|---|---|---|
| `R_low` | source world (S04.03: accounts, typed persistent and transient stores, balances, time) and intrinsic world | G16–G23 |
| `R_rep` | intrinsic world and backend states: storage representation (G27), memory and frames (G32), calldata (G35, G40), world and payments (G42–G44) | G24–G44 |
| `R_evm` | the assembly machine and the pinned EVM state: byte memory, real `KECCAK256` slots, stack, accounts and code | G46, G47 |

State-level specification transfer (a storage invariant read on the EVM
world, not only through later transactions) needs one of these relations
exported in functional form. That is open scope question
[Q6](#q6-state-level-transfer).

## The six contracts

`SourceSpec` (line 281) bundles the independent source side: `Input`,
`Syntax`, `Resolved`, the judgments `Parses`, `Resolves`, `WellFormed`,
`InProfile`, the session language `lang` and `meaning : (r : Resolved) →
WellFormed r → InProfile r → lang.Prog`. `meaning` is total on admitted
input because its proofs are arguments.

### 1. Source admission and parsing — `Admission`, `CheckedFrontend`

**Types.** `Admission S` (line 330) has `frontend : S.Input → Option
S.Resolved` and two fields:

- `sound`: an accepted input is `S.Admitted` (line 323), meaning it parses
  under `Parses`, resolves under `Resolves`, is `WellFormed` and is
  `InProfile`;
- `complete`: every admitted input is accepted with exactly its resolution.

For a proof-producing frontend, `CheckedFrontend S` (line 336) splits
`frontend` into `produce` and a Lean `check`, with three fields:

- `checked`: acceptance by the checker implies admission;
- `accepted`: what is produced passes the checker;
- `complete`: every admitted input produces its resolution with some
  certificate.

`SourceSpec.Unambiguous` (line 306) requires `Parses` and `Resolves` to be
functional, which `complete` needs to be meaningful. It is an S00/S01
obligation.

**Observation.** Acceptance with the resolved graph, or rejection.
Rejection is exact by `complete`: an input is rejected only if it is not
admitted.

**Premises.** The pinned settings and compilation-unit identity are part of
`Input` (G00 and G12). There are no other premises.

**Non-circular because** `Parses` and `Resolves` are relations from the pinned
grammar and type rules (S00/S01), not the frontend's code. A solc JSON AST,
a digest or `ScopeScan.within` (`Solidity/Frontend/Source.lean:299`)
instantiates neither: the last certifies only a feature list.

**Vacuity is excluded.** A frontend that rejects everything fails `complete`
on any admitted input. One that accepts everything fails `sound`. G07's
malformed-source controls exercise both.

### 2. Lowering — `Lowering`

**Types.** `IntrinsicSpec` (line 346) is the intrinsic world type, its
session language and `ofWorld`. `Lowering S I` (line 354) has:

- `lower : (r : S.Resolved) → S.WellFormed r → S.InProfile r → I.World`.
  It is total by its type, which proves admission coverage: there is no
  `Option` and no importer refusal.
- A pass `S.lang → I.lang` whose domain contains every source meaning (`dom`)
  and whose output is `ofWorld (lower …)` (`agrees`).
- Its certificate `cert : Cert pass`.

**Observation and relation.** The shared `Event` and `Outcome`. The
certificate gives `Refines` in both directions at every allowed environment
(`Cert.refines`, line 202). Typing preservation is in the target type
itself, since `lower` produces intrinsic `Prog C Γ Γ'`. Evaluation order and
failures are preserved because they show in the events and outcomes.

**Premises.** Only the approved environment set `I.lang.Allowed` and its
resources.

**Non-circular because** `S.lang` and `S.meaning` come from S02–S04 without
the lowering. The import gate in [non-circularity](#non-circularity-as-a-checkable-gate)
enforces this. An always-reverting or erased lowering fails `Refines.completes`
on any source program that completes with a success (G07 control).

### 3. Compilation — `Compilation`

**Types.** `Compilation I Asm` (line 389) has `compile : I.World →
Asm.Prog`, total, a pass whose domain contains every lowered world (`dom`),
`agrees`, and `cert`. Its pass is the composition of all backend passes
(G24–G44) by `Cert.comp`. Calls, deployment, runtime dispatch and linking
are passes like any other, not side conditions: dispatch on the ABI
selector, receive and fallback (G40) and constructor/initcode generation
(G44) produce the session behaviour that `Event.deploy` and `Event.tx`
observe, and linking is the `CodeUnit.links` table of the `Artifact`
(line 372) that contract 4 resolves.

**Premises.** None beyond allowed environments. Fragment predicates may be
the `Dom` of an inner pass. The closure hypothesis of `Pass.comp` and the
`dom` field ensure no such predicate survives into contract 3: every lowered
world is in the domain.

**Vacuity is excluded** for the same reason as contract 2. An always-reverting
backend fails `need_ok` at the first source success.

### 4. EVM execution — `Execution`

**Types.** `Execution Asm V` (line 398) has `assemble : Asm.Prog → Artifact`,
total, and a certified pass `Asm → V.lang` whose output is `V.load (assemble a)`.
The pass composes:

- instruction selection, stack lowering, labels and loops, assembly and byte
  encoding (G45);
- jump and `JUMPDEST` realization of structured control (G45.03);
- the bridges to the pinned EVM: numeric, byte memory and calldata, storage
  with real hashing, transient storage (`TLOAD`/`TSTORE`, reset at the end
  of the transaction), environment, hash, call/create/return with returndata
  and revert bytes, and rollback of persistent and transient state and of
  balances on revert, and the transaction (G46, G47).

The `Artifact` is a table of `CodeUnit`s (`initcode`, `runtime`, library
link sites) for every contract and library of the input, with the selected
one (`main`); `load` deploys it with its libraries linked.

`EvmSpec` (line 381) is the pinned EVM as a `Lang`, with `load` installing
an artifact and running a session. Its resources are gas, memory, stack and
code size. Its `Admissible` is the approved resource profile
([Q2](#q2-fixed-evm-limits)). Its `Allowed` is the full set of pinned EVM
environments less approved premises only ([Q4](#q4-environment-model),
[Q7](#q7-gas-dependent-environment-behaviour)): it is fixed by G06 and the
user, never chosen by the compiler, so it cannot leave out malformed
calldata, value sent to a non-payable function or hostile callees.

**Non-circular because** `EvmSpec` is the pinned EVM semantics from G06, not
the compiler's own machine, and the import gate (below) applies to it as to
the source: `load` must decode bytes by the pinned EVM's own decoder, never
by an inverse of `assemble`. The current `Evm.Machine` is at most an inner
language here (see the [reuse map](#reuse-map)).

### 5. Composition: the public theorem — `PublicCorrectness`

`PublicCorrectness S V compiler envAbs` (line 409) is the conjunction of
three statements:

1. **Coverage, and no success on unsupported input.** For every input, the
   compiler returns an artifact exactly when the input is admitted.
2. **Environment coverage.** Every allowed source environment is the
   abstraction of an allowed EVM environment.
3. **Refinement.** For every admitted input, every artifact the compiler
   returns, and every allowed EVM environment `e`:
   - `envAbs e` is an allowed source environment, and
   - the source session meaning at `envAbs e` refines the artifact's EVM
     sessions at `e`, at the source's and the EVM's admissible resources.

Sessions include deployment (`Event.deploy`) and every sequence of
transactions (G50). The final public statement is the conjunction of:

- `PublicCorrectness` with `compiler` the concrete pipeline definition, the
  composition of the frontend and of contracts 2–4. It must be computable
  (no `noncomputable`, no choice in its definition) and be run on G07's
  controls, since the type alone does not make a parameter executable;
- `SourceSpec.Idealized`, unless the user approves a source-side resource
  ([Q1](#q1-source-resources));
- `SourceSpec.NonVacuous` (line 315): admitted inputs whose meanings, at
  allowed environments, complete with a success with data, complete with a
  revert, and diverge. Without it an empty input type, `InProfile := False`
  or a `sem` that ignores the program would make every contract vacuous.

The obligations of the roadmap read off this contract as follows:

- **Success and failure are preserved.** `Outcome` is part of the final
  observation, so a source success is a target success with the same return
  bytes, and a source revert is a target revert with the same data
  (`Refines.completes`, `Refines.sound`).
- **No always-revert compiler.** Any admitted program with a completing
  success refutes it, by `Refines.completes` and statement 1 above.
- **Divergence** is matched by `Refines.diverges` and the forward direction:
  prefixes of growing events.
- **No fixed fuel.** Fuel is a resource index of a consistent family, not a
  premise.
- **Resource abstraction.** Target exhaustion is `final = none`, and adequacy
  is the composed `need`.

**Premises.** Exactly the allowed EVM environment set and the admissible EVM
resources, both approved by the user (G00 and G06). There is no
hash-injectivity premise. Adding one requires approval
([Q3](#q3-hash-collisions)).

### 6. Verification and trust — `SpecTransfer`

`SpecTransfer S V compiler envAbs` (line 422) says that for every admitted
input and allowed EVM environment, two kinds of source specification hold
of the bytes:

- **Safety (box-like).** A downward-closed prefix property that holds at
  every admissible source prefix holds at every admissible EVM prefix. A box
  postcondition, "if it completes with `success d` then `Q d`", is downward
  closed.
- **Completion (diamond-like).** A source completion at an admissible bound
  gives an EVM completion with the same outcome at an admissible bound.

The semantic half is proved from contract 5 (`PublicCorrectness.transfer`,
line 434, no axioms). The rest of contract 6 is meta-level and owned by G51,
G54 and G55:

- **Rule soundness.** Every added calculus rule is sound. `Proves.valid`
  (`Solidity/Calculus/Sound.lean:38`) is the existing form, on the intrinsic
  typed run.
- **The bridge from `⊨` to these prefix properties.** On the intrinsic
  language this needs:
  - the box's acceptance of revert, divergence and exhaustion to be read as
    a downward-closed property;
  - the diamond's acceptance of exhaustion to be excluded from completion
    transfer, since an exhausted diamond witnesses no completion;
  - then contracts 2–5.
- **Trust.** No `sorry`, no new axioms and a reproducible kernel check. The
  existing gates are `scripts/check-trust.sh` and `TrustAudit.lean`
  ([assurance.md](../assurance.md)).
- **Automatic search is separate.** `SpecTransfer` transfers whatever is
  proved; it does not ask any tactic to find the proof. The approved target
  and exclusions of `sol_prove`/`sol_decide` remain unchanged, and a
  specification that automation does not prove is a search limitation, not a
  gap in the compiler's contracts (roadmap obligation 6). G51.02 records the
  approved search target separately from these contracts.

### Non-circularity as a checkable gate

The proposal for G07 has three parts:

1. **Import whitelist.** The modules instantiating `SourceSpec` (S00–S05)
   may import only an explicit whitelist: Lean's prelude, the new source
   modules, and named datatype modules (such as the one defining `Ty`), each
   with its S05 correspondence theorem. In particular they reach neither
   `Solidity.Syntax.Scoped` (the intrinsic programs) nor
   `Solidity.Semantics.Run` (their run), nor `Solidity.Evm.*`,
   `Solidity.Frontend.*` or `Solidity.Syntax.Elab*`. A blacklist would not
   do: an S04 module could define its own `toIntrinsic : Resolved → Prog …`
   and set `meaning := Prog.run ∘ toIntrinsic`, and `Lowering.lower :=
   toIntrinsic` would make contract 2 an identity. This is a mechanical
   check in the style of `scripts/check-layers.mjs`.
2. **No `meaning` through the pipeline, checked both ways.** `S.meaning` must
   not mention `I.lang`, `lower` or a later layer (enforced by (1)), and the
   converse check: the constants `Lowering.lower` unfolds to include no
   constant of the source closure other than the whitelisted datatypes and
   the judgments it consumes.
3. **The EVM end too.** The module instantiating `EvmSpec` imports the pinned
   EVM (G06: the core interface, or the external adapter in `Bridge/`) and no
   compiler module, so `load` cannot decode an artifact by the inverse of
   `assemble`.
4. **Reuse of an intrinsic type is a correspondence theorem.** If the source
   semantics reuses an intrinsic datatype (say `Ty` or `Storage C`), S05
   proves its correspondence. Reuse never defines the source by compiled or
   lowered output (roadmap, "Independent source definitions").

## Pass certificates and proof boundaries

### Certificate shape

A pass `π : Pass L₁ L₂` (line 180) has an input domain `Dom`, a function
`run` on that domain and `envAbs`. A **certificate** `Cert π` (line 192) is
data, not only a proposition. Its fields are:

- `envSound` and `envOnto`;
- `need : (p : L₁.Prog) → π.Dom p → L₂.Env → L₁.Res → L₂.Res`, the
  constructive resource bound;
- `need_ok`: at every allowed target environment and admissible source
  bound, `need` is admissible and the source prefix is below the target
  prefix there;
- `back`: every admissible target prefix is below an admissible source
  prefix.

`Cert.refines` (line 202) turns a certificate into `Refines` for one program
and environment.

### Composition lemma

`Pass.comp π₁ π₂ closed` (line 209) needs
`closed : ∀ p h, π₂.Dom (π₁.run p h)`. The second pass must accept every
output of the first, so a domain cannot remain a restriction of the composed
pass. Its statement:

```lean
def Cert.comp (c₁ : Cert π₁) (c₂ : Cert π₂) (closed : ∀ p h, π₂.Dom (π₁.run p h)) :
    Cert (π₁.comp π₂ closed)
```

This is `Solidity/Roadmap/Contracts.lean:217`, proved; it depends on
`propext` only, pinned by `#guard_msgs`. The composed bound is
`need₂ ∘ need₁`; the backward direction chains the two `back` fields.

Mixed programs (G24) are handled by passes whose domain is all intrinsic
programs. A per-feature compiler is an inner component, and its fragment
predicate is discharged inside the pass, not exported.

### Boundaries

| Boundary | From → to | Contract | Trusted base on each side |
|---|---|---|---|
| Frontend | L0 → L2 | 1 (`Admission` or `CheckedFrontend`) | Source: the pinned grammar and type rules as Lean relations. External: solc only as an untrusted certificate producer. |
| Lowering | L2/L4 → L5 | 2 | Source semantics S02–S04; the intrinsic world's semantics |
| Backend | L5 → L7 | 3 | Composed `Cert`s of compiler passes; no fragment predicate in the final `dom` |
| EVM | L7 → L8 → L9 | 4 | The pinned EVM semantics (G06). The core states the interface; an external implementation (EVMYulLean) stays in `Bridge/`. |

No boundary uses the next layer's semantics to define the previous one:

- the source is defined without L5;
- L5 has its own run;
- the backend languages are the compiler's;
- the EVM is pinned externally.

Each boundary is a `Cert`, so the four compose by `Cert.comp`. Contract 1
supplies the admitted inputs.

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
| `Contract`, `Stmt`, `Prog`, `State`, `TTx` | `Solidity/Syntax/Raw.lean:404`, `Solidity/Syntax/Scoped.lean:335`, `:445`, `Solidity/Semantics/State.lean:115`, `:105` | Components of `IntrinsicSpec.World` and its states | (a) Function bodies live inside call statements (an inductive-inductive contract is avoided, [intrinsic.md](../intrinsic.md), "What stays extrinsic"). (b) A recursive call is unrolled to `recDepth = 1024` frames whose bottom is `exhausted` (`Stmt.callRec`, `Scoped.lean:429`; `Prog.recBase`, `:455`; `recDepth`, `:469`). Under `Idealized` source resources this is a cutoff that G37 must remove, unless [Q1](#q1-source-resources) approves call depth as a source resource. (c) `TTx.ext` is a static response table keyed by call: two identical calls read the same entry ([Q4](#q4-environment-model)). |
| `THalt`, `TRes`, `Prog.run` | `Solidity/Semantics/Run.lean:58`, `:79`, `:1153` | The final value of an intrinsic prefix, after mapping to `Outcome` | `THalt` erases error classes. A failing `assert` is `.panic` without its code; `.revertWith d` keeps revert data where the run has it, but overflow, bounds, empty `pop` and division by zero are plain `.revert` and lose their `Panic` codes, as do `Error(string)` and the distinction of empty data ([solc-alignment.md](../solc-alignment.md), "Remaining deltas", first item). Mapping to `Outcome` needs `Prog.withPanics` (`Solidity/Syntax/Checked.lean:587`) or the G38 revision. `.exhausted` must become "prefix ends" (`final = none`), never an observation. |
| `TLoop.run` (classical, divergence by `Classical.choose`) | `Solidity/Semantics/Run.lean:565` | The limit of a prefix family | It is not itself a resourced family. |
| `Prog.runF` (loop fuel) and `Prog.runF_approx` | `Solidity/Semantics/RunFuel.lean:319`, `:449` | The intrinsic family indexed by loop fuel; `Roadmap.typedRunPrefixes` (`Contracts.lean:454`) is the plug | `Prefixes.Consistent` (fuel monotonicity) is not proved yet: a child obligation of G24. There are no events; external calls are a table lookup, not an `Event`. |
| Push at `2^256 - 1` elements is `exhausted` (decision 15) | [intrinsic.md](../intrinsic.md), decision 15 | A resource stop (`final = none`) | solc panics with `0x41` at length `2^64` ([solc-alignment.md](../solc-alignment.md), "No bound on a dynamic array's length"). The pinned language is solc's, so S04 must define the `0x41` panic, and the intrinsic run then deviates from the source. G23/G30 must close the gap through `R_low`; it is not an exclusion. |
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

## Open scope questions

Each needs a user decision. None blocks this document.

### Q1. Source resources

Should the source be idealized (`SourceSpec.Idealized`: unbounded fuel,
unbounded recursion), or should the user approve a source-side resource, for
example internal recursion depth?

**Evidence.** The intrinsic run cuts recursion at 1024 frames
(`recDepth`, `Solidity/Syntax/Scoped.lean:469`). The roadmap forbids "finite
inlining/call-depth cutoff in the final semantics" (G37). With `Idealized`,
the compiler must realize deep recursion, for instance with frames in
memory, bounded only by gas.

### Q2. Fixed EVM limits

Which EVM resource profile is `EvmSpec.lang.Admissible`?

**Evidence.** Pinned limits that may make the forward direction false for
in-profile programs:

- the 1024-word stack and the 1024 call depth;
- the block gas limit;
- the runtime code size limit (EIP-170, 24,576 bytes) and the initcode size
  limit (EIP-3860, 49,152 bytes): a large admitted contract may compile to
  code the EVM refuses to deploy.

The roadmap requires such a conflict to be recorded and resolved with the
approved profile. It may not be resolved by erasing the program or by
silently idealizing the EVM. Options for the user:

- a recorded idealization of a named limit;
- an approved profile restriction (an exclusion with evidence, under G00);
- a compiler obligation, such as splitting into libraries, that is proved.

### Q3. Hash collisions

May contract 5 carry a premise about `KECCAK256`? If so, which one, for
example "the preimages hashed by this execution prefix do not collide"?

**Evidence.** The scope forbids global injectivity and requires any new
premise to be approved ([coverage-plan.md](../coverage-plan.md), "Scope
contract"). The current machine makes collision-freedom structural (`Slot`
terms). As stated, `PublicCorrectness` has no hash premise. Without approval
G46.05 must prove a representation that needs none, or report the gap.

### Q4. Environment model

Which environments are `Allowed`? In particular:

- a history-dependent callee strategy (the EVM's real behaviour: a callee's
  answer can depend on earlier calls) versus the current static `TTx.ext`
  table;
- callback (reentrancy) depth;
- whether the no-callback reading (`transferSemantics`) is a premise or a
  proved case;
- the existing modelling assumption that address 0 has no code
  ([solc-alignment.md](../solc-alignment.md), the `try` row);
- sender funds and precompile addresses.

**Evidence.** `envOnto` requires the source to accept every allowed EVM
environment's abstraction, so a narrow source environment set forces a narrow
EVM one. Narrowing is a scope decision.

### Q5. Observation granularity

Is the external `Event` list right as the public observation? It contains
the deployment, calls, payments, creations, answers and transaction outcomes
with ABI bytes.
Logs are excluded per the scope.

**Evidence.** Under these observations exact revert bytes are observable, so
G38 must preserve `Panic` codes ([solc-alignment.md](../solc-alignment.md),
"Remaining deltas", first item). A coarser observation, such as the failure
class only, would make that easier but weaker.

### Q6. State-level transfer

Must the public theorem also export a functional decoding of EVM storage to
the typed world? That would let a storage invariant transfer as a state
property, not only through later transactions.

**Evidence.** Session observations are enough for safety and completion
properties of interactions (`SpecTransfer`). A state invariant over
"reachable worlds" (`Lifetime.Reachable`, `ContractWorld.Reachable`) needs
`R_rep` exported, and a relation exported as a relation could be trivial.
Hence a function: `decode : EvmWorld → Option IntrinsicWorld`.

### Q7. Gas-dependent environment behaviour

How do gas and the environment interact? The contracts give one resource
bound per session (`Lang.Res`) and read exhaustion of the compiled system's
own execution as the end of a prefix. Two things are not decided:

- **Per-transaction gas.** A real session has a gas limit per transaction
  request, chosen by the sender. `Event.tx` records no gas, because gas is
  an excluded observation. Is "one bound per session, admissible per the
  profile" the approved reading, or must `Res` be a gas limit per request?
- **Gas-shaped answers.** In the EVM a call forwards at most 63/64 of the
  remaining gas, `transfer` and `send` forward a 2300 stipend, and a
  reentrant callback can run out of gas and be caught by the callee, after
  which the session continues. A callee's answer can therefore depend on gas.
  An `Allowed` set that ignores gas is a decision. The alternatives: let
  callee answers range over all outcomes regardless of gas (an
  over-approximation the source must also allow), or model the forwarded gas
  in the environment.

**Evidence.** [solidity-scope.md](../solidity-scope.md) excludes "exact gas
forwarding/stipends/refunds and real machine resource limits" as
observations; it does not say how the environment's gas-dependent answers
are quantified.

### Q8. System boundary: libraries and created contracts

Is the compiled system every contract and linked library of the compilation
input, so that linked library calls and calls between its own instances are
internal semantics, not environment events?

**Evidence.** Linked external library calls run on the caller's storage
([solidity-scope.md](../solidity-scope.md), "What requires explicit
abstraction"). An environment answer cannot mutate our storage, so modelling
libraries as environment would lose behaviour. The contracts therefore take
the whole input as the system: `Event.create` names a contract by its
position in the input, and `Artifact` is a table of `CodeUnit`s with library
link sites. The user should confirm this boundary, and whether
`type(C).creationCode`/`runtimeCode` (admitted only with matching artifacts,
[source-admission.md](source-admission.md)) observe the artifact table.

## Child obligations

Every field of the contracts has an owner.

| Field | Obligation | Owner |
|---|---|---|
| `SourceSpec.Parses`, `Unambiguous` (parse) | The pinned grammar as a relation; unambiguity | S00 |
| `Resolves`, `WellFormed`, `Unambiguous` (resolution) | Static semantics as relations; functionality | S01 |
| `InProfile` | Profile and combination predicate, with exclusion evidence | G00, G15 |
| `lang`, `meaning`, `inhabited` | Session semantics with events and outcomes, consistent prefix families (`Prefixes.Consistent`), nontrivial allowed environments | S02–S04, S05 |
| `Idealized` or an approved source resource | Q1 | user, then S03.04 |
| `Admission` or `CheckedFrontend` | Sound and complete frontend | G05 (interface), G08–G15 |
| `IntrinsicSpec` | The intrinsic world with events and prefix families; fuel monotonicity of `Prog.runF`; panic codes; no recursion cutoff | G22–G24, G37, G38 |
| `Lowering` (`lower`, `dom`, `agrees`, `cert`) | Total lowering and its certificate | G16–G23, G48 |
| `Compilation` | Total backend; composed `Cert`s; removal of the payment asymmetry and of the capacity premises | G24–G44, G49.01 |
| `Execution`, `EvmSpec` | Assembly, encoding and pinned EVM bridges; `Admissible` per Q2 | G06, G45–G47, G49.02 |
| `PublicCorrectness` | The composed public theorem with deployment and sessions | G49.03, G50 |
| `SpecTransfer` and its calculus bridge | `⊨`-to-prefix bridge; rule soundness | G51 |
| Non-circularity gate | The import-closure check described above | G07 |
| Always-revert and erased-observation controls | Instances of `Refines.completes` on inhabited programs | G07, G49.03 |
| Trust | Axiom inventory of the final theorems | G54, G55 |
| `Lang.consistent` for every layer | Consistency of each prefix family (fuel or gas monotonicity) | owner of that layer: S03.04, G24, G45, G46.06 |
| `SourceSpec.NonVacuous` | Success-with-data, revert and divergence witnesses at allowed environments | S05, G07 |
| Concrete `compiler`, computable `need` | The public theorem instantiated with the actual pipeline; no choice in `need` | G49.03, G54 |
| Import whitelist and the `EvmSpec` gate | The gate described in "Non-circularity as a checkable gate" | G07 |

Not done here: no instance of any contract is constructed, and no existing
theorem is restated against them.

## Handoff

- **Base revision:** `127c2ee59de16971e45b08a2def54f4e5fae8e2a`.
- **Deliverables:**
  - this document;
  - `Solidity/Roadmap/Contracts.lean`, registered in `Solidity.lean`;
  - one status line in [coverage-plan.md](../coverage-plan.md) under G01;
  - one link line in [docs/README.md](../README.md).
- **Checked, and how:**
  - `lean_diagnostic_messages` on `Contracts.lean`: no errors, warnings or
    infos besides the pinned axiom guards.
  - `#print axioms` (run once in the editor): `Cert.comp` and
    `Refines.trans` use `propext`; `PublicCorrectness.transfer` and
    `Refines.diverges` use none. The results for `Cert.comp` and
    `PublicCorrectness.transfer` are pinned in the file with `#guard_msgs`.
  - `node scripts/check-layers.mjs`: 155 core modules, 0 reach the
    elaborator.
  - `node scripts/check-orphans.mjs`: 0 orphaned.
  - `bash scripts/check-trust.sh`: 0 findings.
  - The full `./run-lean.sh` result is recorded in the CLOUD-RESULT of this
    batch.
  - Every cited declaration and line was checked with `git grep` at the head.
- **Ledger:** the [child obligations](#child-obligations) table.
- **Remaining:** every contract instance (all groups above) and the eight open
  scope questions.
- **Not edited** (forbidden by the batch rules):
  - `docs/module-map.md` has no row for `Solidity/Roadmap/` yet; it is a
    follow-up for the integrator.
  - `scripts/check-layers.mjs` does not list `Solidity.Roadmap.*` as core.
    The module imports `Solidity.Evm.Machine`, which is outside `CORE`, so it
    sits above the core without reaching the elaborator.

## Review

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
   decided silently. They are now open scope question Q7.
6. **Observation gaps.**
   - There was no deployment observation: added `Event.deploy`.
   - Created code was named by a compiler-chosen number: now a source
     identity, read off `Artifact.contracts`.
   - Linked libraries were environment events: the compiled system now
     includes them, and `Artifact` carries link sites. The boundary is open
     scope question Q8.
7. **An arbitrary `compiler` parameter** does not make output executable.
   The final statement uses the concrete, computable pipeline run on G07's
   controls. The unused `Prefixes.Emits` was removed.

Not changed: the skeptic's "already acknowledged" items (Q1–Q5, G51's meta
half, `Prog.runF` monotonicity, now covered by the `Lang.consistent` row).
