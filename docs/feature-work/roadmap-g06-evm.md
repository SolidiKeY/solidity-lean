# Roadmap G06: pinned EVM semantics, observations and the certificate boundary

G06 ([coverage-plan.md](../coverage-plan.md), wave 0): "Establish reproducible
pinned EVM semantics/observation interfaces and a dependency-free core
certificate boundary, with external adapters in Bridge. Inventory every
existing machine disagreement and required bridge lemma."

This document is the G06 deliverable. `Solidity/Roadmap/Evm.lean` states its
interfaces as Lean definitions (statements only). G06 closes no
source-to-bytecode obligation. It fixes what G45–G47 prove against and lists
what they owe.

Base revision `caf52ecd4dde5d37cbc0098d47de1a01aa218285`. Branch
`cloud/roadmap-w1-20261029/g06-evm-interface`. Binding decisions:
[solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29). This
document follows them. Three places where a decision cannot be met as stated
are [questions](#open-scope-questions), not reopened decisions.

## Contents

1. [Machine inventory](#1-machine-inventory)
2. [Disagreements with pinned Osaka](#2-disagreements-with-pinned-osaka)
3. [The pinned semantics interface](#3-the-pinned-semantics-interface)
4. [The observation interface](#4-the-observation-interface)
5. [Mapping to G01's `EvmSpec`, and findings for G01](#5-mapping-to-g01s-evmspec-and-findings-for-g01)
6. [The core/Bridge certificate boundary](#6-the-corebridge-certificate-boundary)
7. [Required bridge lemmas and owners](#7-required-bridge-lemmas-and-owners)
8. [Reference tooling pins](#8-reference-tooling-pins)
9. [Open scope questions](#open-scope-questions)
10. [Checks](#checks), [Handoff](#handoff), [Review](#review)

## 1. Machine inventory

Every EVM-like machine or EVM reference in the repository at the base revision:

| # | Machine | Location | What it is | Fork |
|---|---|---|---|---|
| M1 | `Evm.Machine`, `Instr`, `Out`, `exec`/`run`, `loopRun` | `Solidity/Evm/Machine.lean:323`, `:185`, `:359`, `:603`/`:611`, `:435` | The compiler's target. It is a word-addressed stack machine with symbolic `Slot` terms (`:99`), `Word = val ∣ slot` (`:165`) and a structured `LOOP`. `CALL` is payment-only. No gas. | none recorded |
| M1′ | Memory-compiler relations over M1 | `Solidity/Evm/Memory.lean`, `MemoryHeap.lean`, `MemorySource.lean` and the rest of `Solidity/Evm/Memory*` | The same machine, with heap/frame relations (`HeapRepr`, `StateRepr`). It defines no new machine. | none |
| M2 | `Evm.lts` (CSLib LTS of M1) | `Bridge/SolidityBridge/Evm.lean:39` | M1's `exec` as a deterministic labelled transition system. `compile_trace_complete` (`:153`) needs payment freedom. | none |
| M3 | The successful-boundary compiler LTS | `Bridge/SolidityBridge/CompilerSimulation.lean:24` | Source/target configurations at successful program boundaries only. Halting and divergence are not transitions. | none |
| M4 | The projected arithmetic reference LTS `RefCfg`/`refLts` | `Bridge/SolidityBridge/ExternalEvm.lean:165`, `:174` | An adapter-side stack of `EvmYul.UInt256` over eight binary operators, simulated by M2 (`simulation`). | none |
| M5 | EVMYulLean `EvmYul.EVM` (`step`, `X`, `Ξ`, `Θ`, `Lambda`, `Υ`) | `Bridge/vendor/EvmYul/EVM/Semantics.lean` (`step` :221, `X` :429, `Ξ` :525, `Lambda` :562, `Θ` :717, `Υ` :823), pin `047f630` in `Bridge/vendor/EvmYul/VENDOR.md` | The full upstream EVM: byte memory, gas, frames, accounts, precompiles 1–10, transient storage. It is fuelled (`OutOfFuel` is separate from gas). Keccak, SHA-256 and BLAKE2 are `@[extern]` opaques (`Bridge/vendor/EvmYul/FFI/ffi.lean`, lines 3–27). | **Cancun** (`TargetSchedule := "Cancun"`, `Bridge/vendor/EvmYul/Wheels.lean:148`) |
| M6 | Projected opcode agreements M1 ↔ M5 | `Bridge/SolidityBridge/ExternalEvm/Dispatch.lean`, `StackOps.lean`, `SignedOps.lean`, `WordOps.lean`, `Power.lean`, `Environment.lean` | Not a machine but the only existing M1/M5 bridge: 18 binary and 2 unary operators, PUSH/POP, DUP/SWAP 1–16 and five environment reads (`EnvironmentAgrees`). They are proved at zero charged gas with positive fuel. | Cancun (via M5) |
| M7 | Checked obstructions M1 ↮ M5 | `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean` | `no_injective_slot_encoding`, `call_arity_mismatch`, `revert_arity_mismatch`, `jump_arity_mismatch`, `jumpi_arity_mismatch`, `mload_arity_mismatch`, `mstore_arity_mismatch`, `slot_add_wrap_mismatch`. | Cancun |
| M8 | `@ethereumjs/evm` 10.1.3 reference replay | `scripts/evm-reference/replay.mjs:51` (and `generated.mjs`, `slice-reference-copies.mjs`) | Message-level `runCall` at 100,000,000 gas (`INITIAL_GAS`, `:18`). It uses a 5,000,000-step host budget, `allowUnlimitedContractSize`/`allowUnlimitedInitCodeSize` (`:54`) and a 1,024 stack. | **Osaka** |
| M9 | Hand-written vector runners | the 12 `scripts/check-*.mjs` EVM runners (list in [§8](#8-reference-tooling-pins)) | `@ethereumjs/vm` `createVM` and `evm.runCall`, from a supplied `node_modules` with no lockfile. Code-size caps are on. | **Cancun** (re-pin owned by the sibling g06-osaka-repin) |

Not machines, but EVM-adjacent and in scope of the inventory:

- **Word-level evaluators** in `Bridge/SolidityBridge/Arith/` (for example
  `Bridge/SolidityBridge/Arith/Widths.lean` and
  `Bridge/SolidityBridge/Arith/Basic.lean`). They are readings of the core's
  *primitive evaluator* as `BitVec`/`ZMod` arithmetic and have no machine
  state. They feed G46.01 only through the typed values. Their recorded
  discrepancies (checked power overflow, negative signed shift counts;
  [bridge.md](../bridge.md#discrepancies)) are source/evaluator findings,
  not EVM disagreements.
- **Source-level world models**, which the pinned EVM's environment must
  abstract to: the contract world (creator-chosen fresh addresses, prefunding
  and collision checks, ledger settlement;
  [contract-world.md](contract-world.md)), the logical transient store
  ([transient-storage.md](transient-storage.md)) and the lifetime transition
  system ([lifetime.md](../lifetime.md), which has no forced ether receipts).

## 2. Disagreements with pinned Osaka

"Pinned Osaka" is Osaka with EIP-170 and EIP-3860 idealized (G01 Q2), so any
code size deploys. Each row lists the machines that disagree, the evidence, and the
resolution the interface ([§3](#3-the-pinned-semantics-interface)) adopts or the
group that discharges it. "Bridge lemma B*n*" refers to [§7](#7-required-bridge-lemmas-and-owners).

| # | Topic | Disagreeing machines | Disagreement (evidence) | Resolution / owner |
|---|---|---|---|---|
| D1 | Symbolic slots | M1–M4, M6 | Slots are terms `root ∣ hash k s off ∣ data s off`, so two slots are equal only as terms (`Solidity/Evm/Machine.lean:99`). No injective `Slot → Fin W` exists (`no_injective_slot_encoding`). Offsets do not wrap (`slot_add_wrap_mismatch`). | A numeric storage relation under the per-run hash premise (`Fixed.NoCollision`), B10. The premise as decided does not cover overlapping slot ranges: [Q3](#q3-storage-slot-ranges-under-the-per-run-hash-premise). G46.03, G46.05. |
| D2 | Word memory | M1, M1′ | `mem : Nat → Word` holds one *word or symbolic slot* per cell, at a cell index. Fixed-cell `mload l`/`mstore l` are macros (`mload_arity_mismatch`, `mstore_arity_mismatch`). The EVM has byte memory with 32-byte big-endian words, quadratic expansion gas and a stack-supplied address. | Byte-memory relation (×32 scaling, numeric slot words, expansion bounded only by gas), B07. G46.02, G45.01. |
| D3 | Jumps | M1, M2 | `JUMP n`/`JUMPI n` skip forward (relative) and `LOOP` is structured (`jump_arity_mismatch`, `jumpi_arity_mismatch`). The EVM takes absolute stack destinations that must be `JUMPDEST` outside PUSH data. | Label layout and jump-destination analysis against the pinned decoder, B03 and B04. G45.03–G45.05. |
| D4 | Call frames | M1–M3, M6 | `CALL` pops 2 words, runs no callee and uses a static `accepts` predicate (`call_arity_mismatch`). It has no calldata, success data or reentrancy. The EVM's `CALL` takes 7 operands and runs callee code in a new frame with rollback. | Frames are observed through `Halt.observe` ([§4](#4-the-observation-interface)). Environment frames are abstracted to strategies (B13), our frames execute. G42, G47. |
| D5 | Depth | M1–M4 | No call depth. M5 fails a call or creation at depth 1024 (`Bridge/vendor/EvmYul/EVM/Semantics.lean:165`, `:201`). | Decided: such a frame fails and the caller continues. The source semantics *forces* that failure (`Pin.callFails`), and an entered frame has a depth (`Schedule.entryDepth`), B12. Internal calls use memory frames (G01 Q2), so they consume no depth. G37, G42.03. |
| D6 | Gas | M1–M4, M6 (zero gas) | The EVM charges gas per opcode, memory expansion, EIP-2929 warm/cold access, the 63/64 rule (`allButOne64`), the 2300 stipend, refunds and the EIP-7623 calldata floor. Osaka adds the EIP-7825 per-transaction cap of 2²⁴. M8 runs 10⁸ message gas, above that cap. | Gas is a resource (`Schedule`, `Res`), not an observation. Frames and transactions may fail from it and the caller continues (decided). Realizability is B11. The cap breaks forward adequacy: [Q2](#q2-the-osaka-per-transaction-gas-cap). G47. |
| D7 | Returndata and revert bytes | M1–M4 | `REVERT` takes no operands and carries no data (`revert_arity_mismatch`). M1 has no `RETURN`, `RETURNDATASIZE` or `RETURNDATACOPY`. M5's `Υ` returns `(σ', A, z, gasUsed)` and drops the output bytes that `Θ`/`Lambda` compute (`Bridge/vendor/EvmYul/EVM/Semantics.lean:823`–`:946`). | The observation is the halt's bytes (G01 Q5: exact ABI and revert bytes, `Panic` included). The adapter reads `Θ`/`Lambda`'s output, not `Υ`'s result, B14. G38, G47. |
| D8 | Transient storage | M1–M4 | Absent from the machine. The source has a logical store ([transient-storage.md](transient-storage.md)). M5 keeps a `tstorage` field per account (`Bridge/vendor/EvmYul/State/Account.lean:47`), clears it at transaction end (`Semantics.lean:944`) and rolls it back with the frame's account map. | `TLOAD`/`TSTORE` relation to the logical store, with reset at transaction end and frame rollback (EIP-1153), B09. G46.03. |
| D9 | Precompiles | M1 (none); M5 (Cancun set 1–10 only, `Semantics.lean:787`–`:796`; SHA-256 and BLAKE2 via FFI) | Osaka has 18: 0x01–0x0a, Prague's BLS12-381 0x0b–0x11 (EIP-2537) and P256VERIFY at 0x100 (EIP-7951). MODEXP has Osaka's bounds and gas (EIP-7823, EIP-7883). Under M5, a call to 0x0b–0x11 or 0x100 reaches an empty account. | Decided: precompiles are fixed functions, never environment code. The table is `Precompile` and `Fixed.precompile`/`precompileGas`, and calls to them are not `Event.call`s. Instances are B15 and B16; the repin is B01. G46.05, G47. |
| D10 | CREATE addresses | M1 (no creation); source world (the creator picks a fresh address; [contract-world.md](contract-world.md)) | The EVM address is `keccak(rlp [sender, nonce])[12:]`. A creation fails at an address with code or a nonzero nonce (EIP-684, EIP-7610) and when the nonce is at 2⁶⁴−1 (EIP-2681). | `Fixed.createAddress` is a fixed function of `Fixed.keccak` (checked against known addresses). The source tracks nonces of the system's accounts, and a creation at an occupied address fails. No address-injectivity premise (G46.05). B17. G44.03. |
| D11 | Fork pin | M5, M9 (Cancun); M1 (none) | G00 disagreement 2. Osaka adds `CLZ` (EIP-7939), the precompiles of D9, the gas cap of D6 and Prague's EIP-7702 delegated code and EIP-7623 floor. | M9 is re-pinned by the sibling g06-osaka-repin. M5 needs an Osaka repin or extension, B01. M1 is an inner language and needs no fork. |
| D12 | Code-size limits | M5 (`i.size ≤ 49152`, `Semantics.lean:254`, `:321`, `:480`; `MAX_CODE_SIZE := 24576`, `:670`); M9 (caps on) | The decision idealizes both. M8 already disables them (`replay.mjs:54`). | `pinned.runtimeCodeLimit = none`, `initcodeLimit = none`. M5 needs a recorded vendor patch or parameter, B02. |
| D13 | Keccak in M5 | M5 | `ffi.KEC` is an `@[extern]` opaque (`Bridge/vendor/EvmYul/FFI/ffi.lean`, lines 20–27), so no Lean proof relates it to `Solidity/Keccak.lean`. | `Fixed` is a parameter. The adapter instantiates it either with `ffi.KEC` (the public theorem then holds for it, but the random-oracle lemma says nothing about a C function) or, better, by a vendor patch defining `KEC` by the core Keccak, B15. G46.05. |
| D14 | Transaction validity and fees | M5 (`Υ` does not validate; balance subtraction is `UInt256` and wraps, `Semantics.lean:823`) | Osaka rejects a request whose sender cannot cover `value + gasLimit·price` (plus blob fee). `Υ` would run it with a wrapped balance. | Decided: an unaffordable request never executes. The adapter must apply validity before `Υ`, B18. Senders' balances are environment inputs net of fees ([§3.5](#35-sender-funds)). |
| D15 | Forced ether | source world, lifetime model ([lifetime.md](../lifetime.md)) | The own balance can rise with no frame of ours running. The coinbase fee credit is `Semantics.lean:939`. The other sources are another contract's `SELFDESTRUCT` beneficiary (EIP-6780 keeps the transfer) and EIP-4895 withdrawals. | Conflicts with "the own balance follows the ledger": [Q1](#q1-forced-ether-and-the-own-balance). |
| D16 | Environment code vs strategies | source (strategies: arbitrary history-dependent functions, G01 Q4) vs M5 (environment accounts run code) | Code realizes only computable strategies, but every finite prefix of a strategy is realizable by code. | `envOnto` must be read on finite prefixes ([§5](#5-mapping-to-g01s-evmspec-and-findings-for-g01), F3), B13. G42.02. |
| D17 | Stack limit | M1 (unbounded stack, `pushes` bound only on array length) | 1024 operand words per frame. | The compiler bounds each frame's stack. Recursion uses memory frames, so this is a compiler obligation, not a resource failure. G45.02. |
| D18 | Evaluator fuel vs divergence | M1 (`loopRun` classical, a fault on divergence), M5 (`OutOfFuel`) | M1's divergence is a fault, not an unfinished prefix. M5's fuel is the right shape. | The fuel of `Res` indexes prefixes, and `OutOfFuel` gives `final = none`. M1 needs a step-indexed run (G01 reuse map). G36, G47. |

## 3. The pinned semantics interface

All names are in `Solidity/Roadmap/Evm.lean`. The module imports only
`Solidity.Keccak`, which has no imports. So whatever instantiates `Pinned`
reaches no compiler module through it (G01's import gate, item 3).

### 3.1 The pin

`Pin` (fork, three optional limits, depth, stack and stipend), `osaka` (the chain's
values) and `pinned` (the decisions' pin, `pinned_eq`: Osaka with
`runtimeCodeLimit = initcodeLimit = none`). `txGasCap` stays `some (2 ^ 24)`
until [Q2](#q2-the-osaka-per-transaction-gas-cap). The answer changes one field.

### 3.2 Fixed functions

`Fixed` holds `keccak` (below 2²⁵⁶, `keccak_lt`), `precompile` (`none` for an
exceptional halt) and `precompileGas`. The source semantics and the pinned EVM
take the **same** `Fixed`. The public theorem quantifies over every `Fixed`, so
it holds for the real functions without trusting them. Their identification is
a bridge lemma (B15, B16). This reads the decisions literally: "opaque hashes
are a fixed parameter instantiated by keccak", and precompiles behave "as
their EVM definitions (the crypto ones through the approved fixed functions)".
A universally quantified parameter needs no approval, because it is stronger
than any instance. The source's current concrete `sha256`/`ripemd160`/`ecrecover`
(`Solidity/Hashes.lean`, `Solidity/Secp256k1.lean`) become the instances of
`Fixed.precompile` at 0x01–0x03, through a correspondence theorem (S05).

- `keccakWord` is the instance by `Solidity/Keccak.lean`, and `withKeccak` is a
  `Fixed` with it.
- `Fixed.NoCollision F hashed` is **the per-run hash premise** (G01 Q3): the
  preimages a prefix hashes do not collide. `NoCollision.mono` shows it is
  downward closed, so it reads on a prefix's own hashed list. The probability
  bound is the sibling hash-collision-bound task's lemma.
- `Fixed.createAddress F sender nonce` is the low 160 bits of
  `keccak(rlp [sender, nonce])` (`rlpBytes`, `rlpList`, `beBytes`, `beFixed`),
  with `createAddress_lt`. The `#guard`s check it at `withKeccak` against the
  published first two creation addresses of `0x6ac7…dbf0`, and check two RLP
  boundary cases.
- `precompileGas` is needed where the *source* fixes the forwarded gas. With a
  2300 stipend, `transfer` to 0x01 (3000 gas) always fails on Osaka, while
  `transfer` to 0x04 (identity, 15 gas on empty input) succeeds. The source
  semantics must compute these from the table, because no resource choice can
  change them.

### 3.3 Precompiles

`Precompile` has the 18 Osaka precompiles. `Precompile.address` maps them to
their addresses and `Precompile.all` lists them in address order. Lemmas:

- `mem_all`;
- `ofAddress?_address`, so `ofAddress?` is a partial inverse;
- `address_injective`;
- `address_pos_lt`: none is at address 0, which stays an account without code
  (approved assumption), and each is below 2¹⁶⁰.

A call or payment to a precompile address runs `Fixed.precompile` with the
value moved to its account. It is internal to the semantics, not an
`Event.call`. Its out-of-gas is a frame failure like any other.

### 3.4 Resources and the decided failure semantics

- `Schedule` holds every gas number chosen outside the compiled system:
  `txGas i` (the `i`-th request's limit), `entryGas k` (the gas the
  environment forwards to the `k`-th frame of ours it enters) and
  `entryDepth k` (that frame's depth). The gas our own calls forward is the
  compiler's choice. Callee answers range over all outcomes regardless of it
  (G01 Q7).
- `Res = schedule × fuel`. Its order (`instance : LE Res`) compares fuel at an
  **equal** schedule, with `Res.le_refl` and `Res.le_trans`. A different schedule
  is a different execution, so gas exhaustion is a completed observation
  (failure, then the caller continues), never the end of a prefix. Only fuel
  ends a prefix. This implements the follow-up "`Lang.Res` must stop ending a
  session at gas exhaustion".
- `Res.Admissible p r` requires every `txGas` within `p.txGasCap` when it is
  `some`, and every `entryDepth ≤ p.callDepth`. `Admissible.of_le` shows that
  fuel does not affect it.
- `FailurePoints` is the source's side of a schedule. For each transaction and
  each entered frame it records whether the item fails from resources, and
  after how many of its events. All of them are admissible, so the source stays
  `Idealized` (G01 Q1).
- The source semantics *forces* the failures no schedule can avoid: a call or
  creation from depth ≥ 1024 (`Pin.callFails`), and a stipend-bounded payment
  whose recipient needs more (precompiles by `precompileGas`; an untyped
  recipient may refuse anyway, G04 Q3).
- **Nested-frame failures** (decided): any external frame of ours may fail with
  a revert its caller sees, and the caller continues. On the EVM this is
  `entryGas`/`entryDepth`. In the source it is `FailurePoints.entry`. The effects
  of the failed frame roll back, but its events stay observed.
- **Transactions** (decided): any transaction may fail from gas and the session
  continues (`txGas`, `FailurePoints.tx`).
- **Internal recursion** uses memory frames (G01 Q2) and is bounded only by gas.
  It is not a separate resource.

### 3.5 Sender funds

Decided: `msg.value` is bounded by the sender's ledger balance, and an
unaffordable request never executes. Interface reading:

- **EVM side.** Validity is Osaka's: `value + gasLimit·price (+ blob fee) ≤
  balance`. An invalid request produces no `Event.tx` and changes nothing.
- **Source side.** An environment account's balance is an environment input
  (G00 Q2). At each request the sender's balance is the EVM balance less the
  upfront fees, and the source admits the request iff `value ≤` that.
- **Consequence for G01.** Fees and refunds depend on gas used, so this
  correspondence is per execution (finding F1).

### 3.6 `Pinned`

`Pinned Art P` holds `pin`, `fixed`, `Env`, `Allowed`, `sem : Art → Env → Res
→ P` and `consistent`. `P` is the prefix type with its order. `Env` is the
whole world: environment accounts with their code, the request and block
sequence, and the block contexts. `Pinned.Admissible` is the pin's. The core's
future pinned semantics and every Bridge adapter are instances.

## 4. The observation interface

`Halt` has three cases: `success` (STOP/RETURN with its data), `revert` (with
its data) and `exceptional` (out of gas, an invalid or unassigned opcode, a bad
jump, a stack limit, a static-mode write). `Halt.observe` gives what the caller
sees: the success flag and the return data buffer.

- `observe_exceptional`: an exceptional halt is the same observation as
  `REVERT(0, 0)`.
- `observe_success`: no failure is observed as success.

Mapped to G01's shared types (`Solidity/Roadmap/Contracts.lean`, `Outcome`
and `Event`):

| EVM fact | G01 observation |
|---|---|
| A transaction's top frame halts with `h` | `Event.tx sender value timestamp input (o h)` with `o (.success d) = .success d`, otherwise `.revert` of the observed bytes (`[]` for an exceptional halt). A gas-exhausted transaction is `revert []`. |
| Deployment of the selected contract | `Event.deploy`, with the address `createAddress` gives on success. |
| A `CALL` from our code to an account outside the system that is not a precompile | `Event.call callee value input static`, then `Event.answer (o h) none` for the callee's halt `h`. |
| A `CREATE` of a contract of the input | `Event.create value contract args`, then `Event.answer … (some address)`, or `none` when it fails. |
| A call to a precompile, or between instances of the system | No event (internal semantics). |
| Gas, logs, raw storage layout, `PUSH0` vs `PUSH1 0`, code bytes | Not observed (G00 exclusions). Log arguments still execute. |

Transient storage is not observed directly. Its effects are observed through
later behaviour within the transaction. The functional `decode : EvmWorld →
Option IntrinsicWorld` (G01 Q6) reads account storage by the same numeric slot
relation as B10 and ignores `tstorage`, which is empty between transactions.

## 5. Mapping to G01's `EvmSpec`, and findings for G01

`EvmSpec` keeps its name (the sibling g01-contracts-rev is revising
`Solidity/Roadmap/Contracts.lean`; this document does not edit it). An instance
is made from any `V : Pinned Artifact (Prefix Event Outcome)` with
`instance : LE (Prefix Event Outcome) := ⟨Prefix.Le⟩`:

```lean
def ofPinned (V : Pinned Artifact (Prefix Event Outcome)) : EvmSpec where
  lang := { Prog := Artifact, Env := V.Env, Res := Res, resLE := inferInstance,
            Allowed := V.Allowed, Admissible := V.Admissible,
            sem := V.sem, consistent := fun a e => V.consistent a e }
  load := id
```

This is a sketch for G01, not checked here, because the module may not import
`Contracts`. It fits the G01 types: `Prefixes.Consistent` is `∀ r r', r ≤ r' →
…` over the given `LE`. The G01 `EvmSpec` docstring lists code size among the
resources. That element is gone (EIP-170/3860 idealized), as the G01
follow-up says.

Findings that the revised G01 statements must absorb. None reopens a
decision. They concern how the contracts express decisions already taken.

- **F1 — the environment abstraction must be per execution.**
  `PublicCorrectness` takes one program-independent `envAbs : V.lang.Env →
  S.lang.Env`. Three of the decided behaviours depend on the code, not only on
  the environment: which transactions and entered frames fail from gas, which
  requests are affordable after fees and refunds, and the gas-dependent part of
  sender balances. No program-independent `envAbs` can produce them. The
  interface puts the gas schedule in `Res` (so the per-program `∃` of
  `Refines` and `Cert.need`/`back` absorbs it). The remaining per-execution
  parts (validity after fees) need either the same treatment or a ∀∃
  environment correspondence per artifact, which is the shape of
  `Certificate.back`/`forth`.
- **F2 — `Diverges` and `NonVacuous` with schedules.** With schedules in `Res`,
  a low-gas schedule always completes with a revert. So `Prefixes.Diverges A`
  (every admissible bound unfinished) is false on both sides for a diverging
  loop. Divergence must be read per schedule: for some admissible schedule,
  every fuel is unfinished. The source analogue is `FailurePoints` with no
  failure. `SourceSpec.NonVacuous`'s divergence witness needs the same change.
- **F3 — `envOnto` on finite prefixes.** EVM environments are code, so they
  realize only computable strategies, while the source quantifies over all
  history-dependent strategies (G01 Q4). Every finite prefix of a strategy is
  realized by code. `envOnto` (and `Certificate.forth`) must ask for every
  finite part of an allowed source environment, or the source's `Allowed` must
  be restricted to code-realizable strategies.
- **F4 — forced depth failures are source semantics.** The decision makes
  depth-1024 failures part of the source, so `SourceSpec.Idealized` survives
  only because the failure is forced by the semantics (`Pin.callFails` on the
  depth the environment reports with each entry), not chosen by a resource.

## 6. The core/Bridge certificate boundary

**What the dependency-free core states.**

1. The interface `Solidity/Roadmap/Evm.lean` (this group).
2. A **core pinned semantics** `core : Fixed → Pinned Artifact …` (owner G46.06
   and G47, future modules outside the Codex-owned `Solidity/Evm/**`). It
   - decodes bytes by its own Osaka opcode table, never by an inverse of
     `assemble` (G01 gate);
   - executes the compiled system's frames exactly for the opcodes it
     specifies;
   - makes every opcode it does not specify **stuck** (`final = none`), so a
     compiler that emits one fails forward adequacy instead of gaining an
     unverified meaning;
   - runs environment frames as their observation only: a strategy answers
     each `Event.call` and may enter the system again at a reported depth with
     forwarded gas;
   - runs precompiles by `Fixed`, and gas by an Osaka gas function over the
     specified opcodes.
3. The compiler proofs (G45–G47) target `core`. Contract 5 is proved for
   `ofPinned (core F)` for every `F`, under `F.NoCollision` of the prefix's
   preimages.

**What an external adapter proves** (in `Bridge/`, never imported by the core):
`Certificate (core F) ext` for its machine `ext` (for EVMYulLean, M5 after
B01/B02). The certificate's fields are:

- `pin`, `fixed`: same pin and same fixed functions;
- `back`: every admissible execution of the external machine, with arbitrary
  environment code, is observed exactly as some admissible core execution;
- `forth`: every admissible core execution is realized by some external
  environment, by code for the strategies and by gas for the failure points
  (with F3's finite reading).

`Certificate.symm` and `Certificate.refl` check its shape. The public theorem
transfers to the external machine by composing `Certificate.back` with
contract 5. That composition lives in Bridge. The core theorem needs no
dependency.

**Why this boundary.** The core cannot import EVMYulLean (Mathlib), and the
public theorem must not rest on an EVM written by the compiler's authors alone.
The certificate makes the external, independently written EVM the reference.
The core semantics is the shared statement, so it is checked against upstream
rather than trusted. Its only executed part is our own code. Environment code
is quantified by strategies (D16), which keeps the core semantics small.

## 7. Required bridge lemmas and owners

Statements are informal where the types are future work. "Core" means the
core pinned semantics of §6.

| Id | Lemma | From → to | Owner | Seed at base |
|---|---|---|---|---|
| B01 | Osaka repin of the external EVM: `CLZ`, the BLS12-381 and P256VERIFY precompiles, Osaka MODEXP, the EIP-7825 cap as a pin field, EIP-7702 delegation and EIP-7623 floor gas | M5 → Osaka | G46.06 (vendor), with G06's pin | `VENDOR.md` refresh procedure |
| B02 | Code-size limits as pin parameters (`none` = no check) in the adapter, as a recorded vendor patch | M5 | G46.06 | `lean-4.24.patch` precedent |
| B03 | Byte decoder agreement: core decoding = `EvmYul.EVM.decode` (PUSH immediates, `JUMPDEST` validity, `D_J`) | core ↔ M5 | G45.05 | — |
| B04 | Label/jump realization: relative and structured control (M1 `jump`, `jumpi`, `loop`) realized by absolute `JUMP`/`JUMPI` to valid destinations | M1 → core | G45.03 | `jump_arity_mismatch`, `jumpi_arity_mismatch` |
| B05 | Opcode step agreement for every opcode the core specifies, with gas charged, as an extension of the projected agreements | core ↔ M5 | G46.01 | `BinaryOpcode.agrees`, `UnaryOpcode.agrees`, `dup_agrees`, `swap_agrees`, `push_agrees`, `pop_agrees` |
| B06 | Instruction expansion: each M1 macro (`mload l`, `mstore l`, `call`, `revert`, `keccakMap`, `keccakArr`) is a verified opcode sequence | M1 → core | G45.01, G45.02 | `Obstructions.lean` |
| B07 | Byte memory: M1 word cells ↔ 32-byte big-endian memory with numeric slot words and expansion gas | M1 → core | G46.02 | — |
| B08 | Calldata and returndata: `CALLDATALOAD`/`COPY` and `RETURNDATA*` against the ABI views | core | G46.02, G40, G47 | — |
| B09 | Transient storage: `TLOAD`/`TSTORE` ↔ the logical transient store, reset at transaction end, rolled back with the frame | source/M1 → core ↔ M5 (`tstorage`) | G46.03 | `resetTransient_*` (source) |
| B10 | Storage: symbolic `Slot` ↔ numeric keccak slots under `Fixed.NoCollision` (and [Q3](#q3-storage-slot-ranges-under-the-per-run-hash-premise)) | M1 → core | G46.03, G46.05 | `no_injective_slot_encoding`, `slot_add_wrap_mismatch` |
| B11 | Gas realizability: every `FailurePoints` is realized by some admissible `Schedule` (monotonicity of gas use in the schedule, the 63/64 rule, entry gas) and every schedule yields some `FailurePoints` | source ↔ core | G47 | — |
| B12 | Depth: core frame depth = M5 `executionEnv.depth`, and `Pin.callFails` matches M5's depth check | core ↔ M5 | G47 | — |
| B13 | Environment realization: every finite strategy prefix is realized by environment code (forth), and every environment code run is observed as a strategy (back), across reentrancy | core ↔ M5 | G42.02, G42.03, G47 | `CallbackTrace.lean` (source traces) |
| B14 | Transaction observation: the adapter's outcome reads `Θ`/`Lambda`'s output bytes and halting flag, and `Halt.observe` matches M5's exceptional halts (consumed gas, empty output) | M5 → core | G47 | `revert_arity_mismatch` |
| B15 | Keccak instance: M5's `KEC` = `keccakWord` (requires replacing `ffi.KEC` by the core Keccak in a recorded vendor patch; impossible against the opaque) | M5 ↔ `Fixed` | G46.05 | `Solidity/Keccak.lean` `#guard`s |
| B16 | Precompile instances: M5's `Ξ_*` (after B01) = `Fixed.precompile`/`precompileGas` at each `Precompile`, and the source's `Hashes`/`Secp256k1` = the same table at 0x01–0x03 | M5 ↔ `Fixed` ↔ source | G46.05 (S05 for the source side) | `Hashes.lean` vectors |
| B17 | CREATE: M5's address computation = `Fixed.createAddress` and the nonce/collision failure rules (EIP-684/7610/2681), with fresh typed storage | M5 ↔ core ↔ source world | G44.03, G46.05 | `createAddress` `#guard`s |
| B18 | Transaction validity and fees: the adapter skips invalid requests before `Υ`, and sender balances net of fees match [§3.5](#35-sender-funds) | M5 → core | G47, G43 | `EnvironmentAgrees` (balances) |
| B19 | Payments: value transfer, stipend, recipient acceptance (untyped: any outcome; typed: their code) and the own balance (pending [Q1](#q1-forced-ether-and-the-own-balance)) | source → core | G43, G47 | `Solidity/Evm/Machine.lean` `pay`, `accepts` |
| B20 | Linked libraries: `DELEGATECALL`-free linking as compiled (library code runs on the caller's storage) | core | G42.04, G44.02 | — |
| B21 | Composition: `Certificate (core F) ext` from B03–B18, and the transfer of contract 5 to `ext` | core ↔ M5 | G46.06, G47, G49.02 | — |
| B22 | Differential cross-check (evidence, not proof): core semantics vs M8 on the generated cases | core vs M8 | G52 | `scripts/evm-reference/generated.mjs` |

## 8. Reference tooling pins

The reference tooling is evidence, never proof. G06 records its pins and edits
no script; the fork of the vector scripts belongs to the sibling g06-osaka-repin.

- **M8** (`scripts/evm-reference`): already Osaka, with code-size caps
  disabled, which matches the idealization. Its lock
  (`scripts/evm-reference/package-lock.json`) pins `@ethereumjs/evm` 10.1.3 and
  `common`/`util` 10.1.2. That is G00 disagreement 5 as observed: the lockfile is
  the pin, and a document saying 10.1.3 for all three is wrong. M8 runs
  `runCall` at 10⁸ gas, above Osaka's 2²⁴ transaction cap. Message-level
  execution with a larger budget is the reading of [Q2](#q2-the-osaka-per-transaction-gas-cap)'s
  first option, not of the chain.
- **M9**, at the base: `check-abi-hex-call.mjs`, `check-abi-vectors.mjs`,
  `check-call-exception-vectors.mjs`, `check-modifier-frames.mjs`,
  `check-operator-aliases.mjs`, `check-public-getters.mjs`,
  `check-recursive-types.mjs`, `check-self-power-data.mjs`,
  `check-slice-copies.mjs`, `check-source-admission.mjs`,
  `check-transient-vectors.mjs` and `check-transient-world-vectors.mjs`
  (all `Hardfork.Cancun`, `evmVersion: 'cancun'`, caps on, no lockfile).
  They differ from the pin in fork and in code-size caps. The repin must also
  disable the caps (or record why a vector needs them) and lock its
  dependencies.
- **M5**: Cancun at `047f630`, B01/B02.

## Open scope questions

Each is a place where a 2026-10-29 decision cannot be met as stated. The rest
of this document does not depend on the answers. Each answer changes one named
definition.

### Q1. Forced ether and the own balance

The decision "the own balance follows the ledger" cannot hold on Osaka if the
ledger records only the system's own payments. A contract's balance also rises
with no frame of ours running, in three ways:

- as the block beneficiary (`Bridge/vendor/EvmYul/EVM/Semantics.lean:939`);
- as another contract's `SELFDESTRUCT` beneficiary (EIP-6780 keeps the
  transfer; our `selfdestruct` is excluded, theirs is environment);
- through EIP-4895 withdrawals.

`address(this).balance` observes the difference.

Options:

- **Environment credits in the ledger (EVM-faithful).** Between transactions,
  and while an environment frame runs, the own balance may rise by an amount
  the environment chooses. The ledger records these credits next to the
  system's own payments, and the source must let `address(this).balance` grow
  with no payment of ours.
- **An approved premise of no forced credits.** The pinned EVM's `Allowed`
  excludes these credits. This is a new environment premise, not EVM behaviour.

### Q2. The Osaka per-transaction gas cap

The source is idealized (G01 Q1: unbounded fuel) and refinement is two-sided:
every admitted source execution needs an admissible EVM execution with the
same observations. A transaction whose compiled code needs more than 2²⁴ gas
(EIP-7825, Osaka) cannot complete on Osaka at any gas limit. "Any transaction
may revert from gas exhaustion" gives the EVM's revert a source counterpart,
but the source's successful completion then has no EVM counterpart, so
forward adequacy fails. The block gas limit raises the same problem with a
larger bound. M8 already runs 10⁸ gas per message.

Options:

- **Idealize the gas caps.** Record EIP-7825 and the block gas limit as an
  idealization, like EIP-170/3860 (`pinned.txGasCap := none`). Two-sided
  refinement is kept, and a too-low gas limit still makes a transaction
  revert.
- **Keep the cap and weaken forward adequacy.** Forward adequacy is required
  only of transactions the cap admits. This is a G01 contract change, and the
  public theorem is weaker for heavy transactions.
- **Keep the cap and the contract.** G47's forward direction stays unprovable
  for such programs and is recorded as unresolved. By the roadmap's rule this
  means the proof is incomplete.

### Q3. Storage slot ranges under the per-run hash premise

The decided premise is that the preimages a prefix hashes do not collide:
`keccak a = keccak b → a = b`. Solidity storage puts a dynamic array's
elements at `keccak(p) + i` and a mapping entry at `keccak(k ‖ q)`, so two
regions can overlap without any equal hash. The same holds for the root slots
`0 … n` when `keccak(p) + i` wraps. The compiled code then really aliases
storage, so B10 is false under the premise as stated. The probability is
small (about q²·L/2²⁵⁶ for spans of L slots) but is not the decided q²/2²⁵⁷
bound.

Options:

- **Extend the per-run premise.** Add that the storage regions a prefix
  accesses do not overlap (hashed bases with their accessed offsets, and the
  root region), with the random-oracle bound extended to spans.
- **Keep the premise as decided.** B10 cannot be proved for overlapping
  regions, and G46.03 records this as an unresolved approved-premise
  obligation, which means it is incomplete.

## Checks

At head (see [Handoff](#handoff) for the commands and results):

- `lean_diagnostic_messages` on `Solidity/Roadmap/Evm.lean`: no errors or
  warnings. Its `#guard`s (two `CREATE` addresses, two RLP cases) and
  `#guard_msgs` axiom pins (`Precompile.address_injective`, `Certificate.symm`:
  no axioms) pass.
- No `sorry`, axiom, `native_decide`, `implemented_by` or `maxHeartbeats` in
  the module.
- `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`,
  `bash scripts/check-trust.sh`, `bash scripts/check-doc-paths.sh` and the full
  `./run-lean.sh`: results in the handoff.

## Handoff

- **Base:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`. **Files:** this
  document, `Solidity/Roadmap/Evm.lean`, and one line each in
  `Solidity.lean`, `docs/module-map.md`, `docs/README.md` and
  `docs/coverage-plan.md`.
- **Definitions** (no premises unless stated): `Fork`, `Pin`, `osaka`,
  `pinned`, `allButOne64`, `Pin.callFails`, `Precompile`, `Precompile.address`,
  `Precompile.all`, `Precompile.ofAddress?`, `Fixed`, `keccakWord`,
  `Fixed.NoCollision`, `beBytes`, `beFixed`, `rlpHead`, `rlpBytes`, `rlpList`,
  `Fixed.createAddress`, `withKeccak`, `Schedule`, `Res`, `Res.Admissible`,
  `FailurePoints`, `Halt`, `Halt.observe`, `Pinned`, `Pinned.Admissible`,
  `SameObs`, `Certificate`.
- **Theorems:** `pinned_eq`, `Precompile.mem_all`,
  `Precompile.ofAddress?_address`, `Precompile.address_injective`,
  `Precompile.address_pos_lt`, `Fixed.NoCollision.mono` (premises:
  `F.NoCollision hs'`, `hs ⊆ hs'`), `Fixed.createAddress_lt`, `Res.le_refl`,
  `Res.le_trans`, `Res.Admissible.of_le` (premise `a ≤ b`),
  `Halt.observe_exceptional`, `Halt.observe_success`, `Certificate.symm`,
  `Certificate.refl` (premise: a reflexive prefix order).
- **Child obligations:** B01–B22 with owners (§7); findings F1–F4 for
  g01-contracts-rev (§5); the core pinned semantics of §6 (G46.06, G47);
  answers Q1–Q3.

## Review
