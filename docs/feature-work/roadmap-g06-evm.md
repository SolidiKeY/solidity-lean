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
document follows them. Three places where a decision could not be met as
stated were raised as [scope questions](#scope-questions-answered-2026-10-29).
The user answered them, together with a hash-region premise and two pin
questions, in a second round recorded in
[solidity-scope.md](../solidity-scope.md) ("Second round (2026-10-29)"). Both
the module and this document encode the answers.

## Contents

1. [Machine inventory](#1-machine-inventory)
2. [Disagreements with pinned Osaka](#2-disagreements-with-pinned-osaka)
3. [The pinned semantics interface](#3-the-pinned-semantics-interface)
4. [The observation interface](#4-the-observation-interface)
5. [Mapping to G01's `EvmSpec`, and findings for G01](#5-mapping-to-g01s-evmspec-and-findings-for-g01)
6. [The core/Bridge certificate boundary](#6-the-corebridge-certificate-boundary)
7. [Required bridge lemmas and owners](#7-required-bridge-lemmas-and-owners)
8. [Reference tooling pins](#8-reference-tooling-pins)
9. [Scope questions (answered 2026-10-29)](#scope-questions-answered-2026-10-29)
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
| M8 | `@ethereumjs/evm` 10.1.3 reference replay | `scripts/evm-reference/replay.mjs:51` (and `generated.mjs`, `slice-reference-copies.mjs`) | Message-level `runCall` at 100,000,000 gas (`INITIAL_GAS`, `:18`). It uses a 5,000,000-step host budget, `allowUnlimitedContractSize`/`allowUnlimitedInitCodeSize` (`:54`) and EthereumJS's built-in 1,024-word stack. | **Osaka** |
| M9 | Hand-written vector runners | the 12 `scripts/check-*.mjs` EVM runners (list in [§8](#8-reference-tooling-pins)) | `@ethereumjs/vm` `createVM`, then `evm.runCall` or `evm.runCode`, from a supplied `node_modules` with no lockfile. Code-size caps are on. | **Cancun** (re-pin owned by the sibling g06-osaka-repin) |

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
| D1 | Symbolic slots | M1–M4, M6 | Slots are terms `root ∣ hash k s off ∣ data s off`, so two slots are equal only as terms (`Solidity/Evm/Machine.lean:99`). No injective `Slot → Fin W` exists (`no_injective_slot_encoding`). Offsets do not wrap (`slot_add_wrap_mismatch`). | **Hashed layout.** The compiler places every storage word at the Keccak of a distinct preimage (roots at `keccak(tag ‖ i)`, array elements at `keccak(p ‖ i)`, mapping entries and struct fields likewise). Physical layout is an excluded observation (G00 Q1) and "solc's slot behaviour" fixes only the logical alias semantics, so this is allowed. Two words then share a slot only if two preimages collide, so the numeric storage relation B10 needs exactly `Fixed.NoCollision`. solc's layout (`keccak(p) + i`, small roots) would also need non-overlap of ranges, which the first-round premise did not give ([Review](#review), S3). The second round extends the premise to `Fixed.NoOverlap`, so solc's layout is also available (B10). G27, G28, G46.03, G46.05. |
| D2 | Word memory | M1, M1′ | `mem : Nat → Word` holds one *word or symbolic slot* per cell, at a cell index. Fixed-cell `mload l`/`mstore l` are macros (`mload_arity_mismatch`, `mstore_arity_mismatch`). The EVM has byte memory with 32-byte big-endian words and quadratic expansion gas. M1's stack-addressed `mloadAt`/`mstoreAt` match the opcodes' arity but address word cells. | Byte-memory relation (×32 scaling, numeric slot words, expansion bounded only by gas), B07. G46.02, G45.01. |
| D3 | Jumps | M1, M2 | `JUMP n`/`JUMPI n` skip forward (relative) and `LOOP` is structured (`jump_arity_mismatch`, `jumpi_arity_mismatch`). The EVM takes absolute stack destinations that must be `JUMPDEST` outside PUSH data. | Label layout and jump-destination analysis against the pinned decoder, B03 and B04. G45.03–G45.05. |
| D4 | Call frames | M1–M3, M6 | `CALL` pops 2 words, runs no callee and uses a static `accepts` predicate (`call_arity_mismatch`). It has no calldata, success data or reentrancy. The EVM's `CALL` takes 7 operands and runs callee code in a new frame with rollback. | Frames are observed through `Halt.observe` ([§4](#4-the-observation-interface)). Environment frames are abstracted to strategies (B13), our frames execute. G42, G47. |
| D5 | Depth | M1–M4 | No call depth. M5 fails a call at depth 1024 (`Bridge/vendor/EvmYul/EVM/Semantics.lean:165`, `:201`) and a creation likewise (`:254`, `:321`). | Decided: such a frame fails and the caller continues. The source semantics *forces* that failure (`Pin.callFails`). It counts every external frame of the system (calls between instances, `this.f()`, creations, library frames) and environment entries at the depth the environment's code reaches, B12. Internal calls within one contract use memory frames (G01 Q2) and consume no depth. G37, G42.03, G47. |
| D6 | Gas | M1–M4, M6 (zero gas) | The EVM charges gas per opcode, memory expansion, EIP-2929 warm/cold access, the 63/64 rule (`allButOne64`), the 2300 stipend, refunds and the EIP-7623 calldata floor. Osaka adds the EIP-7825 per-transaction cap of 2²⁴. M8 runs 10⁸ message gas, above that cap. | Gas is a resource (`Schedule`, `GasRes`), not an observation. Frames and transactions may fail from it and the caller continues (decided). Realizability is B11. The cap broke forward adequacy ([Q2](#q2-the-osaka-per-transaction-gas-cap)). Answered: EIP-7825 and the block gas limit are idealized (`pinned.txGasCap = none`, `blockGasLimited = false`). G47. |
| D7 | Returndata and revert bytes | M1–M4 | `REVERT` takes no operands and carries no data (`revert_arity_mismatch`). M1 has no `RETURN`, `RETURNDATASIZE` or `RETURNDATACOPY`. M5's `Υ` returns `(σ', A, z, gasUsed)` and drops the output bytes that `Θ`/`Lambda` compute (`Bridge/vendor/EvmYul/EVM/Semantics.lean:823`–`:946`). | The observation is the halt's bytes (G01 Q5: exact ABI and revert bytes, `Panic` included). The adapter reads `Θ`/`Lambda`'s output, not `Υ`'s result, B14. G38, G47. |
| D8 | Transient storage | M1–M4 | Absent from the machine. The source has a logical store ([transient-storage.md](transient-storage.md)). M5 keeps a `tstorage` field per account (`Bridge/vendor/EvmYul/State/Account.lean:47`), clears it at transaction end (`Semantics.lean:944`) and rolls it back with the frame's account map. | `TLOAD`/`TSTORE` relation to the logical store, with reset at transaction end and frame rollback (EIP-1153), B09. G46.03. |
| D9 | Precompiles | M1 (none); M5 (Cancun set 1–10 only, `Semantics.lean:787`–`:796`; SHA-256 and BLAKE2 via FFI) | Osaka has 18: 0x01–0x0a, Prague's BLS12-381 0x0b–0x11 (EIP-2537) and P256VERIFY at 0x100 (EIP-7951). MODEXP has Osaka's bounds and gas (EIP-7823, EIP-7883). Under M5, a call to 0x0b–0x11 or 0x100 reaches an empty account. | Decided: precompiles are fixed functions, never environment code. The table is `Precompile`, `Fixed.precompile` (quantified) and `precompileGas` (fixed to Osaka's), and calls to them are not `Event.call`s. Instances are B15 and B16; the repin is B01. G46.05, G47. |
| D10 | CREATE addresses | M1 (no creation); source world (the creator picks a fresh address; [contract-world.md](contract-world.md)) | The EVM address is `keccak(rlp [sender, nonce])[12:]`. A creation fails at an address with code or a nonzero nonce (EIP-684) or non-empty storage (EIP-7610; M5 checks code and nonce only, `Semantics.lean:664`–`:667`), and when the nonce is at 2⁶⁴−1 (EIP-2681). | `Fixed.createAddress` is a fixed function of `Fixed.keccak` (checked against known addresses). The source tracks nonces of the system's accounts, and a creation at an occupied address fails. No address-injectivity premise (G46.05). An address equal to a precompile's installs the account, but calls there still run the precompile, on both sides. Address 0 is excluded by the approved "address 0 has no code" assumption. B17. G44.03. |
| D11 | Fork pin | M5, M9 (Cancun); M1 (none) | G00 disagreement 2. Relative to Cancun, Prague and Osaka add `CLZ` (EIP-7939, Osaka), the precompiles of D9 (BLS12-381 Prague, P256VERIFY Osaka), the gas cap of D6 and Prague's EIP-7702 delegated code and EIP-7623 floor. | M9 is re-pinned by the sibling g06-osaka-repin. M5 needs an Osaka repin or extension, B01. M1 is an inner language and needs no fork. |
| D12 | Code-size limits | M5 (`i.size ≤ 49152`, `Semantics.lean:254`, `:321`, `:480`; `MAX_CODE_SIZE := 24576`, `:670`); M9 (caps on) | The decision idealizes both. M8 already disables them (`replay.mjs:54`). | `pinned.runtimeCodeLimit = none`, `initcodeLimit = none`. M5 needs a recorded vendor patch or parameter, B02. |
| D13 | Keccak in M5 | M5 | `ffi.KEC` is an `@[extern]` opaque (`Bridge/vendor/EvmYul/FFI/ffi.lean`, lines 20–27), so no Lean proof relates it to `Solidity/Keccak.lean`. | `Fixed` is a parameter. The adapter instantiates it either with `ffi.KEC` (the public theorem then holds for it, but the random-oracle lemma says nothing about a C function) or, better, by a vendor patch defining `KEC` by the core Keccak, B15. G46.05. |
| D14 | Transaction validity and fees | M5 (`Υ` does not validate; balance subtraction is `UInt256` and wraps, `Semantics.lean:823`) | Osaka rejects a request whose sender cannot cover `value + gasLimit·price` (plus blob fee). `Υ` would run it with a wrapped balance. | Decided: an unaffordable request never executes. The adapter must apply validity before `Υ`, B18. A request the EVM drops is `TxFate.dropped` on the source side, and the sender's balance after upfront fees is `TxFate.runs`'s `senderBalance` ([§3.5](#35-sender-funds)). |
| D15 | Forced ether | source world, lifetime model ([lifetime.md](../lifetime.md)) | The own balance can rise with no frame of ours running. The coinbase fee credit is `Semantics.lean:939`. The other sources are another contract's `SELFDESTRUCT` beneficiary (EIP-6780 keeps the transfer) and EIP-4895 withdrawals. | [Q1](#q1-forced-ether-and-the-own-balance), answered: environment credits. The environment may raise the own balance between transactions and during environment frames, and the ledger records the credits. B19. |
| D16 | Environment code vs strategies | source (strategies: arbitrary history-dependent functions, G01 Q4) vs M5 (environment accounts run code) | Code realizes only computable strategies, but every finite prefix of a strategy is realizable by code. | `envOnto` must be read on finite prefixes and committed history ([§5](#5-mapping-to-g01s-evmspec-and-findings-for-g01), F3), B13. G42.02. |
| D17 | Stack limit | M1 (unbounded stack, `pushes` bound only on array length) | 1024 operand words per frame. | The compiler bounds each frame's stack. Recursion uses memory frames, so this is a compiler obligation, not a resource failure. G45.02. |
| D18 | Evaluator fuel vs divergence | M1 (`loopRun` classical, a fault on divergence), M5 (`OutOfFuel`) | M1's divergence is a fault, not an unfinished prefix. M5's fuel is the right shape. | The fuel of `GasRes` indexes prefixes, and `OutOfFuel` gives `final = none`. M1 needs a step-indexed run (G01 reuse map). G36, G47. |
| D19 | Static entries | M1–M4 (no static mode) | The environment may `STATICCALL` any of our functions. `SSTORE`, `TSTORE`, `LOG*` and value-carrying `CALL` then halt exceptionally. | Entries carry a static flag in the core semantics and the source, B24. G42.02, G42.05, G47. |
| D20 | Code as data | M1 (code is an instruction list) | `CODECOPY`/`CODESIZE`, constructor arguments appended to initcode, and immutables patched into the runtime code make the installed code differ from `CodeUnit.runtime`. | Installed-code relation, B25. G44.01, G44.02. |
| D21 | Nonces | source world (no nonces) | A contract's nonce starts at 1 (EIP-161), and the creator's nonce rises when `CREATE` starts, even if the initcode fails. Both fix later `createAddress` values. | The source tracks the system's nonces, B17. G44.03. |
| D22 | Stipend payments to our own instances | source (G04 Q3: typed recipients run their own code) vs M5 | `transfer`/`send` to an instance of the system succeed only if the *compiled* `receive`/fallback fits in 2300 gas. EIP-2200 also makes `SSTORE` fail at 2300 gas or less remaining. | [Q3](#q3-stipend-payments-to-the-systems-own-instances), answered: a compiler-independent `StipendRule` decides which bodies fit, and the compiler is proved to fit them (`StipendRule.Fitted`), B28. G43. |
| D23 | Reentrant entries | G01 `Event` (no entry event) | An environment frame entering the system, and our answer to it, is not an observation, so wrong callback return data is not observed. | Finding F6. G42.03. |

## 3. The pinned semantics interface

All names are in `Solidity/Roadmap/Evm.lean`. The module imports only
`Solidity.Keccak`, which has no imports. So whatever instantiates `Pinned`
reaches no compiler module through it (G01's import gate, item 3).

### 3.1 The pin

`Pin` holds the fork, three optional limits, the depth, the stack and the
stipend. `osaka` has the chain's values. `pinned` is the decisions' pin
(`pinned_eq`): Osaka with `runtimeCodeLimit = initcodeLimit = none`,
`txGasCap = none` and `blockGasLimited = false`. The last two record the
answer to [Q2](#q2-the-osaka-per-transaction-gas-cap). So every gas schedule
is admissible (`GasRes.admissible_pinned`), while a too-low limit still makes
a transaction fail or be dropped. The public theorem must state
`V.pin = pinned` for its EVM, because `Pinned.pin` is a label that `sem` is
not forced to respect.

### 3.2 Fixed functions

`Fixed` holds `keccak` (below 2²⁵⁶, `keccak_lt`), `precompile` (`none` for an
exceptional halt) and `precompileGas`. The source semantics and the pinned EVM
take the **same** `Fixed`.

- **Quantified.** The public theorem quantifies over `keccak` and `precompile`,
  so it holds for the real functions without trusting them; their
  identification is a bridge lemma (B15, B16). This reads the decisions
  literally: "opaque hashes are a fixed parameter instantiated by keccak", and
  precompiles behave "as their EVM definitions (the crypto ones through the
  approved fixed functions)". Quantifying over a function proves every
  instance, the EVM definition included. It does stop the compiler from
  *relying* on a precompile's value (for example, using identity to copy
  memory). That costs nothing, because the compiler needs no precompile.
- **Fixed by the pin.** `precompileGas` is an EVM definition, not a crypto
  function, and the theorem fixes it to Osaka's. Quantified, a huge gas value
  would make a successful source `sha256` unrealizable under a cap.
- **The source side.** The source's current concrete `sha256`, `ripemd160`
  and `ecrecover` (`Solidity/Hashes.lean`, `Solidity/Secp256k1.lean`) become
  the instances of `Fixed.precompile` at 0x01–0x03, through a correspondence
  theorem (S05). `SourceSpec` must take the same `F` (finding F5).

Definitions over `Fixed`:

- `keccakWord` is the instance by `Solidity/Keccak.lean`, and `withKeccak` is a
  `Fixed` that uses it.
- `Fixed.NoCollision F hashed` is **the per-run hash premise** (G01 Q3): the
  preimages hashed by an execution prefix do not collide.
  - `NoCollision.mono` shows the premise is downward closed.
  - `hashed` must come from the *source* execution, so that the premise does
    not depend on the compiler. G01 must expose it (finding F7).
  - The compiled code's preimages are determined by the source's under the
    hashed layout (D1, B10).
  - The probability bound is the sibling hash-collision-bound task's lemma.
- `Fixed.NoOverlap F L roots hashed` is **the extended per-run premise**
  (second round): no two hashed regions of `L` slots overlap modulo 2²⁵⁶, nor
  a region and a root slot. `NoOverlap.noCollision` shows it includes
  `NoCollision` when `0 < L`.
- `Fixed.createAddress F sender nonce` is the low 160 bits of
  `keccak(rlp [sender, nonce])`, built from `rlpBytes`, `rlpList`, `beBytes` and
  `beFixed`, with `createAddress_lt`. The `#guard`s check it at `withKeccak`
  against the published first two creation addresses of `0x6ac7…dbf0`, and
  check two RLP boundary cases.
- `precompileGas` matters where the *source* fixes the forwarded gas. With a
  2300 stipend, `transfer` to 0x01 (3000 gas) always fails on Osaka, while
  `transfer` to 0x04 (identity, 15 gas on empty input) succeeds. The source
  semantics must compute these results from the table.

### 3.3 Precompiles

`Precompile` lists the 18 Osaka precompiles, `Precompile.address` gives their
addresses and `Precompile.all` lists them in address order. Lemmas:

- `mem_all`;
- `ofAddress?_address`, so `ofAddress?` is a partial inverse;
- `address_injective`;
- `address_pos_lt`: none is at 0, which stays an account without code (an
  approved assumption), and each is below 2¹⁶⁰.

A call or payment to a precompile address runs `Fixed.precompile`, and any
value moves to the precompile's account. It is internal to the semantics, not
an `Event.call`. A precompile that runs out of gas is a frame failure like any
other.

### 3.4 Resources and the decided failure semantics

- **EVM resource.** `Schedule` is each request's gas limit `txGas i`. Which
  transactions run out of gas depends on the code, so the limit is a
  resource, not an environment input.
  - The gas and depth with which environment code enters the system belong to
    that code, so they are part of the environment.
  - The gas our own calls forward is the compiler's choice. Callee answers
    range over all outcomes regardless of it (G01 Q7).
- `GasRes = schedule × fuel`. Its order (`instance : LE GasRes`,
  `GasRes.le_refl`, `GasRes.le_trans`) compares fuel at an **equal** schedule.
  - A different schedule is a different execution, so gas exhaustion is a
    completed observation (failure, then the caller continues), never the end
    of a prefix. Only fuel ends a prefix.
  - This implements the follow-up "`Lang.Res` must stop ending a session at
    gas exhaustion".
- **Admissible EVM resources.** `GasRes.Admissible p r` requires every
  `txGas` within `p.txGasCap` when it is `some`. `Admissible.of_le` shows fuel
  does not affect it.
- **Source resource: `FailurePoints`.**
  - Each request has a `TxFate`. `dropped` means invalid: the sender cannot
    cover value and upfront fees, or the limit is below intrinsic gas. `runs
    senderBalance failAfter` gives the sender's balance after upfront fees and
    where the request fails from gas, if it does.
  - The `k`-th **external frame of the system**, in start order, may fail
    after that many of its events. These frames are environment entries, calls
    between instances, `this.f()`, initcode and library frames.
  - All of these are admissible, so the source stays `Idealized` (G01 Q1).
- **Forced failures.** The source semantics forces the failures no resource
  can avoid:
  - a call or creation from depth ≥ 1024 (`Pin.callFails`, counting every
    external frame);
  - a stipend-bounded payment whose recipient needs more gas: a precompile by
    `precompileGas`; an untyped recipient may refuse anyway (G04 Q3); our own
    instances fail exactly where the `StipendRule` says the body does not fit
    ([Q3](#q3-stipend-payments-to-the-systems-own-instances), answered).
- **Nested-frame failures (decided).** Any external frame of ours may fail with
  a revert its caller sees, and the caller continues. Its effects roll back;
  its events stay observed.
- **Transactions (decided).** Any transaction may fail from gas, and the
  session continues.
- **Internal recursion** uses memory frames (G01 Q2) and is bounded only by
  gas. It is not a separate resource.

### 3.5 Sender funds

Decided: `msg.value` is bounded by the sender's ledger balance, and an
unaffordable request never executes.

- **EVM.** Validity is Osaka's: `value + gasLimit·price (+ blob fee) ≤
  balance`, and the limit must cover intrinsic gas (with the EIP-7623 floor).
  An invalid request produces no `Event.tx` and changes nothing. During
  execution, `BALANCE(sender)` reads the balance after the upfront fees.
- **Source.** The request's `TxFate` carries that post-fee balance (it depends
  on the gas limit, a resource). The source runs the request iff it is not
  `dropped` and `value ≤ senderBalance`.
  - Backward: every EVM run or drop has a source fate.
  - Forward: a source `dropped` is realized by a limit below intrinsic gas,
    and a source run by a limit and environment balance covering the fees.
- **Other environment accounts.** Their balances are environment inputs
  (G00 Q2). They are affected by the system's payments to them and by
  environment activity in between.

### 3.6 `Pinned` and the certificate

`Pinned Art P` holds `pin`, `fixed`, `Env`, `Res` (with `resLE`), `Allowed`,
`Admissible`, `sem : Art → Env → Res → P` and `consistent`.

- `P` is the prefix type with its order.
- `Env` is the whole world: environment accounts with their code, the request
  and block sequence, and the block contexts.
- The external EVM takes `Res := GasRes` and `Admissible := GasRes.Admissible
  pin`. The core semantics of [§6](#6-the-corebridge-certificate-boundary) may
  take another resource type.

`Certificate core ext` is §6's boundary. `Certificate.refl` checks that it is
satisfiable, and `Certificate.back_le` reads it on one artifact.

## 4. The observation interface

`Halt` has three cases: `success` (STOP/RETURN with its data), `revert` (with
its data) and `exceptional` (out of gas, an invalid or unassigned opcode, a bad
jump, a stack limit, a static-mode write). `Halt.observe` gives what the
caller sees: the success flag and the return data buffer.

- `observe_exceptional`: an exceptional halt is the same observation as
  `REVERT(0, 0)`. Only gas tells them apart, and gas is not observed.
- `observe_success`: no failure is observed as success.

Mapped to G01's shared types (`Solidity/Roadmap/Contracts.lean`, `Outcome`
and `Event`):

| EVM fact | G01 observation |
|---|---|
| A transaction's top frame halts with `h` | `Event.tx sender value timestamp input (o h)`, with `o (.success d) = .success d` and otherwise `.revert` of the observed bytes (`[]` for an exceptional halt). A gas-exhausted transaction is `revert []`. A dropped request has no event. |
| Deployment of the selected contract | `Event.deploy`, with the address `createAddress` gives on success. |
| A `CALL` from our code to an account outside the system that is not a precompile | `Event.call callee value input static`, then `Event.answer (o h) none` for the callee's halt `h`. |
| A `CREATE` of a contract of the input | `Event.create value contract args`, then `Event.answer (o h) (some address)`. A failed creation has `none`, and the revert data the catch clause reads is in `o h`. |
| A call to a precompile, or between instances of the system | No event (internal semantics). |
| An environment frame entering the system, and its result | **No event in G01 at the base** (finding F6). |
| Gas, logs, raw storage layout, `PUSH0` vs `PUSH1 0`, code bytes | Not observed (G00 exclusions). Log arguments still execute. |

Transient storage is not observed directly. Its effects show in later
behaviour within the transaction. The functional `decode : EvmWorld →
Option IntrinsicWorld` (G01 Q6) reads account storage through the same
numeric slot relation as B10 and ignores `tstorage`, which is empty between
transactions (B26).

## 5. Mapping to G01's `EvmSpec`, and findings for G01

`EvmSpec` keeps its name: the sibling g01-contracts-rev is revising
`Solidity/Roadmap/Contracts.lean`, and this document does not edit it. Given
any `V : Pinned Artifact (Prefix Event Outcome)` and `instance : LE (Prefix
Event Outcome) := ⟨Prefix.Le⟩`, an instance is

```lean
def ofPinned (V : Pinned Artifact (Prefix Event Outcome)) : EvmSpec where
  lang := { Prog := Artifact, Env := V.Env, Res := V.Res, resLE := V.resLE,
            Allowed := V.Allowed, Admissible := V.Admissible,
            sem := V.sem, consistent := fun a e => V.consistent a e }
  load := id
```

This sketch is not checked here, because the module may not import
`Contracts`. It fits the G01 types, since `Prefixes.Consistent` is `∀ r r', r ≤
r' → …` over the given `LE`. The G01 `EvmSpec` docstring lists code size as a
resource. That resource is gone (EIP-170/3860 idealized), as the G01
follow-up says.

The revised G01 statements must absorb the findings below. None of them
reopens a decision; they concern how the contracts express decisions already
taken.

- **F1 — what depends on the code goes into `Res`.** `PublicCorrectness`
  takes one `envAbs : V.lang.Env → S.lang.Env` that does not depend on the
  program. That works only if every code-dependent quantity is a resource:
  - which requests are dropped;
  - the post-fee sender balance;
  - where a transaction or an external frame fails from gas.

  This interface puts them in `GasRes`/`FailurePoints`, so the per-program
  `∃` of `Refines` and `Cert.need`/`back` absorbs them. The environment map
  then stays program-independent (as `Certificate.envMap` is).
- **F2 — divergence across schedules.** With a gas schedule in `Res`, every
  EVM transaction ends: at a fixed finite `txGas` it runs out of gas. So
  `Prefixes.Diverges A` (every admissible bound unfinished) is false on the
  EVM for every program, and `Refines.diverges` is vacuous. `Refines` itself is
  unaffected: an unfinished source prefix at the no-failure fate lies below an
  EVM prefix at large gas and small fuel. Two changes are needed:
  - Divergence must be read as "never completes other than by a resource
    failure, with admissible prefixes of unbounded length". In the source this
    is every fuel unfinished at the no-failure `FailurePoints`. On the EVM it
    means every completion is a gas failure that `back` maps to a failure
    point.
  - `SourceSpec.NonVacuous`'s revert and divergence witnesses must be taken at
    the no-failure `FailurePoints`. Otherwise failure point 0 makes every
    program revert.
- **F3 — `envOnto` on finite prefixes and committed history.**
  - EVM environments are code, so they realize only computable strategies,
    while the source quantifies over all history-dependent strategies (G01 Q4).
    Every finite prefix of a strategy is realized by code, so `envOnto` (like
    `Certificate.forth`) must ask only for finite parts of a source
    environment.
  - Environment code's state inside a reverted frame or transaction is rolled
    back. A strategy may therefore depend only on *committed* history, plus the
    outcome of a frame as its caller saw it. Otherwise only a gas side channel
    could realize it.
- **F4 — forced failures are source semantics.** The source semantics itself
  forces the depth-1024 and stipend failures (`Pin.callFails`, `precompileGas`).
  `SourceSpec.Idealized` survives because no resource has to avoid them.
- **F5 — the source takes `Fixed`.** `SourceSpec` (or `PublicCorrectness`)
  must be parameterized by the same `F : Fixed`. The public theorem is then
  `∀ F, F.precompileGas = osaka gas → …`.
- **F6 — entries into the system are observations.** `Event` needs an entry
  event: an environment frame calling one of our instances with caller, value,
  input and static flag, and our outcome bytes. Without it, a compiler that
  returns wrong data from callbacks or view re-entries satisfies contract 5,
  against G01 Q4 (unbounded reentrancy) and Q5 (exact bytes).
- **F7 — the hashed preimages come from the source.** `PublicCorrectness`
  needs the per-run premise over a function of the source prefix (the
  preimages the source execution hashes), not over the EVM's hashes.
- **F8 — the public theorem fixes the pin.** It must state `V.pin = pinned`
  and that `V.fixed` is the quantified `F`.

## 6. The core/Bridge certificate boundary

**What the dependency-free core states.**

1. The interface `Solidity/Roadmap/Evm.lean` (this group).
2. A **core pinned semantics** `core : Fixed → Pinned Artifact …`. Its owners
   are G46.06 and G47, in future modules outside the Codex-owned
   `Solidity/Evm/**`. It
   - decodes bytes by its own Osaka opcode table, never by an inverse of
     `assemble` (the G01 gate);
   - executes the compiled system's frames exactly, for the opcodes it
     specifies;
   - runs environment frames by their observation only: a strategy answers
     each `Event.call` and may enter the system again, with its own depth,
     gas and static flag;
   - runs precompiles by `Fixed`, and gas by Osaka's gas function over the
     specified opcodes.
3. **Specified artifacts.** The certificate covers only artifacts whose
   reachable decoded code uses specified opcodes (`Certificate.Specified`). A
   compiler lemma (B27, G45.05) shows that every compiled artifact is
   specified. An unspecified opcode is therefore neither stuck (which would be
   indistinguishable from "still running") nor given an unverified meaning:
   the compiler never emits one.
4. The compiler proofs (G45–G47) target `core`. Contract 5 is proved for
   `ofPinned (core F)` for every `F` with Osaka's precompile gas, under the
   per-run premise.

**What an external adapter proves** (in `Bridge/`, never imported by the core):
`Certificate (core F) ext` for its machine `ext`, which for EVMYulLean is M5
after B01/B02. The certificate's fields:

- `pin` and `fixed`: the same pin and fixed functions;
- `Specified`: the artifacts covered;
- `envMap`, `envSound`: one environment map, fixed before the artifact, that
  takes allowed external environments to allowed core ones. It must preserve
  the shared components (accounts, requests, block fields; B23), so that an
  input the core reads wrongly cannot be repaired by choosing another
  environment;
- `back`: every admissible external execution of a specified artifact is
  observed exactly as an admissible core execution at the mapped environment;
- `forth`: every admissible core prefix is realized by an external
  environment whose image agrees with the core's on that prefix. This is F3's
  finite reading, with strategies realized by code and failure points by gas.

`Certificate.refl` shows the certificate can be satisfied. Whether it
discriminates (an always-reverting core does not certify a succeeding `ext`)
is a G07 negative control. The public theorem transfers to the external
machine through `Certificate.back` composed with contract 5 at the mapped
environment; that composition lives in Bridge (B21). The core theorem needs
no dependency.

**Why this boundary.**

- The core cannot import EVMYulLean (Mathlib).
- The public theorem must not rest on an EVM written only by the compiler's
  authors.
- The certificate makes the external, independently written EVM the
  reference. The core semantics is the shared statement, checked against
  upstream rather than trusted.
- The core executes only our own code. Environment code is quantified by
  strategies (D16), so the core semantics stays small.

## 7. Required bridge lemmas and owners

Statements are informal where the types are future work. "Core" means the
core pinned semantics of §6.

| Id | Lemma | From → to | Owner | Seed at base |
|---|---|---|---|---|
| B01 | Osaka repin of the external EVM: `CLZ`, the BLS12-381 and P256VERIFY precompiles, Osaka MODEXP, EIP-7610, the EIP-7825 cap as a pin field, EIP-7702 delegation and the EIP-7623 floor gas | M5 → Osaka | **G06 residual** (decision follow-up "Pins (G00, G05, G06)"), carried out in the vendor by G46.06 | `VENDOR.md` refresh procedure |
| B02 | Code-size limits as pin parameters (`none` = no check) in the adapter, as a recorded vendor patch | M5 | G06 residual, with B01 | `lean-4.24.patch` precedent |
| B03 | Byte decoder agreement: core decoding = `EvmYul.EVM.decode` (PUSH immediates, `JUMPDEST` validity, `D_J`) | core ↔ M5 | G45.05 | — |
| B04 | Label/jump realization: relative and structured control (M1 `jump`, `jumpi`, `loop`) realized by absolute `JUMP`/`JUMPI` to valid destinations | M1 → core | G45.03 | `jump_arity_mismatch`, `jumpi_arity_mismatch` |
| B05 | Opcode step agreement with gas charged, for every opcode the core specifies, extending the projected agreements: arithmetic and control (G46.01), memory (G46.02), storage (G46.03), environment (G46.04), hashing (G46.05), calls and creation (G47) | core ↔ M5 | G46.01–G46.05, G47 | `BinaryOpcode.agrees`, `UnaryOpcode.agrees`, `dup_agrees`, `swap_agrees`, `push_agrees`, `pop_agrees` |
| B06 | Instruction expansion: each M1 macro (`mload l`, `mstore l`, `call`, `revert`, `keccakMap`, `keccakArr`) is a verified opcode sequence | M1 → core | G45.01, G45.02 | `Obstructions.lean` |
| B07 | Byte memory: M1 word cells ↔ 32-byte big-endian memory with numeric slot words and expansion gas | M1 → core | G46.02 | — |
| B08 | Calldata and returndata: `CALLDATALOAD`/`COPY` and `RETURNDATA*` against the ABI views | core | G40, G41, G46.02, G47 | — |
| B09 | Transient storage: `TLOAD`/`TSTORE` ↔ the logical transient store, reset at transaction end and rolled back with the frame | source/M1 → core ↔ M5 (`tstorage`) | G46.03 | `resetTransient_*` (source) |
| B10 | Storage: symbolic `Slot` ↔ numeric slots, under `Fixed.NoOverlap` of the source's preimages (answered) for solc's layout, or `Fixed.NoCollision` for the hashed layout (D1) | M1 → core | G27, G46.03, G46.05 | `no_injective_slot_encoding`, `slot_add_wrap_mismatch` |
| B11 | Gas realizability: every `FailurePoints` is realized by some admissible `GasRes` and environment code (gas use monotone in the limit, the 63/64 rule), and every `GasRes` yields some `FailurePoints` | source ↔ core ↔ M5 | G47, G46.06 | — |
| B12 | Depth: core frame depth = M5 `executionEnv.depth` over all external frames, and `Pin.callFails` matches M5's depth checks | core ↔ M5 | G47 | — |
| B13 | Environment realization: every finite strategy prefix over committed history is realized by environment code (forth), and every environment code run is observed as a strategy (back), across reentrancy | core ↔ M5 | G42.02, G42.03, G47 | `CallbackTrace.lean` (source traces) |
| B14 | Transaction observation: the adapter's outcome reads the output bytes and halting flag of `Θ`/`Lambda`, and `Halt.observe` matches M5's exceptional halts (all gas consumed, empty output) | M5 → core | G47 | `revert_arity_mismatch` |
| B15 | Keccak instance: M5's `KEC` = `keccakWord`. This needs `ffi.KEC` replaced by the core Keccak in a recorded vendor patch, and is impossible against the opaque | M5 ↔ `Fixed` | G46.05 | `Solidity/Keccak.lean` `#guard`s |
| B16 | Precompile instances: M5's `Ξ_*` (after B01) = `Fixed.precompile` and Osaka's `precompileGas` at each `Precompile`; the source's `Hashes`/`Secp256k1` = the same table at 0x01–0x03 | M5 ↔ `Fixed` ↔ source | G46.05 (S05 for the source side) | `Hashes.lean` vectors |
| B17 | CREATE: M5's address computation = `Fixed.createAddress`, with nonce rules (EIP-161 start at 1, creator bump) and failure rules (EIP-684, EIP-7610 storage case missing from M5, EIP-2681), fresh typed storage, and a precompile-address creation | M5 ↔ core ↔ source world | G44.03, G46.05 | `createAddress` `#guard`s |
| B18 | Transaction validity and fees: the core and the adapter drop invalid requests (validity, intrinsic gas, EIP-7623 floor) before execution; `TxFate` matches ([§3.5](#35-sender-funds)) | M5 → core → source | G43, G47 | `EnvironmentAgrees` (balances) |
| B19 | Payments: value transfer, stipend, recipient acceptance (untyped: any outcome; typed: their code) and the own balance with environment credits ([Q1](#q1-forced-ether-and-the-own-balance), answered) | source → core | G43, G47 | `Solidity/Evm/Machine.lean` `pay`, `accepts` |
| B20 | Linked libraries, under the empty link map only (answered): no unresolved link references; the compiled call (on the caller's storage, a `DELEGATECALL` the compiler emits although source `delegatecall` is excluded) and call protection | core | G42.04, G44.02 | — |
| B21 | Composition: `Certificate (core F) ext` from B03–B18 and B23–B27, and the transfer of contract 5 to `ext` | core ↔ M5 | G46.06, G47, G49.02 | — |
| B22 | Differential cross-check (evidence, not proof): core semantics vs M8 on the generated cases | core vs M8 | G52 | `scripts/evm-reference/generated.mjs` |
| B23 | Environment opcodes and `envMap`: `CALLER`, `CALLVALUE`, `TIMESTAMP`, `ADDRESS`, `SELFBALANCE`, `BALANCE` and the admitted block fields read the same values in M5 and in the core at `envMap e` | core ↔ M5 | G46.04 | `EnvironmentAgrees`, `Environment.lean` |
| B24 | Static mode: entries carry the static flag, and state-changing opcodes halt exceptionally under it | core ↔ M5, source | G42.02, G42.05, G47 | — |
| B25 | Installed code: initcode with appended constructor arguments, immutables patched into runtime code, `CODECOPY`/`CODESIZE` | core | G44.01, G44.02 | — |
| B26 | `decode` (G01 Q6): the EVM world's storage, read through B10's relation, decodes to the intrinsic world | core → source | G46.03, G49.02 | — |
| B27 | Specified output: every compiled artifact's reachable decoded code uses only opcodes the core specifies; in-transaction events are extracted from M5's `Θ` (which emits no `Event.call`/`answer`, so it needs a vendor hook), with fuel prefixes realized for `SameObs` | compiler → core; M5 → core | G45.05, G46.06, G47 | — |
| B28 | Stipend rule: every `receive`/fallback body the `StipendRule` admits compiles to code that completes within 2300 gas, with EIP-2200's sentry counted (`StipendRule.Fitted`). The source fails every other stipend payment to our own instances | source → core | G43, G47 | — |

## 8. Reference tooling pins

The reference tooling is evidence, never proof. G06 records its pins and edits
no script. The fork of the vector scripts belongs to the sibling
g06-osaka-repin.

- **M8** (`scripts/evm-reference`) already runs Osaka with the code-size caps
  disabled, which matches the idealization.
  - Its lock (`scripts/evm-reference/package-lock.json`) pins `@ethereumjs/evm`
    10.1.3 with its own nested `common`/`util` 10.1.3, while the top-level
    `common`/`util` that `replay.mjs` imports are 10.1.2. That is G00
    disagreement 5 as observed: the lockfile is the pin, and both versions are
    in use.
  - M8 runs `runCall` at 10⁸ gas, above Osaka's 2²⁴ transaction cap.
    Message-level execution with a larger budget matches the answered
    [Q2](#q2-the-osaka-per-transaction-gas-cap) (gas caps idealized), not the
    chain.
- **M9**, at the base: `check-abi-hex-call.mjs`, `check-abi-vectors.mjs`,
  `check-call-exception-vectors.mjs`, `check-modifier-frames.mjs`,
  `check-operator-aliases.mjs`, `check-public-getters.mjs`,
  `check-recursive-types.mjs`, `check-self-power-data.mjs`,
  `check-slice-copies.mjs`, `check-source-admission.mjs`,
  `check-transient-vectors.mjs` and `check-transient-world-vectors.mjs`.
  - All use `Hardfork.Cancun` and `evmVersion: 'cancun'`, keep the caps on and
    have no lockfile.
  - They differ from the pin in fork and in code-size caps. The repin must
    also disable the caps (or record why a vector needs them) and lock its
    dependencies.
- **M5** is Cancun at `047f630` (B01/B02).

## Scope questions (answered 2026-10-29)

Each question marked a place where a first-round decision could not be met
as stated. The coordinator relayed the user's answers in a second round. They
are recorded in [solidity-scope.md](../solidity-scope.md), "Second round
(2026-10-29)", and encoded here. The questions are kept as asked, each with
its answer.

**Second-round answers that concern G06:**

- **Q1: environment credits.** The environment may raise the own balance
  between transactions and during environment frames, and the ledger records
  these credits. This is a source environment input (B19), not a resource.
- **Q2: idealize both caps.** EIP-7825's per-transaction cap and the block
  gas limit are idealized (`pinned`, `pinned_eq`, `GasRes.admissible_pinned`),
  recorded like EIP-170/3860.
- **Q3: a stipend rule.** A compiler-independent source cost rule decides
  which `receive`/fallback bodies fit the 2300 stipend (`StipendRule`), and
  the compiler is proved to fit them (`StipendRule.Fitted`, B28).
- **Hash regions: the per-run premise is extended.** No two hashed regions of
  length ≤ L overlap, nor a region and a root slot, with a bound of about
  q²·L/2²⁵⁶. This is `Fixed.NoOverlap L roots hashed`.
  `Fixed.NoOverlap.noCollision` shows that it includes the first-round
  premise. B10 may therefore use solc's layout (`keccak(p) + i`, small roots)
  under `NoOverlap`, besides the hashed layout of D1.
- **Settings: solc's two pipelines only.** These are legacy with the
  pragma-selected ABI coder, and via-IR with ABI coder v2. This fixes the
  compiled bytecode's settings provenance (G00 disagreement 7, G05). It does
  not change the pinned EVM.
- **Library links: the empty link map only.** No artifact carries unresolved
  library references (`CodeUnit.links = []`). B20's link-address part is
  therefore empty; B20 keeps the compiled call and call protection.

### Q1. Forced ether and the own balance

The decision "the own balance follows the ledger" cannot hold on Osaka if the
ledger records only the system's own payments. A contract's balance also rises
with no frame of ours running:

- as the block beneficiary (`Bridge/vendor/EvmYul/EVM/Semantics.lean:939`);
- as another contract's `SELFDESTRUCT` beneficiary (EIP-6780 keeps the
  transfer; our own `selfdestruct` is excluded, but theirs is environment);
- through EIP-4895 withdrawals.

`address(this).balance` observes the difference. Prefunding a future `CREATE`
address is already modelled ([contract-world.md](contract-world.md)).

Options:

- **Environment credits in the ledger (EVM-faithful).** Between transactions,
  and while an environment frame runs, the own balance may rise by an amount
  the environment chooses. The ledger records these credits next to the
  system's own payments, and the source must let `address(this).balance` grow
  without any payment of ours.
- **An approved premise of no forced credits.** The pinned EVM's `Allowed`
  excludes these credits. This is a new environment premise, not EVM
  behaviour.

### Q2. The Osaka per-transaction gas cap

The source is idealized (G01 Q1: unbounded fuel), and refinement is
two-sided: every admitted source execution needs an admissible EVM execution
with the same observations. With the cap kept, the forward direction fails in
three ways:

- **Long transactions.** A transaction whose compiled code needs more than
  2²⁴ gas (EIP-7825) cannot complete on Osaka at any gas limit. The decision
  "any transaction may revert from gas exhaustion" settles the backward
  direction: the EVM's revert has a source counterpart. It does not settle the
  forward direction, because the source's successful completion then has no
  EVM counterpart.
- **Deployment.** Code deposit costs 200 gas per runtime byte, plus initcode
  and calldata gas. A contract above roughly 80 KB therefore cannot deploy
  within 2²⁴ gas, which voids the decided "any code size deploys" (G01 Q2).
  Large calldata is likewise invalid under the EIP-7623 floor.
- **Depth.** The 63/64 rule leaves too little gas for a frame near depth 1024
  to do anything. Admitted entries at such depths are unrealizable unless the
  gas is unbounded.

The block gas limit raises the same problem with a larger bound; its decided
follow-up is again only the backward direction. M8 already runs 10⁸ gas per
message.

Options:

- **Idealize the gas caps.** Record EIP-7825 and the block gas limit as an
  idealization, like EIP-170/3860 (`pinned.txGasCap := none`). Two-sided
  refinement and "any code size deploys" both hold. A too-low gas limit still
  makes a transaction revert or be dropped.
- **Keep the cap with a source-level cost bound.** A compiler-independent
  source cost measure, with a proved compiler gas bound, decides which
  transactions forward adequacy covers. Heavier transactions and large
  deployments lose forward adequacy, and the public theorem (a G01 change) is
  weaker for them. A compiler cannot escape the bound by burning gas, because
  the measure is the source's.
- **Keep the cap and the contract.** G47's forward direction stays unprovable
  for such programs and is recorded as unresolved, which by the roadmap's rule
  means the proof is incomplete.

### Q3. Stipend payments to the system's own instances

G04 Q3 decided that typed recipients run their own code. A `transfer`/`send`
to an instance of the compiled system forwards exactly 2300 gas. Whether it
succeeds on Osaka depends on the *compiled* `receive`/fallback: its gas, and
EIP-2200's rule that `SSTORE` fails at 2300 gas or less remaining.

- The source cannot fix the result without depending on the compiler.
- The source cannot leave the result open either, because no resource choice
  changes a fixed stipend, so the EVM cannot realize both results.

This is the one gas-dependent result that neither "frames may fail" nor
idealization can resolve.

Options:

- **A source-level stipend cost model.** A compiler-independent rule says
  which `receive`/fallback bodies fit the stipend (for example, no storage
  write and a bounded body). The source fails the payment otherwise, and the
  compiler is proved to fit whatever the rule admits.
- **Weaken forward adequacy for these payments.** A source success may be
  matched by an EVM failure for stipend payments to our own instances, as a
  recorded weakening of contract 5.
- **Exclude these payments from the profile.** `transfer`/`send` to a typed
  instance of the system become out of profile, under G00's exclusion rules.

## Checks

Run at the head of this branch:

| Check | Result |
|---|---|
| `lean_diagnostic_messages` on `Solidity/Roadmap/Evm.lean` | No errors or warnings. Its `#guard`s (two `CREATE` addresses, two RLP cases) and `#guard_msgs` axiom pins (`Precompile.address_injective`, `Certificate.back_le`: no axioms) pass. |
| `grep` for `sorry`, `axiom`, `native_decide`, `implemented_by`, `maxHeartbeats` in the module | None. |
| `node scripts/check-layers.mjs` | `155 core modules, 0 reach the elaborator`. |
| `node scripts/check-orphans.mjs` | `734 reachable, 0 orphaned, 0 not allowed`. |
| `bash scripts/check-trust.sh` | `0 findings`. |
| `bash scripts/check-doc-paths.sh` | 46 missing references, the base count; none from this change. |
| `./run-lean.sh` (background, log grepped), first run | `lake build`: `Build completed successfully (719 jobs)`. `lake build SolkeyTestSuite` failed: `Solidity.TestSuite.Derived17` was killed (`Lean exited with code 137`, out of memory, while running in parallel with the other `Derived*` modules). That shared file belongs to the memory-loops lane and was not touched. |
| `./run-lean.sh`, second run (incremental, after the review and answer commits) | `Build completed successfully (719 jobs)`, then `Build completed successfully (262 jobs)` (Derived17 built). `check-solkey.sh`: `solkeycheck: 37 mismatch(es)`, unchanged from the base's 37, so baseline only. The script exits 1 on that existing drift. |

## Handoff

- **Base:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`. **Files:** this
  document and `Solidity/Roadmap/Evm.lean`, plus one line each in
  `Solidity.lean`, `docs/module-map.md`, `docs/README.md` and
  `docs/coverage-plan.md`.
- **Done:**
  - the machine inventory M1–M9 and disagreements D1–D23;
  - the pinned semantics, observation and certificate interfaces, as Lean
    statements;
  - findings F1–F8 for G01;
  - bridge lemmas B01–B28 with owners;
  - questions Q1–Q3, answered in the second round and encoded.

  No source-to-bytecode obligation is closed.
- **Definitions** (no premises unless stated): `Bytes`, `Fork`, `Pin`, `osaka`,
  `pinned`, `allButOne64`, `Pin.callFails`, `Precompile`, `Precompile.address`,
  `Precompile.all`, `Precompile.ofAddress?`, `Fixed`, `keccakWord`,
  `Fixed.NoCollision`, `Fixed.NoOverlap`, `beBytes`, `beFixed`, `rlpHead`, `rlpBytes`, `rlpList`,
  `Fixed.createAddress`, `withKeccak`, `Schedule`, `GasRes` with its `LE`
  instance, `GasRes.Admissible`, `TxFate`, `FailurePoints`, `StipendRule`,
  `StipendRule.Fitted`, `Halt`,
  `Halt.observe`, `Pinned`, `SameObs`, `Certificate` and `Certificate.refl`
  (premise: a reflexive prefix order).
- **Theorems:**
  - `pinned_eq`;
  - `Precompile.mem_all`, `Precompile.ofAddress?_address`,
    `Precompile.address_injective`, `Precompile.address_pos_lt`;
  - `Fixed.NoCollision.mono` (premises `F.NoCollision hs'` and `hs ⊆ hs'`),
    `Fixed.createAddress_lt`;
  - `Fixed.NoOverlap.noCollision` (premises `F.NoOverlap L roots hs` and
    `0 < L`);
  - `GasRes.le_refl`, `GasRes.le_trans`, `GasRes.Admissible.of_le` (premise
    `a ≤ b`), `GasRes.admissible_pinned`;
  - `Halt.observe_exceptional`, `Halt.observe_success`;
  - `Certificate.back_le` (premises: a specified artifact, an allowed
    environment, an admissible resource).
- **Remaining child obligations:**
  - B01–B28 with owners (§7); B01/B02 are G06 residuals;
  - findings F1–F8 for g01-contracts-rev (§5);
  - the core pinned semantics of §6 (G46.06, G47);
  - the discriminating certificate control (G07);
  - the random-oracle bound for `Fixed.NoOverlap` (sibling hash-collision-bound);
  - B28 (stipend rule and compiler fit, G43).
- **Resources:** the first full run took 74 min wall time (`real 74m24s`, `user 199m38s`); the incremental rerun took 4 min 23 s. The summed RSS of all processes, sampled every 20 s, peaked at 18.4 GB. That figure counts shared pages more than once (the VM has 15 GB), so it overstates the peak; no per-process peak was recorded (`/usr/bin/time` is absent).

## Review

A finder and a separate skeptic reviewed the first commit (`7a21241`). Both
were read-only subagents and neither used the Lean server. All findings
below were checked against the code. Each was confirmed unless stated
otherwise and is fixed at the head.

**Finder (facts and citations).** Every vendor, core and Bridge line
citation, theorem name and anchor checked out except the following, all
fixed:

1. M8's lockfile has nested `common`/`util` 10.1.3 as well as the top-level
   10.1.2 (§8).
2. Not all M9 runners use `runCall`; some use `runCode` (M9 row).
3. EIP-7610 concerns non-empty storage, and M5 lacks it (D10, B01, B17).
4. M1 also has stack-addressed `mloadAt`/`mstoreAt` (D2).
5. D5's citations covered calls only; creation depth checks were added.
6. The 1,024 stack in M8 is EthereumJS's default, not a setting.
7. BLS12-381 is Prague, not Osaka (D11).
8. The Checks and Handoff sections had no results.
9. This Review section was empty.
10. `Bytes` and the `LE` instance were missing from the Handoff.

**Skeptic (design).** All confirmed except where noted:

- **S1 (major).** `Certificate` chose a fresh environment per execution, so a
  core reading an input wrongly could still certify, and contract 5 did not
  transfer. Fixed: one `envMap` with `envSound` and preservation of the shared
  components (B23), `∃` over resources only, and a finitary `forth`.
  `Certificate.symm` was removed, since the map has one direction.
  `Certificate.back_le` was added.
- **S2 (major).** Unspecified opcodes were "stuck", which `final = none`
  cannot tell from running, and `back` was unprovable for such artifacts.
  Fixed: `Certificate.Specified`, and the compiler lemma B27 that compiled code
  is specified.
- **S3 (major).** The old Q3 (slot ranges) was not a question. The compiler
  controls layout, which is unobservable, so a hashed layout makes the decided
  premise sufficient. Fixed: D1 and B10 adopt the hashed layout; the question
  was removed.
- **S4 (major).** Gas limits in the resource can make a request invalid, which
  the source could not mirror. Fixed: `TxFate.dropped` and the post-fee sender
  balance in the source resource (§3.5, F1).
- **S5 (major).** Failure points covered only environment entries. Fixed:
  `FailurePoints.frame` covers every external frame of the system, and depth
  counts all of them (D5).
- **S6 (major).** Q2's option 2 depended on compiled gas, so a gas-burning
  compiler escaped it. Q2 also missed the deployment-size conflict with "any
  code size deploys" and the depth/63-64 evidence. Fixed in Q2: option 2 now
  uses a source-level cost measure, and the backward-only reading of the
  follow-up is argued.
- **S7 (major).** F2's per-schedule divergence never holds on the EVM, and the
  `NonVacuous` revert witness became trivial. Fixed: F2 rewritten.
- **S8 (major).** A quantified `precompileGas` made the theorem false under a
  cap. Fixed: it is fixed to Osaka's (§3.2, F5). The objection that
  quantifying non-approved precompiles contradicts "as their EVM definitions"
  is **not confirmed**: a universally quantified result includes the EVM
  definition, and the compiler needs no precompile value. The address-0 and
  precompile-address creation cases are now explicit (D10).
- **S9 (major).** Stipend payments to our own typed instances raise a genuine
  decision gap. Added as D22 and Q3.
- **S10 (major).** Entries into the system are not G01 observations. Added as
  D23 and F6.
- **S11 (major).** Rollback limits code-realizable strategies to committed
  history. Added to F3 and B13.
- **S12 (major).** The source of the hashed-preimage list was undefined.
  Fixed: F7, and B10 takes the source's preimages.
- **S13 (minor).** The pin label and `Certificate.refl` are not
  discriminating. Fixed: F8 and the G07 negative control.
- **S14 (minor).** Entry gas and depth belong to environment code. Fixed:
  they were removed from `Schedule`.
- **S15 (minor).** Gaps in the inventory: static entries, code as data,
  nonces, failed-creation revert data, and prefunding in Q1. Fixed: D19–D21,
  B24, B25, B17, the §4 row and Q1.
- **S16 (minor).** Gaps and owners in the B list. Fixed:
  - B20 restated;
  - B23 (environment opcodes, G46.04), B26 (`decode`) and B27 (`Θ` event
    extraction) added;
  - B05 split by area; G41 added to B08 and G46.06 to B11;
  - B01/B02 recorded as G06 residuals, per the decision follow-up.
