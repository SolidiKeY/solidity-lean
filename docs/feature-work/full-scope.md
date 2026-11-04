# Full scope, optimizer and solc validation

Status (2026-11-04): **authorized; not yet implemented.** The user withdrew
every recorded exclusion and asked for the whole language, an optimizing
compiler and proofs that solc's own output behaves like the source semantics
([decision](../solidity-scope.md#full-scope-decision-2026-11-04)). This document
plans the three extensions as groups and parallel lanes. It closes no proof
obligation; the manifest keeps reporting actual admission until each group
lands with its evidence.

Three extensions, one endpoint:

- **X — the whole language.** Every feature in `docs/solidity-features.json`
  becomes `model` (or `abstract` with an approved environment premise). No
  `Unmodelled` constructor remains reachable from in-profile source.
- **O — an optimizing compiler.** This repository's compiler gains an
  optimizer, every pass proved (or validated per program) to preserve the
  public source-to-bytecode theorem.
- **T — solc translation validation.** A checker that, for one contract,
  proves in Lean that the bytecode solc 0.8.38 emits (legacy and via-IR,
  optimizer off and on) refines the source semantics. This is a per-program
  theorem, not a proof of solc's C++ code.

## Design decisions

Proposed with the plan; X01 freezes them in G01's contracts before the X lanes
pass their final checks.

- **D1 — compiler-dependent values.** `gasleft()`, `gas`, `msize`, `pc`, own
  `codesize`/`codecopy` and `type(C).creationCode`/`runtimeCode` read the
  compiled artifact. The source semantics takes the artifact table as a
  parameter (the G00 Q5 pattern, extended), plus a gas oracle the target
  execution supplies. The non-circularity whitelist of G07 records why this is
  not defining the source by the compiler. Supersedes G06 D6 and YQ2.
- **D2 — exact gas.** The pinned EVM semantics charges the Osaka schedule
  exactly (memory expansion, warm/cold access, refunds, the 63/64 rule,
  stipends). Gas exhaustion stays a failure the source allows; gas *values*
  become observations through D1. Code-size limits (EIP-170, EIP-3860) are
  modelled as creation failures, replacing the G01 Q2 idealization.
- **D3 — solc's physical layout.** Storage and transient slots, packing, `layout
  at`, and memory (scratch `0x00`–`0x3f`, free-memory pointer `0x40`, zero slot
  `0x60`) follow solc's documentation, so raw observations agree with solc.
  This compiler's representation must agree with it (G27, G32, Y04, Y05);
  the word-cell machine of `Solidity/Evm/Machine.lean` is refined by a byte
  memory before X lanes close.
- **D4 — non-memory-safe assembly.** Admitted. The memory view loses the
  `MemOK` guarantee inside such a block and recovers it only through a proved
  writeback; the optimizer treats the block as opaque (as solc does).
- **D5 — premises that stay.** Only cryptographic and chain premises remain:
  the per-run hash non-collision premise (G01 Q3), the approved crypto
  functions, and environment inputs universally quantified. These are not
  language exclusions.
- **D6 — optimizer correctness relation.** Passes preserve every observation
  except gas values; with D1, a program that reads gas is related to the
  artifact the optimizer actually produced, so the public theorem stays exact.
  Gas improvement is measured (benchmarks), and proved only where a pass
  carries a cost lemma.

## Groups

Each group follows the [VM execution contract](../coverage-plan.md#vm-execution-contract):
code, kernel-checked proofs, inhabited witnesses, negative controls,
finder/skeptic review, handoff in this document.

### X — the whole language

| Group | Deliverable | Depends on |
|---|---|---|
| X01 | **Contracts and manifest.** Amend G01 for D1–D6 (observations: gas values, logs with topics and order, raw call/return bytes, code and codehash; artifact parameter; byte memory). Rescope all 30 rows in `solidity-features.json`, `Unmodelled`, `Feature.exclusion_complete` and the upstream ledger; regenerate the catalog. | — |
| X02 | **Environment fields.** `block.*` (coinbase … slotnum per fork), `blockhash`, `blobhash`, `tx.origin`, `tx.gasprice` as quantified inputs with chain premises; source semantics, admission, lowering, compiler. | X01 |
| X03 | **Gas and resources.** D2 in `Solidity/Backend` and the source semantics: `gasleft`, `{gas: …}` options, exact stipends, refunds, call depth, code-size failures; compiler preservation under D1. | X01, G45 interface |
| X04 | **Raw bytes and low-level calls.** `msg.data`, `msg.sig`, byte-oriented `fallback(bytes)` input/output, `address.call`/`staticcall`/`delegatecall` with raw bytes and returndata; `delegatecall` to a known callee runs its code over the caller's storage, to an environment callee havocs storage. Shares Y07.01's definitions. | X01, Y06 |
| X05 | **Creation and code.** `new C{salt: s}` and the CREATE2 address, `selfdestruct` under EIP-6780, `address.code`/`codehash`, `extcodesize`/`extcodecopy`, execution of arbitrary creation/runtime bytecode through the EVM semantics. Shares Y07's definitions. | X01, X04 |
| X06 | **Physical layout.** D3: storage/transient slot and packing views, `layout at`, byte memory and the free-memory pointer as source-visible state; compiler agreement (replaces the "unobservable layout" reading of G27/G32). | X01, Y04, Y05 |
| X07 | **Logs and full assembly.** `emit` as observations (topics, data, order; YQ6), anonymous events, `log0`–`log4`; assembly tier D: `gas`, `msize`, `pc`, `codesize`/`codecopy` under D1, non-memory-safe blocks under D4. | X01, X03, X06, VY4 |
| X08 | **Composition.** G03 ledger rows and combinations for X02–X07; no residual exclusion predicate in G48–G51; upstream corpus rows formerly excluded re-run as in-profile. | X02–X07 |

### O — optimizing compiler

| Group | Deliverable | Depends on |
|---|---|---|
| O01 | **Pass framework.** A typed pass interface over the lowering IR and over Yul (`Pass : Prog → Prog` with `Preserves`), composition lemma into `Compilation.correct` / G49, and a translation-validation interface (`Validator`, `validate_sound`) for untrusted passes. Benchmarks of current code size and gas. | current `Evm.Compiler`, `Yul/Compilation` |
| O02 | **Value passes.** Constant folding and propagation (checked arithmetic keeps its Panic), copy propagation, expression simplification with solc's rule list as the reference, dead-code and unused-variable elimination. | O01 |
| O03 | **Structural passes.** Inlining of internal functions, common-subexpression elimination, redundant `sload`/`mload` and store elimination (needs X06's aliasing facts), loop-invariant code motion, unused-function pruning. | O01, O02 |
| O04 | **Backend passes.** Peephole rules, jumpdest removal, block deduplication, constant optimizer (`PUSH` vs computed), stack scheduling with proved stack-depth bounds. | O01, G45 |
| O05 | **Cost lemmas and settings.** `runs`-style trade-off, cost lemmas for the passes that carry them, a gas regression suite, optimizer on/off as a setting of the public theorem. | O02–O04, X03 |

### T — solc translation validation

| Group | Deliverable | Depends on |
|---|---|---|
| T01 | **solc's Yul dialect.** The full EVM Yul dialect solc emits (builtins, `datasize`/`dataoffset`/`datacopy`, `setimmutable`/`loadimmutable`, `linkersymbol`, `memoryguard`, objects) on the core Yul semantics, pinned to 0.8.38; import of `--ir` and `--ir-optimized` output. | `Yul/`, X06 memory view |
| T02 | **IR matcher.** Unoptimized via-IR Yul against the source: match each `fun_<name>_<id>` and helper (`checked_add_*`, `abi_decode_*`, `array_push_*` …) to its `Stmt`/runtime definition, emit a simulation proof per function, then per contract (dispatcher, constructor). Generalizes `Evm/Signed.lean` and `Evm/Exp.lean`. | T01, G01 relations |
| T03 | **Yul optimizer validators I.** One validator per step of solc's default sequence, first the expression-level ones: ExpressionSimplifier, CommonSubexpressionEliminator, SSATransform/reverse, UnusedPruner, UnusedAssignEliminator, LiteralRematerialiser, ConditionalSimplifier. | T01 |
| T04 | **Yul optimizer validators II.** Structural steps: FullInliner, ExpressionInliner, LoopInvariantCodeMotion, ForLoopConditionInto/OutOfBody, StructuralSimplifier, EqualStoreEliminator, UnusedStoreEliminator, StackToMemoryMover; a fallback symbolic-equivalence checker for steps without a dedicated validator. | T01, T03's framework |
| T05 | **Yul to bytecode.** Validate solc's EVM code transform and stack layout generation: bytecode (decoded by `Solidity/Backend/Opcode.lean`) simulates the optimized Yul, via source maps and a stack-layout certificate inferred from the bytecode. | T01, G45, X03 |
| T06 | **Legacy pipeline.** No IR: a bytecode validator that symbolically executes legacy output (optimizer off and on) against the source semantics, with the relation built from `storageLayout`, source maps and the legacy codegen patterns; the legacy optimizer's steps (peephole, CSE, constant optimizer, deduplication, jumpdest removal) validated at assembly level. | T02's relations, X06, X03 |
| T07 | **Public theorem and tool.** `solc_validated : validate src artifact = true → Refines artifact src` for both pipelines and both optimizer settings; a `sol_validate` command and CLI; incompleteness reported precisely (an unvalidated step says which). | T02–T06 |
| T08 | **Corpus and bugs.** Run the validator over the upstream semantic tests and the repository's `.sol` files in all four modes; regression rows for solc's `bugs.json` (each known optimizer bug must be rejected on its trigger). | T07 |

## Lanes

Sized by the [sizing rules](../coverage-plan.md#sizing-rules): one 16 GiB VM,
eight to ten hours, three or four groups as a dependency chain. Lanes on the
same row of the wave table run **in parallel**; a lane may prepare against a
frozen interface early, but passes its final check only on integrated
prerequisites.

| Lane | Checkpoints, in order | Starts after |
|---|---|---|
| VX1 | X01, X02 | — |
| VX2 | X03, O05's benchmark harness | VX1; V13 (G45 interface) for the final check |
| VX3 | X04, X05 | VX1, VY2 |
| VX4 | X06 | VX1, VY2; V10/V11 take D3 as an agreement obligation |
| VX5 | X07, X08 | VX2–VX4, VY4 |
| VO1 | O01, O02, O03 | — (against the current compiler; re-validated at V16) |
| VO2 | O04, O05 | VO1, V14 (G45) |
| VT1 | T01, T02 | VX4's memory view for the final check |
| VT2 | T03, T04 | VT1's T01 |
| VT3 | T05, T06 | VT1, VX2 |
| VT4 | T07, T08 | VT1–VT3 |

### Waves

| Wave | Parallel lanes | Notes |
|---|---|---|
| A | VX1, VO1, VT1 | Start now; independent writes (manifest/contracts, `Evm`/`Yul/Compilation` passes, `Yul/` dialect and `Frontend/SolcJson`). |
| B | VX2, VX3, VX4, VT2, VO2 (when V14 lands) | After VX1 merges. VX4 coordinates with V10/V11 owners on layout files. |
| C | VX5, VT3 | After wave B's prerequisites. |
| D | VT4 | Then G48–G55 (V16/V17) close with X, O and T included. |

Peak is five concurrent lanes, plus the main chain V07–V17 and VY1–VY5.
Gate new Lean agents on memory as for the other lanes. File ownership for
conflicts: X01 owns `solidity-features.json`, `Language/FeatureInfo.lean`
and `Roadmap/Contracts.lean`; VO lanes own new `Solidity/Optimizer/**`; VT
lanes own new `Solidity/SolcValidation/**` plus `Frontend/SolcJson/Ir*`.
Register new modules with `scripts/coord-tools/register.sh` and add
`docs/module-map/` rows.

## Done when

- The roadmap's [done-when](../coverage-plan.md#done-when) list holds with no
  exclusion: every manifest row is `model` or approved `abstract`.
- The public theorem covers optimizer on and off, and every pass is proved or
  validated with `validate_sound`.
- `solc_validated` is kernel-checked; the T08 corpus run validates every
  in-profile upstream row in all four modes or names the solc step that has
  no validator yet (an open item, never an exclusion).

## Handoffs

None yet.
