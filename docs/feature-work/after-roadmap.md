# After the roadmap: automation and a usable compiler

Status (2026-10-31): **planned, not started.** These lanes extend the roadmap
of [coverage-plan.md](../coverage-plan.md) and the inline-assembly lanes of
[inline-assembly.md](inline-assembly.md). The roadmap proves the compiler
correct for one pinned profile. It does not improve proof automation (G51
keeps the approved automation target) and does not make compiled code cheap
or deployable in practice (no optimizer; G01 Q2 idealizes code size). This
document plans both. Calculus options (modes) are deliberately left out.

Each lane follows the [VM execution contract](../coverage-plan.md#vm-execution-contract)
and the [sizing rules](../coverage-plan.md#sizing-rules): eight to ten hours
of agent work, three or four groups, implementation with kernel-checked
proofs, finder/skeptic review and a handoff per checkpoint in this document.
**A lane starts only after the user answers the decisions it lists** and
they are recorded in [solidity-scope.md](../solidity-scope.md); M7-next in
particular waits for the user's go ([automation.md](../automation.md#m7-next--a-checkpoint-of-the-theorem-not-started)).

## Part 1 — Proof automation

### Where the cost is

Laziness is already the design ([rule-repair.md](../rule-repair.md#what-lazy-means-here)):
writes, copies and resets stay symbolic and are read through `find`/`read`;
long arrays are `SVec.rep` (`Tools/LazyStorage.lean`). More laziness only
moves work from the walk into the leaf: `ifElseJoin` made the walk linear,
and the leaf then timed out at six `if`s until `CloseJ` existed
([automation.md](../automation.md), M6–M8). The remaining costs are
continuation copies, inlined callees, unrolled loops and the decision
procedure; the user's decisions c, c′, d, e3′ and e3″ stay (undecidable or
unprovable classes answer *unknown*). The SolKey-shaped rules and `⊢ₖ` are
not refactored; automation adds Lean-only rules with soundness proofs, as
`ifElseJoin` and `internalCallSummary` do.

### Groups

| Group | Deliverable | Source of the item |
|---|---|---|
| AU01 | **`DecisionTheorem'`.** For every leaf in `Fml.inTarget` outside a decidable `Fml.Residue`, `decideGoal` proves or refutes; `Fml.Residue` names each open gap with a reason; `DecisionTheorem` unchanged; split `Examples/Decision*.lean` into modules under 300 s each; tag `milestone-m7-next`. | automation.md M7-next steps 1–4 |
| AU02 | **Decision gaps.** Shrink `Fml.Residue`: fixed arrays and arrays below keys and fields, arrays of structs and arrays, broader memory blocks, the halting `||` operand; `Fml.Covered ⊆ Fml.inTarget` on program-free leaves (M4's list); the 511-node bound from fuel computed from the formula. | M7 plan steps 5, 6, 8 |
| AU03 | **Walk size.** A2: an unannotated literal-bounded loop is reported by a warning naming it, its unrolling kept as today (no new option), PolySize re-measured; joins of branches with several assignments without substituting terms; a conditional term in `dl!` and the `ifElseJoin` chain rows; the kernel closer on a joined mapping key (`boolKeyMappingSymbolicKey`); joined values with two bases or past `CloseSplit.splitMax`. | M8 "What is left" 1, 3–6, 8 |
| AU04 | **Sharing.** Leaves of doubling call families that stay 2ᵏ for non-offset callees: share call results through fresh locals in the leaf; the cost of a loop's leaves past `{anon}` (measure one leaf first). | M8 item 2, call summaries |
| AU05 | **Abstract hashes in the closer.** Hash values as free terms `hash(preimage)`, injective by construction; a simulation theorem: a concrete run whose hashed preimages do not collide behaves as the abstract run, so a verdict on the abstract leaf transfers under the approved per-run premise (G01 Q3, `Solidity.Hash.CollisionFree`). Applies to leaves that use hashes only by equality and as keys; numeric uses keep the current premise. Closes the e3″ class (`gapHashNegForall`). No new option: the validity statement is unchanged. | hash discussion 2026-10-31 |
| AU06 | **Automation for new features.** Closer coverage and gate rows for the rules G51 and Y09 add: byte memory, raw slots, keccak slot arithmetic as lazy symbolic writes with read-over-write laws; `scripts/check-automatic.mjs` over the new TestSuite and corpus obligations. | roadmap G51, inline-assembly Y09 |

### Lanes

| Lane | Checkpoints, in order | Starts after | Decisions |
|---|---|---|---|
| VA1 | AU01, AU02 | AQ1 | AQ1 |
| VA2 | AU03, AU04 | AQ1; independent of VA1's files except `Calculus/Rules.lean` (rebase) | AQ1, AQ2 |
| VA3 | AU05, AU06 | VA1; V16 and VY2 for AU06 (AU05 first, AU06 as backfill until then) | — |

### Decisions

| ID | Question | Recommendation |
|---|---|---|
| AQ1 | Start M7-next and the M8 leftovers? | Yes, VA1 and VA2 in parallel. |
| AQ2 | A2 without options: keep unrolling unannotated literal loops and only warn? | Yes; the opt-in switch waits for the options work. |

## Part 2 — A usable compiler

### What exists and what is missing

| Feature | Exists | Missing | Owner |
|---|---|---|---|
| Events | `LOG n` (`Backend/Opcode.lean`); logs in the source (S04.04); ABI encoder (G41); YQ6 approved | lowering `emit`, logs in G01's observation, bridge rows | **VY4** (Y07.02), not repeated here |
| Code size | `runtimeCodeLimit := some 24576` (`Roadmap/Evm.lean`), idealized by G01 Q2 | refusal of oversized artifacts | PC03 |
| Tooling | JSON CLI (`Frontend/Cli.lean`), artifacts (`Backend/Creation/`), solc-JSON import | standard JSON, ABI JSON, metadata, source maps, layout report, adapters | PC08, PC09 |
| Gas | one cost lemma (`Evm/MemoryCompile.lean`) | any optimizer; internal frames live in memory (G01 Q2) | PC01, PC02, PC04–PC07 |
| Releases | pins and re-pin procedures | a repeatable per-release procedure | PC10 |
| solc as oracle | G52 differential testing | — | roadmap G52 |

Etherscan verification and Foundry's compiler support are outside this
repository; PC09 only provides adapters and documentation.

### Groups

| Group | Deliverable | Depends on |
|---|---|---|
| PC01 | **Internal frame representation.** Measure the gas of memory frames against stack frames on the corpus; propose G37's representation (stack slots where the depth allows, memory otherwise); decision PQ1. Becomes the **first checkpoint of V12** if approved before V12 starts. | V11 |
| PC02 | **Gas baseline.** A harness running compiled corpus contracts through the Bridge EVM with gas (M5, EVMYulLean) and recording gas and code size against solc 0.8.38 legacy, legacy `--optimize` and via-IR `--optimize`; the numbers in this document; the target ratio of PQ4. | V14 (G45), V15 Bridge adapters |
| PC03 | **Code-size enforcement.** The compiler refuses runtime code over 24 576 bytes and initcode over 49 152 bytes (EIP-170, EIP-3860) with a precise reason; the coverage theorem gains a "fits" premise; G01 Q2's idealization is replaced (PQ2). | V16 (G49) |
| PC04 | **Verified basic optimizer.** Passes over `Backend` instructions, each with a correctness proof composing into G45.06: constant folding, PUSH/POP and DUP/SWAP elimination, jump threading, dead-code removal, better instruction selection. | PC02, G45 |
| PC05 | **Stack scheduling.** Locals and temporaries on the stack under PC01's representation, with a proved stack discipline and the stack-depth limit as a compile-time refusal or spill. | PC01, G37, G45.02 |
| PC06 | **Translation validation.** An untrusted block-local optimizer (common subexpressions, store-to-load forwarding, `SLOAD` reuse) with a checker proved sound by symbolic execution of basic blocks; refused output falls back to unoptimized code. | PC04, G46 |
| PC07 | **Global optimizations.** Inlining, redundant storage-access elimination across blocks, dead stores, loop-invariant code motion; through PC06's validator or direct proofs. Research risk: split into children when measured. | PC06 |
| PC08 | **Compiler interfaces.** standard-JSON input and output, ABI JSON proved to match the typed signatures, metadata with its CBOR trailer, source maps, a storage-layout report. | V14 (G44 artifacts) |
| PC09 | **Integration.** Foundry and Hardhat adapters calling the compiler as an external process; user documentation; the solc-oracle mode of G52 as a command. | PC08 |
| PC10 | **Release procedure.** A scripted re-pin per solc release and EVM fork: manifest delta, feature rows, grammar and builtin tables, bridge rows, re-run gates; applied once to the first release after 0.8.38. | V17 |

### Lanes

| Lane | Checkpoints, in order | Starts after | Decisions |
|---|---|---|---|
| — | PC01 inside V12 | V11 | PQ1 |
| VP1 | PC02, PC04, PC03 | V15; PC03 waits for V16 (backfill) | PQ2, PQ4 |
| VP2 | PC05, PC06 | V12 with PC01, VP1 | PQ3 |
| VP3 | PC07 | VP2; a continuation lane if measured larger | PQ3 |
| VP4 | PC08, PC09 | V14; independent of VP1–VP3 | — |
| VP5 | PC10 | V17 and a new solc release | — |

Gas is the long pole: VP1 narrows the gap to solc without its optimizer;
matching solc's optimizer needs VP2, VP3 and probably continuation lanes.

### Decisions

| ID | Question | Recommendation |
|---|---|---|
| PQ1 | Change G01 Q2 so internal frames may live on the stack? | Yes, decided before V12 starts; memory remains for deep or reference-holding frames. |
| PQ2 | Replace the code-size idealization by enforcement? | Yes, with the "fits" premise in coverage. |
| PQ3 | Optimizer trust: proved passes, translation validation, or both? | Both: proved passes for PC04/PC05, validation for PC06/PC07. |
| PQ4 | Which gas ratio against solc `--optimize` counts as done? | Set from PC02's baseline. |

## Totals

| Part | Lanes |
|---|---|
| Automation | VA1–VA3 (3) |
| Usable compiler | VP1–VP5 (5), plus PC01 inside V12 and continuation lanes for VP3 |

## Handoffs

- [VA2 AU03/AU04](after-roadmap-va2.md): bounded runtime recovered; conditional notation and measurement controls checked, AU03/AU04 implementation still incomplete.
