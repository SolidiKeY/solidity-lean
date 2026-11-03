# The documents

Open [module-map.md](module-map.md) first. Each fact lives in one document;
the others link to it. Finished work is recorded as what is in force; its
history is in git.

**Language coverage**

| Document | Holds |
|---|---|
| [dafny-parity.md](dafny-parity.md) | Pinned Dafny feature audit, Solidity relevance, support and remaining semantic gaps. |
| [feature-work/compiler-project-services.md](feature-work/compiler-project-services.md) | Multi-file compiler/LSP support, scoped specifications, formatting, refactoring and concurrent function proofs. |
| [feature-work/solidity-lsp.md](feature-work/solidity-lsp.md) | Persistent Solidity LSP, warm Lean workers, editor services, validation and remaining limits. |
| [extension-proof-performance.md](extension-proof-performance.md) | Desktop closed-derivation proposals, checked fallback, worker timings and limits. |
| [generated-c-performance.md](generated-c-performance.md) | Generated C call paths, native walk/certificate timings and optimization limits. |
| [simp-performance.md](simp-performance.md) | Simplifier profiles, guarded joined preparation, measured gains and completeness limits. |
| [browser-simple-benchmarks.md](browser-simple-benchmarks.md) | Matched small-program SolKey/native/browser timings, audit optimization and remaining cold/simplifier costs. |
| [web-ide.md](web-ide.md) | Offline static browser workbench, WASM runtime, storage contract and real-editor comparison. |
| [dafny-editor-parity.md](dafny-editor-parity.md) | Real Dafny/Solidity Lean editor comparison harness, feature discovery, measurements and completeness limits. |
| [feature-work/dafny-verification.md](feature-work/dafny-verification.md) | Typed loop measures, finite membership, entry audits, certified source witnesses and editor integration. |
| [feature-work/filtered-membership.md](feature-work/filtered-membership.md) | Finite literal filters, typed binders, snapshots, capture handling and semantic limits. |
| [coverage-plan.md](coverage-plan.md) | Full compiler/proof roadmap: 18 VM lanes of eight to ten hours covering 118 proof work packages, dependencies, explicit exclusions and source-to-bytecode completion gates. |
| [feature-work/roadmap-g01-interfaces.md](feature-work/roadmap-g01-interfaces.md) | Roadmap G01: intrinsic layer interfaces, observations, the six final theorem contracts, pass certificates, reuse map and the decisions they implement. |
| [feature-work/frontend-parse.md](feature-work/frontend-parse.md) | Lane V05 (G08–G11): the checked lexer and parser to S00's syntax: lexical certificate, token yield and layouts, precedence, whole-source parsing, coverage, corpus regression and G05 parse-stage instance. |
| [feature-work/roadmap-g05-frontend.md](feature-work/roadmap-g05-frontend.md) | Roadmap G05: audit of frontend, provenance and unsafe elaborator paths; checked certificate interfaces for raw input, parse, resolution and metadata; link settings and admitted settings. |
| [solidity-scope.md](solidity-scope.md) | The pinned language audit: scope policy (model, abstract, exclude) and the exclusions. |
| [feature-work/roadmap-g00-scope.md](feature-work/roadmap-g00-scope.md) | Roadmap G00: pins and their disagreements, evidence for each recorded exclusion, manifest/ledger reconciliation, owners and open scope questions. |
| [feature-work/roadmap-g03-ledger.md](feature-work/roadmap-g03-ledger.md) | Roadmap G03: constructor/feature → admission → lowering → backend → EVM → theorem ledger with combinations and decision rows, and the module/lemma dependency ledger (`scripts/roadmap-g03-ledger.py`, generated JSON). |
| [solidity-feature-inventory.md](solidity-feature-inventory.md) | Generated from `solidity-features.json`: each feature's requirement, scope, status and evidence. Do not edit. |
| [semantic-gaps.md](semantic-gaps.md) | What of Solidity's semantics is still open, and the chain facts an obligation assumes: the work list. |
| [solc-alignment.md](solc-alignment.md) | Where the interpreter follows solc rather than KeY, and why; the remaining deltas. |
| [solidity-upstream-tests.md](solidity-upstream-tests.md) | The pinned solc test snapshot, its runner and the working/broken/blocked lists. |
| [solc-validation.md](solc-validation.md) | What is checked against solc, and the checks still to build. |
| [feature-work/integration.md](feature-work/integration.md) | Index of the per-feature documents in `feature-work/` (source admission, declarations, operators, aggregates, recursive types, ABI and hashes, transient storage, contract world, calls and exceptions, finite dispatch) and their shared decisions. |
| [feature-work/cloud-integration-20261028.md](feature-work/cloud-integration-20261028.md) | Eight finished feature-cloud workstreams, merge decisions, historical replay controls and combined validation. |
| [feature-work/cloud-integration-01-09.md](feature-work/cloud-integration-01-09.md) | Combined cloud tasks 01–09: snapshot scope, conflict resolutions, regression checks and remaining blockers. |
| [feature-work/roadmap-g02-measure.md](feature-work/roadmap-g02-measure.md) | Roadmap G02: measured cold/warm/cache-restore build baseline, slowest and largest modules, OOM, cache recipe, stale artifacts and the ten-hour VM assessment. |
| [feature-work/roadmap-g06-evm.md](feature-work/roadmap-g06-evm.md) | Roadmap G06: every EVM-like machine and its disagreements with pinned Osaka, the pinned semantics and observation interfaces, the core/Bridge certificate boundary and the bridge lemmas with owners. |
| [feature-work/roadmap-g07-gates.md](feature-work/roadmap-g07-gates.md) | Roadmap G07: inhabited and negative controls of the G01 contracts, the non-circularity, axiom-pin and baselined regression gates, and the failures recorded at the base. |
| [feature-work/source-s00-s01.md](feature-work/source-s00-s01.md) | Source definitions S00/S01: the pinned grammar as intrinsic syntax, constructor index, upstream mapping, precise rejection and declaration graph; static typing, resolution and constants. |
| [feature-work/frontend-static.md](feature-work/frontend-static.md) | Static frontend checkers G12–G14: import resolution and identities, type checking against S01, inheritance; their G05 checker instances. |
| [feature-work/source-s04-state.md](feature-work/source-s04-state.md) | Source definitions S04.01–S04.03: source state (values, aggregates, memory, calldata, storage), ABI and revert observations, world, transient storage, call frames and rollback. |
| [feature-work/source-s02.md](feature-work/source-s02.md) | Source semantics S02: resolved bodies in elaborated units, closed typing gaps, run-time values, arithmetic, effect order per pipeline, references and failures. |
| [feature-work/source-s03.md](feature-work/source-s03.md) | Source semantics S03: statements, modifiers with repeated placeholders, constructor order, internal/external/callback call frames, horizons and divergence. |
| [feature-work/source-s05.md](feature-work/source-s05.md) | Source semantics S05: the composition into G01's `Lang`, the source-constructor ledger, controls, reviews and the lane's handoff. |
| [feature-work/source-soundness.md](feature-work/source-soundness.md) | Lane V04b: integration of the source semantics with G13's checker, type soundness (preservation, gap-relative progress), reviews and handoff. |
| [feature-work/roadmap-g04-restrictions.md](feature-work/roadmap-g04-restrictions.md) | Roadmap G04: current compiler theorems, every fragment/input restriction and its discharging group. |
| [feature-work/roadmap-g06-osaka.md](feature-work/roadmap-g06-osaka.md) | Roadmap G06 child: hand-written EVM vector scripts re-pinned from Cancun to Osaka; both-fork measurements, bytecode comparison, lane re-runs and Lean-side pin obligations. |
| [feature-work/fixed-point-semantics.md](feature-work/fixed-point-semantics.md) | Fixed-point types: the pinned specification, the reference model `Language/FixedPoint.lean`, silent-spec proposals, scope questions and roadmap owners. |
| [feature-work/hash-collision-bound.md](feature-work/hash-collision-bound.md) | The approved per-run hash premise `CollisionFree` and the kernel-checked random-oracle birthday bound (q²/2²⁵⁷ for keccak), adaptive-query scope and how G27.05/G46.05 use them. |
| [feature-work/cloud-integration-10.md](feature-work/cloud-integration-10.md) | Cloud task 10 integration: committed ABI/error repairs, merge decisions and combined validation. |
| [feature-work/roadmap-decisions-impact.md](feature-work/roadmap-decisions-impact.md) | Roadmap: what each 2026-10-29 user decision affects, whether existing proofs survive, and the owning group. |
| [feature-work/storage-hashed-layout.md](feature-work/storage-hashed-layout.md) | The hashed storage layout model (slot terms, words through a hash parameter, bounded offsets), its separation under the region premise, the EVM `Slot` correspondence and the keccak instantiation with solc slot vectors (G27.05/G46.05 preparation). |
| [feature-work/backend-assembler.md](feature-work/backend-assembler.md) | Roadmap G45.05/G45.04 lane: the Osaka instruction datatype, byte encoder/decoder and jump-destination analysis, then the assembler; a handoff per checkpoint. |
| [feature-work/precompiles.md](feature-work/precompiles.md) | Osaka's 18 precompiles as computed core functions with gas and failure laws, G06's `Fixed` instance, the vector provenance and the Bridge agreement. |
| [feature-work/stipend-cost-rule.md](feature-work/stipend-cost-rule.md) | The compiler-independent stipend cost rule (G06 Q3): which `receive`/fallback bodies fit 2300 gas under cold access costs, its examples and the compiler obligation (G43). |
| [feature-work/inline-assembly.md](feature-work/inline-assembly.md) | Authorized inline assembly extension: the exclusions it reopens, tiers, groups Y01–Y10, lanes VY1–VY5 and approved decisions YQ1–YQ7; implementation gates remain open. |
| [feature-work/compiler-transport-proofs.md](feature-work/compiler-transport-proofs.md) | Compiler transport proofs, reached failure controls, full small-frame output and remaining Source/EVM obligations. |
| [feature-work/memory-operation-proofs.md](feature-work/memory-operation-proofs.md) | Typed Source/heap/word memory-operation lemmas, reached decrement failures and the remaining physical/backend boundary. |
| [feature-work/primitive-return-projection.md](feature-work/primitive-return-projection.md) | Primitive return-byte validation before binding/discard, checked controls and the remaining O1 operational boundary. |
| [calldata-slice-copies.md](calldata-slice-copies.md) | Calldata slices: fresh copies, aliases and their origins. |
| [source-inputs.md](source-inputs.md) | EVM input premises of imported obligations and canonical self addresses. |

**The calculus and its proofs**

| Document | Holds |
|---|---|
| [calculus.md](calculus.md) | Formula syntax, tactics, walks, chains, proof trees and symbolic updates. |
| [lean-key-rule-map.md](lean-key-rule-map.md) | The authority for the map from solkey's taclets, update and theory symbols to Lean names. |
| [options.md](options.md) | Calculus options: callbacks, overflow, clean tails, evaluation order. |
| [loops.md](loops.md) | Loops: decisions, the invariant rules, status. |
| [correctness.md](correctness.md) | Direct `Spec` correctness, the bridges from proofs, and the model choices behind the statements. |
| [key-equality.md](key-equality.md) | KeY's `=`: no definedness test, `wt(s)` a predicate, how the closers read an equation. |
| [function-specs.md](function-specs.md) | Per-function `requires`/`ensures`/`\old`/`\forall`, invariants, `sol_spec`. |
| [lifetime.md](lifetime.md) | Transaction traces from the constructor, whole-contract safety, invariant induction. |
| [automation.md](automation.md) | The deciding closer: M0–M8, the decision theorem's features and gaps, M7-next. |
| [complete-verification.md](complete-verification.md) | The exact-reduction pipeline, its stages, tools and limits. |
| [assurance.md](assurance.md) | Trust gates, the memory compiler's invariants, remaining assurance work. |
| [rule-repair.md](rule-repair.md) | How to repair a broken rule: semantics first, rejection gates, soundness. |
| [intrinsic.md](intrinsic.md) | The intrinsic design: decisions in force, gate G0, what stays extrinsic, open items. |
| [kernel-port.md](kernel-port.md) | Where each mini-solkey chapter landed, and what is still open. |

**solkey**

| Document | Holds |
|---|---|
| [solkey-migration.md](solkey-migration.md) | The pinned solkey, migration tooling, how to re-pin, remaining parity gaps. |
| [testsuite-proofs.md](testsuite-proofs.md) | Proving solkey's TestSuite by `⊢`: decisions, pipeline, measured costs. |
| [corpus-parity.md](corpus-parity.md) | The solkey corpus verdicts per contract. Generated by `scripts/solkey-port.mjs`; do not edit. |
| [solkey-feedback.md](solkey-feedback.md) | Open improvement requests to solkey. |

**Tools and build**

| Document | Holds |
|---|---|
| [contributing.md](contributing.md) | Verification commands, Lean setup, tactic development, worktrees and memory limits. |
| [cli.md](cli.md) | The native `solidity-lean` CLI. |
| [solidity-testing.md](solidity-testing.md) | Testing `.sol` files: CLI, JavaScript and Lean APIs. |
| [feature-work/generated-differential.md](feature-work/generated-differential.md) | Bounded typed generated cases against real solc/EVM, provenance, shrinking and remaining D/E work. |
| [compiler-verification.md](compiler-verification.md) | The EVM compiler: the theorem, the machine, the fragment. |
| [bridge.md](bridge.md) | The optional Bridge package: Mathlib/CSLib, EVMYulLean, Loom and Velvet adapters. |
| [refactoring-progress.md](refactoring-progress.md) | Completed getter/provenance refactors, bounded validation and the remaining dispatch-signature candidate. |
| [parallelism.md](parallelism.md) | The core apart from the elaborator, the layering check, the split convention. |
| [latex.md](latex.md) | LaTeX notation and the checked trace export. |
| [site.md](site.md) | The examples site on GitHub Pages. |

| Document | Holds |
|---|---|
| [feature-work/backend-creation-artifacts.md](feature-work/backend-creation-artifacts.md) | G44.02 creation artifact component proofs, runtime installation scope and remaining composition obligations. |
| [feature-work/backend-failure-emission.md](feature-work/backend-failure-emission.md) | G38 component: executable failure and return bytes, exact local slice proofs and remaining integration obligations. |
| [feature-work/storage-value-representation.md](feature-work/storage-value-representation.md) | G27 typed storage representation, bounded validation, reviews and remaining composition obligations. |
| [feature-work/backend-scalar-lowering.md](feature-work/backend-scalar-lowering.md) | G25 preparation: numeric instruction-slice semantics, typed selection certificates, queue status and remaining composition/validation obligations. |

| Preparation lane | Document |
|---|---|
| G31 environment/metadata opcode lowering | [backend-environment-lowering.md](feature-work/backend-environment-lowering.md) |

V08's partial world-lowering checkpoint is recorded in
[roadmap-v08-world-lowering](feature-work/roadmap-v08-world-lowering.md):
intrinsic world/callable adapters and one-step Source-boundary components
(custom errors, ABI, emit, Keccak, transient journals, payments). No theorem
yet links Source executions to the intrinsic world or to bytecode.

V15 P10 partial checkpoint: [fetched-byte EVM steps against EvmYul](feature-work/roadmap-v15-p10.md),
including the frozen CALL/RETURNDATA/JUMP interface consumed by later lanes.

P1 runtime-frame partial checkpoint: [foundation, frozen interfaces v1–v3 and producers](feature-work/runtime-frame-p1.md); [P1-CALL value-call producer](feature-work/p1-call-producer.md) and [G37.03/P4 typed dispatch](feature-work/roadmap-g37-dispatch-p4.md).
G33 finite struct defaults: [pair and nested struct default construction](feature-work/roadmap-g33-struct-defaults.md).
G22/G42 read-only calls: [typed source calls, callbacks and the static-world frame](feature-work/g22-readonly-calls.md); [world-call consumers](feature-work/g42-world-call-consumers.md).
G21 closed failure lowering: [literal, boolean custom-error and slice failures](feature-work/g21-failure-lowering.md).
V07 source lowering (G16–G18.01): [scalar/effectful lowering, P12 context map, declaration-location graphs](feature-work/roadmap-v07-lowering.md).
P6 physical memory: [word frames, byte journal, uint arrays, reference stores](feature-work/physical-memory-interface.md).
G18.02/.03 aggregates: [storage path typing, graph fields, memory writes and aliases](feature-work/g18-aggregates.md).
G36.01 structured flow: [target branch and exit selectors](feature-work/roadmap-g36-structured-flow.md).
V09 compiler passes: [G24–G31 pass components](feature-work/roadmap-v09-compiler-passes.md).
V10 storage operations: [copy, clear, push and pop over storage graphs and targets](feature-work/roadmap-v10-storage-operations.md).
Inline assembly VY1: [Yul syntax, checking and word semantics](feature-work/inline-assembly-vy1.md).
Inline assembly VY2: [physical memory views, adapters and recursive loops](feature-work/yul-physical-memory.md).
Label execution: [byte-PC control edges](feature-work/backend-label-exec.md). Diamond try H8: [bounded source model](feature-work/diamond-try-h8-source-model.md).

P8 partial checkpoints: [admission and failure resources](feature-work/p8-admission.md), including the [P8a frozen interface](feature-work/p8-admission.md#frozen-interface) and [settings and assembly boundary](feature-work/p8-admission.md#all-settings-and-producer-assembly), and the [P8b frozen consumer interface](feature-work/p8b-frozen-interface.md).

P9 and Source soundness checkpoints: [checked call graphs](feature-work/p9-checked-callgraphs.md), [allocation and frame preservation](feature-work/source-preservation-allocations.md) and [checked call-program progress](feature-work/source-progress-checked.md).

Feature-work records write the cloud VM's workspace root as `${VM_WORKSPACE}` and its setup directory as `${VM_SETUP}`.

- [G18 storage cells](feature-work/g18-storage-cells.md): operation-level Source/IR cell consumers and inhabited controls; full aggregate lowering remains open.
- [Integer-valued mapping copy](feature-work/g18-scalar-mapping-copy.md): all-key storage relations and a captured-slot copy consumer; physical/runtime closure remains open.
- [Dynamic storage array access](feature-work/g18-array-access.md): actual length/bounds and selected-cell transports, with invalid-representation controls.
Source callback history producer components: [G22 Source histories](feature-work/g22-source-history-producer.md).
Compiler-pass integration checks and retained local applications are described in [the compiler-pass record](feature-work/roadmap-v09-compiler-passes.md#integration-checks).
V10 Source operation clients and remaining integration: [storage operations](feature-work/roadmap-v10-storage-operations.md#source-operation-clients-c145).
Registered V10 Source operation clients: [storage operation views and Source clients](feature-work/roadmap-v10-storage-operations.md#operation-views-and-source-clients).
