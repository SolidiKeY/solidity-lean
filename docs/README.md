# The documents

Open [module-map.md](module-map.md) first. Each fact lives in one document;
the others link to it. Finished work is recorded as what is in force; its
history is in git.

**Language coverage**

| Document | Holds |
|---|---|
| [dafny-parity.md](dafny-parity.md) | Pinned Dafny feature audit, Solidity relevance, support and remaining semantic gaps. |
| [feature-work/dafny-verification.md](feature-work/dafny-verification.md) | Typed loop measures, finite membership, entry audits, certified source witnesses and editor integration. |
| [feature-work/filtered-membership.md](feature-work/filtered-membership.md) | Finite literal filters, typed binders, snapshots, capture handling and semantic limits. |
| [coverage-plan.md](coverage-plan.md) | Full compiler/proof roadmap: 18 VM lanes of eight to ten hours covering 115 proof work packages, dependencies, explicit exclusions and source-to-bytecode completion gates. |
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
| [feature-work/inline-assembly.md](feature-work/inline-assembly.md) | Proposal (not started) to cover inline assembly: the exclusions it reopens, tiers, groups Y01–Y10, lanes VY1–VY5 and the decisions YQ1–YQ7 they wait for. |
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

- [Inline assembly VY2 preparation](feature-work/inline-assembly-vy2.md): physical codecs, finite storage/selected byte-heap writeback and retained-allocation resizing/supported byte/mixed aggregate heap views and selected word/dynamic uint256 retained-capacity/simultaneous heterogeneous struct and canonical bool/reference array writeback with retained-capacity resizing and canonical scalar-memory extension with exact legacy compatibility, real alias controls and joint ordinary-memory source/placement composition and arbitrary finite canonical owned-inventory writeback, registered residual journals, actual selected-step MemOK and outstanding concrete integration.

VY2 [heap enumeration preparation](feature-work/inline-assembly-vy2.md#computed-ordinary-heap-inventory-2026-11-01) derives canonical typed inventories from actual heap cells; full assembly closure remains open.

VY2 [packed-slot complements](feature-work/inline-assembly-vy2.md#packed-slot-complement-journaling-2026-11-01) covers canonical finite field/residual composition and actual source frame controls; whole-store and assembly closure remain open.

VY2 [computed word-layout registrations](feature-work/inline-assembly-vy2.md#computed-word-layout-registrations-2026-11-01)
derive canonical path/slot/hash agreements under actual owner per-run conditions;
packed/whole-store/source/compiler closure remains open.

VY2 [declaration-derived packing](feature-work/inline-assembly-vy2.md#declaration-derived-packed-registrations-2026-11-01)
computes canonical mixed-field registrations and source/journal controls;
whole-store and assembly closure remain open.

VY2 [nested source-registry preparation](feature-work/inline-assembly-vy2.md#nested-declared-source-registry-and-writeback-2026-11-01)
connects computed nested paths to actual source writeback and residual journals;
full-lane integration remains open.

VY2 [recursive fixed paths](feature-work/inline-assembly-vy2.md#recursive-fixed-declaration-paths-2026-11-01)
adds checked recursive metadata traversal and concrete canonical source/journal
composition; full assembly closure remains open.

VY2 [ordered ordinary roots](feature-work/inline-assembly-vy2.md#ordered-ordinary-root-declarations-2026-11-01)
adds checked cross-root packing/source-bank/readback components; full lane remains partial.

VY2 inherited-root canonical preparation: see [lane queue](feature-work/inline-assembly-vy2.md#inherited-active-contract-roots-2026-11-01).

VY2 computed active literal origins: [lane evidence](feature-work/inline-assembly-vy2.md#computed-active-layout-origin-2026-11-01).

VY2 [computed dynamic storage headers and live inventories](feature-work/inline-assembly-vy2.md#computed-dynamic-headers-and-live-element-inventories-2026-11-01)
records the canonical preparation/source-frame checkpoint and remaining full-lane obligations.


VY2 [ownership-changing complements](feature-work/inline-assembly-vy2.md#ownership-changing-dynamic-complements-2026-11-01)
connect computed dynamic snapshots to actual source/residual execution; full lane remains open.


VY2 [packed dynamic unsigned ownership](feature-work/inline-assembly-vy2.md#packed-dynamic-unsigned-ownership-2026-11-01)
adds computed partial-slot source/residual preparation; full original lane remains open.


VY2 [signed dynamic integer ownership](feature-work/inline-assembly-vy2.md#signed-dynamic-integer-ownership-2026-11-01)
adds canonical signed source/residual preparation; full original lane stays open.

VY2 scalar-family dynamic storage component: [lane record](feature-work/inline-assembly-vy2.md) (`ScalarDynamicHeader`, `ScalarOwnershipPlan`); canonical preparation only, original full lane unfinished.

VY2 combined primitive storage inventory: [lane record](feature-work/inline-assembly-vy2.md) (`PrimitiveDynamicSnapshot`, `PrimitiveOwnershipPlan`); canonical persistent preparation, not full Yul support.

VY2 nested primitive-member storage preparation and original unfinished queue:
[inline-assembly-vy2](feature-work/inline-assembly-vy2.md#vy2-nested-primitive-members-2026-11-01).

VY2 recursive dynamic struct preparation and unfinished original work:
[inline-assembly-vy2](feature-work/inline-assembly-vy2.md#vy2-recursive-dynamic-structs-2026-11-01).


VY2 aggregate dynamic-array preparation and retained-alias boundary:
[original lane queue](feature-work/inline-assembly-vy2.md#vy2-aggregate-dynamic-array-preparation-2026-11-01).
