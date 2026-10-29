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
| [coverage-plan.md](coverage-plan.md) | Full compiler/proof roadmap: 32 VM lanes of four to ten hours covering 115 proof work packages, dependencies, explicit exclusions and source-to-bytecode completion gates. |
| [feature-work/roadmap-g01-interfaces.md](feature-work/roadmap-g01-interfaces.md) | Roadmap G01: intrinsic layer interfaces, observations, the six final theorem contracts, pass certificates, reuse map and open scope questions. |
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
| [feature-work/roadmap-g06-evm.md](feature-work/roadmap-g06-evm.md) | Roadmap G06: every EVM-like machine and its disagreements with pinned Osaka, the pinned semantics and observation interfaces, the core/Bridge certificate boundary and the bridge lemmas with owners. |
| [feature-work/roadmap-g02-measure.md](feature-work/roadmap-g02-measure.md) | Roadmap G02: measured cold/warm/cache-restore build baseline, slowest and largest modules, OOM, cache recipe, stale artifacts and the ten-hour VM assessment. |
| [feature-work/roadmap-g04-restrictions.md](feature-work/roadmap-g04-restrictions.md) | Roadmap G04: current compiler theorems, every fragment/input restriction and its discharging group. |
| [feature-work/roadmap-g06-osaka.md](feature-work/roadmap-g06-osaka.md) | Roadmap G06 child: hand-written EVM vector scripts re-pinned from Cancun to Osaka; both-fork measurements, bytecode comparison, lane re-runs and Lean-side pin obligations. |
| [feature-work/fixed-point-semantics.md](feature-work/fixed-point-semantics.md) | Fixed-point types: the pinned specification, the reference model `Language/FixedPoint.lean`, silent-spec proposals, scope questions and roadmap owners. |
| [feature-work/hash-collision-bound.md](feature-work/hash-collision-bound.md) | The approved per-run hash premise `CollisionFree` and the kernel-checked random-oracle birthday bound (q²/2²⁵⁷ for keccak), adaptive-query scope and how G27.05/G46.05 use them. |
| [feature-work/cloud-integration-10.md](feature-work/cloud-integration-10.md) | Cloud task 10 integration: committed ABI/error repairs, merge decisions and combined validation. |
| [feature-work/roadmap-decisions-impact.md](feature-work/roadmap-decisions-impact.md) | Roadmap: what each 2026-10-29 user decision affects, whether existing proofs survive, and the owning group. |
- [Cloud task 10 integration](feature-work/cloud-integration-10.md) — committed ABI/error repairs, merge decisions and combined validation.
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
