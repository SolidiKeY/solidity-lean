# Dafny features relevant to Solidity

The audit pins [dafny-lang/dafny at `de36f2ec1f9c530080eff7929ae28229f45da069`](https://github.com/dafny-lang/dafny/tree/de36f2ec1f9c530080eff7929ae28229f45da069), inspected on 2026-10-26, and compares it with local baseline `23d23377`.
The [machine-readable inventory](dafny-features.json) records 36 feature families,
23 inspected upstream files and their Git blob IDs, source sections, local
implementation evidence, assessments and next actions. `localBaseline` identifies
the initial checkout; subsequent checked additions are reflected in the current
assessments and recorded in [the implementation notes](feature-work/dafny-verification.md). Reference-manual
chapters 3–15 are represented; the types file also contains chapter 6.

This is a selected-section review of language, verification and tooling families.
It does not enumerate every Dafny AST constructor, establish semantic equivalence,
or assert that every feature has been implemented. Local evidence identifies
implementation or its boundary; a path by itself is not a proof of parity.
The separate [Solidity inventory](solidity-feature-inventory.md) remains the
source of truth for admitted Solidity syntax and runtime gaps.

[Supplementary specification research](dafny-specification-research.json) records
14 further pinned implementation/test inspections and proposed finite-domain
comprehension and predicate interfaces. Those proposals are planned work, with
explicit capture, snapshot and definedness boundaries.

`present` means the stated facility exists within its documented fragment;
`partial` includes restricted shape, different semantics or an incomplete source
interface; `missing` means the source facility is absent; `notApplicable` marks
Dafny facilities that are not Solidity runtime requirements. `host` relevance
means Lean already supplies proof infrastructure: it does not claim that Dafny
syntax is accepted by the Solidity importer. A source feature and a Lean proof
facility must not be conflated.

## Inventory

| Family | Relevance | Status | Upstream | Local assessment and next action |
|---|---|---|---|---|
| `preconditions` | specification | present | [Specifications.md:34](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L34) | Requires clauses and imported NatSpec preconditions already generate checked obligations. **Next:** Preserve argument binding and definedness; add source-associated diagnostics. |
| `postconditions` | specification | present | [Specifications.md:65](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L65) | Ensures, result values and contract invariants are already supported for admitted source shapes. **Next:** Associate failed obligations with their source specifications. |
| `old-state` | specification | partial | [Expressions.md:677](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Expressions.md#L677) | Entry snapshots cover storage and ledger; there is no general labeled-state expression surface. **Next:** Add typed labeled snapshots and reusable two-state predicates if needed. |
| `quantifiers` | specification | partial | [Expressions.md:1266](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Expressions.md#L1266) | Both forall and exists are supported over primitive domains, including checked Presburger quantifier alternation and array-property fragments. General specification collection domains remain incomplete. The source compiler rejects snapshot/return binder capture and preserves primitive-binder shadowing of reference paths. **Next:** Extend typed specification domains and checked quantifier automation. |
| `function-frames` | specification | partial | [Specifications.md:633](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L633) | Assignable syntax already names roots, fields, indices and wildcard descendants; general modular frame application remains limited. Dafny write restrictions and local final-state framing differ. **Next:** Carry precise assigns information into effectful contract application. |
| `loop-invariants` | verification | present | [Specifications.md:706](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L706) | Supported invariant loop rules have soundness proofs; present does not cover every memory or callback body. **Next:** Extend explicitly unsupported loop-body shapes. |
| `loop-frames` | verification | partial | [Statements.md:1592](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L1592) | Computed loop anonymisation tracks storage roots. Aliases, memory and finer locations remain conservative. **Next:** Introduce typed finer location sets, alias-aware effects and memory frames. |
| `termination-metrics` | verification | partial | [Specifications.md:93](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L93) | Unsigned scalar variants and typed NatSpec tuple measures are supported. Ordinary diamond loops with an admitted frame, no break flag and no quantified invariant clauses generate lexicographic VCs that require all components to be defined and a strict decrease after every successful body turn. Box and callback proofs retain partial-correctness erasure. Ordinary diamonds still accept exhaustion; separate statement-indexed SourceCertificate values certify successful runs of the exact declared tuple. Signed/general source metrics and total recursive termination remain open. **Next:** Broaden admitted frames, invariant clauses and metric sorts; add checked first-iteration reasoning for do-while; connect automatic VCs to strict successful-termination certificates and establish callback and recursive total termination. |
| `modular-calls` | verification | partial | [Specifications.md:731](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L731) | UseContract already applies callee contracts. Automatic summaries cover restricted value computations and do not provide arbitrary precise effectful summaries. **Next:** Add effectful summaries with checked frames and explicit read dependencies. |
| `recursive-contracts` | verification | partial | [Specifications.md:93](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Specifications.md#L93) | Recursive contracts, including callbacks, are proved by induction over bounded unrolling with accepted exhaustion. This is not Dafny total-termination parity. **Next:** Add a separately stated total-correctness result with genuine decreases. |
| `ghost-variables` | host | partial | [Topics.md:193](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Topics.md#L193); [Programs.md:92](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Programs.md#L92) | Lean supplies ghost proof variables; a source-level ghost declaration, update and erasure discipline is absent. **Next:** If adding source ghost state, prove noninterference with runtime state. |
| `lemmas-predicates` | host | partial | [Types.md:4324](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L4324) | Lean definitions and theorems provide reusable lemmas; the source specification language has no general named predicate or lemma-call layer. **Next:** Expose checked reusable specification predicates without new trusted axioms. |
| `proof-blocks` | host | present | [Statements.md:2365](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L2365) | Lean tactic blocks and checked calculus chains provide proof authoring facilities; Dafny source syntax is not implemented. **Next:** Only add source-associated proof syntax for a concrete authoring need. |
| `opacity-reveal` | host | partial | [Statements.md:2047](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L2047) | Lean abstraction and explicit rewriting cover host proof control; there is no Dafny reveal statement in Solidity specs. **Next:** Use explicit checked rewrite lemmas; optional source proof surface remains separate. |
| `assert-assume` | runtime | partial | [Statements.md:1851](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L1851) | Solidity assert panics at runtime whereas Dafny assert is erased. Proof assumptions must not be presented as proved runtime behavior. **Next:** Keep ghost assertions distinct and report unchecked assumptions explicitly. |
| `spec-collections` | specification | partial | [Types.md:1259](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L1259) | Explicitly typed finite equality-membership is admitted in source specifications with every operand checked at one primitive sort, including empty keys. It follows existing KeY equality, including halting terms. First-class collections, cardinality, sequences, multisets and mathematical maps remain absent from the source interface. **Next:** Add reusable collection models and operations with explicit definedness and typed denotation; preserve the distinction from finite equality-membership. |
| `comprehensions` | specification | missing | [Expressions.md:1298](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Expressions.md#L1298) | General set, map and sequence comprehensions are not in the specification expression grammar. **Next:** Start with bounded typed comprehensions and checked denotation. |
| `numeric-types` | runtime | partial | [Types.md:219](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L219) | Solidity bounded signed/unsigned arithmetic and mathematical KeY int exist. Their semantics deliberately differ from Dafny unbounded numeric defaults. **Next:** Preserve widths, checked overflow and division failures when extending admitted arithmetic. |
| `floating-real-ordinal` | notApplicable | notApplicable | [Types.md:349](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L349) | Dafny floating-point, real and ordinal runtime types are not Solidity runtime types. Host mathematical models are separate. **Next:** No runtime implementation required for Solidity parity. |
| `refinement-types` | host | partial | [Types.md:1935](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L1935) | Dependent contexts and bounded values encode invariants; Solidity value types follow Solidity semantics rather than Dafny subset/newtype rules. **Next:** Use host refinements for proof invariants; source refinements need their own checked interface. |
| `algebraic-datatypes` | host | present | [Types.md:3355](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L3355) | Lean inductive families already model syntax and proof data. Solidity enum and struct behavior remains separate. **Next:** No new runtime syntax required; optional ghost model types can remain host Lean. |
| `arrays-aliasing-allocation` | runtime | partial | [Types.md:2712](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L2712) | Typed storage, memory and aliases are implemented with explicit remaining source and recursive-type gaps. Fresh/allocated specification expressions are not generally exposed. **Next:** Add typed allocation observations and complete reference-bearing source shapes. |
| `functions-lambdas-generics` | host | partial | [Types.md:3123](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L3123) | Lean provides higher-order models. Solidity function values are separately inventoried; Dafny generic/lambda runtime semantics do not transfer directly. **Next:** Separate higher-order ghost models from Solidity function-value execution. |
| `classes-traits-inheritance` | runtime | partial | [Types.md:2379](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L2379) | Contract inheritance, overrides and libraries already have a Solidity feature inventory; Dafny classes/traits are analogues, not equivalent semantics. **Next:** Follow solc declaration identity, initialization and dispatch requirements. |
| `modules-refinement` | host | partial | [Modules.md:1](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Modules.md#L1); [Refinement.md:1](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Refinement.md#L1) | Lean modules organize proofs; Solidity imports are separately modeled. Dafny abstract/export/refinement modules have no direct Solidity counterpart. **Next:** Express contract refinement as explicit correctness theorems when required. |
| `iterators-coinduction` | host | notApplicable | [Types.md:2910](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Types.md#L2910) | Solidity has no Dafny yield/iterator construct. Lean can represent coinductive or trace models without changing Solidity runtime syntax. **Next:** Add trace abstractions only for a concrete verification claim. |
| `control-flow` | runtime | partial | [Statements.md:984](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L984) | Assignments, calls, branches, loops and break/continue already exist; admitted shapes and remaining gaps are in the Solidity inventory. Tuple annotations survive loop-local scope, renaming, nested loops and break/continue/return lowering. Declaration-ID renaming preserves lexical shadowing, specification bindings, named call labels and counterexample source positions. Dafny match/binding guards are separate constructs. **Next:** Complete admitted Solidity shapes rather than introducing unrelated Dafny syntax. |
| `nondeterminism-havoc` | verification | partial | [Statements.md:200](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Statements.md#L200) | Typed havoc and external response/callback abstractions exist. Such-that assignments and arbitrary ghost nondeterminism lack a general source surface. **Next:** Retain explicit typed models and abstraction premises. |
| `automation-budgets` | tooling | partial | [Attributes.md:401](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Attributes.md#L401) | Bounded search, heartbeat limits, chunked proofs and runner timeouts exist; editor resource and cancellation behavior needs tests. **Next:** Expose stable per-obligation timing and reliable cancellation. |
| `triggers-induction` | host | partial | [Attributes.md:883](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Attributes.md#L883); [Topics.md:1150](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Topics.md#L1150) | Lean induction and checked replay provide host proof automation. Dafny SMT trigger syntax is not implemented or necessary for existing kernel proofs. **Next:** Prefer checked reusable lemmas and bounded replay to unchecked solver claims. |
| `counterexamples` | tooling | partial | [UserGuide.md:1048](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/UserGuide.md#L1048) | The opt-in source pipeline exposes a kernel-certified refutation of the exact original Fml.Valid obligation with the same typed model prestate. Primitive argument values, transaction, initial storage, ledger and balance are retained; exact declaration IDs and parameter indices add source names. The editor validates the transport and suppresses stale or unsolicited results. Positioned model-state sequences, general collection expansion, constructor reachability, replay, complete post-states and general callback or recursive witnesses remain open. **Next:** Extend certified source witnesses to additional semantic readings and positioned intermediate model states. |
| `audit-vacuity-dead-code` | tooling | partial | [UserGuide.md:418](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/UserGuide.md#L418) | Axiom checks remain. Entry-condition auditing now retains kernel-checked certificates of impossibility or possibility tied to the original scoped obligation; bounded failure is unknown. CLI and editor auditing are opt-in and impossible/unknown checks cannot pass strict suites. Constructor reachability and general dead-code analysis remain open. **Next:** Extend assurance to constructor reachability and unreachable branches; entry possibility alone does not establish a successful execution. |
| `unit-tests-generation` | tooling | partial | [UserGuide.md:601](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/UserGuide.md#L601) | Source verification runners and checked fixtures exist. General Dafny-style coverage-guided test generation is not implemented. **Next:** Export certified counterexamples as reproducible regression inputs. |
| `cli-project-artifacts` | tooling | partial | [UserGuide.md:850](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/UserGuide.md#L850) | Lake artifacts, source runners and JSON reports exist. A stable editor/CLI protocol is a separate integration contract. **Next:** Preserve report status, source identity and configuration semantics across clients. |
| `ide-language-services` | tooling | partial | [VSCodeIDE.md:3](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/VSCodeIDE.md#L3) | The Solidity Lean extension provides verify/discover/cancel, optional save verification, Test Explorer, diagnostics, hover, exact source IDs/ranges/hashes and stale-result suppression. Opt-in entry audits show vacuous proofs, and exact-goal refutations display certified model prestates. Completion/navigation and positioned execution traces remain open. **Next:** Add completion/navigation and further source-associated language services using explicit compiler evidence. |
| `plugins-backends` | notApplicable | notApplicable | [Plugins.md:1](https://github.com/dafny-lang/dafny/blob/de36f2ec1f9c530080eff7929ae28229f45da069/docs/DafnyRef/Plugins.md#L1) | Lean metaprogramming and optional Bridge provide extension points. Dafny compiler backends for other languages are not Solidity requirements. **Next:** Keep the core dependency-free; place optional adapters in separate packages. |

## Semantic boundaries that affect a port

Dafny `modifies` restricts **writes**, including a write of the existing value or
a write later undone. Its reference manual explicitly contrasts this with KeY's
final-state interpretation (`Specifications.md`, lines 686–704). Local
`assignable` obligations state final-state equality outside the allowed locations.
They cannot be called exact implementations of Dafny's write discipline.
Function specification syntax already names fields, indexed entries and wildcard
descendants; root-only precision is a computed **loop havoc** limitation.
Dafny itself does not provide an array-element frame-field form
(`Specifications.md`, line 447); quantified unchanged properties provide another
way to express preservation.

Dafny `assert` is a compiler-erased proof statement. Solidity `assert` has runtime
panic behavior. Solidity checked arithmetic, revert/rollback, aliases and external
callbacks retain their own semantics even where Dafny offers a similarly named
proof construct. An arbitrary assumption must never become a successful proof
without its premise appearing in the claim or trust report.

Dafny recursion termination is established with well-founded lexicographic
`decreases` metrics. Local recursive contracts are proved over bounded unrolling,
whose exhausted bottom frame is accepted by the modal policy. That correctness
result is useful but does not prove total termination. Loop variants and real
EVM gas or stack limits also remain distinct claims.

Lean already supplies inductive types, generic/higher-order definitions, lemmas,
modules and proof blocks. Adding another surface for these is an authoring
choice, separate from missing Solidity semantics. Dafny compiler backends,
iterators/yield and floating-point runtime types are not automatic implementation
requirements for a Solidity verifier.

## Remaining semantic work

The main reusable directions are precise effectful call summaries and read
frames; finer computed loop frames through aliases and memory; strict tuple termination certificates from automatic VCs and total recursive
termination; typed ghost collections, comprehensions and reusable source
predicates; labeled old-state and fresh/allocated observations; and evidence for
broader condition satisfiability and unreachable branches. Each needs a separately
stated invariant, denotation and soundness proof. Existing contracts, quantifiers,
recursive contracts, loop invariants and certified counterexamples should be
extended from their current implementations.

The source is authoritative where older prose differs. In particular,
`Solidity/Calculus/RecursionCallback.lean` and
`Solidity/Examples/Tactics/Recursion.lean` already provide recursive callback
contracts and `rec_auto_c`; the older open-items list in `function-specs.md`
does not reflect that implementation.

## Editor and test requirements

Dafny's inspected verification-diagnostics, cancellation and document-edit suites
show useful integration boundaries. Its reference manual lists diagnostics,
quick fixes, completion/navigation, counterexamples, ghost highlighting and
verification gutter status. Those are a tool inventory, not evidence that the
corresponding Solidity extension is complete.

The audited baseline contains Lean editor configuration and a tested LSP site
exporter, with no Solidity extension package. Any extension added after that
baseline needs its own implementation and test evidence. Useful checks include:

- UTF-8 solc byte offsets converted to UTF-16 editor positions, including non-ASCII text.
- Unsaved documents and suppression of results for an obsolete document version.
- Cancellation on edits, close, rerun and deactivation, including subprocess cleanup.
- Distinct proved, pending, skipped, unsupported and process-error results; an import gap must not appear verified.
- Multiple contracts, overloaded function signatures and source paths containing spaces.
- Retained batch progress and partial reports after interruption.
- Real extension-host activation, commands, diagnostics, save behavior and disposal, in addition to unit tests.

A mocked VS Code API or a simulated verifier tests controller behavior. It does
not establish that a real installed extension or the Lean prover succeeds. State
these validation levels separately.

## Validation and review

Run offline from the repository root:

```sh
node scripts/check-dafny-features.mjs
node --test scripts/check-dafny-features.test.mjs
```

The checker fixes the 36-family vocabulary and inspected upstream path set,
checks the upstream commit pin, inspection date, source blob identifier format,
reference chapter and inspected-source citation coverage, nonempty assessments
and local evidence files. Negative tests reject
dropped/duplicated families, unreviewed references, unsafe or stale local paths,
unsupported statuses and malformed entries. It does not download or rehash
upstream blobs, verify remote line bounds, or establish semantic completeness.
Repinning upstream requires a new source review.

The inventory and six tests pass offline at this milestone. The inventory-only
audit introduces no Lean source change, core dependency, proof axiom or semantic
parity theorem. The repository-wide documentation-path checker reports 13 existing
missing references in vendored metadata and an external Mathlib reference;
none names the new audit files. The focused evidence checker and diff whitespace
check pass.

Read-only finder and skeptic reviews checked the inventory, evidence, validator
and tests without invoking Lean. Neither found a blocking parity or validation
issue. The skeptic suggested validating the inspection date; this is now checked,
including an impossible-date regression. All 18 sources inspected at that stage were explicitly
cited by a feature. The scope remains a family audit, not full Dafny implementation.

## Source verification extension

The first extension milestone added [a VS Code extension](../vscode/README.md)
for this repository. It provides verify/discover/cancel commands, optional
verification on save, per-signature Test Explorer runs, diagnostics and proof
status hover. It preserves the backend's proved/pending/import-gap/process-error
distinctions. That milestone did not add Solidity completion, source ghost syntax
or counterexample presentation; subsequent additions are recorded below.

The importer retains solc declaration IDs through `SolcFun`, `ImportRow` and
the testing JSON. The file runner associates exact function ranges by those IDs,
converts UTF-8 bytes to UTF-16 positions, and checks the compiler header's source
hash. This handles overloaded/renamed declarations without name guessing.
Synthesized constructors point to their contract. The editor rejects obsolete
document versions and mismatched hashes; BOMs and CR/CRLF/LF positions are
covered. Backend execution is asynchronous and bounded, and cancellation also
terminates detached descendant tool processes.

Validation on 2026-10-26:

- 35 offline inventory, source-location, controller and subprocess tests pass.
- Real solc/Lean integration checks pass for overload/source metadata, the
  Runner fixture and selection/listing; inline assembly retains its current
  source-policy verdict `excluded` (an older test expected `unsupported`).
- The 236-job `Solidity.Frontend.Testing` build passes.
- Full `./run-lean.sh` passes: 622 default-target jobs, the 247-job
  TestSuite target, and all 131 read-bearing annotations from 377 solkey taclets.
  A concurrent TestSuite attempt hit this environment's 16 GiB memory limit;
  retrying with `LEAN_NUM_THREADS=1 lake build SolkeyTestSuite` succeeded before
  the final wrapper run completed.
- A real VSCodium 1.143.17183 extension host passes ten checks: activation,
  command dispatch, a backend process, Test Explorer items, hover, diagnostics,
  edit invalidation, actual solc/Lean proof, an actual pending obligation and
  compiler declaration ranges. This uses Code's extension API; the CI job
  separately configures Microsoft's VS Code through `@vscode/test-electron`.
- Packaging produces an installable VSIX; installation in an isolated editor
  profile succeeds. Core layering, module reachability and both feature
  inventories pass their offline checks.

The finder and skeptic independently reproduced a file-run loop caused by
publishing results into the collection being iterated. File runs now snapshot
their children and a regression requires each function to run once. Their
position findings led to the BOM/CR fixes. A final launcher review found stale
caller-supplied success files could produce a false pass; every launch now uses
a fresh temporary report and only copies checked evidence to the requested
output. Tests cover both stale rejection and fresh success. Workspace discovery
also drops its silent 200-file cap, and cancellation stops its queued files;
regressions cover that queue boundary, opening a document, and saving a dirty
file before a backend starts.

The final source review also confirmed existing Presburger quantifier alternation in
`Solidity/Calculus/QuantArithmetic.lean` and its decision examples; the quantifier
family now records that supported fragment explicitly.

The remaining semantic work above is still open. No semantic parity or new
verification soundness claim follows from adding this editor interface.

## Verification and model-prestate additions

The [implementation notes](feature-work/dafny-verification.md) describe the
dependency-free well-founded and lexicographic loop theorems, typed finite
primitive membership, certified entry-condition audits, and opt-in exact-goal
source refutations with editor model-prestate display. The audit now records
23 upstream blobs, including the pinned counterexample request, handler, response
and regression tests. These additions retain the partial assessments and
remaining work in the current inventory; they do not establish full Dafny parity.
