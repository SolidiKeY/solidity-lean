# Architectural refactoring progress

## Second-pass investigation

The 2026-10-27 second pass starts from `98d2682c`. The earlier getter and
provenance increments remove independent pieces of state, but leave the
elaborator's binding metadata split across synthetic locals. The following
assessment follows actual source-to-run and formula-to-proof paths, rather
than treating the earlier two increments as an architecture-wide audit.
The table describes the baseline at `98d2682c`; completed changes follow below.

| Subsystem and traced path | Structural versus dynamic invariants; alternative considered |
|---|---|
| Source: `Source.read`, `SolcJson.readContract`, `Import`, `elabStmtsP` | Compiler modes and getter result pairing are now structural. JSON identities, unsupported source types and compiler settings remain boundary checks. Replacing all JSON access with a typed AST is substantial, but duplicating solc's complete schema would add a second AST without eliminating source-admission policy. |
| Elaboration: `FunDecl.paramCtx`, captures, call frames, `widthPath?`, `narrowPure`, `ECtx.toNCtx` | Core positions are typed, but a local's width/ABI shape is a separate `#x` pseudo-binding. Function/bytes/nominal readers compare two list positions; reference shapes can consult outer metadata separately. A binding with attached metadata removes this synchronization entirely. Selected below. |
| Syntax and execution: `Idx`, `Stmt`, `Prog`, `State`, `TRun`, `Out` | Contexts, primitive types, storage paths and heap growth are intrinsic. Raw parsing still requires checking at elaboration. Replacing the scoped syntax again would not remove those boundary checks. A common effect interpreter for deterministic and callback runs could reduce clauses, but callbacks deliberately change the relation and invariant obligations. It needs a separate semantic equivalence design, not textual consolidation. |
| Storage and heap: `SVal`, `SFields`, `Path`, `Heap`, `Grown`, observations | Values and paths carry their types; heaps carry identities and extension witnesses. Recursive declarations have a separate certified `TypeGraph` foundation. Migrating ordinary contracts to that graph would remove the legacy/graph boundary and enable guarded recursion, but must also migrate Theory observations, signatures, deletion and copy proofs; compatibility cannot be assumed from the separate foundation. |
| Calculus: `Tm`, `Upd`, `Premise`, `Stmt.step`, `Proves`, soundness | Sort/context invariants and update landing contexts are structural. One rule dispatches each statement; soundness connects its premise to the run. A generic effect algebra cannot replace taclet-specific premises without losing the required KeY presentation. Existing recursor definitions and compiled twins deliberately separate cheap kernel reduction from executable pattern matching. |
| Automation and tools: `ProofTree.ruleAt?`, `Tree`, derivation replay, closers | Tactics elaborate kernel-checked proof terms. Tree action and children are independent data; an algebraic leaf/rule tree could enforce their relationship. It would simplify tool invariants, but not prove tactic completeness or remove the metaprogram boundary. Search budgets, replay and local caches are intentional. |
| EVM: `Compiler.compile`, `Compilation`, `Memory.CompiledProg`, `correct` | The common entry already returns a branch-indexed certificate and correlated input/output relations. A separate intrinsic fragment AST would duplicate the scoped program; the memory path already carries erased structural certificates. Rewriting core fragment recognition could simplify proofs, but must preserve its fast recognizer and requires measurement across the simulation stack. |
| World, lifetime and callbacks: catalog-indexed accounts, atomic frames, `ExecP` | Storage identity, frame rollback and heap growth are structural. Installed-code and funding checks depend on the current world and cannot be erased by a stable handle. Folding these models into the single-contract run would alter the external oracle boundary rather than merely simplify it. |

### Ranked transformations

| Rank | Transformation | Significance, scope and removable complexity | Guarantees and migration cost/risk | Expected simplification |
|---|---|---|---|---|
| 1 | Attach local metadata to its binding | Whole elaborator plus importer and formula readers; remove pseudo-locals, shadow-order scans and metadata filtering | Metadata cannot exist without its local or be inherited from a shadowed binding. Medium migration; broad rebuild and source-shape regression risk | High, without changing execution or calculus representations |
| 2 | One recursive declaration graph for ordinary storage | Fundamental type/semantics/Theory/signature migration; remove the parallel graph foundation's compatibility boundary | Guarded recursive declarations intrinsic across consumers. Very high cost and proof/checking risk; feature admission must remain closed during migration | Potentially very high, but requires a dedicated cross-layer correspondence milestone |
| 3 | Intrinsic core compiler fragments | Compiler, fragment recognizer, simulation proofs; remove recognizer/code synchronization | Code derived from a fragment certificate. High proof migration and reduction-performance risk; memory compiler already uses this design | Medium; avoid a duplicate program AST |
| 4 | Algebraic proof-tree nodes | Tree data, growing strategy, script/JSON/UI consumers; remove invalid action/children combinations | Open/closed leaves cannot have children. Medium migration, tool-output pin risk | Medium, confined to proof presentation |
| 5 | Dedicated finite-dispatch signatures | Candidate/getter/call/alias analysis; remove scalar candidates and repeated function reshaping | Callable signatures guaranteed structurally. Low-medium cost, conservative unknown/reference admission risk | Modest; deeper than naming cleanup but smaller than the selected binding migration |

Ordinary file splitting, naming and shared helper extraction are not ranked as
architectural transformations. The selected design changes the source of truth:
each program-local constructor stores its own shape. `ECtx.toNCtx` then projects
one real binding per entry. Metadata readers use the nearest local once. Existing
source width tables and ABI markers retain their meanings; this is not a claim
that the shape language itself becomes intrinsic.

Migration: replace the `LocalTy.shape` constructor and `shapeEntry`, migrate every producer and
consumer together, then verify shadowing, capture/call/return shape propagation,
source import and existing proofs. Keep the old representation out of the final
tree. Commit the coherent representation change after focused checks, then
record broader verification separately. No additional dependency or heartbeat
increase is planned.

Checking-cost warning: touching `Syntax/Elab/Context.lean` invalidates its broad
consumer graph. History `e8c288e1` and `2a1db139` introduced shape entries for
language support, not checking speed. Preserve `1a7d5b0e`'s callee memoization
and compiled/kernel representation boundaries. Heavy checks run sequentially
under `MemoryMax=12G`, `MemorySwapMax=0`, with a 12 GiB host reserve.

### Binding migration implementation and review

Committed as `4600458d` (`Bind local metadata`).

`LocalTy.val`, `alias` and `mem` now carry their own width/ABI shape. All
parameter, return-frame, importer and capture producers use that representation;
there is no metadata pseudo-local or compatibility adapter. The three positional
metadata scans disappeared. `toLTy` is the single projection used by `toNCtx`
and formula binder discovery; parameter readers no longer flatten extra entries,
and reference captures declare their complete metadata in one operation.

The read-only finder and skeptic independently confirmed a rebinding regression:
`elabUpd` initially discarded an existing reference's attached shape. `ECtx.refine`
now preserves the target metadata when its scoped type stays the same. New
quantifier/where/program declarations clear outer metadata instead. Regressions
cover memory/storage identity updates, string markers, and a following program
that must still reject writing 256 to a uint8 element. They also cover byte,
function and array shadowing, capture propagation, missing-binding refusal and
metadata/width changes that require no extra formula binder.

Focused elaborator and frontend rebuilds passed at 1.60 and 2.53 GiB peak
aggregate RSS respectively. The 270-job focused rebuild (new binding checks,
Checked, AbiFeatures and PublicGetters) passed at 4.97 GiB peak aggregate RSS.
The latest 21 binding guards also pass per-file diagnostics. Final broad results
are recorded below. The layer check passes.
The orphan check reports 33 existing ignored scratch modules; no new reachable
module is orphaned. The prose-path check reports 20 existing missing references
in archived validation JSON and an upstream Mathlib source citation, plus six
ambiguous short names outside the changed prose. User-owned scratch files and
unrelated untracked logs remain.

The initial LSP pass retained eight workers. Its idle workers were released,
leaving three files, and the task-owned server was moved into a 6 GiB scope with
swap disabled for subsequent allocations. Heavy shell checks retain their
separate 12 GiB cap. No other session's workers were terminated.

### Proof-tree target and migration

Committed as `14260603` (`Make tree leaves intrinsic`).

Reassessment after the binding migration found one smaller but independent
representation improvement worth completing: `Tree.node` accepted any `Act` and
any child array, so an open or closed leaf could carry hidden children. Its
producers used empty arrays; consumers relied on that convention when
counting goals, emitting scripts and reporting closure.

The target is a shared node header and three constructors: open leaf, solved
leaf, and rule with children. Remove the separate `Act` representation and
read the constructors directly; only a rule constructor can contain children. Migrate tree growth and tactic prefixing
directly, with no legacy `node` adapter. Existing tree/node/JSON/replay pins
exercise public consumers. This is a data-model invariant, not a new proof
correctness or tactic-completeness claim. History of `TreeData` shows no speed
rationale for the independent action/children fields; rebuilding its importers
is the expected checking cost.

Implemented without an adapter or separate action view. `openGoals` and script
generation now recurse on the constructors directly, and the node-inspection
tool reads tactics from the same constructors. Read-only finder and skeptic
reviews found no remaining defects, including after removing `Act`. The final
289-job build of both proof-tree pin modules and the binding regressions passes,
with a measured 2.41 GiB peak aggregate RSS. Per-file diagnostics pass for all
three changed modules. Existing display, JSON, branch-label, node and replay
pins were preserved without editing their expected output.

### Reassessment and remaining work

The two new increments complete their migrations: no detached shape entries,
old tree constructors or dual action/tree representation remain. The binding
change also eliminated parameter-list flattening, repeated local lookups and a
second state mutation for reference captures. The tree change eliminated the
action layer rather than retaining it as another synchronized representation.

The recursive-storage graph remains a substantial follow-up, not an achieved
ordinary-source migration. It changes the admissible type universe and requires
an explicit correspondence through observations, term operations and deletion
before replacing legacy storage. Existing separate graph certificates do not
establish that correspondence. The core compiler alternative is not selected:
the public compilation entry already couples its recognizer and code through a
certificate and the memory branch is intrinsic; another fragment AST has no
demonstrated net simplification yet. Finite-dispatch signatures were deferred at
that milestone; the follow-up below completes their migration. This investigation
does not claim the architecture is fully optimized.

Competing binding designs were a second name-to-shape map, a generic wrapper
around every local, and constructor-attached metadata. A second map retains the
shadowing/synchronization problem. Constructor fields keep metadata on program
locals without giving specification-only storage/KeY-int locals meaningless
shape slots. `ECtx` remains a named elaboration boundary because resolution and
freshening precede the intrinsic `Idx`/`Stmt` representation; the change does
not add an untyped runtime representation.

For trees, an action-indexed child family could also forbid leaf children, but
would retain a separate action value and propagate its index through consumers.
The algebraic tree provides the same leaf guarantee with one representation.

Another foundational alternative is indexing primitive core types by bit width
instead of retaining widths in source metadata and lowering narrow arithmetic.
It could consolidate narrow checks, but would also restrict the states quantified
by existing formulas and require a correspondence for source promotions, casts,
overflow guards and KeY's printed steps. Intrinsic widths alone do not remove
those observable guards or the separate ABI kinds (`address`, bytes, enum and
function markers). A second numeric syntax plus a lowering adapter is not a
demonstrated simplification. This alternative is not implemented or claimed
equivalent; a semantics-preserving target needs establishing first.

### Final second-pass verification

Recorded on 2026-10-27, after both representation commits. No Lean code changed
between these checks and the subsequent JavaScript repair, which strengthens an
existing source regression's expected report. Later follow-up results are separate.

| Check | Result |
|---|---|
| Full library | 685 jobs passed, including the 21 binding guards, existing proof-tree/JSON/replay pins, OpenLoops and decision examples. |
| TestSuite | 259 jobs passed, including the pinned obligation/axiom report. |
| Normal `./run-lean.sh` | Exit 0 with the tracked configuration and the explicit frozen rule file. The preceding driver completed both builds but used an incorrect rule-file path at its final step; that path was corrected before counting the command as passing. |
| Frozen sort conformance | 377 taclets, 131 read-bearing annotations, all matching `tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key`. |
| Source regressions | 22 finite-dispatch, nine getter-dispatch, one getter-plan and seven public-getter cases covered. The original run passed 38 and exposed the stale count described below; the repaired case then passed its focused rerun. |
| Static TestSuite and automation | 564 selected functions: 552 derived, 11 refuted, one excluded, none pending; 491 automatic and 61 using a step budget. |
| Layers | 152 core modules, none reaches the elaborator. |
| Reachability | 700 reachable modules; passes with an explicit allow-list containing only the 33 pre-existing untracked scratch modules. The unqualified audit still reports those scratch files. |
| Resource bounds | Heavy jobs ran sequentially under `MemoryMax=12G`, `MemorySwapMax=0`, with a 12 GiB available-memory reserve. The guard observed a peak aggregate RSS of 11.60 GiB during the large build sequence. No resource stop was counted as a passing check. |
| Working tree and prose | Diff whitespace checks pass. The whole-repository prose audit retains the 20 pre-existing missing references and six ambiguous names described above. The temporary build configuration and baseline worktree were removed. |

The source regression expected 15 `PublicGetters` report rows, but inherited
public functions were deliberately added to testing entries in `62338a6f` after
that pin was written. An isolated checkout of baseline `98d2682c`, using the
same compiler checkout, independently returned 16 names in discovery mode with
no errors, including `GetterBase.inherited`. This was a stale test expectation,
not an additional admitted function introduced by either refactor.

The repaired test pins the exact sorted array of all 16 function/status pairs,
so missing, unexpected and duplicate rows fail. Both false assertions remain
`pending`, the collision helper remains `internal`, and every positive entry,
including `inherited`, must be `proved`. Finder and skeptic reviews confirmed
the baseline explanation and that the new assertion strengthens coverage.

## Earlier pass

The earlier getter/provenance representation changes are implemented and verified. The
upstream pull was merged in `dc044e71`, preserving its enum/UDVT getter support.

| Change | Commit | Structural guarantee |
|---|---|---|
| Getter plans | `2669fa75` | Each input keeps its binding, type, source key and ABI type together; each result keeps its binding/type/expression together. A completed plan requires a first result. |
| Compiler provenance | `82f67125` | Historical versus analysed compilation is one mode; pipeline, settings, historical-fixture flag and effective coder are derived observations. |
| Final verification record | `ffa05eb2` | Library, TestSuite and frozen sort checks passed after restoring the normal build configuration. |

## Decisions and limits

Getter traversal uses `GetterPath`; completion produces `GetterPlan` with
`first` and `rest`. `params`, `sourceParams`, `abiParams` and `rets` are
projections, and `returnText` renders scalar or tuple returns without `head!`.
The source refuses a getter with no returned members, including a struct whose
only members are omitted arrays/mappings. Bounds guards, generated-name
freshness, named mapping arguments and source ABI identities are preserved.

`Compilation.historical` carries no recorded pipeline/settings;
`Compilation.analysed pipeline settings` carries the selected analysis input.
Historical v1 has an unknown effective coder. Analysed legacy compilation uses
the requested coder; via-IR uses v2 even if v1 was requested. Settings text is
still validated by `Source.read`: manually constructing a provenance record
is not a compiler-validation certificate.

No interpreter, taclet or proof-rule changes, dependencies, axioms or heartbeat
increases were needed. The two code areas received read-only finder and skeptic
reviews without remaining confirmed defects. Relevant Git history did not show
that these representations were introduced for checking speed; changing frontend
modules still invalidates their consumers.

## Validation

Recorded on 2026-10-27; job counts describe that verification snapshot.
The full-build snapshot is recorded in `ffa05eb2`. The subsequent documentation
refresh regenerated advisory feature metadata and checked that file alone;
it did not rerun the full library or TestSuite build.

| Check | Result |
|---|---|
| Changed Lean files | Per-file error diagnostics passed. |
| Direct getter-plan regression | Mapping metadata, scalar/tuple order, omitted fields, mixed array/mapping traversal and omission-only refusal passed (`scripts/getter-plans.test.mjs`). |
| Provenance regression | Historical v1/v2, analysed legacy/via-IR, settings preservation and malformed/downgraded metadata refusals passed (`scripts/source-provenance.test.mjs`). |
| Existing getter regressions | Success/false-assertion and reference-return refusal tests passed. |
| `./run-lean.sh` | Exit 0: 684 library jobs, 259 TestSuite jobs and the frozen sort check. Includes public-getter proofs and source-admission report quotation checks. |
| Frozen sort check | 377 taclets; all 131 read-bearing annotations match. |
| Layer check | 152 core modules; none reaches the elaborator. |
| Frozen TestSuite static audit | 564 selected functions: 552 derived, 11 refuted, one excluded, no pending. The scoped table itself contains 563 obligations. |

Use `tests/migration/solkey/keyext.solidity.examples` for the static TestSuite
audit and its `solidityProgramRules.key` for `SOLKEY_RULES`; the sibling checkout
has drifted from this fixture. These passing checks are not a theorem of
compiler/extractor equivalence. Source refusals and unsupported boundaries remain.

The local documentation audit after integrating cloud task 10 checked links,
heading anchors and Lean-file citations across all 72 tracked Markdown files
without findings. The feature
manifest, generated report and Lean catalog pass the generation-consistency
check; the catalog's per-file error diagnostics also pass. Five stale `missing`
assessments now describe bounded partial support with evidence; ordinary
recursive-source support remains missing. Feature scopes and admission policy
were not changed.
Read-only finder and skeptic reviews confirmed those bounded assessments and
corrected operator wording to distinguish symbols from unary/binary signatures.

At documentation-refresh snapshot `b5e6438d`, the whole-repository prose
checker reported seven missing references:
six in an archived validation JSON record and one upstream Mathlib citation in
a Lean source comment. These are outside the current Markdown documents and
were not rewritten to alter historical evidence.

## Resource bounds and resuming work

Acquire `/tmp/solidity-lean-feature-groups-20261025/writer.lock` before writes or
Lean checks, then reread Git status. Preserve unrelated work. Keep heavy checks
sequential and use a hard systemd scope (`MemoryMax=12G`, `MemorySwapMax=0`) plus
an available-memory guard with a 12 GiB reserve. Do not terminate other sessions'
workers. Keep at most four LSP files open.

Use `LEAN_NUM_THREADS=1` and explicit `-j1` for large fresh proof checks; the
environment variable alone started an additional Lean thread in the measured
probe. A session-specific alternate TOML can add `-j1` to library `weakLeanArgs`
without changing the tracked lakefile. Remove the temporary file after checking.
Do not confuse virtual address reservations for thread stacks with resident RAM.
The existing OpenLoops proof passed under the 12 GiB cap at 9.32 GiB aggregate
RSS; this does not establish that a clean rebuild fits 10 GiB.

Keep private artifact caches on disk under `.lake/refactor-cache`, not on the
RAM-backed `/tmp` filesystem. A private cache repaired reported fetches whose
object files were absent. Resource guards stopped earlier attempts when other
jobs filled RAM/swap; the completed proof artifacts were reused after headroom
returned. No resource stop was counted as a passing check.

Rebuild `Solidity.Frontend.Testing` before JavaScript regressions using
`build:false`, and `Solidity.Tools.Upstream` for the finite-dispatch production
import checks. Sandbox Node child-process EPERM calls for the same bounded host
check, not changed verdicts. No verification for the earlier getter/provenance
increments is pending.

## Finite-dispatch signature follow-up

The continuation starts from `11ea6b34`. Candidates still stored a general `Ty`
even though declaration/getter producers only built functions. Consumers rebuilt
the outer function type for each internal/external call and returned `none` for
an impossible scalar case. This was a representation invariant left to convention.

The replacement `FiniteDispatch.Signature` contains parameter and result lists.
Candidate source/native fields use `Option Signature`: unsupported source kinds
and missing metadata remain explicit unknowns, not omitted targets. The call-site
mode is separate from its signature; nested function components keep their own
mode in `Ty`. `parseCallable` performs the scalar/function discrimination once
at the external type-string boundary. Ordinary declaration and getter producers
construct signatures directly, and all target/alias comparisons use them. The
old `asExternal` adapter and comparison-time visibility rewriting are removed.
Native rendering reuses `Ty.native` at one boundary, so it has no second spelling
to synchronize with nested function types.

This change preserves native-key spelling, source/native separation, unknown and
reference refusals, getter visibility, alias checks, and the restricted internal
zero-argument memory-byte return. A fresh source IR or a sum that conflates
unknown metadata with known reference candidates would obscure those distinctions;
neither is introduced. Relevant history records admission/getter changes rather
than a checking-speed rationale for the old representation. This edit has 74
frontend consumers, so verification remains sequential under the same memory cap.

The changed Lean file's error diagnostics and the new signature regression pass.
The regression checks a kernel equality of
native-key rendering for arbitrary component lists, nested visibility, scalar and
unknown/reference refusals, fuel exhaustion and memory-byte location retention.
Read-only finder and skeptic reviews found no missed consumer or behavioral
change. They traced unknown/reference handling, source-kind collisions, getter
eligibility, visibility, aliases and nested function modes against the old code.

The final frontend rebuild passed at 1.69 GiB peak aggregate RSS. The initial
source-suite run passed 25 cases and refused to run six production-path checks
because `Tools.Upstream` was out of date; no assertion verdict failed. That
consumer was rebuilt successfully at 1.34 GiB peak. The complete 31-case source
rerun passed with zero failures at 1.40 GiB peak; the new signature test also
passed at 1.31 GiB peak. All 32 focused cases are covered without changing an
existing verdict. Final library/TestSuite/frozen-sort confirmation remains pending.
