# Architectural refactoring progress

## Second-pass investigation

The 2026-10-27 second pass starts from `98d2682c`. The earlier getter and
provenance increments remove independent pieces of state, but leave the
elaborator's binding metadata split across synthetic locals. The following
assessment follows actual source-to-run and formula-to-proof paths, rather
than treating the earlier two increments as an architecture-wide audit.

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
The latest 21 binding guards also pass per-file diagnostics. Broader checks
remain pending. The layer check passes.
The orphan check reports 33 existing ignored scratch modules; no new reachable
module is orphaned. The prose-path check reports 20 existing missing references
in archived validation JSON and an upstream Mathlib source citation, plus six
ambiguous short names outside the changed prose. User-owned scratch files and
unrelated untracked logs remain.

The initial LSP pass retained eight workers. Its idle workers were released,
leaving three files, and the task-owned server was moved into a 6 GiB scope with
swap disabled for subsequent allocations. Heavy shell checks retain their
separate 12 GiB cap. No other session's workers were terminated.

## Current state

The two selected representation changes are implemented and verified. The
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
`build:false`. Sandbox Node child-process EPERM calls for the same bounded host
check, not changed verdicts. No verification for these two refactors is pending.

## Remaining candidate

The lower-priority candidate is a dedicated parameter/result signature for
finite-dispatch candidates in `Frontend/SolcJson/Contract.lean`. It would remove
`asExternal`'s impossible scalar case. Keep `Ty` parsing at the external boundary
and migrate `candidate`, `getterCandidate` and `inspectCall` together if pursued.
Preserve unknown/reference candidates, source/native distinctions, alias checks
and the restricted zero-argument internal memory-byte return.

This is future work, not an unfinished part of either completed increment.
Validate any such change with `scripts/finite-dispatch.test.mjs` and
`scripts/getter-dispatch.test.mjs` against rebuilt frontend artifacts; do not add
another representation unless its simplification justifies those migration risks.
