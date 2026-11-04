# Executable memory/reference lane

Status: blocked at A's committed interface; compiler-fixture backfill prepared.
This is not completion of the assignment or a runtime acceptance claim.

Repository: `/workspace/solidity-lean`; assigned branch:
`codex/solidity-directruntime-20261104/memory-references`.
Pinned base: `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
The checkout was clean on bootstrap branch `work` at that exact base.
`git fetch origin master` succeeded; `origin/master` equals that base and
`git merge-base --is-ancestor BASE origin/master` and the assigned HEAD passed.
No unrelated work was reset, no push/merge/publication was performed.

## Queue and dependency handoff

1. Inventory and controls: partial, with full compiler AST fixtures below.
   Exact intrinsic support traced; closure and kernel proofs remain pending.
2. Location-aware adapter: blocked. At the pinned base,
   `Solidity/Frontend/ExecutableAst` does not exist. A fresh
   `git ls-remote --heads origin 'codex/*directruntime*'` returned no heads.
   Therefore no concrete committed A interface is available to consume.
   Do not build a parallel translator, change DirectRuntime or invent an API.
3. Runtime controls: pending admission and proof closure for every row.
4. Fresh native/browser: blocked on adapter/integration, all verdicts pending.
   D handoff is this fixture manifest, not a claim that D ran it.

A must supply its interface commit and import/API contract. Once available,
implement only under `Solidity/Frontend/ExecutableAst/Memory/`, consuming it
without edits to Shared or DirectRuntime. There is currently no adapter API
to instruct A to import. No new Lean modules were created; hence no central
registration rows are proposed yet. Add a local manifest and module-map row
proposals when actual modules exist; do not edit generated roots.

## Existing model (read-only inventory at the pinned base)

| Boundary | Existing support and restriction |
|---|---|
| Surface syntax | `RawExpr.newArr (T : RawTy) (n : RawExpr)`; `RawStmt.declMemory` and `declStorage` each take type, name and optional initializer (`Solidity/Syntax/Raw.lean`). Reuse these constructors. |
| Allocation admission | `elabNewTy` in `Solidity/Syntax/Elab/Values.lean` returns `(R : RefTy) ×' R.newArrOk = true`; only `.array E` with `E.mapFree && E.defaultOkS` passes. Fixed arrays may have defaults but are not `new R(n)` types. `elabSize` requires a simple uint, capturing a compound expression through the existing machinery. |
| Declaration admission | `Solidity/Syntax/Elab/Arms.lean` checks both declared and allocated reference types for equality; memory/storage on a primitive is refused. Default memory declaration requires map-free and default-wellformed evidence. Storage aliases use `checkPath`, not memory allocation. |
| Alias versus copy | `elabMRhs` in `Solidity/Syntax/Elab/Values.lean`: a matching memory path becomes `.alias`; a matching storage path becomes `.copy`, requiring map-free. Incompatible types and primitives throw. |
| Typed allocation | `newArrT : (R : RefTy) → PrimTy.uint.Denote → R.newArrOk = true → SVal (.ref R)` replicates `SVal.dflt E`, with `newArr_lt` proving length below 2^256 (`Solidity/Semantics/Run.lean`). |
| Identity and copying | `MRhs.evalT` returns `TRes (Grew C Γ σ.H (HRef · R))`. Alias returns the same reference and unchanged heap; copy/new use existing `copyStToMG`. `TRun.declMem` pushes `some g.val`; `rebindMem` updates the reference local. |
| Reads/writes | `MPath.mvalT` rejects unset locals; `MLoc.addrT`, `Val.evalT`, `TRun.assignMem` route indexed access through the typed heap. Missing cells return `TRes.ofOpt` failure (model revert). No new index semantics needed. |
| Calculus | `Solidity/Calculus/Step.lean` declaration binds and rebinds the memory local. `rebindMemStep_sound` and `sound_allocCopy_newArr` are existing soundness components in `Solidity/Calculus/SoundMem.lean`. `Solidity/Calculus/MemRead.lean` imports the existing Spine/Laws/Ok/Pass symbolic read and bounds components; module presence does not establish closure of these fixtures. |
| Modalities | `Modality.onTHalt` in `Solidity/Semantics/RunFrame.lean` accepts revert for box, but diamond accepts only exhausted. Panic is separately excluded by `afterRunTR`; `Solidity/Calculus/Problem.lean` documents false assertion exclusion for both. Always-revert cannot pass the required positive diamond Identity. |
| Executable gap | `Solidity/Tools/DirectRuntime.lean` private `statements` refuses every nonprimitive local at `VariableDeclarationStatement`; `expression` has no allocation FunctionCall/NewExpression case. It already translates IndexAccess and Assignment; route these to existing raw expressions/statements after location-aware admission. Type-name parsing alone does not give executable support. |

The model has signed int, uint and bool primitives. Fixed-size arrays are not
fixed-point numeric types. Nested references require the existing map-free and
default conditions. Do not claim bytes, structs, mappings, narrow integer types,
calldata, or any unimplemented type is executable just because a type exists.

Existing producer reuse points, without producer edits:
`Solidity/Backend/MemoryOps/SourceAlias.lean`,
`Solidity/Backend/MemoryOps/SourceDeclaration.lean`,
`Solidity/Backend/MemoryOps/PhysicalReferenceStore.lean`, and
`Solidity/Roadmap/V16/SSCP2/NewAllocation.lean` (including `newData_valid`,
`allocation_mem`, `eval_new_mem`, `local_new_mem`). These are conditional Source,
representation and allocation components; they do not prove the compiled
DirectRuntime Identity obligation. Reuse, never duplicate, and retain their
premises and boundaries. No Source/Core/backend files were changed.

## Fixtures and decisive controls

Owned packet: `tests/directruntime-20261104/memory-references/`.
Run `node tests/directruntime-20261104/memory-references/fixtures.cjs`.
The compiler is pinned by SHA-256 and exact version before use. Each source has
complete standard JSON input/output, retaining all compiler AST metadata.
Legacy and via-IR AST-analysis settings are recorded independently, without
claiming code generation or EVM execution. This script performs no verification.

72 full compiler AST outputs cover 18 scenarios, each in box/diamond and
legacy/via-IR settings: exact signed Identity, false assertion, default zero,
alias writes, false copy assumption, separate allocations, zero reads/writes,
boundary reads/writes, empty successful allocation, uint Identity, bool default
and alias, fixed-array default and alias, nested-reference alias, and storage
copy. Storage copy includes explicit `require` guards, so success is conditional;
its universally quantified diamond must remain unproved because wellformed
initial storage may fail those guards. Its box expectation remains positive.
The unannotated Identity twin must prove through both fresh runtimes.
Every false assertion must remain unproved in both modalities.
Zero/OOB controls may prove box under the existing model, never diamond.
Solc bounds failures panic externally; the existing intrinsic model uses revert.
This semantic deviation is recorded, not silently repaired in this lane.

Eight compiler-invalid source controls cover primitive memory, missing location,
storage/calldata allocation, incompatible elements, fixed-array allocation,
negative length and memory mapping. Six corrupted output controls cover absent,
unknown and incompatible locations, incompatible element type and absent type
name. Corrupted ASTs are explicitly not compiler-produced; they have no valid
compiler provenance and their admission results remain pending. They must never
be treated as successful verification.

`manifest.json` keeps expected outcomes separate from admission, proof closure,
native and browser results, all marked pending. AST compilation is external
fixture validation, not a kernel theorem or trusted-verifier result. Ordinary
requests must never load Lean env/kernel/elaborator/tactic frontend. Optional
certificates and development proofs do not relax that boundary.

## Validation and resources

`evidence/fixtures.log`: exit 0; 72 valid fixtures, eight compiler-invalid controls,
six generated malformed controls; recorded wall 2.2827517 s and peak RSS
165988 KiB. `/usr/bin/time` was absent on an initial attempt; Node's monotonic
clock/resourceUsage supplies these metrics. The shell retry exited 0.
No malformed AST was admitted or verified by this run.

Actual toolchain version probes: Lean 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613
(Lean 4.24.0). Lean/Lake are in `/workspace/.setup/tools/lean-4.24.0-linux/bin`,
not the initial PATH. No Lean elaboration/build was started. No Lean MCP
diagnostic/goal tools are available in the current tool catalog; use per-file
checks if exposed later and the repository wrappers otherwise.

Outer cgroup: memory.max 17179869184, memory.swap.max max; host SwapTotal zero.
This is NOT a compliant Lean scope. Docker daemon 28.4.0 answers on the local
socket, with no active containers/images observed. Before any Lean build,
create/verify a 12 GiB/no-swap scope and preserve H1 4 GiB headroom;
LEAN_NUM_THREADS=1 and explicit -j1; serial heavy checks. Do not count tool
availability as setup success or logical success. KeySort, full run-lean,
trust/axiom audit and fresh native/browser gates remain pending.
`RUNTIME_GATE_PASS` is NOT issued.

No new theorem/axiom signatures exist: this checkpoint changes only test data,
its generator and this owned document. Existing signatures at base/head are
unchanged, to be sealed as evidence. Required independent finder and skeptic
reviews are recorded in the evidence directory before committing.

## Producer and review limits

V11's operation components retain initial representation, resolution, bounds,
capacity, arithmetic and heap-shape premises; the physical/fetched-EVM boundary
is still open, as recorded in `docs/feature-work/memory-operation-proofs.md`.
`docs/feature-work/memory-copies.md` records the important V2 allocator witness
requirement and uninhabited draft certificates; a capacity premise alone must
not be reused as successful runtime evidence. The MRS/CR consumer mapping must
be finalized against A's actual interface; no alternate backend is authorized.
V16's Source `newArray` size failure at 2^64 and nested-reference default refusal
are separate from the intrinsic heap's `newArrT`; the nested fixture tests the
intrinsic path, not a claim of Source semantic equivalence.

The complete raw solc outputs retain unsigned builtin referencedDeclaration
IDs. A/D must consume the intended full-output decoding/normalization boundary;
these are not prevalidated trimmed fixtures and must not be fed as such.

Independent read-only finder and skeptic reviews both found the same expectation
bug: storage-copy runtime require guards do not restrict universal initial
storage. Fixed its model outcome to conditionalSuccessOrRevert and required
universal diamond verdict to false; box remains true. Both reviewers rechecked
all four manifest rows and documentation after regeneration and confirmed the
fix. Neither used Lean or changed files. Finder independently checked all 72
source hashes, input source bytes, AST existence, error-free compiler outputs
and pipeline settings. No further substantive finding was reported. Reviews
cover this backfill checkpoint only, not implementation or whole-assignment
acceptance. See `evidence/reviews.txt`.

Lightweight gates: JavaScript syntax, `node scripts/check-layers.mjs`,
`bash scripts/coord-tools/register.sh --check`, and
`bash scripts/check-doc-paths.sh` all exited 0. Layer output reports
562 core modules with zero reaching elaborator or checked parser adapters.
The doc-path gate reports pre-existing ambiguous basename references but no
missing reference failure. `git diff --check` passed.
