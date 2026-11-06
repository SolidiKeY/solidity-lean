# H62 item 4: generic InternalFlow controls

Status: **blocked; full assignment unfinished**. This is a reviewable additive
census/backfill checkpoint, not completion of any semantic gate.

## Checkout and boundaries

Repository: `/workspace/solidity-lean`. Branch:
`codex/solidity-h62-4-20261106/generic-internalflow`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The original clean `work` checkout was at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
`git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4`
succeeded; `git merge-base --is-ancestor BASE origin/master` exited 0.
Created the assigned branch at BASE under the repository writer lock. No resets,
merges, pushes, default-branch writes, generated roots, registry edits or owner
source edits. The goal inspection tool is unavailable; no goal was created/reset.

Writes are restricted to the assigned tests/scripts directories and this document.
All 271 family originals remain byte-identical to BASE. No Lean declarations,
frozen statements, proof budgets, axioms, sorrys or interfaces were changed.
No Yul Raw/vector generator or H55 work is duplicated. No registration fragment
is needed yet: this checkpoint adds no Lean module.

## Queue status

1. Partial: deterministic conservative lexical inventory and exact source/header
   hashes are saved. Semantic case classification and per-case audit adjudication
   are unfinished. Do not equate filename/control-name heuristics with all cases.
2. Blocked: intrinsic parameterized semantic lemma and typed fixture table are not
   implemented/proved. No exact-instance migration is claimed.
3. Blocked: semantic correspondence, all negative/refusal coverage and Lean
   reproduction acceptance remain required. External census acceptance passes.
4. Blocked: before/after semantic checking measurements are unavailable without a
   migration implementation and working dependency closure. No timing delta or
   slowdown claim. Stop if an eventual comparable measurement exceeds 10%.

Additional witness/isolated fixture proofs require the same intrinsic typed-run
imports which fail at the baseline dependency below. No substitute AST, weakened
premise, decide table, trust shortcut or unverified proof has been supplied.

## Census and audit mapping

`census.py` scans every original family file, not just `*Controls.lean`. It masks
comments/strings without changing offsets, retains all declaration headers,
header hashes, declaration-slice hashes, full source hashes, and guard/axiom
command locations. Full source hashes are authoritative byte-preservation
checks. Header hashes are lexical source headers, **not elaborated types**;
inferred types require Lean. Declaration slices can contain intervening commands.

Inventory: 271 files, 3,599 lexical declarations, 2,190 theorem-like declarations.
57 Controls files contain 912 declarations including 577 theorem-like declarations.
There are negative-name candidates in 64 additional non-Controls files. These
numbers do not certify semantic case completeness. Full inventory is off git:
`/workspace/h62-evidence/generic-internalflow/original-inventory.json`, SHA256
`b1535a1f91512c882b49b8bf780fe7a41f54a8dda0fa22a1c5ba4a08b4457014`.

Coordinator inputs were independently checked against `sha256.json` (all five
pass). `refactor-audit-20261106.md` item 9 explicitly names the OrderedEffectful
Scalar/Storage, RecursiveScopeCompiler/ScalarSourceCompiler,
EffectfulRuntime/EffectfulStorageRuntime, AllocatingArguments/MutatingCaller
twins. The scanner marks their 14 matching files as candidates. Item 11 searches
for shared sourceReverted/pushes_zero/allocationCostProg/HRef/HeapRepr/AllocatorRepr
uses; 151 files have these broad search hits, not necessarily duplicated lemmas.
Item 16 motivates data tables for the 57 Controls files; its Yul Raw and numeric
examples remain out of scope. Manual semantic matching is still pending.

## Gates and resource evidence

Official archive: `/workspace/h62-toolchain/lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` (PASS).
Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
The installed 4.24.0 was identified but used for no proof check or build.

VM cgroup cap 16 GiB, SwapTotal 0. Checks are serial with writer lock,
`LEAN_NUM_THREADS=1`, explicit `-j1`, per-process address-space cap 12 GiB,
300-second wall/CPU bounds and sampled group RSS/4 GiB available reserve guard.
The group RSS guard is sampled, not a hard aggregate cgroup cap. The wrapper
preflights resources and cleans up its owned process group. No systemd-run.
No Lean MCP diagnostic tools were exposed; direct bounded per-file checking used.

- `bash scripts/h62/item4/generic-internalflow/acceptance.sh /workspace/h62-evidence/generic-internalflow`:
  PASS, exit 0; seven tooling regression tests; BASE/current inventories identical;
  deterministic byte reproduction and `git diff --check`. This is external
  acceptance, not semantic proof.
- `python3 scripts/h62/item4/generic-internalflow/bounded.py -- /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean -j1 --tstack=131072 Solidity/KeySort.lean`:
  PASS, Lean exit 0, 1.728617431 s, sampled peak group RSS 518,987,776 bytes;
  `prerequisites.log`. Initial attempt used missing `/usr/bin/time`, ran no Lean;
  retained in `keysort.log` and corrected with the checked-in bounded wrapper.
- `PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-internalflow/build.py --lean /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean --output /workspace/h62-build435/generic-internalflow Solidity.Semantics.Run`:
  FAIL, exit 1; dependency `Solidity.Syntax.Raw`, 3.553651547 s,
  sampled peak group RSS 1,498,533,888 bytes. KeySort/AST/SpecSyntax compiled first.
  Uses only fresh external 4.35 artifacts; no 4.24 cache. No theorem validation
  claim follows from the passing predecessors.
- Full affected validation and `./run-lean.sh`: pending, not run past known failed
  prerequisite. No RUNTIME_GATE_PASS. Semantic proof/axiom audit: pending.

## Typed dependency and owner coordination

`DEP-435-RAW` / dependency_toolchain_migration: unchanged
`Solidity/Syntax/Raw.lean` fails Lean 4.35 at lines 597, 650, 665, 682, 684
(String/Slice API changes). Owner per verified ownership snapshot:
`solidity-h62-6-20261106/migrate-syntax` (`H62-6-MIGRATE-SYNTAX`, reserved).
This file is outside this worker's scope. Exact-file request saved at
`tests/h62/item4/generic-internalflow/owner-request.json` for coordinator pickup.
`relay.sh` is absent: no relay delivered and no owner agreement inferred.
The diagnostic is `/workspace/h62-build435/generic-internalflow/Solidity.Syntax.Raw.log`;
summary `/workspace/h62-evidence/generic-internalflow/build-run.log`.

Family originals also remain read-only until exact-file relay agreement. No
family migration patch exists yet. Coordinator should obtain/apply the approved
dependency overlay, preserve source ownership, and resume all four checkpoints.
Do not fix Raw locally or silently use 4.24 as a substitute.

## Independent reviews and fixes

Finder `/root/census_finder` and skeptic `/root/census_skeptic` reviewed read-only,
without Lean/server/builds/writes. They identified truncated result-type lets,
equation-style body/header confusion, command line offsets, resource preflight
and descendant cleanup, baseline-output aliasing and missing-build-target false
passes. All concrete findings were fixed with focused acceptance coverage.
Finder re-reviewed all 2,190 theorem-like lexical headers and passed the current
family census; semantic-completeness caveat remains. Skeptic final follow-up is
recorded in off-git `reviews.json`. Reviews apply to this tooling milestone only;
future semantic milestones still require their own finder/skeptic reviews.

## Resume and handoff

Full original inventory below lists each Controls file; every other declaration
and embedded client/control remains in the off-git JSON. Reproduce using the
acceptance command above; resume the isolated builder only after approved owner
dependency migration. Then classify all cases semantically, select generic
intrinsic lemmas, build typed fixture tables and exact-instance correspondence,
preserve refusals, obtain owner-applied migration and registration, run affected
and final gates, and measure before/after under identical toolchain/tree/cache/
resource conditions. Persistent assignment remains unfinished and blocked.

Export paths: `/workspace/h62-artifacts/generic-internalflow/original.patch`,
`handoff.md`, `SHA256SUMS`; evidence directory above, exported without build bulk.
Committed head is recorded in the external handoff/result after commit to avoid
self-referential hashes. The coordinator can retrieve these from this same VM.

## Original Controls inventory (lexical counts)

| Original file | Declarations | Theorem-like |
|---|---:|---:|
| `RuntimeFrameCodeAuthenticationControls.lean` | 15 | 13 |
| `RuntimeFrameV3AllocatingCallCoherenceControls.lean` | 5 | 1 |
| `RuntimeFrameV3AllocatingHeadViewsControls.lean` | 14 | 10 |
| `RuntimeFrameV3AllocatingOuterClaimsControls.lean` | 7 | 3 |
| `RuntimeFrameV3AllocatingOuterFamilyControls.lean` | 13 | 5 |
| `RuntimeFrameV3AllocatingOuterPlanControls.lean` | 5 | 3 |
| `RuntimeFrameV3AllocatingOuterZeroControls.lean` | 8 | 5 |
| `RuntimeFrameV3AllocatingRecursiveCheckControls.lean` | 23 | 18 |
| `RuntimeFrameV3AllocatingScalarControls.lean` | 25 | 12 |
| `RuntimeFrameV3AllocatingScalarLeavesControls.lean` | 15 | 14 |
| `RuntimeFrameV3AllocatingScopedCheckControls.lean` | 11 | 10 |
| `RuntimeFrameV3AllocatingScopedEndpointControls.lean` | 5 | 5 |
| `RuntimeFrameV3AllocatingScopedTransportControls.lean` | 4 | 2 |
| `RuntimeFrameV3AllocatingSourceCertificateControls.lean` | 8 | 5 |
| `RuntimeFrameV3AllocatingSourceViewsControls.lean` | 8 | 7 |
| `RuntimeFrameV3AllocatingTurnViewsControls.lean` | 9 | 8 |
| `RuntimeFrameV3AllocationInventoryControls.lean` | 1 | 1 |
| `RuntimeFrameV3CallProducerControls.lean` | 39 | 20 |
| `RuntimeFrameV3CallProducerRefArrayControls.lean` | 42 | 17 |
| `RuntimeFrameV3CallProducerRefStructDefaultControls.lean` | 39 | 19 |
| `RuntimeFrameV3CallProducerRefStructRebindControls.lean` | 44 | 22 |
| `RuntimeFrameV3CallProducerRefTupleControls.lean` | 33 | 17 |
| `RuntimeFrameV3CallProducerRefTupleFrameControls.lean` | 9 | 7 |
| `RuntimeFrameV3CallerStorageFrameControls.lean` | 49 | 22 |
| `RuntimeFrameV3DisjointScalarControls.lean` | 38 | 27 |
| `RuntimeFrameV3DistinctParentControls.lean` | 26 | 16 |
| `RuntimeFrameV3DistinctScalarControls.lean` | 22 | 10 |
| `RuntimeFrameV3EffectfulRuntimeControls.lean` | 17 | 16 |
| `RuntimeFrameV3EffectfulSourceCheckControls.lean` | 13 | 10 |
| `RuntimeFrameV3EffectfulSourceSelectionControls.lean` | 18 | 11 |
| `RuntimeFrameV3EffectfulStorageRuntimeControls.lean` | 22 | 15 |
| `RuntimeFrameV3FreshAllocationContentsControls.lean` | 1 | 1 |
| `RuntimeFrameV3FullScalarLoopControls.lean` | 5 | 2 |
| `RuntimeFrameV3FullScalarPrefixControls.lean` | 4 | 1 |
| `RuntimeFrameV3NativeAllocationCoherenceControls.lean` | 5 | 1 |
| `RuntimeFrameV3NativeDescentHeapControls.lean` | 1 | 1 |
| `RuntimeFrameV3NativeReturnRepresentationControls.lean` | 1 | 1 |
| `RuntimeFrameV3NativeScalarAgreementControls.lean` | 1 | 1 |
| `RuntimeFrameV3OrderedEffectfulStorageControls.lean` | 36 | 17 |
| `RuntimeFrameV3PrimitiveCallerControls.lean` | 30 | 14 |
| `RuntimeFrameV3RecursiveScopeControls.lean` | 17 | 12 |
| `RuntimeFrameV3SameCallControls.lean` | 11 | 8 |
| `RuntimeFrameV3ScalarCallerControls.lean` | 14 | 12 |
| `RuntimeFrameV3ScalarClaimsControls.lean` | 14 | 12 |
| `RuntimeFrameV3ScalarContinuationControls.lean` | 11 | 11 |
| `RuntimeFrameV3ScalarDescentControls.lean` | 7 | 2 |
| `RuntimeFrameV3ScalarDualControls.lean` | 20 | 20 |
| `RuntimeFrameV3ScalarEmitterControls.lean` | 19 | 17 |
| `RuntimeFrameV3ScalarPairedTransportControls.lean` | 1 | 1 |
| `RuntimeFrameV3ScalarPlanControls.lean` | 13 | 11 |
| `RuntimeFrameV3ScalarPrefixControls.lean` | 20 | 17 |
| `RuntimeFrameV3ScalarRecursiveControls.lean` | 23 | 14 |
| `RuntimeFrameV3ScalarReentryControls.lean` | 9 | 9 |
| `RuntimeFrameV3ScalarReturnControls.lean` | 20 | 16 |
| `RuntimeFrameV3ScalarSourceCompilerControls.lean` | 26 | 17 |
| `RuntimeFrameV3ScopedScalarControls.lean` | 11 | 7 |
| `RuntimeFrameV3TypedHeapExtensionalityControls.lean` | 5 | 1 |
