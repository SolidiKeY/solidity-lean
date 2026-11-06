# H62 item 4: generic InternalFlow controls

Status: **blocked; full assignment unfinished**. This is a reviewable additive
census/backfill checkpoint. H70 classification of all 57 suffix Controls files is
complete; no semantic Lean gate or full assignment completion is claimed.

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
   hashes are saved. H70 semantic classification and per-case audit9/11/16
   adjudication are complete for all 57 suffix Controls files. Embedded Checks/Client
   controls in other family files remain semantically unclassified. The full
   checkpoint remains partial; no original declaration is dropped.
2. Blocked: intrinsic parameterized semantic lemma and typed fixture table are not
   implemented/proved. No exact-instance migration is claimed.
3. Blocked: semantic correspondence, all negative/refusal coverage and Lean
   reproduction acceptance remain required. External census/classification acceptance passes.
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
examples remain out of scope. Those initial search hits were candidates only.
H70 replaces candidate-only interpretation within the 57 suffix Controls files
with manual per-declaration adjudication, described below. Embedded controls in
other family files remain pending.

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
  PASS, exit 0; 16 tooling regression tests (7 census + 9 classification);
  BASE/current inventories identical; every Controls declaration/header/hash and
  guard command conserved; semantic inventories reproduced byte-for-byte;
  `git diff --check`. Evidence: `semantic-acceptance.log`. This is external
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
H70 confirms accepted ticket relays to `migrate-syntax` and
`solidity-v12-v17-20261031/v12-flow-calls`. `relay.sh` is host-only, not a VM
installation task. Accepted routing does not supply a dependency overlay or
exact-file edit agreement. Neither has been inferred.
The diagnostic is `/workspace/h62-build435/generic-internalflow/Solidity.Syntax.Raw.log`;
summary `/workspace/h62-evidence/generic-internalflow/build-run.log`.

Family originals also remain read-only until exact-file relay agreement. No
family migration patch exists yet. Candidate exact-file request
`tests/h62/item4/generic-internalflow/family-owner-request.json` nominates
`RuntimeFrameV3CallerStorageFrameControls.lean:no_ref` and
`RuntimeFrameV3OrderedEffectfulStorageControls.lean:no_struct` for possible
owner-applied instances of a future proved typed absence lemma. These are distinct
candidates, not established duplicate bodies. Coordinator should obtain/apply the approved
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
future semantic proof milestones still require their own finder/skeptic reviews.

H70 classification received a separate independent read-only finder and skeptic
review across all 57 files/912 declarations. Both pass classification accounting
and multi-facet fidelity, not Lean elaboration or proof replay. The skeptic's
liveness wording correction was applied: the storage variant transports fragile
storage-alias liveness through storage equality **while retaining explicit
heap-reference liveness**. Both reviewers require the full checkpoint to stay
partial because embedded controls remain pending. Evidence:
`/workspace/h62-evidence/generic-internalflow/semantic-reviews.json`.

## Resume and handoff

Full original inventory below lists each Controls file; every other declaration
and embedded client/control remains in the off-git JSON. Reproduce using the
acceptance command above; resume the isolated builder only after approved owner
dependency migration. Classify embedded controls outside the completed H70 subset;
then select generic
intrinsic lemmas, build typed fixture tables and exact-instance correspondence,
preserve refusals, obtain owner-applied migration and registration, run affected
and final gates, and measure before/after under identical toolchain/tree/cache/
resource conditions. Persistent assignment remains unfinished and blocked.

H70 export paths: `/workspace/h62-artifacts/generic-internalflow/h70/original.patch`,
`handoff.md`, `SHA256SUMS`; evidence snapshot:
`/workspace/h62-evidence/generic-internalflow/h70/`. Previous checkpoint artifacts
remain at the parent export path. Build bulk is not exported.
Committed head is recorded in the external handoff/result after commit to avoid
self-referential hashes. The coordinator can retrieve these from this same VM.

## H70 semantic classification and audit adjudication

Completed H70 subset: all 57 filename-suffix Controls files, 577 original theorem
declarations and 335 fixture definitions/aliases (912 declarations). These counts
include helper lemmas and do not claim 577 independent executions. No declaration
was invented, removed, split, weakened or migrated. Embedded Checks/Client sections
outside this subset remain pending; the complete 271-file lexical inventory stays
available. `unclassified: 0` in the new output is scoped to these 57 files only.

Source map: `tests/h62/item4/generic-internalflow/semantic-cases.txt`.
Expander: `scripts/h62/item4/generic-internalflow/classify.py`. Each case has
manually assigned nonexclusive conclusion facets; no semantic label is inferred
from its name. Every record retains the full original header, header/slice hashes,
line and kind; every file retains its source hash and guard commands. Original
`negative_candidate` fields remain lexical hints only. Exact headers govern all
quantifiers, hypotheses, observations and conjuncts; facets do not replace them.

Generated off-git artifact:
`/workspace/h62-evidence/generic-internalflow/semantic-inventory.json`, SHA256
`2dff3601783cb66895fd3324a925c262575c9ecacc6890f30fb474cfe9c9f8c1`.
It includes per-declaration audit9/11/16 dispositions and all facet definitions.
Reproduction uses the acceptance command above or:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-internalflow/classify.py \
  --inventory /workspace/h62-evidence/generic-internalflow/original-inventory.json \
  --output /workspace/h62-evidence/generic-internalflow/semantic-inventory.json
```

Audit adjudication is deliberately narrower than a refactor approval:

- **9:** The four named twin pairs are recorded with exact source filenames and
  distinct semantic boundaries. Ordered scalar/storage and effectful runtime
  variants differ in fragile-alias handling; explicit heap liveness remains.
  RecursiveScopeCompiler/ScalarSourceCompiler differ in recognition of wrappers
  at every recursive level versus exact canonical bodies. AllocatingArguments/
  MutatingCaller differ in old-heap effects. Five Controls files are direct pair
  controls; four support the same boundaries; the rest carry no direct named-twin
  claim. Similar imports alone establish no substitution theorem.
- **11:** No named sourceReverted/pushes_zero/allocationCostProg/Loc.data motif was
  found in InternalFlow. Ordinary HRef/HeapRepr/AllocatorRepr use does not establish
  copied proof bodies. Exactly two Controls helper candidates are adjudicated:
  no_ref excludes every reference from an empty heap, while no_struct excludes
  struct references from a singleton uint-array heap and needs constructor
  disjointness. Preserve their separate exact instances. The audit's eight shared
  MemoryCopies fixtures belong outside this lane.
- **16:** A typed table may index existing fixtures and observations. Semantic
  execution, reconstruction, correspondence and counterexample proofs must still
  be parameterized kernel proofs. No decide-table replacement. Source-language
  refusal, source bare revert/panic/payload/exhaustion, target outcomes, Entry
  witnesses and claims are separate facets. No Yul Raw/vector generator work.

Critical retained distinctions include positive admission/Entry for reverting
inputs (`negative_member`, `negative_entry`), compiler acceptance of bad-evaluating
arguments (`bad_selected`, `bad_root`), source exhaustion with target success,
success without allocator ownership, two positive Heap.Keeps facts with unequal
heaps and non-default new objects, and byte-exact payload/panic preservation.
`wrong_active` is a conditional observation, not an existence witness.
`AllocatingSourceViews.actual_exhaustion` asserts source exhaustion/non-revert only.

Next generic proof candidates are typed halt-constructor separation after actual
source-run witnesses, intrinsic view reconstruction/correspondence, and typed
reference absence. Keep vector ordering, missing-export counterexamples, capacity
boundaries, zero-owner success and fragility witnesses as full exact obligations.
These are candidates, not proved generic lemmas or owner-approved migrations.

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

## Embedded classification tranche 1 (latest H70 disposition)

Completed classification of explicit `Checks` namespaces only in:

| Original file | Namespace lines | Theorems | Fixtures |
|---|---|---:|---:|
| RuntimeFrameV3AllocatingSource.lean | 130–244 | 14 | 3 |
| RuntimeFrameV3MutatingSource.lean | 180–324 | 15 | 10 |
| RuntimeFrameV3AllocatingResume.lean | 216–317 | 11 | 6 |
| RuntimeFrameV3MutatingResume.lean | 210–381 | 20 | 7 |

All 86 declarations retain every original inventory field and lexical header/hash.
This adds 60 original theorem declarations and 26 fixtures to the earlier 57-file
classification, not 60 new executions. All other embedded controls remain pending;
full checkpoint 1 is partial. Core declarations outside these bounded namespaces
are not silently classified. No original or Lean source changed.

Source map: `tests/h62/item4/generic-internalflow/embedded-cases.txt`; expander:
`scripts/h62/item4/generic-internalflow/embedded.py`. It validates exact frozen
inventory/source hashes and current source bytes, namespace start/end lines, absence
of nested blocks, exact case sets and duplicate/unknown facets. Generated bulk:
`/workspace/h62-evidence/generic-internalflow/embedded1/embedded-inventory.json`,
SHA256 `26d74afd7017cdad06ac88feb3c9f726929c8b3c632e1d8ad83b5f945c98f133`.

Allocating specifications assert actual Heap.Keeps; mutating Resume specifications
preserve old array lengths only. Continuation relates all residual source horizons
and retains all error classes, rather than asserting only success. The map keeps
non-revert/non-success separate from exhaustion, representation failure separate
from compiler refusal, and the wrong-reference read-bound counterexample separate
from allocation/admission refusal. Complete headers retain every original conjunct.
Audit 9 preserves allocating/mutating effects; audit 11 typed halt separation remains
a candidate after actual semantic witnesses; audit 16 permits data indexing only,
not replacing source execution proofs with decide tables. No H55 work is duplicated.

Independent read-only finder and skeptic reviewed all four regions without Lean,
servers, builds or writes. Finder requested an explicit read-bound counterexample
facet; applied. Skeptic passed conservation and semantic distinctions. Final review
receipt is saved with the evidence. Acceptance command:
`bash scripts/h62/item4/generic-internalflow/acceptance.sh /workspace/h62-evidence/generic-internalflow/embedded1`
passes 19 tests (7 census, 9 suffix classification, 3 embedded), exact current/base
byte preservation and deterministic reproduction. No new Lean check, semantic
gate, timing comparison, axiom or sorry claim. Historical KeySort success and Raw
migration failure remain unchanged; full affected validation is pending.

Latest routing supersedes earlier current-owner notes: syntax ticket destination
`solidity-h62-6-20261106/migrate-syntax`; current V12 delivery is pending to
`claudecloud/move5-20261106/v12-p1` for exact files
`RuntimeFrameV3CallerStorageFrameControls.lean` (`no_ref`) and
`RuntimeFrameV3OrderedEffectfulStorageControls.lean` (`no_struct`). Host journals
determine delivery acceptance. No relay establishes owner agreement or validation.
Do not edit originals while waiting. No relay installation task.

Next read-only work: continue remaining embedded Checks/Client regions (including
ParentPrefixes, AllocatingPrefixes and MutatingPrefixes) with explicit boundaries,
full conservation and independent reviews; do not count them complete now. Full
proof/fixture/correspondence/migration/timing queue remains unfinished. Export:
`/workspace/h62-artifacts/generic-internalflow/embedded1/` with cumulative patch,
handoff and SHA256 manifest; prior exports preserved.

## Embedded classification tranche 2: prefix Checks

All original declarations in ParentPrefixes.Checks (100–172: 3 theorems,1 fixture),
AllocatingPrefixes.Checks (114–250:12,4), and MutatingPrefixes.Checks
(102–349:22,12) are classified and conserved. Total54 declarations=37 theorems+17
fixtures; cumulative classification674 original theorem declarations+378 fixtures.
These are not independent execution counts. Other embedded controls remain pending;
full checkpoint1 is partial and the proof/migration/measurement queue unfinished.

Map: `tests/h62/item4/generic-internalflow/prefix-cases.txt`; expander `prefix.py`
in the assigned scripts directory. The boundary checker now accepts explicit
region/facet parameters; default four-region output is unchanged. Prefixes add
no Continuation conclusion. Preserve running versus stopped loop horizons; source
write/evaluation success versus target activation success; actual Heap.Keeps versus
length-only preservation; and failure of a particular GrowsAllocator budget versus
missing ownership or incorrect computed cost. The full source headers remain
authoritative for all conjuncts. Audit9/11/16 dispositions retain the prior semantic
limits and do not approve any refactor or semantic decide table.

Independent read-only finder and skeptic PASS (no Lean/server/builds/writes).
All54 records retain every original inventory field, ordering and hashes; final
expansion matches source map. Acceptance passes22 tests and deterministic full
reproduction; original271 family files remain byte-identical. No new Lean checks.
Historical KeySort success and unchanged Raw dependency failure remain historical,
not new passing semantic gates. No RUNTIME_GATE_PASS, new axiom/sorry, raised budget,
original edit or timing delta.

Evidence: `/workspace/h62-evidence/generic-internalflow/embedded2/acceptance.log`;
`prefix-inventory.json` SHA256
`47c090ad626e9419d272bdba97a1cd1a5d94ea8200dbdb7e35d4fdd11755c2a8`.
Cumulative/incremental patches and handoff:
`/workspace/h62-artifacts/generic-internalflow/embedded2/`, with SHA256SUMS.

Raw notice is recorded in `raw-prerequisite-notice.json` under assigned tests.
Reported source074e62c1840dd2d7ab19c95ca5d437ebfe57dbb8 and patch hash are
user-relayed metadata, not locally verified/applied artifacts. Thirty reported
axiom-growth entries require root review; no trust acceptance or holds lifted.
Wait for reviewed migrate-syntax Raw prerequisite and current Claude V12 exact-file
agreement for the two no_ref/no_struct files. Current-owner delivery to
`claudecloud/move5-20261106/v12-p1` remains pending; host journals determine acceptance.

Fresh-thread handoff is ready after four completed census/classification work
items. Coordinator should continue this exact VM, branch and existing goal; no
replacement goal/thread is self-launched. Next independent read-only work remains
unclassified embedded Checks/Client regions, with explicit region inventory and
full per-declaration semantic accounting. Do not declare full checkpoint completion.

## H82 retirement checkpoint

No new proof implementation. Prior implementation head c98a7d018f528c9b049d32ee82baa40ea4aa7f6d.
Only handoff records/owner-request dispositions changed. Original visible assignment,
full work/backfill queue, original owner map, scope manifest and all open obligations
are committed under tests/h62/item4/generic-internalflow/handoff/. Prompt provenance
explicitly states that byte-exact frozen rendered SHA verification is unavailable;
the visible assignment was reconstructed from this thread, not a coordinator-local
path. The recorded rendered SHA is provenance only, not a verified file digest.

Retirement handoff_to solidity-inline-assembly5-20261031/vy4-world. Integration
belongs to successor after final stopped/head acknowledgement. The later generic
continue instruction conflicts with explicit retirement; clarification requested,
and only safe handoff packaging performed. Implementation stopped. No new goal,
VM, thread, source change, proof or push. H71 original-lane push permission is not
available; original no-push remains binding. No master push.

H82 standing agreements withdraw proof-only exact-file agreement requests; owner
permission still governs statement, dependent definition, interface, budget, axiom
and exclusion changes. Raw remains unapplied with30axiom-growth entries awaiting
root review. ClaudeV12 current-owner forwarding is staged, not agreement. No Claude
source edit/message. All original files and evidence preserved.

Goal PAUSED could not be set: the exposed goal tool accepts only complete|blocked;
no pause/update/get tool exists in this context. Do not interpret local stopping
as a successful persistent-goal pause. No complete/block transition substituted.
No automatic implementation continuation is authorized under the retirement order.

Final sealed export: /workspace/h62-artifacts/generic-internalflow/retirement/,
with cumulative patch, lane.bundle, full handoff input files, evidence archive,
open-items.json and SHA256SUMS. Earlier artifacts remain intact. No Lean recheck or
known timing STOP rerun for these handoff-only changes. Historical validation
boundaries remain; full assignment is unfinished.

## Successor world/rollback provenance tranche

Read-only source census at successor input 371ac25a44ae9a77500da2308229992a675ac508. This tranche classifies three additional producer boundaries; it does not extend the prior 674-theorem/378-fixture totals or claim exhaustive embedded-control coverage.

| Actual declaration/module | Established boundary | Still required |
|---|---|---|
| `Backend/Transient/SourceFrames.source_body_exact`, `source_static_child` | Actual `Source.writeAt` primitive bodies, with explicit parent/child static flags; static child retains the prior parent write. | Actual G42 call entry, ABI dispatch, environment outcome and complete callback adequacy. |
| `Yul/World/TransientTargetRollback.store_rollback` | An actual successful `transientSlotStore?` preparation, explicit nonstatic frame, and coupled Source/residual/target rollback restore the complete local input. | Universal preparation/layout, callee reachability, full-bank and transaction adequacy. Its checked preparation premise is not a desired callee outcome. |
| `Yul/World/PendingCoupling.WorldLogAt` | Signature only: full physical relation, actual G42 Step, complete Source execution, ordered observations and successful-target endpoint are producer fields. | A concrete instance proving those fields, including source-origin and owner-reviewed G01/H25 observation relation. |

`Backend/WorldCalls/Premises` explicitly supplies conditional interfaces rather than an executable world CALL producer. An inhabited primitive body or checked local store is therefore not evidence that `WorldLogAt` is inhabited. Source raw halts keep their own bytes; only completed outcomes constrain the last-returndata field. Coarse target revert/fault has no invented machine endpoint.

No Lean declaration, proof, evaluator, statement or budget changed. Migration compatibility remains with migrate-root-gate (`Syntax/Raw.lean` and reported axiom growth); this source census does not accept that prerequisite.

## Successor Client failure-stage tranche

Read-only accounting after published-master adoption; no original theorem or prior census total changed. These two explicit `Client` regions distinguish argument failure from callee-write failure. Names below are lexical declaration accounting, not a Lean completeness oracle.

- `RuntimeFrameV3OrderedArgumentFailure.Client`: `checked_failure`, `image`, `source`, `target_suffix`, `target`, `program`, `whole_source`, `whole_target`, `failure_stages`, `source_not_exhausted`, `target_not_ok`, `target_not_fault`, `zero_control`. Raw source SHA256 `b1ad0c1702c629e9aff090f9486303188f3363a1dcafb149079fe905ed285094`.

- `RuntimeFrameV3EffectfulScalarFailure.Client`: `arguments`, `actual_write_failure`, `source`, `write_code`, `target`, `program`, `whole_source`, `whole_target`, `arguments_not_failure`, `source_not_exhausted`, `target_not_ok`, `target_not_fault`, `zero_control`. Raw source SHA256 `9feb953f97636546175128d2396a1e65769b46adfdcd851e89b2ac8a174de3c5`.

OrderedArgumentFailure: `checked_failure` retains failing argument evaluation, every function/depth/destination and every target suffix. `source`, `target_suffix`, `target`, `whole_source` and `whole_target` transport that same actual failure through the prepared prefix; `failure_stages` contrasts the valid literal count. The not-exhausted/not-ok/not-fault observations and `zero_control` preserve the distinction from a genuinely shallow recursive call.

EffectfulScalarFailure: `arguments` actually succeeds; `actual_write_failure` is a concrete heap-write refusal. `source` and `target` therefore locate failure in the callee write, not argument decoding. `write_code` pins the selected writer; whole-program lemmas retain the preparation prefix. `arguments_not_failure`, `source_not_exhausted`, `target_not_ok`, `target_not_fault` and `zero_control` preserve all contrasts. Neither region supplies Source panic bytes, G42 callback execution, monetary rollback or a target reverted machine.

Generalization must keep the stage-specific actual argument/write evidence and original depth/suffix quantifiers. It must not collapse both failures into an unqualified supplied revert result. Full semantic correspondence, axiom audit and comparable timings remain open.

## Successor ArrayProbe embedded region

Explicit region: `RuntimeFrameV3ArrayProbe.lean`, `Checks` namespace, from its explicit opening through `end Checks`. Source hash: `6a5c206775042a7ca8577b63685a79c3f569327bed78deb86d1479d7f311f3f2`. This is one bounded region, not completion of the embedded census; previous aggregate counts remain unchanged.

Fixtures: `F` and `input` alias the existing Countdown/AllocatorReturn fixture; `bad` writes local count3 and `badMachine` writes word3 at cell3. `bad_repr` proves the actual full StateRepr after that local change; `bad_ownership` separately preserves the struct allocator relation. These are initial representation facts, not successful bounds/admission assumptions.

`good_evaluated` reads the actual indexed value9; `bad_evaluated` is actual coarse source revert. `good_read` executes the public selected code with word9 pushed. `wrong_read` rejects word7 by observing the pushed stack head, rather than an execution-only projection. `bad_not_exhausted` distinguishes the failed read from exhaustion. `good_target` proves the read-and-pop code restores the entire input machine. `bad_target` retains arbitrary target suffix and proves revert using `failure_suffix`. No reverted machine or panic payload is invented.

All nine theorem declarations and four fixture declarations are retained in this accounting. A generic migration must preserve both representation relations, the different good/bad inputs, full success machine and arbitrary-suffix failure. No producer implementation, theorem, fixture or proof budget changed; kernel acceptance and comparative timing of any future helper remain separate obligations.
