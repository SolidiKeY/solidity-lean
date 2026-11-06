# H62/H63 Source migration overlay

**Overall blocked; original goal incomplete.** Sole migration lane owner:
`solidity-h62-6-20261106/migrate-source`. Branch:
`codex/solidity-h62-6-20261106/migrate-source`. Published base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Checkout: `/workspace/solidity-h62-6-migrate-source`.
The older clean `/workspace/solidity-lean` work checkout is preserved.
Base ancestry against HEAD and fetched origin/master passes. No push, merge,
PR, publication, pre-gate, ownership transfer or cut-over has occurred.
All original Source files and tracked lean-toolchain remain byte-identical to base.

## Checkpoints

| Checkpoint | State | Decisive evidence |
|---|---|---|
| 1 Census and clean old baseline | Done, with bounded evidence below | All 199 assigned Source modules / 246 local prerequisites pass; complete old type ledger and hashes |
| 2 Official release adaptation | Blocked | Exact official pin installed; isolated Ctor repair passes; external dependencies fail; H78 public shim compatibility incomplete |
| 3 New full build and matched timing | Blocked | 15 target modules pass, 3 fail, 228 import-blocked; no complete target run or valid timing delta |
| 4 Reviewed migration handoff | Partial | Reviewable unapplied proof patch, tooling and diagnostic artifacts ready; integration/whole migration gate unfinished |

Evidence directory: `/workspace/h62-migrate-source-evidence`.
All coordinator inputs passed their supplied sha256.json. Official target archive:
lean-4.35.0-linux.tar.zst, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake 5.0.0-src+eb6cafb. Actual bounded KeySort passes in new-keysort-final.
Baseline: official Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. Old archive SHA256
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.
Absolute private compiler paths select releases; no tracked toolchain edit.

## Complete old census, proof build and boundaries

The pinned census has exactly the 199 explicitly assigned files: 4,428 lexical
candidates, 47 external local prerequisite modules, 11 external direct imports,
and 489 external consumer edges. Independent import-header reconciliation and
comment/string/order negative controls pass. Lexical candidates are navigation,
not elaborated proof or witness coverage.

Clean old run old-clean-04 passes all 246 modules, including all 199 Source modules:
wall **2275.218421954 s**, sampled peak group RSS **8263950336 bytes** (7.70 GiB).
Horizon alone: 705.884 s, same peak RSS. The complete imported-constant ledger has
**17,542 entries** across all 199 requested Source modules. It includes constructors,
recursors, equations, instances and declarations in other namespaces defined here.
API capture passes. Raw ledger api-full-old.json is 666 MB, intentionally off git.
frozen-interfaces-old.json records per-declaration SHA256; frozen-source-files.sha256
freezes every original file, including statements, definitions and budgets.

This is a clean olean/proof-elaboration build of the assigned closure. It is not
native executable compilation, the repository-wide run-lean.sh final gate, a new
H70 simultaneous-hypothesis witness audit, or a source-to-EVM correctness theorem.
No new-toolchain all-directory success or RUNTIME_GATE_PASS is asserted.
No Lean MCP tools are exposed; bounded CLI per-file diagnostics are used.

## Resource and timing reproducibility

Use scripts/h62/item6/migrate-source and tests/h62/item6/migrate-source.
The VM hard cgroup cap is 16 GiB; CPU quota is four; no system swap. One heavy job
at a time, LEAN_NUM_THREADS=1, explicit -j1, tstack 131072, Lean heap 10000 MiB,
4 GiB available-memory reserve, and a sampled 12 GiB group-RSS stop. The latter is
a watchdog, not a kernel cap. No systemd-run. Writer lock spans every heavy check.
Both executables and import paths are forced after lake env; no master cache.
Reports retain exact commands/exits, RSS peaks sampled at 50 ms, diagnostic VMS, actual
versions and release archive hashes. Fixture reports bind SHA256 before launch
and check input stability afterward.

Before either accepted full measurement, use identical clean-page preparation:

```sh
python3 scripts/h62/item6/migrate-source/cold-cache.py \
  /workspace/h62-migrate-source-evidence /workspace/.setup/tools/lean-4.24.0-linux
```

Only task-private clean pages are advised for eviction; no files or global cache
settings change. build.py --out must name a fresh directory; its private LEAN_PATH
excludes workspace/shared artifacts. The comparison script requires both complete
passing runs, exact module order, matching resource profile and census base,
correct old/new versions, and the coordinator target archive SHA. Every regression
escalates; >10% stops. Invalid/incomplete runs cannot produce a timing pass.
Actual before/after comparison and delta remain **pending/undefined**.

Failed preparation runs remain explicit failure evidence: old-clean-01 was stopped
for tooling fixes. Old-clean-02 hit the reserve in Horizon at per-module 389.706 s
(whole failed run 972.143 s), with 7.3 GB provisioning clean cache present.
Old-clean-03 failed std::bad_alloc at per-module 461.294 s / 5606068224 RSS bytes
(whole run 1013.790 s); cgroup OOM/max counters were zero. Its self-imposed 12 GiB
virtual-address limit incorrectly stood in for RAM. The corrected single-file
probe passed 715.030 s, 8110936064 RSS bytes, 16827170816 virtual bytes, inherited
RLIMIT_AS unlimited. It reused imports and is not an accepted clean baseline.
The complete old-clean-04 independently validates the corrected resource setup.
Neither resident nor proof budgets were raised; AS reservation is not RSS.

## Concrete proof-only candidate and owner delivery

Committed proposal: tests/h62/item6/migrate-source/ctor-candidate.patch.
Patch SHA256:
`4eae67d556a0f322499c3695b0db0582cf259c08d1e55b2ea9d41dce96f55881`.
It changes only Syn.nodes_eq and Syn.excl_ctor proof bodies, including two unused
simp arguments. All definitions, theorem headers, premises, exclusions and
observations stay unchanged. The full 112-constructor completeness proof remains.
Constructor-head congruence avoids recursive simplifier expansion; explicit Bool
cases handle the changed conditional elimination. No maxHeartbeats increase.
History inspection found S00 construction/review commits, no speed fix undone.

Final isolated fixture SHA256:
`92a08a3c6879c88df6b1a6720fa0dc284e453c286fe384ee8b3471cb29657247`.
Old check: exit0, 56.030609418 s, 1502949376 sampled RSS bytes.
New check: exit0, 22.954620345 s, 680759296 bytes. Both headline theorem axiom sets
are exactly [propext]. These are isolated fixture observations, not all-directory
before/after timing. The first rejected candidate's errors/sorryAx printouts remain
failed evidence and are never treated as accepted proofs.

MS-OWNER-CTOR requests coordinator/live Source producer agreement before editing
only this original file. Original Source/Ctor is still unchanged and still fails
new-toolchain compilation. The candidate is reproducible from the exact base with
ctor-fixture.py. No direct owner delivery or original-file permission is claimed.
relay.sh is host-only, not a worker installation task. owner-requests.json records
exact files, patch paths and hashes for coordinator retrieval.

H70 audit-v10-storage, audit-roadmap, migrate-roadmap and migrate-root-gate pings
were acknowledged with the committed patch/head/hash. Only their supplied excerpts
were received; the full staged Roadmap payloads have not been obtained or reviewed.
Their witness/totality/gas/fork queues remain their owners' work.

## Cross-directory failures and generated-use validation

new-diagnostic-01: **15 pass (5 Source), 3 fail, 228 import-blocked**.
MS-DEP-HASH: migrate-hash owns CollisionBound, with contains equality failure at407,
omega failures at660/680 and failed-elaboration guard-message mismatches.
MS-DEP-SYNTAX: migrate-syntax owns Raw, with String/Slice changes at597/650/665/682/684.
No outside-scope original was edited or silently repaired. Source/Ctor fails at641
(timeout at the original200000 budget) and715 (dependent conditional elimination).
Await owner-reviewed external overlays and Source original-file coordination.

Partial old/new inventories explicitly say complete=false and request 5/199 modules:
2365 old entries,2422 new;18 missing names,75 additions,555 changed raw type/universe
records,1792 identical. Independent reviews matched139 explicitly named authored
declarations with identical raw types. This is bounded evidence, not full-directory
compatibility. Missing16 enum toCtorIdx helpers and2 hygienic names remain compatibility
reconciliation items under H78; generated origin does not waive public APIs.
All555 changed rows are generated, but not all changes are alpha/formatting:
Syn.noConfusion and FrameBudget.noConfusionType change argument structure; Q.isInt's
generated equation uses a changed BEq Int instance. Under H78 these public generated differences require compatibility preservation;
source-written statements and proof budgets remain frozen.

**H78 supersedes the earlier Q-MS-API-01 answer. Generated public API is
frozen too.** Compatibility shims must keep the old shapes available to existing
users; do not edit users to accommodate changed generated signatures. Authored
statements, semantics, proof/resource budgets and trust policy remain unchanged.
The earlier exemption and its receipt are historical, not current authority.
Each shim must be listed with its name and old/new signature for cut-over review.
The complete old raw declaration ledger remains a reference superset; public versus
private/generated classification still needs semantic verification, not regex waiver.

A bounded semantic bridge in IntegerInstanceSemantics checks Q.isInt=true iff its
numerator modulo denominator is zero, plus an inhabited zero positive control,
on both releases. It certifies only that contract. Standard axiom closures differ:
old spec [propext,Quot.sound], old zero []; new spec/zero
[propext,Classical.choice,Quot.sound]. No new axiom declaration, sorry,
native_decide, trust-policy change or axiom-pin edit was introduced. The standard
closure change is retained for root classification rather than hidden.

## Reviews, checks and resumption

Independent finder and skeptic used no Lean server/jobs and made no edits. They
found and confirmed fixes for workspace cache precedence, missing resource-stop
rows, compiler path/fixture hash binding, path-containment checks, incomplete timing
acceptance, release/base identity and partial-ledger labelling. They accepted the
proof-only Ctor approach and identified the generated API/axiom-closure limits.
Final finder/skeptic review accepted the stated proof/evidence boundaries. Both
requested a deterministic fingerprint generator and precise peak-sampling wording;
those findings are fixed before export.

Layer check passes:857 core modules reach neither elaborators nor checked-parser
adapters. Generated-root and fragment checks pass. Repository doc-path check fails
one **pre-existing, unchanged, out-of-scope** optional Mathlib citation in
feature-work/after-roadmap-va1.md; see MS-DOC-EXTERNAL. No such fix is authorized here.
New scoped document paths and git diff whitespace checks must pass before export.

Resume the original persistent goal on this same VM/branch. Do not reset/create a
goal or self-launch a replacement thread. Root/coordinator must resolve owner
coordination and external migration overlays. Then apply approved
proof repair, recheck every assigned module under the exact official release,
reconcile frozen interfaces and standard axioms, run matched clean old/new metrics
and required full affected/repository gates, fix reviews, and complete the root-gate
handoff. Fresh-thread handoff goes to the coordinator. No partial checkpoint or
failed required gate constitutes full assignment completion.

## Fingerprint reproduction

```sh
python3 scripts/h62/item6/migrate-source/fingerprints.py \
  /workspace/h62-migrate-source-evidence/census-base.json \
  /workspace/h62-migrate-source-evidence/api-full-old.json \
  /workspace/h62-migrate-source-evidence
```

Each row hash is SHA256 of its complete raw ledger record encoded UTF-8 after
json.dumps(sort_keys=True, ensure_ascii=False, separators=(",", ":")). The outer
manifest uses sorted keys/indent2. Partial ledgers are rejected; requested modules
must equal the assigned census and current source bytes must match every frozen
file SHA. This algorithm hashes compiler representations without asserting
cross-version semantic equality. Bulk outputs stay off git; the generator is tracked.

## Generated declaration source-use inventory after clarification

generated-uses.py scans exactly the199 owned files, masks comments/strings, and
records qualified/receiver direct-spelling candidates with line/column and enclosing declaration
candidates. It includes recursors, matchers, constructor injectivity, equation
names and ctorIdx. This is lexical navigation, not Lean name resolution; both unqualified explicit references and implicit
tactic/elaborator references are omitted. Current pinned source has364
candidates;67 ctorIdx references are in Horizon. No source originals changed,
so **adapted generated-declaration source uses on this branch: []**.

The Ctor proposal still contains only proposed proof-body adaptations to
Syn.nodes_eq and Syn.excl_ctor, validated in an isolated fixture. It remains
unapplied and is not recorded as an accomplished Source edit. Target Source file
checks, including implicit generated uses, remain blocked by the saved Hash/Raw
owner dependencies and original-file coordination. H78 prohibits adapting existing users to generated signature changes; future
compatibility shims must enter the cut-over manifest with name/old/new signature
and proof/statement-budget validation. This preparatory audit rejects every tracked or untracked Source difference.
It does not accept or validate an adaptation manifest; that validator remains
future work when approved original-file changes are available.

The latest H70 tickets add consumers, not edit/Lean-restart permissions. The
migrate-lowering full handoff was requested by exact coordinator staged path and
SHA in the updated receipt; it has not been delivered or reviewed. Existing
performance/trust STOP dispositions remain untouched. No new Lean runs were made
for this policy/documentation update.

## H78 compatibility work and retained STOP

The H78 receipt is /workspace/h62-migrate-source-evidence/h78-compatibility.
h78-shims.py deterministically reproduces the prototype fixture/Source.Syntax
proposal and complete signature manifest. No Source original or user was edited.
The16 old toCtorIdx names are absent in4.35, and every old raw function type equals
the replacement ctorIdx type. Conditional test declarations restore the exact old
names in the new isolated environment and preserve existing declarations in old.
All16 constructor-exhaustive pointwise equality proofs pass both compilers, with
no axioms, using fixture SHA2d36de90b3aa57f7643c1c3e6639c666426eedffc67efb10f3d01e167d078310.
These are **type/value prototypes, not accepted unchanged-user API shims**.

Finder identified missing alias metadata: old aliases are protected, reducible
abbreviations, while the prototype uses plain def. Old ctorIdx itself was reducible;
new ctorIdx is regular. Reducible/protected behavior, deprecation and completion
metadata need reconciliation and new validation after STOP disposition. A simple
alias to the new target must not be called full backward compatibility yet.

The old-shaped H78Compat.Syn.noConfusionType/noConfusion namespace candidates do
not restore original public names. The old-role check fails executable generation
for noConfusion and its example; a noncomputable correction is unvalidated.
The new-role check was not run. Empty printed axiom lists after this failed run
are not a passing proof gate. The official compiler automatically installs changed
original-name declarations; duplicate replacement is rejected and exact qualified
name resolution returns the real constant before fallback aliases. Namespace-only
wrappers cannot satisfy H78. A root-owned supported naming/generation strategy is
required under the same official compiler and dependency-free-core constraints.

**MS-H78-SHIM-PERF-STOP:** old fixture wall4.404726603s, new5.213439807s
(+18.3601226%); sampled RSS645775360→1652035584 bytes (+155.8220221%).
The old role skips existing declarations while the new role elaborates16 extra
prototype defs. This is not an attributable full Source regression comparison;
the observation nevertheless retains STOP. No further Lean checks or repeated
measurements are authorized by inference. Root review/disposition is pending.

The16 public-name prototypes below all have old signature and proposed shim
signature T→Nat (new4.35 original name absent; replacement T.ctorIdx : T→Nat):

| Name under Solidity.Source | Old signature | Proposed shim signature |
|---|---|---|
| AddOp.toCtorIdx | AddOp → Nat | AddOp → Nat |
| AssignOp.toCtorIdx | AssignOp → Nat | AssignOp → Nat |
| Constness.toCtorIdx | Constness → Nat | Constness → Nat |
| CtorVis.toCtorIdx | CtorVis → Nat | CtorVis → Nat |
| DataLoc.toCtorIdx | DataLoc → Nat | DataLoc → Nat |
| Denom.toCtorIdx | Denom → Nat | Denom → Nat |
| EqOp.toCtorIdx | EqOp → Nat | EqOp → Nat |
| MulOp.toCtorIdx | MulOp → Nat | MulOp → Nat |
| Mutability.toCtorIdx | Mutability → Nat | Mutability → Nat |
| OrderOp.toCtorIdx | OrderOp → Nat | OrderOp → Nat |
| PrefixOp.toCtorIdx | PrefixOp → Nat | PrefixOp → Nat |
| ShiftOp.toCtorIdx | ShiftOp → Nat | ShiftOp → Nat |
| StateVis.toCtorIdx | StateVis → Nat | StateVis → Nat |
| SuffixOp.toCtorIdx | SuffixOp → Nat | SuffixOp → Nat |
| UserOp.toCtorIdx | UserOp → Nat | UserOp → Nat |
| Visibility.toCtorIdx | Visibility → Nat | Visibility → Nat |

All16 remain unapplied and incomplete for H78 because of the documented metadata
findings. The separate failed shape candidates have these signatures:

| Candidate (not original public API) | Legacy shape | v4.35 original generated shape |
|---|---|---|
| H78Compat.Syn.noConfusionType | {c : Cat} → (P : Sort u) → Syn c → Syn c → Sort u | (P : Sort u) → {c : Cat} → Syn c → {c' : Cat} → Syn c' → Sort u |
| H78Compat.Syn.noConfusion | {c : Cat} → {P : Sort u} → {x y : Syn c} → x=y → legacy noConfusionType P x y | {P : Sort u} → {c} → {x : Syn c} → {c'} → {y : Syn c'} → c=c' → HEq x y → new noConfusionType P x y |

No production shims have been installed or accepted. Source/Ctor's earlier proof
proposal stays unapplied and is not a substitute for H78 public API compatibility.
Other generated public signatures across199 modules remain to reconcile after
owner overlays, permission and STOP resolution. Goal remains incomplete.
