# H62 item 2: v07-lowering audit — blocked proof validation, preliminary backfill

Repository: /workspace/solidity-lean
Branch: codex/solidity-h62-2-20261106/audit-v07-lowering
Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4
Initial checkout: clean branch work at 6cf853aea0417155aca29ddb91f1767d3f3a3cc4. Fetched origin/master at 821e3e8f4c7a5ac3a51dc5cba8be813bb173e310; git merge-base --is-ancestor BASE origin/master exited 0. Created assigned branch at BASE without resetting existing work.

This is a reviewable tooling checkpoint, not completion of any of the four audit checkpoints. No frozen statements touched; no Lean declarations/helpers added; new sorry/axiom count zero. No registered roots, central maps, cache pins, producer originals or H55 work changed.

## Queue and evidence boundary

1. Inventory: partial lexical backfill, 162 mapped modules / 968 theorem/lemma tokens, each unique by file and offset. All candidates retain pending premise classification, simultaneous witness and elaborated statement fidelity. Local names and source-tail hashes are NOT exact frozen signatures. Structure-field contracts, fully qualified names, inherited section parameters and interface/hypothesis classification remain to do.
2. Simultaneous witnesses: pending; no proof claimed. Unchanged dependency migration prevents checking the full mapped import closure.
3. Supported-program success/totality: pending, including reject-all/always-revert negatives and observable failure/gas/fork boundaries. No fabricated supported-program premise.
4. Verified witness/fidelity census: pending; all 968 candidates currently uncovered, owner V07 (v07-v11/v07-lowering), subject to exact statement classification. This count is preliminary and includes statements without hypotheses. It is not an exhaustive interface-contract certificate.

No V07 theorem has been established weakened/vacuous in this checkpoint, so no vacuity ESCALATE is invented. DEP-MIGRATION-001 is an external dependency compiler blocker. Static backfill remains possible and unfinished; this handoff does not assert every backfill obligation is blocked or complete.

## Reproduction and actual gates

All evidence under /workspace/h62-audit-v07-evidence, bulk off Git. All five coordinator-input hashes matched sha256.json. Official archive SHA256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d matched toolchain-pin.json.

- Branch/base/remote ancestry check: pass, git merge-base --is-ancestor BASE origin/master, exit 0.
- Official lean --version: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release. lake --version: Lake 5.0.0-src+eb6cafb (Lean 4.35.0).
- KeySort: LEAN_NUM_THREADS=1, ulimit -v 12582912; official lean -j1 --tstack=131072 Solidity/KeySort.lean: exit 0, Bash real 1.235s. Output keysort.log. Initial timing wrapper exited 127 because /usr/bin/time absent; rerun used Bash time.
- census.py --output /workspace/h62-audit-v07-evidence/census.json: exit 0. Repeated to census-repeat.json; cmp exit 0, deterministic 162/968. census-check.log.
- PYTHONDONTWRITEBYTECODE=1 flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/h62/item2/audit-v07-lowering/check-imports.py --repo /workspace/solidity-lean --toolchain /workspace/h62-audit-v07-evidence/toolchain/lean-4.35.0-linux --evidence /workspace/h62-audit-v07-evidence/import-check: exit 1. First unchanged module Solidity.Hash.CollisionBound fails after 3.414s; import-check/results.json records exact argv, source hash and timing. Details in owner ticket.
- Full ./run-lean.sh, affected Lean proofs, acceptance, axiom checks and before/after timings: pending. No RUNTIME_GATE_PASS or full gate claim. No refactor made; comparative timing delta unavailable. Do not infer <=10% slowdown from KeySort.

Runtime: approximately 17GiB visible memory, no system swap, enclosing cgroup memory.max=17179869184. Compiler serial with -j1, LEAN_NUM_THREADS=1, 12GiB address-space cap, four-GiB available-memory checks every 0.1s, 300s per module. No systemd-run or old v4.24 cache used. Direct compiler driver checks frozen import closure only, not repository acceptance. No Lean MCP exposed.

## Reviews and handoff

Independent read-only finder and skeptic confirmed counts and pending boundaries. Both found resource-monitor/result-recording gaps; fixed. Both found a stale status variable after the fix; corrected and reproduced compiler exit 1. Final reviews confirm no remaining tooling findings for this run. Full review summary: /workspace/h62-audit-v07-evidence/reviews.txt. Neither used Lean/server or changed files.

Owner ticket: tests/h62/item2/audit-v07-lowering/owner-ticket.md. relay.sh absent; ticket saved for coordinator retrieval, not sent. No source-edit authorization assumed. Resume on this same branch/base with coordinator-supplied statement-preserving migration overlay; never silently change base or toolchain. The original persistent goal was supplied; get_goal absent and optional per coordinator, no new goal created.

Artifacts: /workspace/h62-audit-v07-evidence/original.patch; handoff.json (full committed head/base/paths); SHA256SUMS. No push, merge, PR, pre-gate or deployment. All four checkpoints remain unfinished.

## H70 static backfill checkpoint (2026-11-06)

The coordinator accepted DEP-MIGRATION-001 via solidity-h62-6-20261106/migrate-hash. Continue waiting for that owner's statement-preserving CollisionBound migration repair; no original-file edit permission is assumed. relay.sh is host-only and requires no VM installation.

New source_inventory.py records exact source headers and hashes for all 968 mapped theorem candidates (964 := bodies, four equation-style declarations), provisional source-qualified names, active namespace/section variable/open commands, original context offsets and source-prefix hashes. These are exact source slices, NOT elaborated signatures. Every theorem occurs once in the mapped list. No inherited context variable is silently assumed to enter the elaborated theorem.

Seven mapped structures with 32 fields now have exact header, complete contract and field slices/hashes. Supplemental imported DeclarationGraph.lean has one structure/13 fields and four helper theorems in separate arrays; it is not a new mapped-module row or expanded proof lane. No source registration changes.

All 6,254 explicit theorem binder groups receive one provisional source category. Categories distinguish a global P8a.Producer contract (15 signatures), request-indexed contracts, indexed environment/context certificates, environment support predicates, relation parameters, per-input predicates and data/type parameters. Result-type arrow domains, quantifier tokens and inherited-variable evidence are retained separately. Syntactic categories are NOT an elaborated hypothesis census, propositionhood certificate, inhabitance evidence or simultaneous feasibility proof. All semantic classification and witness statuses remain pending. Counts and the exact 15 producer names are in premise-summary.json off Git.

P8 source warnings were checked against ResourceContractLaw1.nat_encodable_resource_impossible. That theorem requires encode/decode/roundtrip for S.lang.Res; the generic V07 statements quantify over arbitrary S. A current-Nat warning does not prove every generic Producer impossible. In particular scalar_value and source_assignment_run keep their explicit producer binders despite not using them in proofs; their statement witnesses must still provide a producer. No frozen statement was changed and no encodability premise was added. No new theorem was established vacuous, so no unsupported vacuity ESCALATE is emitted.

verify-source-inventory.py checks all frozen source/module-map hashes, signature slices/hashes, source-prefix hashes, context offsets, full contract slices/hashes, all field slices/hashes, independent line-oriented mapped declaration counts, unique identities and the 15 explicit producer-bearing signatures. It includes the confirmed trailing-field-documentation boundary regression. Generation repeated byte-identically. Commands, actual exits (0), timing and decisive output are in static-checks.json and source-verify.log. This is static artifact consistency only. No Lean checks were repeated while the producer-owned import dependency remains failing; previous KeySort pass and import failure remain the latest runtime evidence. No before/after proof-time claim or RUNTIME_GATE_PASS.

Required independent finder and skeptic reviews ran read-only without Lean. Finder confirmed exact map equality/counts and found following-declaration docs in final field envelopes; fixed by trimming trailing trivia. Skeptic requested checks for new full-contract, prefix and map hashes; added. Final review evidence saved as static-reviews.txt. Semantic premise review, simultaneous witnesses, successful totality/negative controls and elaborated fidelity still require work; all four main checkpoints remain unfinished. No new Lean declarations, sorry or axioms, no frozen-interface edits. Static backfill is a reviewable source-inventory checkpoint, not completion of the original assignment.

Review scope clarification: the 6,254/11-category/no-unresolved result covers explicit binders in mapped theorem signatures only. Four structure-parameter classifications remain unresolved in Admission (S, reference, origins, roots); these are retained, not hidden. Supplemental rows are not counted in the mapped theorem statistic.

## Inventory completion handoff after coordinator resume (2026-11-06)

Before this item, git fetch origin master succeeded, reaching 5f7bb1441. Inspected the latest log and code differences: no upstream audit counterpart, no V07 mapped source changes and no CollisionBound repair. Therefore the coordinator's conditional rebase instruction did not trigger; retained the isolated assigned branch and exact frozen base. Full observed master SHA, commands, exits and decisive empty relevant diffs: /workspace/h62-audit-v07-evidence/master-inventory-check.json.

Finished the remaining source-only inventory item: four Admission parameter groups now have categories sourced from their imported definitions: P8a.Spec (global specification), P8a.OperationalReference (independent global operational reference), P8a.SourceOrigins (global origin interpretation), and P8a.RootModel (global root/feature model). These categories do not assert inhabitation or adequacy. All mapped/supplemental explicit binder groups now have a syntactic category; semantic classification remains pending. The previous four-unresolved note is historical and superseded by this section.

Added dependency_inventory.py for selected supplemental imported contracts only: 17 exact definitions / 82 fields (Spec alias; eight P8 structures; Roadmap SourceSpec, five predicate definitions, Admission and CheckedFrontend). This is not a transitive dependency closure or a new proof scope. Exact declarations and field source/hashes are in dependency-inventory.json off Git. Producer still requires its failure projection, source realization, extraction, checked frontend, admission, agreement, unambiguous/approved/all-pipeline/nonvacuous laws simultaneously. Each selected contract retains unproved inhabitation and pending elaboration; individual field availability proves no producer witness.

Final static checks pass: both generators reproduce byte-identical outputs; verifier checks source/header/contract/field ranges and hashes, identities/duplicates and frozen counts, including the optional 17-definition/82-field check. Exact commands, exit 0, generator timings and decisive output: inventory-final-checks.json and inventory-final-verify.log; source-verify.log refreshed with the same complete output. No new Lean execution, no proof-time comparison or runtime-pass claim. Required finder and skeptic reviewed independently without Lean; stale artifact regenerated and supplemental verification output saved. See inventory-final-reviews.txt.

Source extraction has no remaining confirmed defect within the delivered mapped census and explicitly selected imported contracts. This does not complete checkpoint 1: semantic hypothesis classification and exact elaborated signatures/fidelity remain pending. Checkpoints 2–4 and all original proofs/controls/full validation remain unfinished. No new Lean declaration/helper, sorry or axiom; no original/central registration edits.

Typed blocking dependency: DEP-MIGRATION-001, owner solidity-h62-6-20261106/migrate-hash, exact file Solidity/Hash/CollisionBound.lean; AcceptedGraphProducer -> P8Bindings -> P8.FrozenInterface -> Roadmap.Contracts -> Hash.CollisionBound. Await that accepted owner repair, with exact commit/overlay and validation, before rerunning affected import/proof gates. No generic Producer impossibility, Nat encodability premise or missing reference implementation is invented as a new theorem assumption.

This is the third committed work item in this thread. Fresh-thread handoff is to the coordinator on this exact VM, branch and original existing goal; do not create/reset a goal or self-launch a replacement. Coordinator resumes when the producer dependency lands. Exported original.patch, handoff.json and SHA256SUMS remain at /workspace/h62-audit-v07-evidence. Final report and handoff.json record full committed head. No merge/push/publication.
