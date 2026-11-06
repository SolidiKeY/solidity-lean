# H62/H63 SortCheck migration — reviewed blocked handoff

Batch `solidity-h62-6-20261106`, owner `migrate-sortcheck`. Overall **blocked, full goal unfinished**. This isolated migration overlay does not transfer live producer ownership. Production SortCheck, statements, premises, observations, proof budgets, toolchain/Lake files, roots/maps and axiom pins are unchanged. No push, merge, PR, pre-gate, freeze or publication.

## Checkout and continuation

Base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; assigned branch `codex/solidity-h62-6-20261106/migrate-sortcheck`; checkout `/workspace/migrate-sortcheck`. Base fetched and verified ancestor of published origin/master before branch creation. Original clean `/workspace/solidity-lean` work branch at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4` preserved. Export metadata records full committed head.

Same VM and existing persistent goal; no replacement goal or thread launched. get_goal is not exposed, explicitly allowed by coordinator. Read repository AGENTS, rule-table conventions, intrinsic G0, module map, build/resource instructions and lean-verify/runtime skills. No Lean MCP tool exposed; guarded CLI/Lake checks used. relay.sh is **host-only**, not a VM installation task; saved exact requests are the coordinator handoff mechanism.

## Coordinator clarification: PERF-01 resolved

Verbatim: “Answer (coordinator, from H62 item 6): a per-module time or memory increase does not stop a migration lane. Record the before/after numbers for that module and continue to the matched clean full-build comparison the task requires; the coordinator reports memory/time growth to the human with the cut-over escalation.”

Tracked source: `tests/h62/item6/migrate-sortcheck/coordinator-clarifications.json`. The earlier conservative Parser-only STOP in checkpoint174fa343 is superseded. Module increases remain recorded in `resume-20261106/module-observations.json`; they do not block this lane. Only the required matched full-build comparison uses its escalation/>10% rule. No full-build delta is currently valid because the new build fails.

## Four checkpoints

| Checkpoint | Status | Evidence / remaining obligation |
|---|---|---|
| 1. Census and clean old build | done | Three source files,46 generated faithfulness invocations,nested helper/pattern cases; old full elaborated658-declaration capture; clean cache-disabled Lake leanArts build all64 dependency modules passes with wall/RSS and independent reviews. |
| 2. Official435 and adaptation | partial | Exact official archive/version pin; KeySort/AST/Annotations pass. Parser proposal fixture/controls/conformance pass. Production edits await exact-file coordination; missing generated API aliases have tested proposals. |
| 3. New full build and matched timing | blocked | Matched clean new Lake attempt fails in read-only Syntax/Raw. Faithfulness/full new interfaces not checked. No valid complete before/after delta. |
| 4. Reviewed migration export | partial | Patch/bundle/evidence/source hashes,old full and new partial interfaces,dependency report and precise requests exported. Production overlay,root-gate acceptance and remaining full gates pending. |

## Identity, resources and measurement

Official435 archive URL: `https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`; SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`, matching coordinator toolchain-pin.json. All five coordinator input hashes verified.

- Old Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake5.0.0-src+797c613. Official old archive SHA256 b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec.
- New Lean4.35.0 commiteb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake5.0.0-src+eb6cafb.
- VM16GiB cgroup memory,4CPU quota,no configured swap. Runner:12GiB per-process address-space bound plus sampled aggregateRSS bound,4GiB available reserve,300s per-module safety timeout,one Lean process at a time. LEAN_NUM_THREADS=1 and explicit -j1; writer lock held. No systemd-run or per-master/shared artifact cache.
- Private off-git Lake project derives from tracked config: absolute selected srcDir/private buildDir,cache disabled,weakLeanArgs add -j1. Only testing-private lean-toolchain written. Each dependency-ordered +module builds leanArts (.olean,.ilean,C); **native C compilation/linking is separate**. Actual commands show -j1. Guard records max concurrent Lean processes; observed1.
- Reports contain actual Lean/Lake versions,official archive digest,runner/census hashes,normalized private profile hash,selected-root source/import hashes before/after and explicit prerequisite artifact hashes for focused checks. Provenance hashing outside build interval. RSS sampled100ms; kernel cumulative child high-water RSS reported separately.

Clean old **Lake** result: `/workspace/migrate-sortcheck-evidence/resume-20261106/old-lake-clean/result.json`: **64/64 pass,382.510216s**, sampled aggregate peak **7142703104 bytes**, kernel cumulative child maximum **6919620KiB**. Source snapshot stable. Earlier374.214s measurement was elaboration-only and is retained as historical evidence, not substituted for Lake.

Clean new **Lake** result: `/workspace/migrate-sortcheck-evidence/resume-20261106/new-lake-clean/result.json`: KeySort,AST,Annotations,SpecSyntax pass; Syntax/Raw fails with String/Slice mismatches at597,650,665,682/684. This belongs to migrate-syntax. No out-of-scope fix attempted. The matched comparison returns **blocked/null delta**, with new-build failure and unequal completed module sets as reasons; not a >10% STOP.

Both attempts used the same frozen runner/census/profile. Exact scripts preserved under `/workspace/migrate-sortcheck-evidence/resume-20261106/matched-attempt-harness`, with hashes matching both reports. Later scanner hardening changes the census hash; **future accepted comparison must regenerate both sides using identical final harnesses, or use the frozen harness identically on both sides where supported**. Never compare unlike runner/profile identities.

## Conformance, controls and proof boundaries

`/workspace/migrate-sortcheck-evidence/resume-20261106/old-conformance/result.json` and `new-fixture-conformance/result.json`: guarded **lean --run SolkeyCheck.lean**, explicit frozen file, both report **377 taclets,131 read-bearing,table131,OK**. Rule SHA256 `02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb`. These execute the real checker via Lean's interpreter; **not a native lake exe or full run-lean gate**. New result uses isolated Parser proposal; production unchanged.

Earlier scoped controls pass on old production and new fixture: **two kernel examples and24 executable guards** covering comments,unknown tokens/sorts,varcond absence/ambiguity,all read domains/sites,legacy valAt,multiset ordering/multiplicity,missing/unannotated taclets,rendering and inventories. Scanner suffix computations remain executable guards,not a new external-parser equivalence theorem. Failed iterations are retained,never counted passing.

Parser proposal changes only l.trim → l.trimAscii.copy and (t.dropRight1).trim → (t.dropEnd1).trimAscii.copy; actual exact diff in parser435-fixture3/proposed-parser.patch. History3b03ac583/e4b8be05a reviewed; no speed-driven guard/row representation undone. String.mk deprecations remain rather than expanding the proposal.

## Frozen interfaces and new compatibility findings

Old complete capture: **658 declarations**, complete printed types/transitive axiom sets. Log SHA256 `85430e37388519d87672f7bd40ae3f12af7f66190f13011b064dd3d7e7cc818a`. Source-primary signatures/statements and budgets frozen by exact source bytes.

Partial capture reuses the same template for Parser/Annotations: old331,new336 declarations;218 baseline public names audited. **26 source-primary printed signatures match**, none missing. **Full partial-interface result remains review-required**:

- Three deprecated generated public aliases disappear: ReadDomain.toCtorIdx,ReadSite.toCtorIdx,SortVarcond.toCtorIdx. Do not discard them as an accepted exclusion.
- Generated noConfusion/helper printed types change; per-definition standard axiom dependencies also change. Printed differences are not automatically semantic changes or automatically accepted.
- Observed total axiom union is propext,Classical.choice,Quot.sound on both sides. No sorryAx/native trust primitive introduced,but unchanged union does not waive per-declaration review or authorize pin regeneration.

Reports/log hashes: parser-interface-comparison-classified.json and old/new-parser-interfaces/ParserInterfaces.log beneath resume-20261106. Text comparison is not cross-version kernel equivalence; full Faithfulness/new complete capture remains blocked.

Test-only compatibility fragment `/workspace/migrate-sortcheck-evidence/resume-20261106/constructor-compat-source3/annotations-compat.fragment.lean` restores the three arrow-typed aliases with original reducible protected form and deprecated target/date2025-08-25 (verified against old Lean CtorIdx generator). It does not restore the old completion-blacklist metadata. **No production aliases applied.** Tests `ConstructorTags.lean` independently freeze exact numeric0..2 domain,0..3 site,0..4 varcond maps. Three universal kernel proofs cover all12 constructors on both compilers: old-constructor-tags-frozen and new-constructor-tags-frozen pass. The final tests supersede weaker same-version ctorIdx equality checks; no theorem/premise was weakened.

## Ownership/dependency/H70 requests

Current exact requests: `/workspace/migrate-sortcheck-evidence/resume-20261106/coordination-requests-current.json`; this supersedes historical performance-stop requests. DEP-SYNTAX-01 needs owner overlay exact base/head/path/hash. OWNER-PARSER-01 and OWNER-ANNOTATIONS-01 need live producer/root-gate coordination before existing-file edits. API-AXIOMS-01 requests review of generated signatures and standard axiom dependence. Silence/routing is not permission. Cross-directory report accounts for all61 repository dependencies and migration owners; no producer ownership transfer.

H70 routes generic-v08 → Parser at requester headbc63858540d294f0e66c60ba62745c6dc90769b1. Reported full handoff14777 bytes/SHA256 b132587155bd438825a5d7f32d2a9f35275689cfc0b8659f8bd0c41067c35b12 lives at host receipt `/home/guilherme/.local/state/cloudvm-coord/receipts/router-20261106T142920Z/solidity-h62-4-20261106__generic-v08/df8196188fc4-HANDOFF.md`, unreadable on this VM. **H70-DELIVERY-01 requests coordinator delivery**, not relay installation. We can supply tested proposals and precise evidence; no owner-authored accepted production overlay/head is claimed. Requester execution proofs,exact instances,correspondence,semantic refusal validation,final builds/full-family measurements remain unfinished/unproved here. Routing authorizes none of those changes.

## Source hashes

- `Solidity/SortCheck/Annotations.lean`: `45bc9365a12b009a45a4352fd3fb6f6bf16098400beb7593dea8c40f5f060188`
- `Solidity/SortCheck/Faithfulness.lean`: `b006ff2d3243ae5b6a2510a1eae5e1e1d8459ba254ff16a89151054b4b67ea8b`
- `Solidity/SortCheck/Parser.lean`: `e21e62c46abaf7f954aaa3447033983d66ba75a1257217f16bacecc1d9a2d330`

## Gates, review and remaining work

Tooling selfcheck includes missing-target/overlay-dependency controls,public/meta/all headers,explicit rejection of unsupported quoted/multiline forms,same-compiler/archive/runner/NaN/time rejection,module-vs-directory eligibility,and deterministic fixture checksums. Import discovery uses selected source_root. Private helper/test modules remain under tests or generated off git; no central registration edits. H44 bulk logs,sources,interfaces and cache outputs remain off git with SHA256 inventories.

Independent read-only finder/skeptic used no Lean server/builds/edits. Confirmed findings fixed: selected-root import provenance,modifier handling,frozen numeric tag cases,inventories,lifecycle cleanup,resource/provenance labels,and stale historical STOP prose. Final review results saved in resumed reviews. Per-module increases are record-only; memory/time growth goes to coordinator cut-over escalation.

Passing static checks and source freeze recorded in the handoff. **Still pending**: production coordination/adaptation,syntax-owner dependencies,full new Faithfulness/build/interfaces,accepted compatibility review,matched successful clean full comparison,native conformance and required ./run-lean.sh final gate. No partial checkpoint declares full success. After these useful work items hand back to coordinator for fresh-thread continuation on exact same VM/goal/state; never self-launch/reset a goal.
