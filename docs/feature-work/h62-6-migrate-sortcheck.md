# H62/H63 SortCheck — H76 applied migration and blocked full handoff

Batch solidity-h62-6-20261106 / migrate-sortcheck. **Full goal unfinished.** H76 resolves migration-branch writer coordination: the tested Parser/Annotations overlay is applied in Solidity/SortCheck. This does not transfer live producer ownership on master. No pushes,merges,PRs,pre-gates,freeze or master publication.

## Branch, ownership and pinned build

Base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch `codex/solidity-h62-6-20261106/migrate-sortcheck`,worktree `/workspace/migrate-sortcheck`. Exact published base ancestry verified at setup; original `/workspace/solidity-lean` work checkout preserved. Final export records full committed head. Same original goal/VM; no reset/new goal or self-launched continuation.

H76 (per H69) explicitly registers each migration lane as writer of its directory and permits tested Parser/Annotations changes preserving statements/budgets. Earlier OWNER-PARSER-01/OWNER-ANNOTATIONS-01 waits are resolved. H70 routing receipts are not validation or live-owner transfer. relay.sh is host-only,not a VM installation task. Clarifications are tracked under tests/h62/item6/migrate-sortcheck/coordinator-clarifications.json.

Only official leanprover/lean4:v4.35.0 archive used: SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`. Lean4.35.0 commiteb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake5.0.0-src+eb6cafb. Old baseline Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake5.0.0-src+797c613;old archive SHA256 b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec. Both release archives and coordinator inputs hashed; actual versions captured in every run report. Tracked lean-toolchain/lakefile untouched; final pin belongs to root lane.

## Applied exact source overlay

- Parser.headerName?: l.trim → l.trimAscii.copy; (t.dropRight1).trim → (t.dropEnd1).trimAscii.copy. Exact diff uses original whitespace. Both trim predicates and character-drop semantics reviewed against official sources. No scanner algorithm/guard/fuel/statement changed; String.mk deprecations left untouched.
- Annotations: restore generated4.24 ReadDomain.toCtorIdx,ReadSite.toCtorIdx,SortVarcond.toCtorIdx as protected,reducible aliases to ctorIdx,with exact deprecated target/date2025-08-25 and completion blacklist. Explicit `type_of% ...ctorIdx` signatures retain the target's full type/binder metadata. No privileged declaration replacement or proof shortcut. Only ordinary checked aliases and completion tags added.
- Faithfulness: byte-identical to pinned base. No original theorem/premise/exclusion/observation/proof budget altered; no maxHeartbeats increase,new axiom,sorry or native_decide. Imports and intrinsic representation unchanged. History3b03ac583/e4b8be05a reviewed; generated rows and executable-guard speed decisions retained.

migration.py reconstructs only this exact source overlay from git-show of the pinned base; selfcheck verifies current files against that map. fixture.py produces deterministic off-git copies from base plus approved compatibility additions. Historical inject mode is explicit; actual-source validation uses the applied files,not proposal fixtures.

## Checkpoint accounting

| Checkpoint | Status | Evidence and remaining work |
|---|---|---|
|1 Census/old clean baseline|done|All3 files/cases,46 generated faithfulness invocations,nested helper,658 old declarations;64/64 clean old Lake leanArts pass with reviews/timings.|
|2 Official435/adaptation|partial|Actual Parser/Annotations applied and checked,native conformance passes. Faithfulness awaits reviewed Syntax dependency;full generated frontend/axiom review remains.|
|3 New full build/matched performance|blocked|Actual directory attempt fails read-only Syntax/Raw;no successful complete new build or valid full delta.|
|4 Reviewed migration packet|partial|Owner-authored source patch/bundle,exact file hashes,interfaces,classifications,requests and gates exported;root acceptance and remaining full validation pending.|

## Gates, exact evidence and limits

Evidence root `/workspace/migrate-sortcheck-evidence`; current phase `h76/`. Each result.json contains exact child command vectors,exit codes,versions,source/import/artifact hashes and resource metrics. No Lean MCP tool exposed; per-file guarded CLI diagnostics used as repository fallback. Read AGENTS,rule-table conventions,intrinsic G0,lean-verify,build/resource policy and managed-runtime instructions.

VM16GiB/4CPU,no configured swap. One heavy Lean process at a time,LEAN_NUM_THREADS=1,explicit-j1,--tstack=131072.12GiB process/address-space and aggregate sampled RSS bound,4GiB available reserve,300s per-task safety timeout;writer lock held. No systemd-run. Private cache-disabled Lake projects/outputs;no per-master/shared artifact cache. Native mode builds5 dependency-ordered object targets then **lake exe solkeycheck**,enforcing exact explicit frozen --key hash. Resource guards and max concurrent Lean count preserved. Provenance hashing outside measured build interval;100ms sampled aggregate RSS and kernel child high-water RSS labelled separately.

Old clean directory Lake leanArts: `/workspace/migrate-sortcheck-evidence/resume-20261106/old-lake-clean/result.json`,64/64 pass,**382.510216s**,sampled peak**7142703104bytes**,maxLean1,stable snapshot. It includes .olean/.ilean/C generation. Earlier374.214s elaboration-only run remains historical. Exact old/new failed matched harness saved in resume-20261106/matched-attempt-harness. Future accepted timing pair must use identical final harness/profile and a clean pinned-base source checkout for the old4.24 measurement (current migration files target435). Never run the old baseline against these new aliases or compare unlike runner hashes.

Actual changed files + controls: `h76/per-file-final/result.json` passes Annotations,Parser,ParserCases,ConstructorTags,AliasMetadata on official435. Five kernel examples (including3 universal numeric proofs of all12 enum constructors),24 executable guards;metadata checks match alias type/root binder/body/protection/reducibility/deprecation/completion. Old metadata control uses pinned old oleans. Scanner guards are finite executable controls,not a new external-parser equivalence theorem.

**Native conformance:** `h76/native-conformance-final/result.json` passes all object builds/link/real executable in **16.474447s**;377 parsed taclets,131 read-bearing,table131,OK. Frozen rule SHA256 `02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb`. This satisfies scoped solkeycheck execution after Annotations edits; it does not prove requester execution correspondence or replace full Faithfulness/run-lean validation. Earlier interpreted/fixture successes are distinguished from this actual native gate. Failed layout/probe iterations are retained and not counted passing;named(x:=...) probe failed on old aliases and was rejected as a claimed old API.

Old full interface capture658 log SHA256 `85430e37388519d87672f7bd40ae3f12af7f66190f13011b064dd3d7e7cc818a`. Count/hash-validated canonical partial captures: old331,new339,all218 baseline public names present. Closed expression serialization erases binder names/type metadata and normalizes universe parameter names by order;retains binder info,constants,levels,indices,all other nodes. Separate full binder-name maps retain frontend metadata. Count/truncation,invalid universe,binder-only,logical-change and named-metadata negative controls fail closed. This is audit evidence,not cross-kernel definitional equality or an interface waiver.

## Exact generated-API/trust delta classification

See `h76/applied-interface-comparison.json` (final run path recorded by handoff if superseded):

- No missing public names;the3 formerly missing aliases now match target signature/binder metadata and original numeric cases.
- Six generated per-constructor noConfusion helpers change34 explicit binders to implicit. Quantified domains/bodies are structurally unchanged after names/metadata normalization;positional call elaboration can change.
- Raw binder-name maps also differ on generated declarations;some names are hygienic/internal. Named-argument behavior is not automatically preserved or automatically broken by a raw rename. No frontend compatibility waiver inferred. Source-primary manual signatures remain unchanged;all exact maps retained.
-20 per-definition axiom sets change. Partial old union was propext;partial new union adds Classical.choice/Quot.sound. Full original658 SortCheck census already used all3;**no new primitive versus full old directory**. This does not waive per-declaration trust review or authorize pin edits. No source axiom/trust declaration added.

Strict overall result remains **review-required**. No official toolchain patch,redefinition of existing generated declarations,statement weakening,exclusion or premise change was attempted to mask these differences. Literal qualified/short-name callsite search is retained but is not dynamic-reference completeness or permission to drop an API.

## Published dependency wait and routed requests

DEP-SYNTAX-01 belongs to migrate-syntax: Solidity/Syntax/Raw.lean String/Slice errors at597,650,665,682/684 block Faithfulness. H76 says no pipeline head/staged reviewed bundle/origin branch;VM lookup also absent (`h76/syntax-status.json`). Wait is recorded by coordinator deps.json. Use only latest **published reviewed** owner commit with exactbase/head/artifact hashes when available. No uncommitted substitute. Source ownership questions are resolved,not the dependency.

H70 solcvalidation requester0bd9e2519c43f1757674d2051a7786ac5688c2bb DEP-SORTCHECK-1 independently reproduces Parser.trim failure. The outgoing exact Parser/Annotations source overlay/native gate answers that prerequisite only;Hash/Language/Semantics/Backend tickets stay with their owners. Reported owner-requests SHA25660807e53469c24e33e81aff91af8d7132d4fc38d87af2ed36a0733db91f8e25f retained as reported,not falsely byte-verified from a reformatted copy.

Audit-roadmap requester63d6ef9f5a50b93a1e2666bfc3c295c4514e2a88 full handoff18260 bytes/SHA256ced72d8eb459cd162ef9323cb38419eebcc321019bb46c0d127962e8012b08d9 is host-staged at `$XDG_STATE_HOME/cloudvm-coord/receipts/router-20261106T160530Z/solidity-h62-2-20261106__audit-roadmap/ced72d8eb459cd162ef9323cb38419eebcc321019bb46c0d127962e8012b08d9-HANDOFF.md`. Request exact delivery to `/workspace/migrate-sortcheck-evidence/incoming/audit-roadmap-63d6ef9f-HANDOFF.md`. No actual-inheritance,ledger/witness completeness or impossibility-proof claim. generic-v08 host ticket/delivery request remains recorded;no execution/correspondence/full-family claim. Only assigned exact-file interfaces/results with committed head/path/hash supplied. Routing acceptance is not owner validation.

## Frozen and migrated source hashes

|File|Pinned base SHA256|Current migration SHA256|
|---|---|---|
| `Solidity/SortCheck/Annotations.lean` | `45bc9365a12b009a45a4352fd3fb6f6bf16098400beb7593dea8c40f5f060188` | `26126bbbd4d8266a3f2fc1de8fbcb6c9f6e350e5b7263f613de3f785cd1757bb` |
| `Solidity/SortCheck/Faithfulness.lean` | `b006ff2d3243ae5b6a2510a1eae5e1e1d8459ba254ff16a89151054b4b67ea8b` | `b006ff2d3243ae5b6a2510a1eae5e1e1d8459ba254ff16a89151054b4b67ea8b` |
| `Solidity/SortCheck/Parser.lean` | `e21e62c46abaf7f954aaa3447033983d66ba75a1257217f16bacecc1d9a2d330` | `9685cfb986c5f4b9ccea0055de3b6e33d251130f6f508e754f7835483015d180` |

## Reviews, export and remaining gates

Independent read-only finder/skeptic used no Lean/server/build/edits. They confirmed source statement/budget preservation,exact metadata,guarded native conformance and strict API review status;confirmed fixes for count/truncation and named-metadata classification. Resumed/H76 review reports are off git. Static layers/generated roots/fragments/whitespace and deterministic selfchecks recorded. Tests/helpers remain in assigned tests scope;no root/module map/pin registrations modified. H44 bulk logs,captures,C/olean/native outputs remain off git with SHA256 inventories.

**Still required:** reviewed published Syntax input,actual full435 Faithfulness/build/full interfaces,frontend/axiom delta review,successful matched clean full timing and required ./run-lean.sh. Per-module time/memory growth is record-only per coordinator PERF-01 clarification;only valid matched full build uses escalation/>10% rule. No valid full delta exists while new build fails. No RUNTIME_GATE_PASS or full goal completion claimed.

Fresh-thread handoff belongs to coordinator on this exact VM/goal/branch after these useful items;never self-launch/reset another goal. Export HANDOFF.md and CLOUDVM-RESULT.json record exact head,artifact/file hashes and gate commands. Goal tool trusted-context limitations,if encountered,are recorded without inventing a state update.
