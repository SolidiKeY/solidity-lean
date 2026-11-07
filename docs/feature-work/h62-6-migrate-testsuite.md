# H62 item 6: TestSuite migration overlay

Repository: `/workspace/solidity-lean`. Assigned branch:
`codex/solidity-h62-6-20261106/migrate-testsuite`.
Published pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The base was fetched from origin/master and remote ancestry verified before
creating this branch. The previous clean `work` branch was preserved.

This directory lane does not own live producer files. No existing Lean file,
root module, module-map fragment, axiom pin or tracked lean-toolchain was changed.
All 49 original TestSuite files are frozen byte-for-byte; no theorem statement,
premise, exclusion, observation or proof budget was changed. No new axiom,
sorry, native_decide, trust shortcut or heartbeat increase was introduced.

## Evidence and reproducibility

Bulk evidence lives off git at `/workspace/h62-migrate-testsuite/evidence`.
The deterministic source census covers all 49 assigned modules, 333 local
import-closure modules and eight direct edges outside TestSuite. It records
all closure source SHA256 values and checks pinned-base identity. It is a
lexical source census, not an elaborated declaration/type census. In particular,
the 563 scoped obligations and Report's 617/552/0/65 counts require Lean's
original guard-message acceptance gates. No source-hash claim substitutes for
these gates or frozen elaborated interfaces.

The pinned official toolchain is from the coordinator's verified
`/workspace/h62-coordinator-inputs/toolchain-pin.json`:
`leanprover/lean4:v4.35.0`, linux release archive SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean reports commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
The old release reports Lean 4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake `5.0.0-src+797c613`.
No get_goal tool was exposed; coordinator explicitly confirmed that absence
is not a blocker and the original persistent goal was retained.

`measure.py` builds each module's olean facet in topological order with
one Lake invocation at a time. Every Lean invocation has `-j1` and
`LEAN_NUM_THREADS=1`; build outputs and caches are private and fresh, with
artifact cache disabled. Wall timing includes serial Lake invocation overhead.
The hard job cgroup cap is 12 GiB with swap allowance zero, inside the
16 GiB VM. No virtual-address limit is applied: Lean reserves large virtual
stacks. The immutable runtime is
`python@sha256:4209fae09a3e20afd863e528bfddc235da5fd5977983e1996cd54cc9a72e6267`.
The repository and both official toolchains are mounted read-only; only the
evidence directory is writable. The runner verifies the job cap/swap values
and that its read-only parent cgroup mount matches observed VM limits.
The 4 GiB available reserve is sampled every 200 ms using the minimum of
MemAvailable and parent cap minus current usage plus reclaimable inactive file
cache. Each summary records runtime image, parent/job limits, CPU settings,
source hashes, commands, exits, timings and sampled aggregate RSS. No systemd-run
was used. CPU quota is four CPUs and affinity is 0–4. No Lean MCP tool was exposed.

The exploratory old-clean-01 was interrupted for review corrections.
old-clean-02 stopped at TermSize with a thread-creation failure under the wrong
virtual-address limiter. Both are unaccepted baselines. TermSize subsequently
passed the controlled hard-cgroup probe (30.986 s, 1,272,651,776 bytes sampled
peak RSS). That reused dependencies and is diagnostic only; the accepted fresh
old-clean-03 result is recorded below. No incomplete wall time is a baseline.
`compare.py` rejects incomplete/subset runs, source/resource/config differences,
wrong Lean commits or Lake versions, config tampering and invalid metrics.
Any regression escalates; a wall or sampled peak RSS regression above 10%
stops. Exactly 10% escalates.

## Backfill and review

The isolated StandardAPIs fixture reproduces the exact kernel refusal
classifier in MemoryLoopReplay/Refusals.lean. It checks a genuine good lemma,
a false lemma, successful action, and propagation of both non-refusal error
classes. It cannot establish Solidity obligation validity or imported API
compatibility. The Python controls cover nested/line comments, strings,
import ordering/cycles, source identity and mutation, incomplete builds,
config mismatches/tampering, wrong versions, NaN/zero metrics and timing/RSS
thresholds. At that checkpoint twenty-two Python controls passed; both official toolchains pass the isolated Lean fixture.

Independent read-only finder and skeptic reviews ran without Lean/server
or edits. Confirmed findings were fixed: unsafe arbitrary subset probes,
swap parsing, missing replay-resume inventory, incomplete provenance,
float threshold boundary, invalid metrics, config digests and toolchain checks.
Both re-reviews passed the static tooling scope. The recorded runtime checks
and remaining owner blockers are recorded in the off-git handoff and result.

## Ownership and remaining gates

Direct external edges and all 284 external closure modules are recorded in
`dependency-report.json`. Existing source adaptations require exact-file owner
coordination. `scripts/coord-tools/relay.sh` was absent in this VM; no absence
was treated as permission. Cross-directory fixes remain their migration owners'
work. This lane never imports another VM's old per-master cache.

The complete migration requires all four checkpoints: clean old build;
pinned-release API adaptation with exact interfaces; clean new full build and
accepted comparison; migration patch/bundle and root-gate handoff with compiled
interface hashes. A failed or partial build does not complete any missing gate.
No RUNTIME_GATE_PASS is claimed by this document. Root-wide run-lean.sh final
validation remains pending until the migration dependency graph is available.
No push, merge, PR, master change, pre-gate or cut-over action is authorized here.

## Recorded regression and resumed checkpoints

The matched isolated fixture passes on both releases but regresses:
old wall 1.809733351 s / sampled peak RSS 636,497,920 bytes;
new wall 2.412217539 s / sampled peak RSS 1,626,386,432 bytes.
This is +33.29% wall and +155.52% sampled RSS. It is one probe per version,
not a full-directory comparison or a throughput conclusion. The initial worker
interpretation paused further Lean runs; the coordinator clarification below
resolves that pause. These module measurements remain recorded for cut-over
escalation while matched clean full-directory measurements continue.

1. Import/source census and the full clean old build are complete: all 333 closure modules, including all 49 assigned modules, passed in old-clean-03 (3359.376553 s; 5822562304 bytes sampled peak aggregate RSS). Original ScopedProblems, Report, Suggestions and refusal controls passed.
2. Exact release archive and versions are verified; new KeySort and isolated
   API controls pass. All-assigned-module compatibility/adaptation is unfinished.
3. Full clean new build and accepted before/after directory comparison are pending.
4. Reviewable tooling patch and dependency/source-hash handoff are supplied;
   compiled old/new interface hashes and full migration patch acceptance remain pending.

Q-PERF-API is resolved by the coordinator's H62 item 6 clarification:

> a per-module time or memory increase does not stop a migration lane. Record
> the before/after numbers for that module and continue to the matched clean
> full-build comparison the task requires; the coordinator reports memory/time
> growth to the human with the cut-over escalation.

The same VM, branch, pinned releases, hard resource bounds and original goal
are retained. No new goal or replacement continuation was created. The fresh
old baseline uses new private outputs under `evidence/old-clean-03`; no previous
partial outputs count toward its clean build.

## Old baseline checkpoint

Command: `H62_RUNTIME_IMAGE=python@sha256:4209fae09a3e20afd863e528bfddc235da5fd5977983e1996cd54cc9a72e6267 bash scripts/h62/item6/migrate-testsuite/run-bounded.sh python3 scripts/h62/item6/migrate-testsuite/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/h62-migrate-testsuite/evidence/old-clean-03`.
Exit 0; summary status pass; all 333 requested modules completed with no resource stop.
The source tree, official releases and bounds remain frozen as documented above.
Both releases default to maxHeartbeats 200000 and maxRecDepth 512.

Independent finder and skeptic reviews confirmed the baseline evidence and
per-module reporting changes. The installed per-module reporter has eleven
passing controls and records growth without stopping the lane; failed/missing
modules and mismatched provenance never receive comparable timing deltas.
The census/comparison/output-collector controls now number twenty-two.

Compiled interface export remains checkpoint 4 work. A whole-environment
export hit the reserve guard; per-module raw rendering then expanded shared
expression nodes into gigabytes. Those diagnostics are unaccepted. Generated
sources, summaries, compressed logs and checksums are retained off git in
`evidence/superseded-raw-interface-logs.tar.gz` and the associated manifest.
A compact structural expression graph is required before accepting interface
hashes. This diagnostic work does not change the passed old build result.

The fresh full v4.35.0 build has now been attempted with identical resources
and fresh private outputs; its external dependency failure is recorded below.
Full timing comparison and final migration acceptance remain pending.

## New-toolchain dependency and compact interface checkpoint

The fresh official v4.35.0 full build `new-clean-01` fails at
`Solidity/Syntax/Raw.lean` after KeySort, AST and SpecSyntax pass. There are five
source error locations (597, 650, 665, 682, 684), involving String/Slice APIs
and a dependent-pattern `endsWith` predicate. No assigned TestSuite module was
attempted. Total partial wall time is 15.293478 s; it is not a full-build timing.
`full-build-comparison.json` correctly reports pending/INCOMPLETE_FULL_BUILD.
The per-module report has 333 rows and three comparable successful modules;
it records individual growth without stopping the lane.

Typed blocker `B-DEPENDENCY-SYNTAX-RAW` requests the Syntax migration owner,
through migration root/gate, to provide an approved exact-file adaptation.
The full request and original error log are saved off git. This worker did not
edit the parser or assume permission from an absent relay tool.

`StringApiBoundary.lean` supplies seven kernel-checked conversion witnesses
(ASCII, Unicode, empty/overrun boundaries) and two explicitly runtime suffix
checks. Both official releases pass the identical fixture. This is scoped
API evidence, not a proof of parser equivalence or any Solidity obligation.

The compact interface format records every module-owned kernel declaration,
including internal declarations, with exact structured names, universe
parameters and constructor-based type fingerprints. It also records all 563
problem definition values and the complete problems table (564 values total).
Proof values are excluded. Binder names, binder information, let annotations,
levels, literal contents and projection fields are retained. Syntax source
positions/raw substring backing, metadata order and identical redundant keys
are normalized; syntax content, names and preresolution are retained.
Conflicting metadata keys fail closed. SHA256 covers full constructor payloads
and child fingerprints; Lean's cached hash only indexes collision-checked
structural sharing. Node numbers do not affect fingerprints.

The deterministic encoder controls run on both releases and check sharing,
binder names, let annotations, metadata content/order/source positions,
redundancy and nested conflict refusal after memoization. Matching old/new
fingerprints are recorded separately from TestSuite compatibility acceptance.
The 46 Python controls cover the codec, census, collector and reporting.
No source declarations or original proof statements have been changed.

These fingerprints capture selected expression bodies and references. They do
not establish transitive dependency semantics or cross-version equivalence.

The accepted old snapshot covers all 49 modules and 8068 kernel declarations
(4316 definitions, 3752 theorems), with 552 proved, 563 problem and 11 refuted
cases and 564 selected definition values. Canonical JSONL SHA256:
`c1c32f44a134169b2dc3586400accd6923ec862292dcec67607de53430391e12`.
No module-owned axiom declarations were found; this inventory is separate from
the original Report proof-audit gate. The new snapshot remains blocked.

Final read-only finder and skeptic reviews confirmed the compact encoder and
collector. The skeptic requested exact matching of the expected metadata
conflict error; the control now rethrows unrelated errors. The corrected
identical fixture passes both releases, with matching canonical fingerprints.
All 46 Python controls and final syntax/source/ancestry checks pass.
Old interface export exit 0: 243.493156 s, sampled peak RSS 1113288704 bytes.
Checkpoint 1 is complete; checkpoints 2–4 retain the external dependency
blocker and unfinished new-interface/full-comparison/root-gate obligations.

## H82 final retirement preservation

Stopped by explicit human-authorized H82 handoff, successor
`solidity-h62-6-20261106/migrate-root-gate`. No new proof/source work or Lean
runs were performed during retirement. Full original rendered assignment,
original queue, exact scope manifest, amendments, remaining queue and schema-v1
waits are committed under `tests/h62/item6/migrate-testsuite/handoff/`, with
SHA256SUMS. Original VM/branch/evidence are preserved. H71 push authorization
was not available, so no branch push was attempted.

The exposed goal tool has no PAUSED operation (only complete/blocked), and the
previous transition failed for missing trusted goal/source-turn context. The
authorized pause is recorded locally; no platform transition success, goal
completion, reset or replacement is claimed. No automatic continuation is
authorized.

H70 confirms migration-Syntax is the accepted compatibility prerequisite. H78
requires exhaustive original public generated API coverage and per-shim
signature records; the old ModuleData kernel snapshot alone does not establish
that inventory (compiler-only extraConstNames are excluded). These obligations
remain with the survivor, together with new snapshot/parity/full comparison
and root final gates. No frozen interface or axiom/proof-budget change was made.

Retirement read-only finder/skeptic reviews verified scope, queue extraction,
checksums and unchanged originals. Original assignment text is transcribed
from the visible original thread, not authenticated as byte-identical to an
unavailable canonical renderer artifact; see its explicit provenance note.
The Syntax prerequisite remains awaited, not locally delivered or accepted.

## Explicit resumption after coordinator merge

The latest coordinator instruction reports this lane merged at master
`20e492ee9` and explicitly directs merging origin/master and continuing. This
resumes the previous H82 retirement in the same VM, branch and original goal;
no reset, replacement goal, new VM or competing continuation was created.
The merge fast-forwarded to `d96f2406d352de7e0b72ba6ac4ab29dc457582c6` after
verifying ancestry of the pinned base, previous final head and coordinator
merge. The earlier retirement section records history, not current disposition.

All 333 source-closure files, including all 49 assigned modules, remain exactly
identical to the accepted pinned-base census. Syntax/Raw.lean retains the same
five known v4.35.0 error locations; no accepted prerequisite patch was delivered.
That dependency failure was not rerun unchanged. No original Lean file or
frozen interface was edited by this lane. Master changed lakefile defaults and
comments, so the historical clean old build remains evidence; a final matched
pair must satisfy the existing strict configuration/source/resource checks.
No comparison result or renewed runtime pass is inferred from the merge.

Independent H78 backfill now explicitly enumerates all kernel and compiler-added
names for each assigned module, rather than omitting compiler-only names.
The old inventory retains 8068 kernel declarations and 104 compiler extras,
including all private/internal/generated names, with zero exclusions. Exact
structured names, universe parameters, declaration kinds and type fingerprints
join to the accepted old snapshot and its complete DAG stream. The 104 compiler
extras have no ModuleData kernel signature and remain explicit unresolved rows.
New signatures, export accessibility, shim names and shim signatures remain
unresolved; naming flags are not an export-visibility proof. No H78 completeness
or compatibility acceptance is claimed. Hash-addressed provenance links the
actual passing official old-toolchain fixture, census, frozen signature file,
manifest and full DAG stream. Large outputs remain off git.

The first structured-name fixture placed a helper before target imports and
failed; the generated import ordering was corrected and fresh evidence retained.
Only a successful final fixture and validated join count toward the inventory.
The 59 Python controls include missing kernel/compiler names, malformed types,
false naming flags, overlap, duplicate rows, failed compiler and snapshot
mutation refusals. Reviewer findings were fixed without source/proof changes.

The Syntax prerequisite and exhaustive new API/parity/full-comparison/root-gate
work remain typed waits; no unrelated unclaimed cleanup or ownership takeover
was performed. No push, default-branch change or cut-over is authorized here.
Detailed H81 policy text was not delivered; this small inventory check retained
the original measured hard 12GiB/no-swap/4GiB-reserve serial settings and makes
no new H81 approval or matched timing claim.

Accepted structured inventory evidence: `public-inventory-old-03` and
`public-api-old-03`. Lean exit0; 13.856743 s; sampled peak RSS 1126273024 bytes.
Inventory SHA256:
`646b9823dc10955d567be8c293512c5273048ef0f5677514f269768c1a585ddf`.
The resumed checkpoint supplies the generator and 13 API-inventory controls
(59 Python controls total). Prior unstructured/syntax-failed probes remain
unaccepted diagnostics for the strengthened schema.

Independent read-only finder and skeptic re-reviews passed the resumed partial
inventory checkpoint. Confirmed findings fixed: structured naming flags,
category overlap, signature schemas/hash formats and naming versus export
visibility. Both independently verified inventory/provenance hashes and
explicit pending fields; neither used Lean/server or edited files.

## Portable artifact verification after ac9d8db2a

The next explicit coordinator instruction reports this checkpoint merged at
`ac9d8db2a`; origin/master was fetched and the lane fast-forwarded to
`ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6`, after verifying original-base and
reviewed-head ancestry. Syntax/Raw.lean and the assigned modules are unchanged.
No new goal, ownership takeover, source/proof edit or Lean run was introduced.

The review minor about VM-only pins is addressed by the committed
[portable evidence manifest](../../tests/h62/item6/migrate-testsuite/evidence-manifest.json)
and [verification instructions](../../tests/h62/item6/migrate-testsuite/README-evidence.md).
The external detailed manifest gives relative paths and sizes/SHA256 for 356 checkout
files (333 closure sources plus 23 lane Python/shell tools and Lean fixtures),
17 evidence-root-relative files, and the existing historical archive itself.
The compact committed descriptor pins that detailed manifest and the archive.
VM paths are location hints only. Bulk outputs and the expanded inventory remain
off git; the deterministic generator and streaming verifier are in git.

Without the pinned detailed inventory, verification reports pending and makes
no source-integrity claim. Once supplied, all original checks remain required.
Explicitly unavailable external artifacts report
`pending_artifacts`/exit2; present mismatches fail. Supplying the manifested
archive or a relocated evidence directory verifies the declared files without
any dependence on the capture location. Archive verification reads compressed
bytes and all 17 required members without extraction. Other historical members
are not interpreted. It is integrity evidence, not a fresh proof or runtime gate.

The API reporter now accepts an explicit artifact root and historical recorded
root, confines captured receipt paths to the supplied directory and writes
relative provenance paths. An actual relocated replay reproduced the same
8172-row inventory SHA256 and retained all 104 unresolved signatures. Compiler
receipt paths are checked as data, never executed. New compilation, export
accessibility, shims, H78 parity, full comparison and root final gates remain
pending on the same accepted Syntax prerequisite.

All 75 Python controls pass, including omitted/missing artifacts, tampering,
missing checkout files, duplicate members and root escapes. Actual archive and
relocated-directory verification pass; checkout-only and absent-directory checks
return expected pending2. Read-only finder/skeptic reviews confirmed the fixes:
run-bounded.sh is now manifested, and unavailable external evidence consistently
stays pending. Neither review used Lean/server or made edits. No RUNTIME or H78
acceptance is inferred from these artifact checks.

## H44 held-increment split

The 1881-line generated inventory from held head `155b1b81e` is preserved
off git. The unmerged increment now commits only a compact path/size/SHA256
descriptor alongside reviewable scripts and docs. Its external detailed
inventory preserves all 356 checkout and 17 evidence checks. The held head is
retained at `refs/backup/h44-migrate-testsuite-155b1b81e` and in its prior bundle.
No original Lean file, theorem, gate criterion or budget was changed.
New loader refusal controls bring the Python total to 81; missing detail stays
pending rather than bypassing checks. Original Syntax/API/full-build waits remain.
