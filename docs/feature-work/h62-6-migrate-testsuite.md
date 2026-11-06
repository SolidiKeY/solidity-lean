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
