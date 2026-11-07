# H62 item 6: Backend migration overlay

Status: **partial; queue resumed by the coordinator's explicit lane-specific
merge-and-continue instruction**. Repository `/workspace/solidity-lean`, branch
`codex/solidity-h62-6-20261106/migrate-backend`.
Frozen assignment base remains `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The previously retired head33dcda9f8b3b5d45e12f788b0f208ec9a6b24b28 was
verified in published origin/master along with reported merge20e492ee9;
this branch fast-forwarded to d96f2406d352de7e0b72ba6ac4ab29dc457582c6.
No local default branch update or push occurred. Historical sections below
retain their point-in-time limits; this section supersedes the retirement stop
for this explicit new instruction. The original goal is not created or reset.
The immutable old baseline worktree is separate and was not restarted.

## Queue state

| Checkpoint | State and evidence |
|---|---|
| 1. Census and clean old baseline | Source census/backfill saved; complete clean baseline and elaborated API census remain pending. |
| 2. Official toolchain and adaptation | Coordinator archive verified and official versions recorded; first frozen axiom-pin failure reproduced. Statement-preserving proof-only fixes have H82 standing permission; body/interface changes retain owner/H57 requirements. |
| 3. All new modules and comparison | Blocked by checkpoint 2. No matched full-build timing delta or regression verdict exists. |
| 4. Migration handoff | Tooling/backfill checkpoint and reproduction exported; full migration patch, elaborated frozen-interface hashes and gate acceptance remain pending. |

## Scope and trust boundary

The checksum-verified coordinator ownership snapshot explicitly assigns exactly
1,919 Backend source files, matching this pinned tree. The lexical import census
finds 2,497 local modules in the closure: 578 outside Backend and 498 direct
cross-directory import edges. `census-base.json` contains every edge, local
external dependency and source-file byte hash; `scope-and-source-freeze.json`
checks ownership equality and records the frozen Backend Git tree. These are
whole-file byte hashes, **not elaborated declaration/type compatibility hashes**.
Lexical declaration candidates are navigation aids, not completeness proofs.
Compiler dependency output still needs independent reconciliation.

Before the authorized origin/master integration at retired head33dc, all
original Solidity sources, `lean-toolchain`, `lakefile.toml`, central maps,
roots and axiom pins were byte-identical to the base. Incoming published master
changes are recorded separately below; no current-tree byte-identity claim is
made against the old base. Backend
baseline lexical counts are zero for `sorry`, `axiom` and `native_decide`.
No new axiom/sorry/native-decision declarations, raised proof budgets, weakened
statements, exclusions, observations, or premises were introduced. New Lean
helpers are confined to the assigned tests directory and need no root edit.

## Toolchain provenance

Coordinator inputs at `/workspace/h62-coordinator-inputs/` all match their
provided `sha256.json`. The selected release is exactly `toolchain-pin.json`:

- Toolchain: `leanprover/lean4:v4.35.0`.
- Official archive: `lean-4.35.0-linux.tar.zst`.
- SHA256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
- URL: `https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.
- Installed privately at `/workspace/migrate-backend-toolchains/lean-4.35.0-linux`.
- Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
- Old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release.
- Old Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
- Old archive SHA256: `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.

The serial diagnostic runner additionally compares the selected new `lean` and
`lake` executable bytes with those extracted directly from this pinned archive.
MCP runs use this same recorded private installation. No v4.24 per-master cache
was restored. No other VM's installation has been audited by this directory lane.

## Exact owner request and reproduction

**ESCALATE Q-RELAY-SLICE** (sources: H62 checkpoint 2; exact-file owner-coordination
rule). Target action: permission through the coordinator/live producer relay to
adapt `Solidity/Backend/Scalar/Slice.lean`, preserving the exact type and semantics
of `Solidity.Backend.Scalar.ternary` and its existing axiom-free pin at line 303.
The required `relay.sh` is absent from this VM/repository, and no owner reply has
been received. The request is saved in `owner-requests.json` for coordinator
retrieval. Absence of a relay/reply is not permission to edit the original.

Original source builds under 4.24.0. Under 4.35.0 it fails with:

```text
error: Docstring on #guard_msgs does not match generated message:
- 'Solidity.Backend.Scalar.ternary' does not depend on any axioms
+ 'Solidity.Backend.Scalar.ternary' depends on axioms: [propext]
```

Do not update the pin to accept the new dependency. The additive fixture
`tests/h62/item6/migrate-backend/TernaryDependency.lean` isolates the issue with
three operation constructors. Plain arithmetic, bitvector equality, literal,
modulo and `if` probes remain axiom-free. Its original-style matched `ternary`
is axiom-free on 4.24.0 and gains `propext` on 4.35.0. Its `ternaryRec` uses
`Op.casesOn`, passes an unchanged axiom-free guard on both versions, and has a
constructor-case/`rfl` equality proof against the original-style function.
The equality theorem itself references the original function and therefore has
`propext` on 4.35.0. This is a candidate technique, **not a repair or full
constructor proof for Backend.Op**. Six kernel-checked controls cover refusal,
both zero-modulus branches, addition, multiplication and a negative result.
No claim about source/compiler/EVM equivalence follows from these finite controls.

Coordination choices (neither changes the pin or grants exclusions):

1. Coordinator supplies the exact-file owner relay/reply here, enabling a
   source-preserving repair followed by complete validation.
2. Hold owned edits and return the reproduction to migrate-root-gate while
   retaining typed blockers and authorized backfill.

## Commands, outcomes and limits

Evidence root: `/workspace/migrate-backend-evidence`.
Commands below run from the repository root; all output files stay off git.

| Command | Outcome / decisive evidence |
|---|---|
| `git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` | Exit 0 before branch creation. |
| `python3 scripts/h62/item6/migrate-backend/census.py --output /workspace/migrate-backend-evidence/census-base.json` | Exit 0; 1,919 assigned files, 2,497 closure modules. |
| `python3 -m unittest discover -s tests/h62/item6/migrate-backend -v` | Exit 0, three lexical controls; `scanner-tests.log`. |
| `python3 scripts/h62/item6/migrate-backend/snapshot.py --evidence /workspace/migrate-backend-evidence` | Exit 0; explicit scope equality, coordinator checksums, frozen source and bulk hashes. |
| `python3 scripts/h62/item6/migrate-backend/build_serial.py --census /workspace/migrate-backend-evidence/census-base.json --toolchain /workspace/migrate-backend-toolchains/lean-4.35.0-linux --output /workspace/migrate-backend-evidence/new-diagnostic` | Exit 1; KeySort/Opcode/Jumpdest/Assembler pass, Scalar.Slice fails its frozen pin; `new-diagnostic/result.json` and module log. |
| Same serial command with `--toolchain /workspace/.setup/tools/lean-4.24.0-linux --output /workspace/migrate-backend-evidence/old-diagnostic` | Deliberately interrupted (exit 130) after 42 successful modules including original Slice. Partial elapsed 216.059 s, cumulative child peak 1,245,804 KiB. **Not a full baseline**. |
| `.venv/bin/python scripts/h62/item6/migrate-backend/check_fixture_mcp.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --output /workspace/migrate-backend-evidence/fixture-old-mcp-final` | Exit 0, MCP `success=true`, `partial=false`, `timed_out=false`, no failed dependencies. |
| Same MCP command with `--toolchain /workspace/migrate-backend-toolchains/lean-4.35.0-linux --output /workspace/migrate-backend-evidence/fixture-new-mcp-guarded` | Exit 0, identical accepted fixture SHA; complete per-file diagnostics pass, guarded recursor axiom pin passes. |
| `timeout --signal=TERM --kill-after=10s 1.5s .venv/bin/python scripts/h62/item6/migrate-backend/check_fixture_mcp.py --toolchain /workspace/migrate-backend-toolchains/lean-4.35.0-linux --output /workspace/migrate-backend-evidence/fixture-mcp-interrupt` | Expected timeout exit 124; cancellation log saved, no surviving live MCP/Lean worker observed. |
| `git diff --exit-code c6f550e281a7e5affa9a99bc2cdaed556dec00e4 -- Solidity lean-toolchain lakefile.toml` | Exit 0. |
| Full old baseline, full new closure, elaborated API hashes, matched comparison and `./run-lean.sh` | Pending; independent old baseline continues below, no pass claimed. |

Direct compiler runs are diagnostics and do not replace repository-prescribed
MCP/final gates. The old diagnostic was stopped to use the prescribed MCP path
for subsequent proof checks; its prefix cannot satisfy the clean baseline gate.
No valid whole-build before/after delta exists; no <=10% acceptance is inferred.
An early fixture experiment used an unavailable name and failed; its v2 logs
are retained as superseded failures, not accepted proof evidence. Final accepted
fixtures contain no unresolved placeholders. The installed MCP library emits
an asyncio transport-destructor warning during shutdown; successful diagnostics
and process cleanup were checked separately. The interruption control also logs
an expected SDK cancellation/BrokenResourceError.

The VM has a 16 GiB memory cap, no swap, and a four-CPU quota. Heavy jobs were
serial, with `LEAN_NUM_THREADS=1`, explicit `-j1`, `--tstack=131072`, `-M12288`,
a 12 GiB monitored limit and 4 GiB available reserve. The writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`; no systemd-run was used.
Private diagnostic outputs start empty. OS page caches were not flushed; these
partial runs establish no matched performance result. No RUNTIME_GATE_PASS is
claimed. Both recorded toolchain versions and KeySort success are available,
but this alone proves neither migration nor runtime acceptance.

## Independent reviews and continuation

Read-only finder `/root/finder` and skeptic `/root/skeptic` used no Lean server
or Lean execution. Confirmed fixes: stale source/census checks, swap detection,
cumulative RSS labeling, child cleanup, archive/executable provenance, startup
resource monitoring, session timeout and cancellation. Both final reviews report
no blocking tooling findings. They explicitly leave full migration, exact API
compatibility, baseline/comparison, owner coordination and final gates unproved.
Their summaries are saved in `reviews.json`. No original Backend source was
changed, so no producer ownership was transferred and no H55 work duplicated.

Resume the same VM and persistent goal. Continue the independent prescribed
clean old baseline while Q-RELAY-SLICE is pending. Retain the frozen pin and
resolve the owner relay before adapting sources.
Then obtain external migration dependencies through their owners, validate all
assigned modules and affected consumers, perform the matched full comparison
(stop >10% regression and escalate any regression), review each milestone,
produce elaborated frozen-interface hashes and final run-lean acceptance, and
export the complete migration bundle to migrate-root-gate. This checkpoint is
only scanner/toolchain/reproduction backfill. Do not create another goal or a
replacement worker, cut over, push, merge, publish or announce a freeze.

Bulk evidence is covered by the committed
`tests/h62/item6/migrate-backend/EVIDENCE.sha256` (relative to the evidence root).
`ARTIFACTS.sha256` additionally hashes the exported patch, bundle, handoff,
committed bulk manifest and final JSON. `FINAL.json` holds the committed head
without a self-referential tracked commit hash.

## Independent old gate continuation

The missing source-owner relay does not block the old clean baseline.
`run_gate.py --checkout /workspace/migrate-backend-baseline --toolchain
/workspace/.setup/tools/lean-4.24.0-linux --output
/workspace/migrate-backend-evidence/old-clean-gate-v3` runs the unchanged
`./run-lean.sh` in a detached build-only worktree at the pinned base, retaining
the exact default targets and hardcoded `.lake/build/bin/solkeycheck` path.
The assigned branch/worktree remains the patch destination. The separate
worktree starts without `.lake/build`; artifact and remote caches are disabled.
A private sysroot symlinks the official release and wraps `bin/lean` with
`flock`, `-j1` and `-M12288`; no official binary is modified.
The supervisor records source tree/head, affinity/quota, live progress, wall/RSS
and resource stops. It explicitly selects and hashes the repository-frozen
SolKey rules; acceptance requires decisive conformance output, never a skip.
RSS is maximum individual-child RSS; cgroup peak separately includes cache and
other VM activity. No resource-stop verdict may become a pass.

Earlier gate setup attempts are retained as unsuccessful evidence: v1 could
not find `/usr/bin/time` (Python wall/child-RSS now used); v2 was deliberately
interrupted after review caught a bypassed serialization wrapper and an
incompatible redirected buildDir. Neither attempt reached the sort wrapper or
changed the main checkout's cached executable. These are not baseline passes.
The corrected v3 gate must finish and its output be audited before checkpoint 1
can be accepted. Final export status records whether this work remains running.

The live v3 baseline log/progress can change while running and is outside the
frozen checkpoint checksum snapshot until the run finishes. Its evidence must
be finalized and checksummed in the next checkpoint.

## Python-only import reconciliation checkpoint

The next backfill increment adds `reconcile_imports.py`, which validates the
1,919 actual assigned source identities, bytes and source imports against the
census; verifies the reachable, topologically ordered 2,497-module local closure
without padding; and compares compiler `.ilean` module identities and direct
import names/order. Missing or unreadable artifacts remain pending (exit 2).
Unresolved non-toolchain imports are rejected. The census now distinguishes
exact `Init`, `Lean` and `Std` namespaces from vendored names such as LeanTeX.

The sealed checkpoint2 report checks all 1,919 source files and matches the
124 available compiler records, with 2,373 artifacts unavailable and no
mismatches. This is **pending**, not a complete census gate. These checks do
not establish artifact freshness, toolchain provenance, import visibility/meta
flags, elaborated type compatibility or semantic equivalence. Fresh build
provenance and final compiler gates remain necessary. Eight Python controls
cover the committed scanner/reconciler; four additional API controls belong
to uncommitted draft work. Both independent read-only reviews passed after
the missing-dependency finding was fixed. No reviewer used Lean or its server.

Reproduction from the assigned checkout:

```sh
python3 scripts/h62/item6/migrate-backend/reconcile_imports.py \
  --source-root /workspace/migrate-backend-baseline \
  --census /workspace/migrate-backend-evidence/census-base.json \
  --artifacts /workspace/migrate-backend-baseline/.lake/build/lib/lean \
  --output /workspace/migrate-backend-evidence/import-reconciliation-progress.json
```

Sealed evidence: `/workspace/migrate-backend-evidence/checkpoint2/`. The
committed `EVIDENCE-IMPORTS.sha256` is relative to that directory. The live
baseline and later reconciliation reports can advance independently.

Additional owned drafts are preserved separately for continuation: a complete
83-constructor actual-opcode recursor fixture; a generated full Slice proposal
copy/diff that changes only the ternary body while retaining its exact written
primary signature, remaining source and every frozen guard; and a structural
API exporter with DAG sharing, strict binder names/annotations, per-declaration
streaming, and a derived runtime cache control. The proposal is not applied.
Their Lean verification, full API compatibility, proof/resource checks and
timings remain pending; none is included as an accepted proof in this commit.
The API count check validates consistency with its exporter header, not
independent declaration completeness. The draft archive/state records exact
paths and hashes. Preserve these owned drafts rather than discarding them.

The old clean gate continues unchanged under the existing goal-owned writer
lock (supervisor PID 20926, session 7208). All preparation above changed only
this lane's scripts, tests and handoff in the assigned worktree; no input in
the immutable baseline worktree changed, and no second Lean job was launched.

## H70 Linking producer-ping proposal (unverified)

The H70 relays identify `Solidity/Backend/Creation/Linking.lean:109` as a
shared dependency of audit-roadmap, audit-v10-storage, migrate-roadmap and
migrate-root-gate. Their complete staged handoffs have been requested from
the coordinator; the host receipt files are not present on this VM. This
section uses only the supplied diagnostic excerpt and the local pinned source,
and does not claim review of those complete payloads.

The committed `creation-linking-unverified.patch` changes one existing proof
step in `Solidity.Backend.Creation.two_links_commute`: it adds
`Location.Disjoint` to the `simpa only` list, explicitly exposing the original
offset disjunction. The original statement, premises, imports, remaining
source and proof budgets are untouched. The original Lean file is unchanged.
The patch SHA256 is
`029b1e07ff623b181ee782f9c6082159ef7433e181a70316b194385e9d01bf4d`.

`generate_linking_fixture.py` deterministically reproduces the proposal copy,
patch and metadata. Resolved-path guards prevent original-source aliases,
pairwise output collisions or writes outside the assigned tests/evidence
areas. Three non-writing guard controls and the deterministic generator check
pass. Independent read-only finder and skeptic reviews confirmed static scope
preservation; neither used Lean or a Lean server. Full proposed copies remain
off Git; sealed metadata and review summaries are under
`/workspace/migrate-backend-evidence/checkpoint3-linking/`.

**This is not a compatible or owner-approved migration patch.** Full H70
payload review, exact-file coordination, actual Lean checks on both pinned
releases, axiom/frozen-API validation, proof budgets, timings and full affected
gates remain pending. No original-file permission is inferred from routing.
The old clean baseline remains active and no second Lean job has been run.
The separate MCP-helper generalization remains an uncommitted draft until
its private-artifact/provenance and no-auto-build behavior are validated.

The proposal packaging was corrected after the first artifact commit: Git's
optional space on an empty context line is omitted. Both `git apply --check`
and `git diff --check` now pass; the proposed Lean bytes are identical. The
first commit's whitespace check failed and is not counted as a passing check.
Updated proposal metadata and controls are sealed in
`/workspace/migrate-backend-evidence/checkpoint3-linking-v2/`; the earlier
evidence directory is retained unchanged.

## API tooling static review; compiler validation pending

The committed `api_inventory.py` and `ApiInventory.lean.in` are preparation
and checking tools, not an accepted elaborated API inventory. They preserve
all imported Backend declaration candidates, including private/generated
names, and structurally serialize types with strict binder names/annotations.
The serializer uses structural expression caching and streams declarations;
Python computes hashes independent of DAG sharing. Only expression metadata
is omitted. No generated declaration or type difference is silently excluded.

Independent finder and skeptic reviews found and fixed three acceptance
hazards: undeclared universe parameters, noncanonical numeric name encodings,
and duplicate declarations silently collapsed during comparison. Index
schema/count/module/row/digest checks precede comparison. Scoped resolved
output guards reject aliases and existing destinations, and the Lean exporter
uses exclusive creation for its temporary file. Nineteen Python controls
pass, including direct malformed-index, open-universe and output-guard cases.

Static evidence, generated drafts and reviews are sealed under
`/workspace/migrate-backend-evidence/api-tooling-static/`; the committed
`EVIDENCE-API-STATIC.sha256` records their hashes. Both official Lean compiler
checks, complete declaration inclusion, provenance, runtime resource checks
and actual old/new API comparison remain pending. Self-reported declaration
count consistency does not independently prove completeness. The unchanged
old baseline remains the sole Lean job; no production source was edited.

## H78 continuation and recovered observation

H78 answers Q-H70-STOP-SCOPE: do not stop the running unchanged old4.24
baseline. Migration lanes continue past time/memory increases, record them
for cut-over review, and keep an 8 GiB per-module cap. This supersedes the
previous performance STOP rule; it grants no axiom/pin/budget relaxation or
live-owner original-file permission. The old gate remains the sole Lean job.

The original supervisor PID20926 disappeared while root20979 and Lake21012
continued. Its last progress snapshot was 9480.310465453 seconds; no final
result or continuous-monitor record covers the subsequent gap. The cause
is unestablished. Cgroup memory.events later showed zero OOM kills; that
observation does not identify the cause. No missing exit/RSS value is invented.

The initial prefix used Lean -M12288 and total12GiB/reserve4GiB. Its config,
wrapper and progress bytes are preserved unchanged as evidence. The private
wrapper now appends -j1 -M8192 after Lake arguments for subsequent modules;
root/Lake, source bytes, selected toolchain and targets were not restarted or
replaced. Future serial/gate launchers use -M8192; the generalized MCP helper
remains an uncommitted runtime-unverified draft with that same lower limit.
This mixed-resource epoch is not a matched clean before/after timing pass.

A detached nontracing observer reacquired this same goal's writer lock.
Its first instance70961 was replaced by reviewed instance72074 without
signaling the baseline. It samples official-Lean descendants only, validates
root and child PID epochs, and uses pidfd only when an owned module's RSS/HWM
exceeds8GiB. OS headroom is recorded as an alert, not another signal condition.
It tolerates arbitrary argv bytes, detects zombie roots and reports unexpected
observer failures. A root zombie exit word is recorded only if actually seen;
otherwise final exit remains unknown. Prior interval/full maximum RSS and
matched timing remain unverified. No observer result proves a Lean theorem.

Automatic approval review rejected the earlier combined recovery action
because it included live ptrace and headroom-triggered module killing beyond
H78's stop conditions. That tool action did not execute. The safer nontracing
observer was accepted. A separate tracing proposal and Q-H78-EXIT-OBS were
then withdrawn after independent review; its executable entry now refuses
unconditionally. It has not been run. No tracing approval is requested now.

Finder and skeptic reviewed the observer without executing Lean or a server.
Confirmed epoch/decoding/zombie/error-status findings were fixed; 21 Python
controls pass. Sealed evidence is
`/workspace/migrate-backend-evidence/h78/static/`, recorded by
`EVIDENCE-H78-STATIC.sha256`. Live progress is separately under
`/workspace/migrate-backend-evidence/h78/recovered-baseline-v2/`.

The latest audit-roadmap requester63d6ef9f5a50b93a1e2666bfc3c295c4514e2a88
still waits for Creation/Linking. Its full18260-byte handoff was requested
for exact delivery (reported SHA256
ced72d8eb459cd162ef9323cb38419eebcc321019bb46c0d127962e8012b08d9).
The supplied summary is not treated as the full verified payload. The existing
committed Linking proposal remains unapplied and Lean-unverified; owner
coordination and complete validation remain pending. All four assignment
checkpoints remain unfinished; no RUNTIME_GATE_PASS or timing verdict.

## H82 retirement preservation checkpoint

Human-approved stop-and-handoff names successor
solidity-h62-6-20261106/migrate-root-gate. No new proof implementation,
source repair or Lean job is authorized in this retirement checkpoint.
All previously owned source drafts are committed explicitly unverified;
generated copies and bulk evidence stay off Git in the authenticated export.
The exact launcher original assignment, historical thread transcription,1919-file scope,
original work/backfill queue, full unfinished accounting and pause capability
record are committed under tests/h62/item6/migrate-backend/retirement/.
Exact ORIGINAL-PROMPT.txt now matches launcher455fea after coordinator delivery;
the earlier complete transcription remains separate historical evidence.
Finder/skeptic corrected the G53 owner-map transcription; no other queue or
scope omission was found. No original Solidity or root toolchain edit.

The delivered Roadmap18260-byte receipt now verifies its advertised
ced72d8eb459cd162ef9323cb38419eebcc321019bb46c0d127962e8012b08d9
SHA256 and was read in full. It adds no accepted Backend migration or witness
result. H82 withdraws old proof-only Q-LINKING-OWNER; retirement, not missing
proof-only owner agreement, prevents new application here. Definition/body,
interface, statement, budget, axiom and exclusion constraints remain.

Coordinator explicitly confirms the later generic Continue does not revoke
retirement. No retired implementation is resumed. Existing baseline/observer
processes are preserved for successor disposition; no restart or new Lean job.
The goal API has no PAUSED transition: only complete|blocked. Actual goal pause
could not be set, and no completion/reset/replacement is attempted. Worker
implementation stops after the final schema-v1 handoff acknowledgement.
No H71 push permission is available; no push occurs.

## Explicit origin/master integration and independent continuation

The coordinator specifically named this lane/head and instructed merging
origin/master into the assigned branch and continuing. This is new explicit
lane authorization, unlike the earlier generic broadcasts. The old retirement
packet remains immutable historical evidence; no goal reset or replacement.

Fetched master is d96f2406d352de7e0b72ba6ac4ab29dc457582c6, one cache-script
commit after the reported20e492ee99a3fa8679aa526de0b6e731d85e4134. Both
that reported commit and final retired33dc were verified ancestors before
`git merge --ff-only origin/master`. No conflict, discard, push or default
branch edit. Coordinator-reported touched/Bridge gates are not local migration
or new-toolchain validation evidence.

The immutable Git ledger from `resume_inventory.py` records original1919,
present1932, unchanged original1917, changed original2 and incoming13 files.
The two original file diffs were inspected: CopyPaths adds explicit axiom-output
guards; PowerBounds sets Elab.async false to avoid retained concurrent tasks.
Those incoming speed/resource changes are preserved. The13 new modules are
incoming/read-only, not an inferred expansion of this lane's frozen assignment.
Git blob identity and source inspection do not establish old/new public types,
axiom fidelity, generated API completeness or semantic equivalence.

`reconcile_imports.py --source-root` now binds the source census/check to the
actual checkout rather than assuming the tooling checkout remains frozen.
It requires an actual Git checkout root. Reproduction for the continuing old
baseline uses --source-root /workspace/migrate-backend-baseline with the old
census and that worktree's private build artifacts. The first resumed snapshot
checked1115 of2497 import records with zero mismatch; missing artifacts remain
pending. This is not artifact freshness or a compiler/type compatibility pass.

H78 preparation now writes metadata schema2 with explicit `isPrivateName`
classification and the protected flag. The common helper definitions were
read in both official toolchain source trees. All private/generated constants
remain included, including public internal-looking names such as _proof_2;
no `Name.isInternal` exclusion is used. Legacy schema1 is refused rather than
silently accepted as visibility evidence. Private/public naming classification
is not complete Lean4.35 module-export accessibility; exported-context/import
visibility, provenance, complete old/new signatures and real shims remain
pending. Both template compiler checks also remain pending.22 Python controls
pass; metadata controls are not proofs of project correctness.

Only the original old baseline remains a Lean job (root20979/Lake21012,
observer72074). No new Lean/MCP session was launched during it, no stopped
module was restarted, and no production source was edited in this continuation.
Per-file checks for the existing Linking/full83-op/Slice proposals stay next
when the serial resource slot becomes available. Original frozen statements,
axiom-free pin and proof budgets remain binding; all four formal checkpoints
are unfinished. Current source/provenance evidence is under
/workspace/migrate-backend-evidence/resume-d96f2406/.

The full post-integration documentation gate initially found five non-existing
references in imported notes and a synthetic test. Under H82's standing
nonsemantic documentation permission, off-Git/proposed paths were quoted,
and the synthetic path was composed without changing its runtime input.
The unchanged full checker now passes with126 ambiguous references, all
resolved. The four affected census tests pass. No checker exemption, placeholder
module, registration, production proof or interface change was introduced.
