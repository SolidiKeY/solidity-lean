# H62 item 6: Backend migration overlay

Status: **partial, not complete; source adaptation blocked**. Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-6-20261106/migrate-backend`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The exported `FINAL.json` records the full checkpoint commit. No pushes,
merges, default-branch edits, root registration, or toolchain cut-over occurred.
The existing clean `work` branch was preserved. The base was fetched explicitly
and verified as an ancestor of published `origin/master` before branch creation.

## Queue state

| Checkpoint | State and evidence |
|---|---|
| 1. Census and clean old baseline | Source census/backfill saved; complete clean baseline and elaborated API census remain pending. |
| 2. Official toolchain and adaptation | Coordinator archive verified and official versions recorded; first frozen axiom-pin failure reproduced. Owned source adaptation awaits coordination. |
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

All original Solidity sources, `lean-toolchain`, `lakefile.toml`, central maps,
roots and axiom pins remain byte-for-byte unchanged against the base. Backend
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
