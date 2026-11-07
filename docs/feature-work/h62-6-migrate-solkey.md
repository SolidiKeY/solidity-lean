# H62 item 6: migrate-solkey handoff

Status: **resumed by explicit coordinator instruction; blocked on retained holds; not complete**. Owner: `solidity-h62-6-20261106/migrate-solkey`.
Branch: `codex/solidity-h62-6-20261106/migrate-solkey`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/migrate-solkey`. Original clean checkout at
`/workspace/solidity-lean` was preserved. The pinned base was fetched and verified
as an ancestor of published origin/master before branch creation.

## Checkpoints

1. **Done:** census at pinned base and clean old source-import closure build.
2. **Blocked:** exact official toolchain verified; external Syntax.Raw migration
   prevents elaborating every assigned module on 4.35.0.
3. **Blocked:** new full build and comparable clean wall/RSS acceptance unavailable.
4. **Partial:** reviewable patch/bundle/export tooling, source hashes, 759 old
   elaborated interface hashes and cross-directory report supplied. New interface
   hashes/comparison and final runtime gates remain outstanding.

No assigned original file or frozen statement was edited. All five originals,
lean-toolchain, generated roots, central module maps and axiom pins remain
byte-identical to base. No new axiom declaration, sorry, native_decide, trust
shortcut, changed premise/exclusion/observation or raised heartbeat budget.
This overlay does not transfer live producer ownership. No push, merge, PR,
cut-over or freeze announcement. Final lean-toolchain change belongs to root.

## Accepted old baseline and resources

Command (exit 0):

```
python3 scripts/h62/item6/migrate-solkey/measure.py --root /workspace/migrate-solkey --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/migrate-solkey-evidence/old-clean-final
```

All **285 modules**, including all five assigned modules, pass.
Wall **1776.720861 s**; maximum child RSS **3,280,612 KiB**;
peak cgroup memory **9,659,658,240 bytes** (includes file cache).
Each module's exact command, exit, wall time, source SHA256 and output OLean
SHA256 are in `old-clean-final/measurement.json`. This narrow source-import
closure build does not substitute for final `./run-lean.sh`.

Fresh outputs; no Lake/per-master cache restored. Official standard library is
provided by each release. OS page cache is uncontrolled. Serial LEAN_NUM_THREADS=1
and explicit -j1, --tstack=131072; VM physical cap 16 GiB, CPU quota 4, no configured
swap, 4 GiB reserve checked against host availability and cgroup headroom, bounded
TERM/KILL cleanup, no artificial virtual-address cap. Both releases default to
maxHeartbeats=200000; no budget was raised. Polling adds up to 250 ms per module.

The failed initial pilot is retained: 1462.017 s before TermSize exited -6 with
“failed to create thread.” Its extra RLIMIT_AS=12 GiB incorrectly restricted
virtual stack reservations. An unchanged TermSize recheck without that extra cap
passed in 29.830 s; a live sample showed 13,404,156 KiB virtual size versus
1,051,480 KiB RSS. The accepted clean run later passed it in 29.607 s. No OOM
was recorded. The failed pilot is not a baseline or proof failure.

## Official pinned build

All coordinator inputs passed `/workspace/h62-coordinator-inputs/sha256.json`.
The required toolchain-pin.json and downloaded release match:

- leanprover/lean4:v4.35.0, official lean-4.35.0-linux.tar.zst.
- SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
- Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
- Lake 5.0.0-src+eb6cafb (Lean version 4.35.0).
- Old Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release.
- Old Lake 5.0.0-src+797c613 (Lean version 4.24.0).

Actual versions, archive identity and resource observations are in toolchain.json,
resources.json and measurement reports. KeySort passes on both exact releases.
No RUNTIME_GATE_PASS is asserted.

## External dependency blocker

Command (exit 1):

```
python3 scripts/h62/item6/migrate-solkey/measure.py --root /workspace/migrate-solkey --toolchain /workspace/migrate-solkey-evidence/lean-4.35.0-linux --out /workspace/migrate-solkey-evidence/new-clean-1
```

KeySort, AST and SpecSyntax pass. Solidity/Syntax/Raw.lean then fails at lines
597, 650, 665, 682 and 684: String.drop now returns String.Slice; Slice.toList
and String.dropRight are unavailable at those uses; passing endsWith directly
fails overloaded-pattern inference. Deprecated String.mk/Slice.dropRight also
produce warnings. Complete diagnostics and shortest import chains proving that
**all five** assigned modules reach Raw are in dependency-blockers.json.

Typed blocker: **EXTERNAL_DEPENDENCY_MIGRATION**. Request to Syntax migration
owner via migrate-root-gate: provide owner-approved compatible prerequisite
migration artifacts/overlay on the exact pin, preserving statements/semantics/
budgets. Raw is read-only here. Required relay.sh is absent; request is saved for
local coordinator retrieval, with no owner reply or permission inferred.

The comparison command exits 1 with “new run is incomplete or failed”:

```
python3 scripts/h62/item6/migrate-solkey/compare.py /workspace/migrate-solkey-evidence/old-clean-final/measurement.json /workspace/migrate-solkey-evidence/new-clean-1/measurement.json
```

**Full-build timing delta: unavailable.** No performance acceptance or claim of
no regression. The comparator rejects incomplete runs, diagnostic modes, changed
settings/tooling/inputs, nonfinite metrics and module-order drift. It escalates
any positive wall/RSS regression and stops strictly above 10%.

## Census, interfaces and finite backfill

Census: five modules, seven direct imports, 280 local dependency modules and
16 standard imports. Eleven fixture-import occurrences include the deliberate
stale-hash rejection. All source commands, guards and fixtures are hashed. These
lexical hashes alone are not semantic interface equivalence.

Old FrozenInterfaces.lean check exits 0 in 44.100 s with **759
declarations**: ComputedRevert21, Constructors42, QuantifiedDiamond46, ScopedFlip11,
TestSuite639. Original declaration kinds, universe parameters, kernel type/value
expressions (including opaque bodies) are captured. All module-owned theorem
axioms are checked; module-owned axioms are rejected. Three public originals use
only propext, Classical.choice and Quot.sound. Normalized hashes are in
old-interfaces.json; new execution/comparison remains blocked by Raw.

Eight isolated String API cases pass on both releases with identical source
SHA256 `053bd25334527afb97c85f6df741afee0b9ee2f0aecc8f36dfecea71186407b7` and default
heartbeat budgets. No premise/conclusion changed during proof repair. Old positive
suffix proof uses explicit eight loop transitions; new proofs use public string
list-model equations. These are finite cases, **not parser correctness or Solkey
migration completion**. check-api.py checks compilation then all eight axiom sets
through StringApiAxioms.lean. Old axioms: six empty, two propext. New axioms: only
propext, Classical.choice and Quot.sound. No nonstandard axiom/trust shortcut.

Only these isolated cases enable experimental.module=true equally on both
versions to allow import-all of standard implementation details. Assigned build
measurements use stock options. This private test option does not edit the
tracked toolchain. MCP goal and multi-attempt tools were used for the difficult
case; a diagnostic request after module-header changes timed out. Only this
lane's daemon tree/scratch files were stopped/removed. Final bounded compiler
and axiom checks are authoritative; no successful final MCP diagnostic is claimed.

**ESCALATE: diagnostic RSS regression.** API case/audit RSS is
208,396 → 468,140 KiB (**+124.64%**),
wall 1.091012 → 1.072779 s. This is an isolated SDK
fixture, not the complete assigned build. It exceeds 10%; further Lean work and
performance acceptance stop for root/gate investigation. No waiver requested.

## Validation and reviews

- Five scanner, five timing-acceptance, five interface and one archive controls:
  **16 external Python tests pass**. These do not prove Lean statements.
- Layer check exits0: 857 core modules, zero reaching elaborators or checked
  parser adapters. Generated-root and fragment checks exit0. Census comparison
  exits0; all five original/dependency/fixture hashes remain unchanged.
- check-testsuite.sh --solkey tests/migration/solkey/keyext.solidity.examples
  exits0: trust clean across54 modules;564 public functions =552 derived+11
  refuted+1 existing excluded, zero pending, plus2 skips. This audits pinned rows.
- check-doc-paths.sh exits1 for a pre-existing missing optional Bridge Mathlib
  path in docs/feature-work/after-roadmap-va1.md. No new missing path or external
  file repair. Default/setup TestSuite snapshot attempts failed; explicit pinned
  snapshot resolves that setup issue. All attempts retained.
- Full new ./run-lean.sh, all assigned new modules, new interfaces and clean
  before/after acceptance remain pending. No failed/pending required gate is done.

Independent finder and skeptic worked read-only without Lean/server. Their
findings fixed command locations/import forms, reserve/termination handling,
NaN/exact10%/tool identity/mode acceptance, opaque/original-kind coverage, unused
axiom rejection, and stale-import provenance. They verified final repairs and
finite-case statement preservation. Skeptic identified the diagnostic RSS rise;
it is escalated above. reviews.json retains outcomes and boundaries.

## Artifacts and continuation

Bulk remains outside Git at `/workspace/migrate-solkey-evidence`; deterministic
generators are committed under scripts/h62/item6/migrate-solkey. The committed
checksum manifest covers a reproducible bulk archive and the exact release.
export.py produces a verified base..HEAD patch/bundle, exact committed identity,
handoff and matching evidence archive with checksums. Mutable goal/head reports
are excluded from the bulk archive to avoid circular hashes.

See tests/h62/item6/migrate-solkey/registration-fragment.md: explicit fixture
checks only; no production roots/module maps/axiom pin edits. Root owns final
registration/toolchain cut-over. Original producer ownership remains intact.

Historical pre-H82 instruction, superseded by retirement below (do not resume
this retired worker): resume this **same VM, branch and original launcher goal**, preferably through
the coordinator's fresh thread after this handoff. Do not create/reset a goal.
Original prompt reference SHA256:
`ab866875b0fdd2e67bb60485af9eb65d4e10e08992421bac2438d6c726b34b55`.
get_goal is not exposed; coordinator confirmed optional inspection absence is not
a blocker. Remaining obligations: owner Syntax migration, complete new closure,
new frozen-interface comparison, full required gates, full clean wall/RSS
comparison and root/gate resolution of diagnostic RSS. Keep goal blocked, not
complete. No push, merge or deployment authorization is implied.

## H82 final retirement disposition

H82 stop-and-handoff and the explicit H70/H82 ordering correction control this
retirement. Generic standing-rule continuation does not revoke that specific
instruction. No new proof work, Lean runs, timing reruns, source changes or shim
implementation occurred in the retirement checkpoint. Successor integration is
owned by `solidity-h62-6-20261106/migrate-root-gate` after final stopped/head
acknowledgement. This worker stops; no automatic implementation continuation is
authorized. Preserve the VM, branch and all evidence.

The authenticated patch/bundle includes the original visible assignment copy,
complete original work/backfill queue, exact scope manifest, schema-v1 waits,
and later owner-ticket provenance under
`tests/h62/item6/migrate-solkey/retirement/`; SHA256SUMS authenticates each file.
Original renderer-byte equality to the supplied prompt reference cannot be
asserted: no get_goal/history export tool is exposed. The full visible original
user assignment, including owner table, is copied from this same thread and its
actual digest is provided. Coordinator-local paths remain provenance only.

Push not performed: no available H71 text establishes lane-push permission; the
original no-push instruction therefore remains. No master push/merge.

Goal PAUSED cannot be set through this session's exposed tools: only stop_goal
with outcome complete|blocked exists, and no pause/get/update tool is available.
Do not substitute complete/blocked for PAUSED, create/reset a goal, or resume.
The local continuation state records authorized PAUSED intent and no active
work. Coordinator must apply the backend pause using its trusted goal context.
All outstanding migration/backfill obligations and waits transfer as recorded;
none are silently complete or waived. Prior sealed handoff is retained.

## Explicit coordinator resumption after integration

The later coordinator instruction explicitly authorizes merging origin/master
and continuing this same branch/goal. It supersedes the preceding retirement
for this worker; historical retirement artifacts remain intact. Published
20e492ee99a3fa8679aa526de0b6e731d85e4134 contains our0dd1adc3f3 head and is
an ancestor of fetched master d96f2406d352de7e0b72ba6ac4ab29dc457582c6. The
assigned branch fast-forwarded cleanly to that integration base. No master
branch mutation or push occurred. Reported gate-touched/Bridge PASS belongs to
the coordinator's integration; it is not a local4.35 acceptance run.

Independent static backfill completed: refreshed census equals the pinned
census byte-for-byte semantically, including all assigned module entries,
fixture hashes and complete dependency closure. Thus Raw's recorded errors
have not been repaired in this source tree. No unchanged timing STOP rerun.

consolidate-existing-api.py retains all759 existing old declarations, exact
universes/kinds/kernel signature expressions and source/capture provenance.
Six names are _proof_ family candidates; no other selected family prefix is
present in this module-owned list. These are name candidates, not authoritative
generation/visibility metadata. No declarations are excluded. Visibility is
explicitly not_recorded, new/shim signatures null, public_inventory_complete
false and implemented_shims empty. H78 remains pending, not waived.

std-import-footprint.py scans SDK import headers only (body character literals
are irrelevant): Basic26->181 and Lemmas137->361 source modules across official
4.24/4.35, no missing source records. This is a static source-import footprint,
not memory attribution/profiling. A narrower version-specific proof/import
strategy is a candidate for root/gate review, not an implemented optimization
or permission to lift the retained+124.6% diagnostic RSS STOP.

Both read-only reviewers caught assert-based validation that Python optimization
could skip. Explicit errors now enforce coverage, uniqueness, signature, kind
and module checks under -O; a deliberately altered signature is rejected.
Both final reviews pass by inspection. No Lean/server run, statement/proof edit,
new premise, axiom, budget change or source shim occurred in this resumed item.

Current schema-v1 waits and remaining full queue are in
tests/h62/item6/migrate-solkey/resume-d96f2406/status.json. No independent static
item remains identified: Raw prerequisite, RSS disposition, authoritative H78
visibility/new exports, and actual VM-readable H81 policy remain necessary.
The inspected durable decision document reaches H64; H81 references alone
are not policy delivery. Original timing/proof gates stay incomplete.

New bulk remains off Git at /workspace/migrate-solkey-resume-d96f2406 with a
committed checksum manifest and deterministic generators. The new delta is
against integration base d96f2406d, not a claim that unrelated imported master
changes are this lane's edits. Earlier complete original assignment, queue,
scope, original evidence and cumulative lane patch/bundle remain authenticated
in /workspace/migrate-solkey-h82-final. No new goal/reset or lane push.

## Portable evidence review follow-up at ac9d8db2a

The coordinator merged8b325fb7a and explicitly instructed fetching master and
continuing. The branch fast-forwarded cleanly to
ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6 after verifying ancestry.
Assigned Solkey and Raw sources remain unchanged. No Lean run or known timing
STOP rerun occurred; the merge message is not a disposition of those holds.

Review minor fixed: compact old-API and SDK summaries are now committed under
tests/h62/item6/migrate-solkey/portable-evidence, referenced by repository-relative
catalog paths. Existing absolute capture paths remain only in historical bulk.
verify-portable-evidence.py can verify repository files without any VM-only
artifact. External H44 archives use relative filenames/member paths and pinned
hashes; --require-bulk refuses missing or corrupted input. With both supplied
archives, all archive/member checks pass. Streaming uses no extraction or writes.
The absence of bulk remains explicit unavailable, never acceptance.

Independent read-only finder/skeptic verified repo-only and full supplied-bulk
checks and reported no defect. Negative controls reject missing required bulk
and corrupt bytes. This validates artifact integrity, not Lean/theorems or H78
compatibility. No statements, definitions, proof budgets, axiom sets or exclusions
changed. Raw/RSS/H81/H78 waits are retained in portable-evidence/status.json.
Q-SOLKEY-HOLDS requests actual policy/disposition/prerequisite delivery, not a
waiver. All presently independent static items are finished; further Lean and
performance acceptance await those inputs. No push, new goal or reset.

## 2026-11-07 working-baseline integration and RSS proposal

The coordinator reports8036ad277 merged to2a43bf4fc and authorizes rebasing the
working baseline/continuing. Fetch verified2a43bf4fcdaf24750265afc8f8be5b420d1d22b0.
Its owned lane files match8036, but8036 is not an ancestor. A normal merge
584a6a5f7ec2d4f55cae3f54e2ca969c2464d6d9 preserves both histories; its tree
equals origin/master. No reset/rewrite, conflict repair, master mutation or push.

Static re-census still equals the pinned assigned/fixture/dependency entries.
Raw, assigned Solkey files and lean-toolchain are unchanged. The new lean-verify
skill requires future outside-server checks through gate.sh per-file; no Lean
was run. No explicit Root RSS disposition or full H81 policy was delivered; a
different lane's documented conservative8GiB setting is not task-specific policy.

Independent backfill: an unapplied import-only proposal for the isolated4.35 API
fixture is committed under tests/h62/item6/migrate-solkey/rss-proposal. It keeps
every statement and proof-body byte unchanged while replacing the umbrella
String.Lemmas header with two defining modules. The captured SDK source graph
shrinks361->330 reachable modules. This is a static hypothesis, not measured
memory, visibility, type/axiom equivalence, or permission to lift STOP.

Generator input checks authenticate both versioned captures and graph against
committed hashes; failed, mismatched-source, old-as-new or altered-graph inputs
are rejected. Both read-only reviewers confirmed the proposal/boundaries; their
missing false-iff lemma-map and version-provenance notes were fixed. No source
application, proof implementation, signature/axiom/budget change or Lean rerun.

All available independent static items are complete. Schema-v1 waits and future
candidate validation are in rss-proposal/status.json. Raw/RSS/H81/H78 holds and
all unfinished original gates remain. Candidate validation, if later permitted,
must use the current per-file gate and compare meaning/signatures/axioms and
resources; no performance result is inferred from import count.
