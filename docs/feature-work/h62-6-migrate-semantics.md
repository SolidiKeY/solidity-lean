> H82 RETIRED / STOPPED. No automatic implementation continuation is authorized.
> Handoff survivor: solidity-h62-6-20261106/migrate-root-gate. Latest generic
> continue relays are retained as evidence and do not revoke the explicit retirement.
> Goal PAUSED cannot be set by the exposed tool (only complete/blocked outcomes);
> no substitute transition, completion, reset or replacement is performed.
> Mandatory original assignment, exact scope, full queues/waits and state are in
> tests/h62/item6/migrate-semantics/retirement/. Final authenticated head and
> cumulative artifacts are recorded in the off-Git retirement handoff.

# H62 item 6: migrate-semantics

Status: blocked, assignment incomplete. No RUNTIME_GATE_PASS or cut-over.

Repository `/workspace/solidity-lean`, branch
`codex/solidity-h62-6-20261106/migrate-semantics`, pinned base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Published base fetched and verified
as ancestor of origin/master before branch creation. No push, merge, PR,
freeze, root registration, pin edit or tracked toolchain/configuration change.
Coordinator clarified that this isolated lane is the registered directory
writer and relay.sh exists only on its host. The prior owner-ack blocker is
resolved; no VM relay is needed. Exact committed head is in exported handoff.json.

## Changes for live owners at cut-over

- `Solidity/Semantics/AbiAccess.lean`: replace 15 obsolete Except.noConfusion
  applications with constructor case elimination. Move bodyValuesA_off's
  simplification after Entered constructor splitting; remove an empty simp.
  No declaration signature, executable definition, import, guard or budget change.
- `Solidity/Semantics/AbiEntryProofs.lean`: prove tailFits_of via symbolic bounded
  modular arithmetic, retaining its exact statement. Seven new private declarations:
  subAt, subAt_eq_sub_of_le, tailFits_at, tailFits_transfer, slt_of_toInt_lt,
  lim_add_one_lt_H, H_lt_W. subAt is a private arithmetic helper matching existing
  sub; the other six are proved lemmas. Zero-tail wraparound and positive-tail
  subtraction are separate cases. The opaque reflection lemma avoids kernel
  recursion in instantiated decision procedures. Reorder regionFits_of's
  reflection/case splitting; explicitly simplify cvalAt's false branch.
  All original statements, executable definitions, axiom guards and limits remain.
- Add scoped census, clean diagnostic, compatibility survey, freeze-manifest
  tooling, five scanner negative controls and four isolated Except proof examples.
  No additional production module/import registration is requested.

The arithmetic refactor warning was given before work. File history contained
4fad27235 and 2e7af4b2e, with no speed change being undone. Failed experimental
proofs are not retained in the committed source; their logs remain off Git.
No new sorry, axiom, native_decide, premise/exclusion, or heartbeat/recursion limit.

## Checkpoints

1. Partial: 82 scoped source files and 162-module dependency closure inventoried.
   Full source hashes account for every original file. Old clean diagnostic
   passes 111 modules then stops in out-of-scope Source.Horizon at 300.188759636s,
   exit -9/MODULE_300S_STOP. Interrupted total wall 989.583601066s and peak child
   RSS 3728392 KiB are not a full baseline. BASELINE_INCOMPLETE remains open.
2. Partial: official coordinator archive SHA256
   7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d verified.
   Lean 4.35.0 Release commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
   Lake 5.0.0-src+eb6cafb. Old Lean 4.24.0 Release commit
   797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
   KeySort passes on both. All five independent ABI modules now pass on 4.35.
   Both modified files also pass on 4.24, including unchanged axiom guards.
3. Blocked: full clean new build, affected validation and run-lean.sh pending.
   Compatibility survey visits all 162 modules: 19 pass, 4 fail, 139 dependency
   blocked. The in-scope failure AbiEntryProofs is repaired in later samples;
   5 assigned modules pass, remaining 77 retain external dependency blockers.
   The survey itself has not been rerun after that repair. No old-version
   artifacts were imported into new checks and no per-master cache was used.
4. Partial: patch/bundle, source and lexical theorem-header hashes, dependency
   request report and checksums exported for coordinator retrieval. 80 of 82
   sources are identical to base. Public theorem headers in the changed two
   match base exactly. These hashes/reviews are not elaborated API equivalence.
   Delivery to migrate-root-gate and final cut-over remain coordinator work.

## Historical matched samples (before H78)

sample-old-02 and sample-new-01 rebuild the same two modified files, using
identical source hashes, module order, serial settings, corresponding already
built import libraries, 12 GiB address-space cap, no host swap and 4 GiB reserve.
This is incremental file checking, not a clean full-directory benchmark.

| Measure | Lean 4.24 | Lean 4.35 | Change |
|---|---:|---:|---:|
| AbiAccess wall seconds | 5.769160289 | 4.015150842 | -30.40% |
| AbiEntryProofs wall seconds | 6.779386821 | 4.763259294 | -29.74% |
| Combined wall seconds | 12.548547110 | 8.778410136 | -30.04% |
| Peak child RSS KiB | 410744 | 560936 | +36.57% |

H76 resolves QMEM (per H69): continue toward matched clean full builds under
unchanged resource limits; include this +36.57% RSS growth in the human cut-over
report. This sample is not a full clean comparison. No memory hold remains.
H76-decision.txt preserves the supplied coordinator answer verbatim.

The fresh H76 clean new attempt (new-clean-h76-01) passes KeySort, all five ABI
modules, AST and SpecSyntax, then fails Syntax.Raw. Nine attempted modules,
eight pass, one fails; complete=false. Interrupted wall 59.729785591s, peak child
RSS 1514316 KiB. This is an incomplete build, not a comparable full-build number.
The old complete baseline and full before/after comparison remain unresolved.

## H78 resource policy and affected-module measurements

H78 directs migration lanes to continue past memory increases, retain before/after
peak RSS and wall time, and keep the 8 GiB module cap. No RSS-growth hold remains;
memory growth must be reviewed at human cut-over. The historical scripts had a
12 GiB address-space ceiling. Their original measurements/settings are retained;
they do not demonstrate enforcement of the H78 8 GiB ceiling.

All four diagnostic runners now share bounded.py: 8 GiB per-process RLIMIT_AS
(a conservative RSS bound for these direct Lean processes), 4 GiB available-memory
reserve, no host swap, 300-second module timeout, one serial Lean job with -j1 and
LEAN_NUM_THREADS=1. This is not an aggregate cgroup RSS cap. No systemd-run,
heartbeat/recursion-limit increase or proof change was made. Existing source
repairs and all public statements remain unchanged this turn.

The helper uses waitid(WNOWAIT) to retain the exited leader's PID while terminating
its owned process group, then wait4 for exact per-child ru_maxrss and reaping.
Timeout/resource stops can never pass, even with exit0. Resource controls exercise
the actual 8 GiB hard/soft AS limit, refusal of a 9 GiB allocation, separate child
RSS values, timeout cleanup, normal-leader descendant termination and stopped-exit0
rejection. Descendant termination is checked; its final reaping belongs to the OS.
Finder/skeptic findings for normal completion cleanup and the stop/exit race were
fixed and re-reviewed. h78-resource-controls-02 passes. These non-Lean controls
establish guard behavior, not proof acceptance.

Matched incremental samples h78-sample-old-02 and h78-sample-new-01 use identical
source-closure hashes, order and finalized guard/settings. Both modified modules
pass on both versions with stop=null. compare_samples.py rejects mismatched input,
settings/order or failed/stopped rows, and refuses matched but non-H78 settings.
A negative control rejects equal12GiB inputs. Exact per-module measurements:

| Module | Old wall s | New wall s | Old RSS KiB | New RSS KiB | Wall delta | RSS delta |
|---|---:|---:|---:|---:|---:|---:|
| AbiAccess | 4.761859098 | 4.515427488 | 341888 | 555376 | -5.18% | +62.44% |
| AbiEntryProofs | 6.771159879 | 4.016633253 | 432896 | 563108 | -40.68% | +30.08% |

Combined sampled wall: 11.533018977 -> 8.532060741 seconds (-26.02%). Maximum
sampled module RSS: 432896 -> 563108 KiB (+30.08%). These are single incremental
samples on the same migrated source tree, not a clean full-directory comparison
or a statistical speed claim. They supersede neither the original pinned-base
baseline requirement nor the remaining full performance gate.

Continuing as directed, new-clean-h78-01 uses fresh outputs and the same 8 GiB guard:
KeySort, five ABI modules, AST and SpecSyntax pass, then Syntax.Raw fails. Nine
attempts/eight passes, complete=false, interrupted wall63.280466661s and maximum
per-child RSS1501364KiB. No resource stop occurred. The fresh clean comparison
cannot complete until the external Raw overlay and other dependency migrations
are supplied; original old Source.Horizon baseline timeout also remains unresolved.
Generated API drift and full affected/root gates remain open, with no exemptions.

```sh
python3 tests/h62/item6/migrate-semantics/resource_controls.py --out /workspace/h62-migrate-semantics-evidence/h78-resource-controls-02
python3 scripts/h62/item6/migrate-semantics/probe.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --lib /workspace/h62-migrate-semantics-evidence/old-clean-02/lib --out /workspace/h62-migrate-semantics-evidence/h78-sample-old-02 --only Solidity.Semantics.AbiAccess --only Solidity.Semantics.AbiEntryProofs
python3 scripts/h62/item6/migrate-semantics/probe.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --lib /workspace/h62-migrate-semantics-evidence/new-clean-h76-01/lib --out /workspace/h62-migrate-semantics-evidence/h78-sample-new-01 --only Solidity.Semantics.AbiAccess --only Solidity.Semantics.AbiEntryProofs
python3 scripts/h62/item6/migrate-semantics/compare_samples.py --old /workspace/h62-migrate-semantics-evidence/h78-sample-old-02 --new /workspace/h62-migrate-semantics-evidence/h78-sample-new-01 --out /workspace/h62-migrate-semantics-evidence/h78-comparison.json
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --out /workspace/h62-migrate-semantics-evidence/new-clean-h78-01
```

The latest Hash-owner receipt a3f49ee0ec1829e63022c90194048d5a1ffe0d22 supplies the
same exact patch digest as the prior H70 receipt. It is not a new source overlay.
hash-owner-h78-01 rechecks that same fixture under the finalized8GiB guard: exit0,
stop=null, wall4.264352025s, exact peak RSS603240KiB. Transport hash and full Git blob
match. Branch Hash remains unchanged and full affected Hash gates remain pending.
hash-owner-h78-ack.json records the receipt and fixture-only result for relay.

This continuation completed four local items: guard/resource controls, matched
samples, a fresh clean attempt, and the Hash-owner cap validation. Full assignment
remains blocked. Fresh-thread coordination retains this same original VM/branch/
goal; do not create or reset a goal, or claim the failed clean gate completed.

## Exact-base old clean attempt and controller calibration (H78)

A private detached worktree at `/workspace/h62-migrate-semantics-base-8g` remains
clean at exact base c6f550e281a7e5affa9a99bc2cdaed556dec00e4. No producer file was
edited there and no branch/default/master change was made. The finalized collector
from the assigned branch ran against that worktree with fresh outputs:

```sh
cd /workspace/h62-migrate-semantics-base-8g
python3 /workspace/solidity-lean/scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/h62-migrate-semantics-evidence/old-clean-h78-01
```

111 modules pass, then Source.Horizon aborts with std::bad_alloc (exit-6) after
99.775619097s, measured RSS1835812KiB. Interrupted total788.722999508s;
complete=false. This occurred under the conservative8GiB virtual-address ceiling;
it does not demonstrate an8GiB resident-memory overrun. h78-clean-attempts.json
checks matching old/new settings and common-prefix order; both full attempts are
incomplete, so full_wall_delta_percent=null. Existing incremental samples remain
separately labeled and are not promoted to clean-build results.

To distinguish virtual-address restriction from the actual memory budget, a managed
Docker diagnostic used the pinned image
python@sha256:4840d514c583a4d3d8cad3940e68dee6f0f6f3635c12fcd0a3d74c21a5b93a54,
verified cgroup-v2 memory.max=8589934592 and memory.swap.max=0, disabled network,
and mounted pinned sources/toolchain/imports read-only. All162 original source
hashes match the pinned snapshot. Inherited RLIMIT_AS is unlimited in this mode;
the memory controller still enforces the8GiB job cap. No memory, heartbeat,
recursion or time budget was raised. The4GiB available-memory guard reads the
actual ancestor VM controller, not the job's8GiB controller.

The diagnostic uses already-built original dependency artifacts: it is not a clean
baseline or a timing comparison with the native samples. KeySort passes, then
Source.Horizon reaches MODULE_300S_STOP: exit-9, wall300.253372037s, process peak
RSS3612648KiB. Charged job-memory peak3948941312bytes; all OOM counters are0.
This establishes the unresolved time-bound prerequisite independently of the
virtual-address allocation failure. It is not evidence that the memory cap was
exceeded, a theorem failed, or the full old baseline completed.

The original run's outer host writer lock was confirmed busy with fcntl and saved
alongside pinned-image, read-only mount and controller inspection evidence in
h78-cgroup-prerequisite-01/launch-inspect.json. lslocks in a nested namespace was
not a reliable indicator. The reproducible launch_cgroup.py now bind-mounts the
same physical host writer.lock and the container script acquires it before Lean.
The wrapper records Docker configuration/state and removes only its own container.
No systemd-run, privileged mode, host networking or daemon restart is used.

Controller roots in mountinfo are namespace-relative (including /..), so ancestry
is checked using the actual cgroup kernfs device/inode under the VM controller's
Docker container ID, not string-prefix inference. Controls reject unverified caps,
regular directories masquerading as controllers and wrong job identities.
h78-cgroup-controls-03 passes with an exclusive host-file lock, actual8GiB cap,
swap disabled and cleanup recorded. Earlier control02 failed closed on overly
strict namespace-string inference; no Lean ran in that control. Review findings
were corrected and independently rechecked. Default native fallback controls04
and the H78 sample comparator also pass after these changes.

```sh
cd /workspace/solidity-lean
python3 scripts/h62/item6/migrate-semantics/launch_cgroup.py --out /workspace/h62-migrate-semantics-evidence/h78-cgroup-controls-03 --control-only
# Optional repeat of the isolated prerequisite; use a fresh output directory:
python3 scripts/h62/item6/migrate-semantics/launch_cgroup.py --out /workspace/h62-migrate-semantics-evidence/h78-cgroup-prerequisite-repeat
```

All container runs have ended and owned containers were removed. Full baseline,
new build, affected validation, generated-interface compatibility and root-gate
acceptance remain unresolved. Native-AS and container-controller measurements
are separate environments and must not be combined into a full timing result.

## Elaborated ABI type evidence (H76)

ExportAbiTypes.lean serializes elaborated constant types (de Bruijn bound
variables, binder visibility, constant names, universe structure/parameter order,
literals and projections). Binder names, metadata and let optimization flags are
ignored; this is syntax comparison, not definitional equivalence or value/trust
auditing. Unknown universe parameters/free/metavariables fail closed; positive
and negative universe controls run during export. Private names are omitted and
the seven new private helpers remain independently reviewed.

api_evidence.py rebuilds all five ABI modules from the exact pinned base with
4.24, then exports those environments and the successful clean4.35 ABI artifacts.
Both sides' source hashes, new OLean hashes, exporter/census hashes and versions
are recorded. All seven Lean subprocesses in abi-api-h76-02 exit0; the comparison
orchestrator exits1 with status=differences and compatibility_gate=fail:

- 848 original non-private constants versus 917 new.
- 761 exact type-AST matches, 54 changed, 33 removed, 102 added.
- Changed/removed APIs are compiler-generated: noConfusion, equation, matcher and
  proof helper declarations. Named authored types checked, including tailFits_of,
  mdec_cval, cpart_agree and bodyValuesA_off, match.
- Generated APIs are not excluded from the frozen-interface requirement. Full
  API compatibility is unresolved. generated-api-owner-request.json sends the
  exact differences to migrate-root-gate for a compatibility plan. No backward
  compiler option, frozen pin, premise or statement was changed to hide drift.

Commands (use a fresh output directory on repeat):

```sh
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --out /workspace/h62-migrate-semantics-evidence/new-clean-h76-01
python3 scripts/h62/item6/migrate-semantics/api_evidence.py --out /workspace/h62-migrate-semantics-evidence/abi-api-h76-02
```

Independent finder/skeptic confirmed all counts, hashes and boundaries, and the
serializer's fail-closed universe guard. Their provenance and explicit failing
API-status findings were fixed. Neither reviewer used Lean/server or wrote fixes.

## External owner requests

No edits outside assigned scope. Request statement- and budget-preserving
migration overlays from corresponding owners/root gate:

- Syntax.Raw: String/Slice API failures at lines 597, 650, 665, 682, 684.
  New drop returns Slice, Slice.toList/String.dropRight availability and endsWith
  method shape differ. Most assigned modules transitively depend on this.
- Hash.CollisionBound: prior failures are addressed by a supplied H70 owner
  overlay. Owner ticket head 78c110f83dc1a30700acd1b5bd34b19f61da6ccd, source head
  2a18afcdba00a85645b0b3079704f78ffcd78860. The isolated fixture below passes;
  branch Hash source stays unchanged. Full owner/root integration remains pending.
- Source.Ctor: original 200000-heartbeat exhaustion at 641 and dependent
  elimination failures at 715. Preserve that budget and all admission exclusions.
- Old baseline Source.Horizon: original source exceeds diagnostic 300s bound.
  Coordinate baseline/gate resolution; no theorem or resource limit was relaxed.

Exact commands, errors, source hashes and per-module dependency statuses are in
survey-01 and old-clean-02, under `/workspace/h62-migrate-semantics-evidence/`.
The original new-clean-01 failure is superseded only for the repaired files.
old-clean-01 was invalid tooling (missing GNU time); sample-old-01 used a
version-specific lemma alias and failed. Neither is a passing gate.

## H70 owner ticket responses

The solcvalidation request DEP-PRIOR-FULL-3 (requester head
0bd9e2519c43f1757674d2051a7786ac5688c2bb) is covered by the existing AbiAccess
repair and fresh H76 clean pass. AbiAccess-owner.patch, AbiEntryProofs-owner.patch
and solcvalidation-owner-response.json are exported for coordinator relay. No
additional production edits were made in response. Other forwarded SortCheck,
Language and Backend requests remain their owners' work; not locally validated.

owner_hash_fixture.py reproduces the supplied Hash overlay in an off-Git fixture
only. Its normalized transport SHA256 matches the supplied
3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff exactly, with
full result Git blob 092971eda8c7d6997276a92ba19b25b7ce05844e. Fixture source SHA256
cfddc9e45edee7ac2f5a83c3212c741034d39a4e700a5384689b4ee6035565a0. Its bounded
4.35 compile exits0 in 4.512271412s, peak child RSS594348KiB, with original axiom
guards unchanged. This establishes fixture compatibility, not full owner gates.
No Hash file was changed in this branch. Original path normalization was corrected
without repeating the passing Lean check. Reviews required exact full blob and
transport SHA checks before compilation; these guards are now enforced and pass
in a separate verification-only run (which is not itself a Lean check).

```sh
python3 scripts/h62/item6/migrate-semantics/owner_hash_fixture.py --out /workspace/h62-migrate-semantics-evidence/hash-owner-h70-01
python3 scripts/h62/item6/migrate-semantics/owner_hash_fixture.py --out /workspace/h62-migrate-semantics-evidence/hash-owner-h70-verify-02 --verify-only
```

## Reproduction, reviews and remaining work

Run the following from the repository root; diagnostic commands write off Git:

```sh
python3 scripts/h62/item6/migrate-semantics/census.py --out /workspace/h62-migrate-semantics-evidence/census.json
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/h62-migrate-semantics-evidence/old-clean-02
python3 scripts/h62/item6/migrate-semantics/probe.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --lib /workspace/h62-migrate-semantics-evidence/new-clean-01/lib --out /workspace/h62-migrate-semantics-evidence/survey-01
python3 scripts/h62/item6/migrate-semantics/freeze.py --base c6f550e281a7e5affa9a99bc2cdaed556dec00e4 --out /workspace/h62-migrate-semantics-evidence/frozen-source-and-signatures.json
python3 tests/h62/item6/migrate-semantics/scanner_controls.py
node scripts/check-layers.mjs
```

Existing output directories are refused; choose new names on repeat. The two
sample commands use probe.py with --only Solidity.Semantics.AbiAccess --only
Solidity.Semantics.AbiEntryProofs and corresponding old/new toolchain/lib paths.
All actual module commands/exits/timings are recorded in summary.json. survey-01
predates final probe hardening (unknown target rejection, public import handling,
nonzero exit on failures); its recorded module statuses remain valid.

Independent read-only finder and skeptic reviews used no Lean/server or edits.
Both found proof-only repairs preserve statements, cases, pins and budgets.
Findings fixed: unused simp arguments; scanner comments/strings/attributes and
root consumers; missing time dependency; source cleanliness; resource summaries;
process cleanup and exit race; survey unknown targets/public imports. Reviewers
confirmed matched hashes, metrics and limits of lexical/interface evidence.
Existing conditional-lemma deprecation warnings remain for old/new compatibility.

Five scanner controls pass. Four isolated constructor proofs pass both versions
but do not validate production modules themselves. Layer check passes: 857 core
modules, zero elaborator or checked-parser reachability. Python AST checks pass.
No Lean MCP tools exposed; bounded serial CLI diagnostics were used. Final
repository run-lean.sh, frozen SolKey conformance and affected validation remain
pending, so no RUNTIME_GATE_PASS. VM cap is 16 GiB; no systemd-run used.

Prior checkpoint work items: AbiAccess repair, full compatibility survey,
and AbiEntryProofs repair/review. Fresh-thread handoff goes to the coordinator
with this same original VM/branch/goal, not a replacement goal. QMEM is resolved. Resolve external migration overlays, the old baseline timeout
and generated API drift; then complete clean matched builds, full interface
verification, affected/final gates and root-gate handoff. Full assignment
remains unfinished; maintain all original proof/resource budgets.

H76/H70 continuation delivered three items: a fresh clean-build attempt, elaborated
ABI interface evidence, and owner-ticket responses/Hash fixture validation. Fresh
thread coordination retains the same VM, branch and original unfinished goal.

This H78 continuation preserves the same original VM/branch/goal. Resource calibration,
matched samples, clean attempts and owner-fixture checks are checkpoint evidence,
not completion of the frozen assignment. The coordinator owns fresh-thread resumption.
