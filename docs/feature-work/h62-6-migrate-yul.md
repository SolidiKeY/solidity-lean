# H62/H63 migrate-yul migration overlay

Owner: solidity-h62-6-20261106/migrate-yul. Repository: `/workspace/migrate-yul`.
Branch: `codex/solidity-h62-6-20261106/migrate-yul`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The original `/workspace/solidity-lean` checkout and its `work` branch are preserved.
`git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4` succeeded;
`git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master`
returned 0. No assigned remote branch existed when inspected.

## Queue status — Nov7 7683091e rebaseline and complete old inventories

Coordinator requested rebaseline on origin/master2a43bf4fc. The original6aadc4999
head was cherry-picked rather than literally ancestral: all3 stable patch IDs and
all task files match upstream fdb282c76,05ba4cc6b,50b9539fd. Preserving merge into
assigned branch produced c60d01cb49e5dff1287de4c572b39fa46bd9a48b; no reset/discard.
Current upstream code includes further producer changes; originalc6 evidence
remains explicitly pinned-source evidence, not a current-master timing baseline.

1. **Partial:** pinned clean2143-module baseline passed. Original persisted-kernel snapshots
   now1774/1774 verified, with55647 declaration records and52406 public records.
   All32734extra compiler names now have source-bound old IR signatures; public
   visibility/attributes and new compatibility remain unresolved.
2. **Partial:** B05 production repair integrated upstream. H78 generated public
   API compatibility and full new-toolchain dependency closure remain pending.
3. **Pending:** full new build, common-source clean timings and regression gates.
4. **Partial:** reviewed tooling/evidence checkpoints; final root handoff pending.

No full API/migration/runtime gate pass, push, default-branch merge or PR claimed.
Original goal only; no create/reset. Historical retirement is superseded by the
coordinator's explicit continue instructions. Original scope/queue remain saved.

## Toolchains and prerequisite evidence

Coordinator inputs are in `/workspace/h62-coordinator-inputs`; all five files
match its `sha256.json`. The pinned official Linux archive is
`/workspace/migrate-yul-artifacts/toolchains/lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

Actual old versions: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release;
Lake `5.0.0-src+797c613` (Lean 4.24.0).
Actual new versions: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release;
Lake `5.0.0-src+eb6cafb` (Lean 4.35.0).
Tracked `lean-toolchain` and lakefile are unchanged. Builds use private TOMLs,
private build directories, disabled artifact cache and `--no-cache`; no
v4.24 per-master cache is used.

Old prerequisite command (exit 0):

```sh
python3 scripts/h62/item6/migrate-yul/build.py --root /workspace/migrate-yul --toolchain /workspace/.setup/tools/lean-4.24.0-linux --artifacts /workspace/migrate-yul-artifacts --census /workspace/migrate-yul-artifacts/evidence/census.json --label old-clean --kind key --clean
```

Decisive output: `solkeycheck: parsed 377 taclets, 131 read-bearing, table covers 131`;
`solkeycheck: OK — annotations match`. Explicit rules file:
`/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key`,
SHA256 `02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb`.
Full commands/results: `/workspace/migrate-yul-artifacts/old-clean/key-result.json`
and `key.log`. This prerequisite took 24.1033 seconds, sampled peak process-group
RSS 825,204,736 bytes. These are prerequisite measurements, not the clean Yul baseline.

The identical command with new toolchain path
`/workspace/migrate-yul-artifacts/toolchains/lean-4.35.0-linux` and label
`new-clean` returned 1. Evidence:
`/workspace/migrate-yul-artifacts/new-clean/key-result.json` and `key.log`.
`Solidity/SortCheck/Parser.lean:76:13` reports invalid field `String.trim`;
subsequent field/type/evaluation errors cascade. Compiler diagnostics mentioning
sorry are cascading error placeholders; this lane added no sorry or axiom.

## Typed dependency request for migrate-root-gate

**B-KEYSORT-API (external owner migration, blocking required prerequisite):**
Owner migration root/gate must arrange the migration of
`Solidity/SortCheck/Parser.lean` on the same pinned toolchain while preserving
its parser behavior and frozen rules. The failing function is `headerName?`,
first error at line 76. The Yul lane cannot edit this out-of-scope file. Re-run
bounded KeySort after an approved owner patch/fixture is provided; do not replace
or skip the prerequisite. No owner reply or imported fix has been received.
No `relay.sh` exists in the supplied repository/setup/coordinator inputs, so
this exact-file owner request is saved here for coordinator retrieval.

The census records all direct cross-directory dependencies and external
consumer paths in `/workspace/migrate-yul-artifacts/evidence/census.json`.
It is source discovery; further API failures must become owner requests, not
out-of-scope edits. Exact-file owner coordination remains required before any
existing Yul source changes.

## Measurement and backfill tooling

`scripts/h62/item6/migrate-yul/census.py` generates the bulk census off Git.
`build.py` builds the source dependency closure one target at a time in
import order; package and library arguments explicitly include `-j1`, with
`LEAN_NUM_THREADS=1`, the original stack setting and unchanged proof budgets.
The inherited VM cgroup hard limit is 16 GiB, CPU quota four CPUs; host swap
is zero. A 250 ms watchdog terminates its own process group above 12 GiB RSS
or below 4 GiB available cgroup reserve. This sampled watchdog is not a hard
12 GiB RSS cap. No systemd-run is used. The writer lock is held for the build;
signals/exit cleanup reap the owned child before releasing it. Driver, private
config, resource snapshot and before/after source hashes are recorded.

For CLEAN Yul measurements, use fresh labels `old-yul-clean` and
`new-yul-clean`, `--kind yul --clean`; never reuse KeySort build directories.
The driver refuses an existing clean build directory. Full runs remain pending.
Private output paths and serial policy are identical between versions.
`compare.py OLD/yul-result.json NEW/yul-result.json` rejects incomplete,
unverified, nonfinite or incomparable measurements; it compares normalized
configuration and target/resource identities, retains both source census hashes,
escalates any wall/RSS regression (exit 2), and stops above 10% (exit 3).
Full repository `./run-lean.sh` final validation remains required after owner
migrations; no successful final gate is claimed.

Deterministic acceptance commands:

```sh
python3 tests/h62/item6/migrate-yul/test_census.py
python3 tests/h62/item6/migrate-yul/test_compare.py
python3 -m py_compile scripts/h62/item6/migrate-yul/build.py
```

Scanner controls cover nested comments, strings, char literals, attributed
definitions, local/anonymous instances, anonymous examples, acceptance commands,
Bridge reverse consumers, full Yul file count and topological ordering.
Comparator controls cover incomplete reports, resource drift, NaN, source
revisions, any regression and >10% stop. These are external Python checks,
not Lean proofs. No existing Lean declaration, statement, premise, exclusion,
observation, proof budget or intrinsic representation has been changed.
No new Lean helper/module, axiom, sorry or trust shortcut was introduced.

## Independent read-only review record

Finder and skeptic agents reviewed source and evidence without Lean servers,
builds or writes. Findings fixed: attributed/anonymous declarations, line
numbers, character literals, Bridge consumers/module names, anonymous examples
and guard controls; test coverage after adding KeySort order; cache-isolated
clean runs; signal cleanup; sampled versus hard memory limits; measured
resources; stale source detection; normalized comparisons; invalid numbers.
Final finder and skeptic dispositions: PASS for tooling only. All findings resolved;
4 scanner controls and 8 comparator controls pass. Review record:
`/workspace/migrate-yul-artifacts/evidence/reviews.md`.
The queue checkpoints remain partial until their full gates/reviews pass.

## Handoff

Coordinator retrieves the branch and static artifacts on this same VM.
Artifact root: `/workspace/migrate-yul-artifacts`.
Original tooling patch: `/workspace/migrate-yul-artifacts/original.patch`.
Handoff export: `/workspace/migrate-yul-artifacts/handoff.md`.
Evidence: `/workspace/migrate-yul-artifacts/evidence` plus each private run directory.
Static checksum manifest: `/workspace/migrate-yul-artifacts/SHA256SUMS`.
No final timing comparison, elaborated frozen-interface hash, all-module new
build, owner approval, or final root gate acceptance exists yet.

## Continuation checkpoint: resource calibration and scoped backfill

The original goal remains active and unfinished. Original VM:
`ccarenv_b64_Y2NhcmVudl8yODkwNjBkZWY4ZjA4MTkxODQxNGQ4ODBiMjNlNzAwNw`.
Goal reference: launcher-owned original objective, rendered prompt SHA256
`97ec48be960b9ab7efbf4fb5c674d50e2306820a8ab6c082e8f9e1b6a8139e53`.
No goal was created/reset; `get_goal` is not exposed, which the coordinator
confirmed is not a blocker. Resume this same VM/branch, not a replacement goal.

The first CLEAN attempt **failed**, not passed:
`/workspace/migrate-yul-artifacts/old-yul-clean/yul-result.json` records 425
successful modules followed by `Solidity.Source.Horizon` resource stop, exit
`-15`, target wall 547.6047 seconds, sampled target/group peak 6,750,199,808 bytes.
Its v1 guard measured raw cgroup headroom, including reclaimable cache as used.
A targeted, explicitly non-clean v2 probe also **failed**:
`/workspace/migrate-yul-artifacts/old-horizon-guard-v2/probe-result.json`, target
wall 653.2827 seconds, RSS 8,292,679,680 bytes. Its recorded stop has cgroup
cap 17,179,869,184, current 14,655,553,536, host available 8,469,323,776, and an
inactive-only estimate of 4,272,156,672 bytes. This is below the fixed 4 GiB
threshold but omits clean active file cache. Neither attempt is a baseline
success; neither establishes a new-versus-old slowdown or a Lean proof error.

The reviewed v3 policy estimates availability after reclaim using:

```text
clean = max(0, file - shmem - dirty - writeback - unevictable)
allowance = min(clean / 2, measured host low-watermark reserve)
available = min(host MemAvailable, cgroup cap,
                max(0, cap - current + clean - allowance))
```

It counts no slab reclaim and retains the raw and inactive-only metrics.
The measured host low-watermark reserve is 88,186,880 bytes. This remains a
sampled estimate, not an allocation guarantee or exact kernel MemAvailable
replica. All numeric bounds remain unchanged: 12 GiB sampled process-group RSS,
`-M12288`, 4 GiB estimated available reserve, hard 16 GiB VM cap, no swap,
`-j1` and `LEAN_NUM_THREADS=1`. No proof budget or VM budget was increased.
Seven resource controls pass; independent finder and skeptic reviewed the
calculation, exclusions and allowance. Prior failures are retained.

Next: run `old-horizon-guard-v3` as a non-clean targeted resource probe. If it
passes, start a fresh `old-yul-clean-v3 --kind yul --clean`; the final new run
must use the identical hashed driver/resource policy and fresh cache. The
original KeySort owner dependency remains unresolved. Do not reuse targeted
probe timing as the full clean baseline. No full timing delta exists.

### String dependency controls

`generate-string-fixtures.py --check` reproduces two small fixtures under the
assigned tests directory. Legacy reproduces the pinned `headerName?` helper;
New changes only String trim/drop API spelling and copies. Each checks 23
finite runtime cases: six accepted inputs and seventeen rejected boundaries,
including ASCII whitespace, digit-leading/punctuated identifiers, brace errors,
backslash rules, Unicode letters, NBSP and vertical tab.

The finite String cases are **external execution checks**, not a universal
parser equivalence proof. An initial uncommitted attempt to reduce the entire
String packet with `decide` did not reduce; its failed diagnostics remain in
`old-string-fixture`, `old-string-fixture-v2`, and `old-string-diagnostic`.
Final fixtures instead clearly separate runtime checks from the two proved
logical guards: `whitespace_exact` has no axioms; `digit_rejected` uses existing
`propext`. No new axiom declaration, sorry, native_decide or budget increase was
introduced. No original/frozen statement or owner parser source was changed.

Passing, source-bound final controls:
`/workspace/migrate-yul-artifacts/old-string-bound/probe-result.json` and
`/workspace/migrate-yul-artifacts/new-string-bound/probe-result.json`.
Both bind fixture and generator hashes before/after. These do not satisfy
KeySort or authorize editing `Solidity/SortCheck/Parser.lean`.

### Private interface inspection controls

`ExportInterfaces.lean` is an external inspection helper under tests; it is
not registered in core. It imports private/all module data, retains every
persisted kernel declaration including shared entries with separate authoritative
provenance, and records IR-only names separately. Explicit Name/Level/Expr
encoding preserves binder information, literals, projections and universe order;
only expression metadata is erased. Type, implementation and proof encodings
remain separate. It records complete ConstantInfo metadata and a private-kernel
transitive axiom union, failing on missing dependencies. Anonymous source checks
still require the prescribed builds; snapshots cover persisted declarations.

`interfaces.py` requires a successful source-bound probe, a fresh output
path/size/SHA256 recorded by that probe, exact exporter/module/output arguments,
and matching private-mode header/footer/count. It retains verified deterministic
gzip snapshots off Git, with separate type/signature/implementation/proof hashes.
Incomplete, unrelated or modified outputs are rejected. All source and generated
payload differences, provenance changes and header/IR differences are retained
for review. Structural agreement is not semantic equivalence, proof replay,
attribute/instance-priority compatibility or proof-budget acceptance.

The isolated `InterfaceFixture.lean` compiles on both official toolchains; only
the v4.24 private-module **control** needs `-Dexperimental.module=true`. That
flag is not added to migration/baseline builds. Both inspectors retain 27
control declarations, three private declarations and the expected transitive
`propext` union. Source-public control signatures match. Seven raw generated
type differences and IR name/count differences remain explicit findings; they
are not accepted production exclusions or migration passage.

Actual bound output/control evidence:

- `/workspace/migrate-yul-artifacts/interface-fixture-old-bound/probe-result.json`
- `/workspace/migrate-yul-artifacts/interface-fixture-new-bound/probe-result.json`
- `/workspace/migrate-yul-artifacts/old-interface-bound/probe-result.json`
- `/workspace/migrate-yul-artifacts/new-interface-bound/probe-result.json`
- `/workspace/migrate-yul-artifacts/evidence/old-interface-bound.json`
- `/workspace/migrate-yul-artifacts/evidence/new-interface-bound.json`
- `/workspace/migrate-yul-artifacts/evidence/interface-controls.log`
- `/workspace/migrate-yul-artifacts/evidence/interface-control-differences.json`

Twelve snapshot acceptance controls pass. The control comparison intentionally
returns exit 2, `differences_require_review`; it is not a passing frozen-interface
migration gate. Full Yul interface exports and comparison remain outstanding.
Finder and skeptic approved the final helper, wrapper and bounded control
checkpoint; neither ran Lean or wrote files. Full affected checks, fresh clean
builds, regression disposition and migrate-root-gate acceptance remain required.

### Routing receipt and owner coordination

The coordinator confirmed `relay.sh` is host-only. Its absence is not a VM
installation task. Keep exact-path requests in CLOUDVM-RESULT for retrieval.
B-KEYSORT-API still requests the root/live owner migration of
`Solidity/SortCheck/Parser.lean` (absolute lane path
`/workspace/migrate-yul/Solidity/SortCheck/Parser.lean`). No owner fix or exact-file
permission has been received. Existing Yul originals remain unchanged.

Incoming H70 routing is context only, not additional source ownership:
requester `solidity-h62-2-20261106/audit-label-execution`, head
`a107fd353aba492a3144da90cabcbde20032ca0c`, requester source
`/workspace/solidity-lean/tests/h62/item2/audit-label-execution/owner-tickets.json`.
Coordinator host receipt:
`/home/guilherme/.local/state/cloudvm-coord/receipts/router-20261106T142920Z/solidity-h62-2-20261106__audit-label-execution/66615193dea4-owner-tickets.json`,
11,017 bytes, supplied SHA256
`4d515bbb0b5de8540c660ccf8c5f0aa5efa3a2f9d502eba8dab5142391ed51f1`.
The full ticket is not staged in this VM and was not inspected here. The
routing reports unfinished audit gates/51 ownership questions; this lane has
not taken over witness/producer work. No permission, budget change, merge,
publication or passing-gate claim is inferred from that routing.

## Passed resource probe; next full clean attempt

`old-horizon-guard-v3` passed: actual fresh `Solidity.Source.Horizon` build,
exit 0, 658.2082 seconds, sampled peak group RSS 8,399,425,536 bytes,
minimum estimated availability 7,187,349,504 bytes, no resource stop.
Both read-only reviewers verified the successful build, source bindings and
unchanged numeric limits. This is a **non-clean resource probe**, not the full
old baseline or a migration performance delta. The first two failures remain
failures in their original directories.

Probe metadata caveat: its `config_sha256` hashes an unused generated probe
config. The command actually consumes
`/workspace/migrate-yul-artifacts/old-yul-clean/lakefile.toml`, SHA256
`224bbb0131bef03069aab1fcc37447c1f6cfc60e280547f768f47ac73521dc19`.
That checksum matches the preserved original build report and the static
checkpoint manifest. Additional binding evidence:
`/workspace/migrate-yul-artifacts/evidence/horizon-v3-config-reference.json`.
Future arbitrary probes must bind consumed `-f` files explicitly; normal full
build mode directly consumes the generated config whose hash it records.

Next full gate is a fresh `old-yul-clean-v3 --kind yul --clean`, using empty
private build outputs and the reviewed v3 driver. No original source, frozen
statement, toolchain pin, proof budget or numerical resource limit changed.
All four migration checkpoints remain unfinished; B-KEYSORT-API remains open.

## Completed clean old baseline and H70 B05 candidate

`old-yul-clean-v3` passed all 2,143 census targets (1,774 Yul, 369 external
closure dependencies), exact topological order, all exits 0, no resource stops.
Wall 7,291.842443605 s; sampled peak process-group RSS 8,441,331,712 bytes;
minimum estimated availability 7,060,635,648 bytes. Lean 4.24.0 and Lake
5.0.0-src+797c613, unchanged 16 GiB cgroup, -j1, -M12288, stack 131072,
4 GiB estimated reserve, no swap, cache disabled and fresh private build path.
Both census-source checks passed. Command:
`python3 scripts/h62/item6/migrate-yul/build.py --root /workspace/migrate-yul --toolchain /workspace/.setup/tools/lean-4.24.0-linux --artifacts /workspace/migrate-yul-artifacts --census /workspace/migrate-yul-artifacts/evidence/census.json --label old-yul-clean-v3 --kind yul --clean`.
Evidence: `/workspace/migrate-yul-artifacts/old-yul-clean-v3/yul-result.json`
and `yul.log`. Independent read-only finder and skeptic verified coverage,
real fresh builds, hashes and bounds; no baseline findings remain. Earlier
failed resource attempts remain failures, excluded from the baseline.
`Solidity.Source.Horizon` took 665.844 s here: report to root/gate owner;
this lane measurement does not establish a pass/fail for a different gate VM's
300 s policy. Full old interface export is still pending.

Latest H70 ticket requester head is d89b309029f9ad57f17711432aeef4990005994b;
ticket SHA256 5f63fe1a9f15bdd857e4bd601f59a36886cc06477474bcbf80bedf6ce2cc6c3d.
B05 is our migration reservation: `/workspace/migrate-yul/Solidity/Yul/ReservedNames.lean`.
The original remains untouched. New-toolchain `b05-new-original` locally
reproduced line 43 maximum recursion depth, exit 1. `b05-new-builtins` passed.
Proposed exact-file patch (not applied):
`scripts/h62/item6/migrate-yul/ReservedNames.proposed.patch`, replacing only
`reservedNames_count`'s `rfl` with `by decide +kernel` (kernel evaluator,
not native evaluation). Deterministic generator pins the original SHA and
preserves all 157 table entries/order, both theorem statements and the other
proof. It generates additive fixtures only. No depth/heartbeat/resource limit
changed. The first exploratory `simp only` candidate added propext to the count
proof and was rejected; its logs remain diagnostic, not accepted evidence.

`b05-old-original` and `b05-old-kernel-candidate` passed in 0.502923 and
0.502956 s respectively, sampled RSS 212,058,112 and 220,250,112 bytes.
`b05-new-kernel-candidate` passed in 0.757696 s, RSS 518,397,952 bytes.
These subsecond non-clean probes have 0.25 s sampling granularity and different
release runtimes; they are not the required clean performance comparison.
The new-release probe costs more wall/RSS; this provisional signal is reported
for root/gate review and is not waived or called a performance pass. No full
new timing delta is available; the >10% full-comparison stop rule remains.
Fresh compiled candidate probes and snapshots also passed on both releases.
`b05-old-original-axioms` confirms original count has no axioms, slotnum uses
propext; the candidate preserves those exact dependencies on both releases.

Three private-mode snapshots in `/workspace/migrate-yul-artifacts/evidence/`
(`b05-old-original.json`, `b05-old-candidate.json`, `b05-new-candidate.json`,
with deterministic gzip payloads) preserve all three original signatures and
metadata exactly. Candidate snapshots are equal across releases; count proof
changes and adds the kernel-generated theorem
`Solidity.Yul.reservedNames_count._proof_1_1` (no new axiom). Original count
snapshot has 3 declarations; candidate has 4, all accounted for. Table raw
implementation hashes differ between original and fixture solely in 31 binder
hygiene names containing their module paths; all other expression fields match.
No raw hashes are erased, normalized away, or accepted as migration equivalence.
The untouched original module and its downstream imports remain unvalidated
on v4.35. Snapshot/fixture success is not migration acceptance.

Reproduction: `python3 scripts/h62/item6/migrate-yul/generate-reserved-fixture.py --check`;
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-yul/check-reserved-controls.py /workspace/migrate-yul-artifacts/evidence`.
Actual bounded probe commands, exits, resource measurements and source/output
hashes live in each `/workspace/migrate-yul-artifacts/b05-*/probe-result.json`.
Exact-file coordinator/live-owner request is still required before applying
the proposed patch; latest H70 routing grants no original-file permission.

External v4.35 dependencies B01 Raw, B02 CollisionBound, B03 Scalar.Slice,
B04 Source.Ctor, B06 Frontend.Checked.Token all occur in this closure and need
owner overlays; their latest reported failures have not been locally replayed.
B-KEYSORT-API is locally reproduced in SortCheck/Parser.lean. B07 optional
Bridge package provisioning belongs its owner; core remains dependency-free.
No source statement/premise/exclusion, original interface, axiom pin, toolchain
pin, central module map or generated root has been edited. No runtime gate pass.

B05 final reviews: finder verified source/table/signatures/trust/output bindings,
no findings. Skeptic verified the same and found a diagnostic tag spelling
(`lambda` versus exporter `lam`); fixed to `lam`, control rerun passes. Neither
reviewer ran Lean or wrote files. This approves the additive checkpoint only.
Initial tooling-suite retry under read-only sandbox failed solely because
tempfile had no writable directory; corrected with an owned artifact TMPDIR.

Current tooling controls: 31 tests passed in 22.742 s using owned artifact TMPDIR.

## H82 retirement: final stopped handoff

Human-approved stop-and-handoff supersedes automatic continuation. Successor:
`solidity-h62-6-20261106/migrate-root-gate`. No new proof implementation follows.
Original VM `ccarenv_b64_Y2NhcmVudl8yODkwNjBkZWY4ZjA4MTkxODQxNGQ4ODBiMjNlNzAwNw`,
checkout `/workspace/migrate-yul`, assigned branch unchanged. Existing launcher
goal was never replaced, reset or completed. Requested state PAUSED cannot be
set: tool discovery exposes only `stop_goal(outcome: complete|blocked)`, no
pause/get_goal. Neither outcome was used as a substitute. Worker stops after
this acknowledgement; no automatic implementation continuation is authorized.

Full old interface export was interrupted safely under H82, supervisor exit130,
261/1774 modules sealed; 1513 remain. Its manifest deliberately records fail /
`export interrupted or incomplete`, not a pass. Current child had already exited;
no Lean, build driver or export process remains. Interrupted export evidence
and partial outputs are preserved, with H82-STOP.json explaining disposition.
Do not resume its same-label export blindly: wrapper requires a fresh label.
A successor may reuse verified sealed evidence through a reviewed resumption
procedure; no such implementation has been added here.

H82 standing agreements withdraw the former B05 exact-file permission request:
the one-line statement-preserving proof-only replacement needs no owner agreement.
Original ReservedNames.lean still matches base because retirement forbids new
proof implementation. The proposed patch and passing additive probes remain
available to the successor. Existing statement/definition/interface/budget/axiom/
exclusion changes still need appropriate owner/H57 handling. H78 requires all
original public generated APIs, without blanket generated exclusions. No shim
was implemented here. Full production old/new generated-API comparison remains
unfinished; isolated inspector fixture differences are recorded, not waived.

Original rendered prompt transcription, full original four-item work queue,
backfill queue and exact1777-entry scope manifest are committed under
`tests/h62/item6/migrate-yul/handoff/`. The original prompt is reconstituted from
the original user thread, with the exact scope string from the authenticated
coordinator ownership input. Its computed SHA differs from the earlier reported
launcher-objective SHA; provenance explicitly separates those two byte streams.
The launcher objective bytes and get_goal are unavailable; no identity claim is
made. Coordinator-local receipt paths remain provenance, not accessible artifacts.

Open obligations for successor:
1. Finish full old exported declaration inventory (261/1774 available), retain all
   generated/public/private evidence and compare exact public shape under H78.
   Census and clean old2143-module wall/RSS baseline already passed.
2. Official v4.35 archive identity/versions are established; adapt Yul with exact
   statement/semantics/budget/axiom preservation. B05 reviewed candidate unapplied.
   Receive/validate required external migrations (Raw, CollisionBound, Scalar.Slice,
   Source.Ctor, Frontend.Checked.Token and SortCheck). New KeySort remains failed.
   B07 optional Bridge dependencies belong migrate-bridge, not intrinsic core.
3. Complete clean new2143-module build using identical settings/cache policy;
   full frozen-interface comparison and meaningful same-policy timing/RSS delta.
   Any regression escalates; >10% STOP. Provisional candidate probe cost increase
   is disclosed, not accepted. Old Horizon665.844s reported for external gate owner.
4. Deliver/replay final root gates, cross-directory compatibility and interface
   disposition. Existing patch/bundle is a partial migration/backfill checkpoint,
   not proof of full success or runtime acceptance.

Backfill completed: lexical scanner/import census, negative scanner/resource/
comparison/interface controls,23 finite String cases with isolated proofs,
source/output-bound reproducible interface tooling and B05 isolated kernel proof.
Backfill unfinished: production new API/case coverage and full clean comparison/
reproduction. No newly unclaimed cleanup has been authorized. Universal parser
equivalence remains an unproved external-owner limitation, not an assigned theorem
or an additional successor obligation from this lane.
No task ownership was taken from producer lanes. No new sorry/axiom/native_decide,
no frozen original statements changed, no budget raised. Kernel fixture proofs
are distinguished from external solc/KeY corpus checks and full compiler gates.

No push: the conditional H71 push authorization itself was not supplied here;
the original no-push restriction remains. No master push, merge, PR or publication.
All work is saved in isolated commits with cumulative patch/bundle and hashes.
Schema-v1 waits are in `tests/h62/item6/migrate-yul/handoff/waits.json`.

Retirement final reviews: finder confirmed prompt/queue/scope/hash integrity and
corrected stale top queue summary. Skeptic confirmed integrity and no active
jobs; clarified external parser equivalence is not an assigned theorem. Exact
H82 retirement source text saved in handoff/h82-retirement-instruction.md.
No Lean reruns or proof changes were made for retirement.

## Resumption milestone: production B05 repair

One proof-only production line changed in Solidity/Yul/ReservedNames.lean:
`reservedNames_count := by decide +kernel`. The definition, both exact theorem
statements, slotnum proof, import and all budgets remain unchanged. H82 standing
agreement applies; no exact-file permission request. No sorry/new axiom/native
shortcut. Generator now reads the immutable starting-commit source via git show,
so historical fixtures remain deterministic after applying the repair.

Evidence directory `/workspace/migrate-yul-artifacts/resume-d96f2406d/` contains
merge-state.json, census.json, post-b05-census.json, production probe reports,
old-production.json/new-production.json (and deterministic gzip raw payloads),
and production-interface-check.json. All bounded probes use the existing guard,
-j1,-M12288,stack131072,LEAN_NUM_THREADS=1,no swap and4GiB estimated reserve.
Original production compile passed old0.754835s/234319872bytes and
new1.258165s/534036480bytes. These non-clean sampled probes are diagnostics,
not a full performance comparison or an accepted regression disposition.

Private production snapshots preserve all3 original names/signatures/metadata,
raw table implementation and slotnum proof. Four declarations on each release:
the added theorem helper is Solidity.Yul.reservedNames_count._proof_1_1.
Old/new production declaration snapshots are equal. Count axioms remain none;
slotnum remains propext. This establishes this module only, not all Yul or H78
public generated API coverage. Earlier snapshot attempts failed due to Lean's
package-root resolution across split library roots; copied the hash-bound
Builtins.olean into each private library and fresh v2 probes passed. Failed
attempts remain recorded, not relabeled.

Current upstream adds Compilation.Artifact and Compilation.CompletionControls,
not present in the original exact scope; they remain read-only. Changed upstream
original sources are Checks.Occurrences,Checks.ScopedSyntax,Checks.WordSyntax.
No baseline mismatch is hidden: full old/new timing comparison needs a common
source tree and identical settings. Existing outside-owned v4.35 dependency
failures and KeySort remain unresolved; no unchanged failing timing gate rerun.

Resumption B05 finder: production signatures/metadata/table/slotnum proof,
axioms, output bindings, immutable-source reproduction and budgets verified;
no findings. Skeptic independently verified the same production evidence,
failed-attempt disposition and timing boundaries; no findings. Neither used Lean
or wrote files. B05 production checkpoint approved; whole queue remains partial.

## Allocation API census and pinned-source inventory partition

Unmodified Solidity/Yul/Compilation/Allocation.lean compiles on official v4.35:
`new-allocation/probe-result.json`, exit0,0.754666s,500707328bytes sampled RSS.
Old/new private snapshots each contain74 declarations; no missing/added names.
The standard comparator exits2 (differences_require_review): eight original
public generated signatures differ. Exact name/kind/universes/visibility/type
ASTs are in `allocation-public-api-records.json` and compressed raw snapshots.
No shim or exclusion is implemented. Four structural changes affect
Frame.noConfusion,Frame.noConfusionType,Slots.noConfusion,Slots.noConfusionType;
both mk.noConfusion signatures also switch P/base/base' from explicit to implicit
and rename h to eq. Both mk.inj differences are hygiene names in current raw types;
they remain reported under H78. IR differences are retained too, not hidden.
This is an unresolved public-API compatibility item for root/live-owner design,
not a passing migration gate. The linearNoConfusionType option only selects the
construction strategy in official source; no flag experiment or budget change
was made to waive these shape differences. Axiom unions match, which alone is
not a signature-preservation proof. Read-only finder and skeptic verified the
74/74 coverage,all8 changes,hashes and limitations; neither ran Lean or wrote.

Independent old API inventory continues from exact base in owned detached view
`/workspace/migrate-yul-baseline`. No commit,branch reset,default branch change
or source proof edit in that view. All original census source hashes verified;
only four copied owned inspection helpers are untracked, byte-identical to the
primary lane. Original private old build cache remains unchanged. Provenance:
`/workspace/migrate-yul-artifacts/resume-d96f2406d/baseline-view.json`.

New deterministic `partition-old-inventory.py` revalidates all261 sealed prefix
summary/raw/gzip/probe/source/helper bindings and versions against the original
census. It produces exactly1513 remaining targets, retaining the full original
source-hash map and graph. This is a coverage partition, not an exclusion. The
original interrupted export manifest is unchanged; its one unsealed raw output
is retained diagnostically and not counted. Reordered-prefix and wrong-census
negative controls both reject before output creation. Actual plan:
`old-inventory-partition-v2/coverage-plan.json`; remaining-census.json is derived
from the original1774-module census, indices261..1773. Final consolidation must
require ordered exact union1774, disjoint fragments, parent hashes and verified
complete snapshots/probes for every module before any full-inventory pass.
Remaining fragment export and consolidation are pending. No full API, timing,
runtime or whole-directory migration acceptance is implied by this partition.

Final partition reviews: finder and skeptic independently verified exact261+1513
coverage, full frozen source map, parent/probe/summary/raw/gzip hashes, detached
base and helper identities, negative controls and no false acceptance. Neither
ran Lean or wrote. No findings. Remaining export/consolidation still required.

## Complete old-inventory checker prepared

`consolidate-old-inventory.py` requires a passing complete suffix and exact
ordered disjoint coverage of all original1774 modules before writing a candidate
result. It rechecks frozen baseline source hashes, parent/census hashes, each
summary/probe/gzip/raw checksum, raw declaration/footer/schema reconstruction,
exact exporter/module/output bindings, old release identity, unchanged resource
helper/driver and helper source identity. Public/private/generated declarations
are retained. Partial validation is running/fail, never a complete inventory pass.
The final result is old persisted-kernel inventory integrity only, explicitly
not cross-version API equivalence, attributes/priority, new build/performance or
runtime acceptance. It must be run through the same bounded driver after the
suffix job completes; no second heavy job is started during export.

Negative controls using the actual running suffix reject incomplete status and
also reject a forged pass label on incomplete coverage, before output creation.
Evidence: resume-d96f2406d/consolidation-negative-control.json and
consolidation-forged-pass-control.json. Full positive consolidation remains
pending until all1513 suffix snapshots are sealed. This tool checkpoint alone
does not finish the original queue or old full-inventory gate.

Consolidation-tool finder and skeptic independently reviewed coverage,source/
artifact/exporter bindings,version checks,negative controls and limited claims;
no findings. Neither ran Lean or wrote. Tool checkpoint reviewed; full positive
consolidation and final inventory gate still pending suffix completion.
The export supervisor was briefly suspended at a probe boundary for this commit;
its active bounded probe was allowed to finish and the same export then resumed.

## Nov7 serializer resource recovery and complete coverage plan

Original suffix export failed after700 sealed modules at
Solidity.Yul.Views.DynamicJournalControls. Old parent manifest and truncated
output remain unchanged. Resource guard stopped it at144.642547487s, sampled
RSS12849807360bytes, availability4289298432bytes below4294967296 reserve; no
passing snapshot was counted. Combined retained coverage was261+700=961.
No unchanged retry, budget increase, source proof edit or omitted declaration.

A separate tests/h62/item6/migrate-yul/ExportInterfacesDag.lean emits schema3
canonical postorder expression DAGs for every type,implementation,proof and
recursor RHS. ExprStructMap uses exact Expr.equal, retaining binder names and
annotations. Canonical JSON node interning preserves literals,universes,let
nondependency flags,projection indices and every expression edge. Only metadata
is erased, exactly as in the original encoder. Free/expression/universe
metavariables reject. The original tree exporter and all sealed sources remain
byte-identical. New representation cannot be compared using old raw tree hashes;
raw encoding-specific hashes are retained, and cross-schema normal comparisons
reject. Control conversion uses a common complete DAG without exponential
expansion. This is external inspection tooling, never a core proof shortcut.

Python expr_dag.py rejects invalid tags/arities/primitives/names/levels,forward
or cyclic refs,wrong roots,duplicates,unreachable nodes and noncanonical order.
interfaces.py requires exact schema/helper binding and validates every Expr
position.47 Python controls pass.22 tree/DAG expression controls per official
release are identical, including all binder kinds,let flags,projections,Unicode,
large naturals and internal metadata. Shared depth64 diamond needs65 nodes.
Initial prototype elaboration errors and an initial parser-indentation regression
were fixed before acceptance; failed diagnostics are retained. The bytecode flag
was moved ahead of dynamic imports per reviewer hygiene feedback.

Matched Allocation control (same old toolchain,view,cache and resources):
74 declarations and144 Expr fields roundtrip exactly, including recursor RHS;
old tree5.793995323s/971530240bytes versus DAG3.020941315s/939442176bytes,
-47.86% wall,-3.30% sampled RSS. This is serializer performance only, not a clean
Lean migration benchmark. History inspected before introducing the separate
encoder; prior speed changes were not undone.

Changed-encoder DynamicJournalControls probe passes with the same -j1,-M12288,
stack131072,16GiB VM cap,no swap,12GiB sampled RSS guard and4GiB reserve:
3.019191437s,1040883712bytes,53 declarations. All31 complete prior diagnostic
rows (62 Expr fields) roundtrip exactly. Failed/truncated old output is retained
and not accepted as coverage. Source proofs and axiom pins are unchanged.

Evidence root `/workspace/migrate-yul-artifacts/resume-2a43bf4fc/`:
expr-control-check.json,python-tests-v2.log,dag-control-roundtrip-timing.json,
dynamic-journal-dag-check.json and source/output-bound probe reports. New helper
copy is frozen in the detached original-base view alongside the original helper;
tracked original sources in that view remain unchanged.

Four-fragment plan explicitly covers261+700+1+812=1774 ordered unique original
modules. First2 incomplete parent manifests contribute only their complete sealed
prefixes; one complete source-bound DAG module is separate; final812 remain a
plain-export fragment. consolidate-fragments.py verifies per-fragment census,
helper/schema/hash provenance and exact global coverage, with no implicit helper
or encoding substitution. Gap,helper/schema mismatch,missing parent hash and
incomplete full coverage controls reject before output creation. A bounded
--prefix-only run verifies all962 available snapshots but returns inventory
statuspartial (not full pass):75.502079s,1846493184bytes,source bindings verified.
The original plan remains immutable; after812 finish, finalize a new plan file
with the final parent checksum, then perform bounded full consolidation.

Read-only finder and skeptic reviewed code,fidelity,53-record recovery,all144
Allocation Expr fields,47 tests,resource bounds and exact fragment coverage;
no blocking findings. Neither ran Lean or wrote. Full1774 consolidation,IR-only
name/type disposition,attributes/priority and all migration gates remain pending.

Remaining812 will use the reviewed schema3 encoder explicitly via export-dag.py,
retaining every expression/declaration with fixed bounds. The schema2 helper
remains unchanged. New four-fragment-plan-dag-tail.json records the changed
transport explicitly (schemas2,2,3,3); earlier plans/probe bindings are immutable.
The exporter reuses the existing bounded driver,sealer and serial checkpoint
logic. No full old/new compiler timing conclusion is drawn from Allocation's
serializer control. Tail performance and resource outcomes remain recorded per
module; no budget increase or omitted type/proof field.

Final finder/skeptic checks approve the explicit812 schema3 exporter and revised
immutable plan; no blocking findings. Final47 Python tests pass in24.988s.
Remaining checksum stays null until the tail completes; no consolidation pass
can be claimed from that pending plan. No reviewer ran Lean or wrote files.

## Completed original old-kernel inventory and second Nov7 rebaseline

All812 DAG tail modules completed. Source-bound complete four-fragment plan is
four-fragment-plan-complete.json; prior partial plans remain immutable. Bounded
consolidate-fragments.py without --prefix-only passes exactly1774 ordered unique
original modules:261+700+1+812. Report complete-old-inventory.json contains55647
persisted declaration records,52406 public records; shared declaration records
are not asserted globally unique. It retains all old kernel types,proof/value
expressions,private/generated records and encoding provenance. IR-only names are
retained in headers; their separate type/visibility disposition remains pending.
This is not attribute/instance-priority validation or new-toolchain compatibility.

Actual checker152.592778158s, sampled peak1799716864bytes, minimum availability
14783451136bytes,exit0,no resource stop,unchanged limits. Original source hashes,
all parent/census/helper/parser/validator hashes and each probe/raw/gzip/summary
binding verified. Report explicitly migration_acceptance=false. Lean4.24.0
commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and Lake5.0.0-src+797c613.
Independent finder/skeptic reviews confirm exact coverage,totals,resource/source
bindings and limited claims; no findings. Neither ran Lean or wrote files.

Coordinator then required origin/master95d1e9cb29dc5a34d1db68af3ca47e47b75e293f.
After in-flight export finished, fetched and verified the reported commit and
7029a97d72bde21abe4b636b8125302debdd65c9 as ancestors; fast-forwarded the clean
assigned branch. Owned task files were byte-identical across this update. No
push,reset,default-branch merge or replacement goal. Original pinned baseline
view/cache remain unchanged. Current source census at95d has1809 Yul modules,
2229 closure modules,35 additions beyond original scope and82 changed original
source hashes. Rebaseline-state evidence is in
/workspace/migrate-yul-artifacts/rebaseline-95d1e9cb2/. Original benchmark and
inventory are historical c6 evidence, not a direct current-tree benchmark.

Original migration remains partial: complete current/new source compatibility,
all generated public interfaces and IR type disposition,new clean build,common
baseline timing/RSS and final root gates remain. Known external Raw/Hash/Scalar/
Frontend/SortCheck failures have unchanged original source files; Source.Ctor
has a producer proof update and needs renewed dependency validation. No new
original declaration,statement,budget,axiom or exclusion was changed by this
serializer/inventory work. Kernel inventory integrity is distinct from external
compiler/KeY/solc validation and full migration acceptance.


## Extra compiler-name accounting — historical header correction

Deterministic census-ir-names.py consumes the completed, previously reviewed
old-kernel inventory and verifies every referenced summary hash. It retains all
32734 extraConstNames across1774 modules (1356 with extra names), including610
records in310 modules which ALSO occur in that module's kernel declarations.
All32734 compiler names are globally distinct in this dataset. The historical
header label "IR-only names; not kernel ConstantInfo declarations" was too
narrow: extra compiler names can overlap kernel declarations. This correction
supersedes that label's interpretation in prior prose, not the immutable raw
headers or their source bindings. No name was omitted from either inventory.

old-compiler-name-census.json retains exact structured names,per-module order,
per-name module membership and explicit kernel overlaps. IR type and public
visibility are null for every name; no public/private inference is made from
name spelling. This accounts for names only, not IR signatures or attributes.
It derives from a previously verified/hash-bound inventory rather than replaying
the full raw/probe validation. It has migration_acceptance=false,empty shims,
and no exclusions or waivers. Generator and name-validator hashes are recorded.

Five accounting controls pass: overlap retained,summary tampering rejected,
incomplete inventory rejected,duplicate name rejected,malformed Name rejected.
Initial local attempts exposed the overlap and a test path typo; both corrected
before acceptance. Finder and skeptic independently reproduce all counts and
bindings and report no findings. Neither ran Lean or wrote files.

This increment contains only additive external census/test tooling and docs.
No original Lean declaration,statement,definition body,budget,axiom or exclusion
changed. Original old-kernel inventory and this compiler-name accounting do not
resolve H78 generated API shims,IR types/visibility/attributes,new builds,clean
common-source performance comparison,KeySort35 or root runtime gates.


## Nov7 4f0a2d6a rebaseline and compiler-signature sample

Fetched and fast-forwarded the clean assigned branch onto coordinator-approved
4f0a2d6abe3a920d8c5a20c8c06d373a1014824d; b8a940f3e is an ancestor. Read the
updated AGENTS audit reference. No source reset,default merge,push or new goal.
Current census has1811 Yul modules and2234 Yul-closure targets (2237
source-union modules including KeySort-only inputs). Census and rebaseline state
are off Git in resume-4f0a2d6ab. Original c6
benchmark/inventory remain historical and are not current-tree acceptance.

Additive external ExportCompilerSignatures.lean records every extraConstNames
entry, optional IR lookup, parameter indices/borrow flags/types,result type and
compiler visibility query separately from kernel types. Composite IR types have
structured tags; terminal types retain exact compiler Repr text. Missing IR is
retained as null, never silently dropped. Visibility query is an observation,
not independently established public API classification; attribute coverage is
still pending. No core imports or intrinsic representations changed.

Source/output-bound Allocation probes pass on original4.24 and official4.35.
Old20 compiler entries,new18: Frame.ctorIdx._boxed and Slots.ctorIdx._boxed are
absent from the new extraConstNames snapshot. Direct new IR lookup of those
old-only names was not performed. Exact old IR signatures and unobserved new
signature nulls are in owner-requests.json for migrate-root-gate via coordinator. All18common IR
signatures match. This does not discharge the previous eight kernel public API
changes,prove these compiler entries private,implement a shim or authorize an
exclusion. Implemented shims remain empty; all compatibility gates stay open.

Performance STOP: old probe1.764966317s/912093184bytes sampled RSS; new
2.520661854s/2003578880bytes. Observed+42.8164percent wall,+119.6682percent RSS.
Do not expand or rerun unchanged newIR probes. This is compiler-inspection/import
runtime,not the required clean migration-build comparison; original whole-build
performance gate remains pending. Both used unchanged bounded policy,j1,12GiB
sampled RSS limit,4GiB reserve,no swap. Initial diagnostic failures and absent
optional private artifact preflight are preserved; only v4 probes accepted.
Seven transport controls pass, including a found nested struct/union signature,
identity mismatch and malformed IR rejection; null IR,counts,truncation and acceptance claims
remain explicit. No Lean MCP tools were exposed; bounded per-file CLI used.

Independent portability backfill removes the fixed VM path from build.py's
KeY rules input. New key invocations require --key-rules KEY_RULES_FILE. Missing
or nonexistent rules fail before artifact writes or Lean jobs; negative CLI
control passes. Historical commands retain their original paths as provenance;
new reusable examples should use --root CHECKOUT --toolchain TOOLCHAIN
--artifacts ARTIFACTS --census CENSUS --label FRESH_LABEL --kind key --clean
--key-rules KEY_RULES_FILE. The frozen baseline driver and historical manifests
are unchanged. No known KeySort failure or timing STOP was rerun.

Finder and skeptic independently reproduced signatures,missing names,source and
output bindings,STOP metrics and input preflight; no blocking findings. Skeptic
suggested nested found-signature controls; added and passing. Neither used Lean
or wrote files. No production Lean declaration,frozen statement,definition body,
proof budget,axiom or exclusion changed. Remaining original queue/backfill and
six dependency/API waits stay open; performance STOP is an additional typed wait.

Skeptic corrected the initial phrase "missing compiler-table entries": observed
absence is from the new extraConstNames enumeration,not a failed direct new IR
lookup for the old-only names. Owner records now label that boundary explicitly.
No additional probe was run; performance STOP remains. Full60 Python tests pass
in25.161s. Finder reports no findings; skeptic's wording finding is resolved.


## Nov7 7683091e rebaseline and old-only compiler inventory supervisor

Fetched and fast-forwarded the clean assigned branch to coordinator-approved
7683091e7c35d265b3b76fdf2a93d0197ce9f556. Prior ebec6cb45 is verified ancestral.
Original c6 source view/cache and historical source-bound inspectors are intact.
No new-toolchain IR run,default merge,push,goal reset or completion.

Additive ExportCompilerSignaturesBatch.lean preserves the frozen single-module
inspector; only namespace/entry point differs. Supervisor deliberately uses
ONE module per bounded process. Contemporaneous original4.24 Allocation control:
single2.267930335s/885678080bytes RSS; one-job batch1.764923368s/882434048bytes.
All20 output records are byte-identical. This is old-inspector transport only,
not a multi-module memory result,new-toolchain acceptance or clean-build speed
claim. Existing4.35IR wall/RSS STOP remains unchanged; this exporter rejects
other tool versions and does not retry that affected lane.

compiler-signatures-batch.py validates bound helper/job files, exact output
coverage,fresh output hashes/sizes and record protocol before sealing. New
export-old-compiler-signatures.py ties original1774-module order and all32734
names to completed old kernel-inventory summaries. It will run1356 nonempty
modules serially. The418 empty headers derive from verified original summaries
with explicit ir_query_performed=false; no fabricated Lean query or name waiver.
Null missing IR remains visible; compiler public flags are observations only.
Full old IR extraction is pending at this checkpoint, not already accepted.

Both reviewers found a preflight gap before launch: redundant zero counts could
skip a nonempty header. Fixed by deriving/checking counts against verified
header counts/exact lists, binding each summary path/hash to its kernel-inventory
row and checking original order/totals. Four negative/plan controls include a
contradictoryzero+totalzero case and identical-byte wrong-summary substitution.
Finder/skeptic read-only revalidation confirms1774 modules,32734 names,418 truly
empty headers; no remaining prelaunch findings. Neither ran Lean or wrote files.
Completion additionally rechecks all headers,inputs,original HEAD/source hashes
and exact total before status=pass; interrupted/failed exports retain sealed
prefixes and remain fail. No proof budget,statement,definition body,axiom,
interface signature or exclusion changes. Bulk outputs stay off Git; deterministic
inspectors/validators/supervisor and controls are committed in this lane.


## Completed original old compiler-observation inventory

Full old-only collection passes all1774 original ordered unique modules:
1356 supervised one-module queries plus418 explicitly derived empty headers.
All32734 original extra compiler names have observed IR signatures; ir_missing=0.
No original name was dropped or waived. Manifest is full-old-compiler/manifest.json
under resume-7683091e7. Historical single-module inspector and all previously
bound helper/parser files remain byte-identical; old c6 source view remains intact.

Bounded verify-old-compiler-inventory.py passes exact original census SHA,corpus
size,all original summary/name identities,all1356 job/probe/raw/sealed-report
bindings,gzip reconstruction,uniform old toolchain versions and final unchanged
input hashes. Actual exit0,6.045821229s,245600256bytes sampled RSS,minavailable
16302698496bytes,no resource stop. complete-old-compiler-inventory.json explicitly
migration_acceptance=false. This validates old observation integrity,not public
API classification,attribute/priority equivalence,new compatibility or semantics.
Terminal IR types retain compiler Repr text; this validator is not an IR checker.

All1356 collection probes exit0 without resource stops or swap. Sum of individual
probe wall times2775.679068528s (NOT end-to-end or migration-build wall),maximum
sampled RSS2083274752bytes,minavailable15066079232bytes. Uniform original resource
policy v3,unchanged12GiB sampled RSS cap/4GiB reserve,explicit-j1/one Lean thread.
Source and actual Lean4.24/Lake versions are bound throughout. No4.35IR rerun;
prior+42.8164percent wall/+119.6682percent RSS performance STOP remains unchanged.

Independent finder and skeptic approve the full dataset with no findings. They
verify full module/name totals,all summary hashes/source-output bindings and
bounded verification evidence; skeptic additionally re-seals first/middle/last
queries with gzip checks. Neither uses Lean or writes files. The new negative
verifier control rejects incomplete results and a substituted corpus before
output; exact original pinned census is required.

Current source census at the7683091e rebaseline has1811Yul modules/2234Yul-closure
targets/2237union sources. There are83 changed original sources,so c6 clean-build
figures remain historical. dependency-report.py records137 direct boundary edges
for original1774assigned modules to58 distinct providers,unchanged edge set.
It preserves providers outside the project source census with null source hashes
rather than dropping them; initial null-provider handling failure was fixed
before report acceptance. All144 current boundary edges include7 outside the
original importer scope. Current37new Yul modules remain read-only observations,
not a scope takeover. Static import/source integrity is not elaborated API proof.

Full original queue stays unfinished: old public visibility/attributes; complete
new generated API compatibility and shims (including eight Allocation kernel
differences and two old-only enumeration entries); all assigned new builds;
common-source clean performance comparison;KeySort35/root gates. Original old
KeySort pass377/131/131 and new Parser String API failure remain historical gate
evidence. No RUNTIME_GATE_PASS. No new production Lean declaration,statement,
definition body,proof budget,axiom or exclusion changed by this tooling work.

Final finder/skeptic reviews of the dependency generator,resource aggregates and
completion wording report no findings. All66 Python tests pass in24.879s.
The current committed handoff section is mirrored in
`tests/h62/item6/migrate-yul/handoff/nov7-old-compiler-completion.md`; final
head-bound artifact state records the actual commit,patch/bundle/evidence hashes
and all original unfinished queue obligations. No push authorization delivered.


## Nov7 d93f6839 rebaseline and focused old declaration metadata

Fetched and fast-forwarded the clean assigned branch to
`d93f6839c613468610ea488356b174cd183e3772`; the complete old-inventory commits
are verified ancestors. The known Syntax.Raw, Hash.CollisionBound,
Backend.Scalar.Slice, Frontend.Checked.Token and SortCheck.Parser failure sources
are unchanged. No unchanged failure or new-toolchain IR performance STOP was
rerun. The original c6 view/cache and all historical inspectors remain intact.

Additive `ExportDeclarationMetadata.lean` observes selected old persisted
families: class entries and out-parameter positions, ordered ordinary/scoped
instance registrations with priority and synthesis order, default instances,
and per-declaration private/protected/class/effective-instance fields. It is not
a generic attribute inventory or public API classifier. Instance expression
Repr text is retained without claiming to typecheck it. No core imports changed.

A fixture exposes an important loader boundary. `importModules` defaults to
`loadExts=false`; aggregate extension state then has initial values. Early
uninitialized trials were rejected. The final observer follows Lean's documented
`enableInitializersExecution` then `loadExts=true` path. That API requires unsafe
IO, confined to this external test inspector's run/main; it supplies no model
proof, axiom or compatibility shortcut. Official old source quotations/hashes
are in `import-api-provenance.json`. Existing constant/raw-IR inspectors were
not changed or silently reinterpreted as attribute classifiers.

The accepted fixture compiles and inspects on actual Lean4.24. It retains18
declarations,1class,4persisted instances and1default. Global priorities17/63,
private priority11 and scoped priority41 are exact; the scoped registration is
retained but inactive without opening its namespace. A local97 declaration
remains while its local attribute does not persist. Default priority7 and
protected/private/class flags match controls. Final inspection exit0,
5.560865639s,2113134592bytes sampled RSS; unchanged limits and no resource stop.
Rejected compile/uninitialized prototypes remain diagnostic evidence only.

The original Allocation sample passes74declarations with exact old kernel
name/private-marker coverage,0class entries,2sizeOf instances at priority1000,
and0defaults. Actual exit0,2.016755444s,780693504bytes sampled RSS. This is one
assigned module, not a completed metadata census or a migration speed comparison.
Fixture controls link the compiled olean hash to the inspection input; both
outputs are source/probe/output-bound and reject partial,uninitialized,count-
mismatched and falsely accepted snapshots. All67Python tests pass in25.521s.
Finder and skeptic independently re-seal both reports and approve controls and
unsafe-IO boundaries with no findings; neither ran Lean or wrote files.

This checkpoint adds only test/tooling code and metadata observations. No
production Lean statement,definition body,proof budget,axiom,interface or
exclusion changed. The full original queue remains: broad compatibility evidence,
generated public API shims,new builds,common-source clean timings,KeySort35 and
root gates. Earlier Allocation kernel/old-only enumeration differences remain
unwaived; no shims implemented. No4.35run occurred in this checkpoint, and its
existing performance STOP remains. Bulk evidence is off Git in
`resume-d93f6839c`; deterministic inspector/fixture/validator/controls are in Git.

Current d93f6839 source census remains1811Yul/2234closure/2237union modules;
85original sources now differ from c6. Static dependency evidence is refreshed
without treating inherited producer changes as migration acceptance. The full
original rendered assignment,queue,exact scope and provenance remain committed
and are included in the authenticated patch/bundle handoff. All prior completed
old inventories are preserved. No H71 push authorization was delivered.
