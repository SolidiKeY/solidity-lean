# H62/H63 migrate-yul migration overlay

Owner: solidity-h62-6-20261106/migrate-yul. Repository: `/workspace/migrate-yul`.
Branch: `codex/solidity-h62-6-20261106/migrate-yul`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The original `/workspace/solidity-lean` checkout and its `work` branch are preserved.
`git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4` succeeded;
`git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master`
returned 0. No assigned remote branch existed when inspected.

## Queue status

1. **Partial:** source/import census and reproduction tooling prepared; full clean
   v4.24.0 build measurement still required. Census: 1,774 Yul modules, 2,143
   source modules in their dependency closure. The source census also lists
   reverse consumers, including the separate Bridge package, and lexical
   declarations, anonymous examples, and acceptance commands. It is not an
   elaborated type/API audit or a proof of exhaustive Lean syntax recognition.
2. **Blocked:** exact official v4.35.0 archive downloaded and SHA256 verified;
   existing out-of-scope KeySort parser does not compile. No source migration
   edits authorized by exact-file owner replies have been made.
3. **Pending:** all assigned modules on v4.35.0, clean before/after wall/RSS
   measurements and regression disposition. No timing delta exists yet.
4. **Partial:** reviewable tooling patch, source hashes and dependency census
   available; final migrated patch/API hashes and root-gate acceptance pending.

The persistent goal remains unfinished. No runtime gate pass, master cut-over,
freeze, merge, push, PR, or deployment is claimed. No H55 work was undertaken.

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
