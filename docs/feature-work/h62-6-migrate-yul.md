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
