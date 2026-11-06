# H62 item 6: Language migration (blocked)

Owner: `solidity-h62-6-20261106/migrate-language`. This is an isolated migration
overlay, with no transfer of live producer ownership. Repository
`/workspace/migrate-language`, branch `codex/solidity-h62-6-20261106/migrate-language`,
pinned base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.

## State and exact continuation

Checkpoint 1 census and clean old build are complete, subject to the independent
review resolutions below. Checkpoint 2 toolchain identity is established, but
production adaptation is blocked. Checkpoint 3 fails on unchanged FixedPoint;
there is no valid whole-directory timing delta. Checkpoint 4 has a reviewable
partial tooling/evidence handoff only. The assignment is NOT complete.

Typed blocker `OWNER-EXACT-FILE-ACK`: the mandated `relay.sh` is absent from the
checkout and attached input directory. Exact-file acknowledgement from the live
producer/coordinator is required before editing any of the eight existing files.
The asynchronous coordinator request identifies all eight assigned files and the
first FixedPoint errors (152, 170, 184). Scope options: provide the relay path so
requests can be sent, or relay the live owners' exact-file acknowledgement. No
absence of response is treated as permission. The isolated-branch authorization
does not itself waive this explicit coordination requirement.

After acknowledgement: adapt FixedPoint proofs first using the isolated fixture's
staged simplification where applicable, recheck per file, then Laws, Abi,
Literals, Storage and Conformance. Do not assume the fixture fixes all failures.
The two catalog modules already compile on the new release. Preserve all names,
types, meanings and budgets, retain module/source census coverage, and regenerate
clean matched timing runs. Escalate any regression and STOP above 10%. Complete
all affected-consumer/final gates and independent reviews before final acceptance.
Do not edit the root toolchain pin, generated module roots, central maps or axiom
pins. Export patch/bundle/checksums for migrate-root-gate; never push or merge.

## Setup, versions and fixed resources

The initial checkout `/workspace/solidity-lean` was clean on `work` at
`6cf853aea`; it remains intact. `git fetch origin refs/heads/master:refs/remotes/origin/master`
and `git fetch origin c6f550e281a7e5affa9a99bc2cdaed556dec00e4` succeeded.
`git merge-base --is-ancestor BASE origin/master` exited 0 (observed remote tip
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`). The assigned worktree was created
at the exact base; no existing work was reset or discarded.

Old: Lean 4.24.0 release, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake `5.0.0-src+797c613` (Lean 4.24.0).
New: official Lean 4.35.0 release, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb` (Lean 4.35.0).
Archive `/workspace/migration-toolchains/lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`,
exactly matching `/workspace/h62-coordinator-inputs/toolchain-pin.json`.
All five coordinator input checksums were independently verified.

VM: cgroup memory cap 16 GiB, CPU quota 4 CPUs, no configured swap and zero swap
usage. Each serial Lean worker uses explicit `-j1 -M8192 --tstack=131072`,
`LEAN_NUM_THREADS=1`. A 100ms sampled aggregate process-group RSS guard stops at
12 GiB, and a cgroup-aware min(host available, cap minus current usage) guard
retains 4 GiB headroom. This is a sampled monitor plus Lean's allocator limit,
not a dedicated 12GiB hard cgroup. No systemd invocation or other worker kill.
All checks acquired the repository writer lock; no Lean MCP is exposed.

Private absolute toolchain paths and private TOML builds keep the tracked
`lean-toolchain` unchanged. Each clean run has a fresh build and cache directory,
`enableArtifactCache=false` and `--no-cache`. No v4.24 per-master cache was used.
OS page caches were warm/uncontrolled for both runs; clean refers to project
artifacts, not an OS cache drop. Module checks target `:olean`, with Lake also
emitting its normal intermediate C/ilean; these are elaboration/kernel checks,
not the full executable/default-target gate. All eight original files remain
byte-identical to BASE, including statements, cases, observations and budgets.

## Census, interfaces and dependencies

`python3 scripts/h62/item6/migrate-language/census.py --require-unchanged`
exits 0. Saved JSON: `/workspace/migrate-language-evidence/census-base.json`.
It freezes all eight source files by SHA256 and checks the base file inventory.
Its 389 declaration-line rows are an audit index, not a Lean parser. Full byte
hashes preserve all original declarations and anonymous cases, regardless of
scanner recognition. Seven internal import edges and only `Lean.Data.Name`
external to Language; no outside-project directory dependency blocks elaboration.

Thirteen baseline production/root consumer import edges include the eight generated-root imports
in `Solidity.lean`, plus Frontend/Admission/RootObservations, Frontend/Source,
Frontend/Static/Standalone, Lowering/P8/FrozenInterface and
Semantics/Nondeterminism/ForkAgreement. These owner directories and the generated
root are read only. Root-gate must validate their migrated downstream closure.
The additive Interfaces test imports three Language modules, yielding sixteen total
tracked direct consumer edges after staging. No new production module or registration
fragment is needed for the test helpers.

`Interfaces.lean` captures all 1,721 baseline constants belonging to Language,
including generated names, printing elaborated types and axiom dependencies.
The baseline audit exits 0 and rejects any `sorryAx` dependency. Its ~1MB transcript
is off Git at `/workspace/migrate-language-evidence/interface-old/fixture.log`.
The transcript SHA256 is recorded in the external manifest. This is an elaborated
baseline type snapshot; source hashes are separate source-preservation evidence.
New-version interfaces and their comparison remain pending until migration builds.
Neither identical source hashes nor a baseline transcript establishes new-toolchain
kernel/API equivalence by itself.

## Gates and decisive evidence

All paths below are under `/workspace/migrate-language-evidence/`.
The reproducible command prefix is
`python3 scripts/h62/item6/migrate-language/measure.py TOOLCHAIN RUN_DIR`.
Each results.json records the exact absolute commands, exits, wall times and
peak sampled aggregate RSS; each module has a corresponding complete log.

| Command suffix / check | Outcome | Evidence |
|---|---|---|
| old toolchain, `old-clean-final` | PASS all eight | `old-clean-final/results.json` |
| new toolchain, `new-clean-final` | FAIL FixedPoint | `new-clean-final/FixedPoint.log` |
| new toolchain, catalog targets independently | PASS Features, FeatureInfo | `catalog-new/results.json` |
| KeySort prerequisite, both versions | PASS `Built Solidity.KeySort` | respective `keysort.log` |
| `--check-file tests/h62/item6/migrate-language/Interfaces.lean --lean-path /workspace/migrate-language-evidence/old-clean-final/build/lib/lean` on old | PASS 1,721 constants | `interface-old/fixture.log` |
| `--check-file tests/h62/item6/migrate-language/DecideFixture.lean` on each | PASS, empty diagnostic logs | `fixture-old-final/`, `fixture-new-final/` |
| `python3 tests/h62/item6/migrate-language/test_census.py` | PASS mutation/deletion/addition/root controls | `census-controls.log` |
| affected consumer closure / full `./run-lean.sh` | PENDING, known upstream Language failure | no success claimed |
| new interface/axiom audit and timing delta | PENDING | cannot compare failed build with passing baseline |

Clean old Language-only wall sum: **45.30031436 seconds** (8 serial module
invocations, excludes versions and KeySort); peak sampled aggregate RSS
**879,906,816 bytes**. The initial pre-review old run also passed, but the
corrected guard's `old-clean-final` is the accepted baseline. Matched old/new
harness source is saved as `measure-matched.py`, with identical harness hashes
in their run directories. New FixedPoint exits 1 after 2.0160 seconds; that is
failure latency, NOT a speed improvement. No RUNTIME_GATE_PASS is declared.

First errors: FixedPoint 152/170 generalization fails after one-stage unfolding
leaves `decide` hypotheses; 184 expects `0 ≤ v` but gets `decide (0 ≤ v)=true`.
Further errors include implicit conversion, integer conversion and ABI roundtrip
proofs. Compiler-generated `sorry` warnings in the failed elaboration are error
recovery output, not authored source admits and not accepted proof artifacts.
No original theorem, premise, exclusion or observation was edited or weakened.
No new axiom, sorry, native_decide or heartbeat increase was added.

## Backfill and proof boundaries

`DecideFixture.lean` isolates the intrinsic signed bounds and range proof.
Simplifying Boolean/decide propositions before unfolding the bounds passes both
releases with the same statement, no new options and no extra budget. A generator
`negative-control.py OUTPUT` reconstructs the one-stage source to distinguish
old pass/new failure. This is local proof compatibility evidence, not a repair or
proof of acceptance of the six fixed-point production modules. Existing
Conformance's original decided cases passed only on the old full Language build.
The census controls run on a temporary Git repository and never change originals.
No external Solidity/EVM conformance test or new semantic claim is asserted.

## Independent reviews

Read-only finder and skeptic used no Lean server and made no edits. Finder found
F1 missing root import edges, F2 deletion escaping the inventory gate, F3 host-only
reserve, and F4 sampled-RSS qualification. Skeptic independently confirmed F1/F3
and warned against equating source hashes with elaborated interfaces. F1/F2/F3
are fixed; negative controls cover frozen source mutation/deletion/addition and
root imports. F4 is explicitly qualified as sampled RSS; baseline elaborated
interfaces are captured separately. Follow-up finder and skeptic reviews confirm F1–F3 are fixed, F4 is accurately
qualified, matched harness hashes and measurements agree, and no success is
claimed from the failed new build. Finder additionally caught the three staged
test-helper consumer edges; the final census is regenerated after staging and
the production/test counts are distinguished above. Reviews used no Lean/server
and made no edits. Artifact verification is recorded in the external evidence handoff.

## Handoff artifacts

External handoff `/workspace/migrate-language-evidence/HANDOFF.md` records the
committed head, base, outstanding obligations and artifact hashes. Exported
patch `/workspace/migrate-language-evidence/original.patch`, bundle
`/workspace/migrate-language-evidence/migration.bundle`, checksum manifest
`/workspace/migrate-language-evidence/SHA256SUMS`. Bulk transcripts/builds remain
off Git. The patch contains additive scoped tooling/tests/documentation only;
there is no production migration patch yet. No push, merge, freeze announcement,
pre-gate or master changes have occurred.
